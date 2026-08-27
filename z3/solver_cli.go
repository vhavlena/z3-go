//go:build cgo
// +build cgo

package z3

/*
#include <stdlib.h>
#include "z3.h"
*/
import "C"

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"strings"
	"time"
	"unicode"
)

// SolverCLI computes Check results by running the actual "z3" executable as
// a subprocess instead of going through Z3's C API, while otherwise
// presenting the same shape as Solver: Assert, SetOption, Push/Pop, Check,
// Model. NewSolver and NewSimpleSolver's doc comments describe formulas
// whose solving time is sensitive to which internal construction/
// search-order Z3's library API picks for a given platform/build; the z3
// executable's own default behavior does not always match either one.
// SolverCLI lets callers reach for that directly when that is the behavior
// they actually need to reproduce.
//
// Model() is reconstructed, not returned by the subprocess directly, and
// leans on Z3 itself rather than a hand-rolled SMT-LIB model parser: after a
// sat result, SolverCLI finds the currently declared 0-ary (constant)
// symbols natively (walking the real ASTs via Z3_solver_get_assertions,
// without the ref-counting AST.Walk/AST.Child helpers - see liveSymbols),
// asks the subprocess for their values via SMT-LIB's (get-value ...), and
// feeds those values - unparsed, exactly as z3 printed them - straight into
// Z3's own Z3_parse_smtlib2_string as equality assertions against a fresh,
// trivial native solver, which is what actually interprets them into a
// genuine *Model. The only custom code involved is a small top-level-paren
// splitter that locates the boundaries between values in the subprocess's
// response text (needed because that response isn't itself valid SMT-LIB
// command syntax Z3's parser can consume directly) - it never interprets
// what a value means. Function symbols with real arity are not
// reconstructed and will simply be absent from the resulting model; when
// that happens ModelIncomplete reports true so callers can detect it rather
// than silently trusting a partial model. If reconstruction fails for any
// reason, Model() returns nil, the same as it would for a Solver that
// hasn't found a model.
//
// SolverCLI is not safe for concurrent use by multiple goroutines.
type SolverCLI struct {
	ctx    *Context
	path   string
	mirror *Solver // tracks declarations/assertions for constant discovery only
	// options are relayed to the subprocess script but never applied to
	// mirror, since mirror is never itself checked against the real formula.
	options []string

	// rawSegments holds the script text actually sent to the z3 subprocess,
	// in the form each assertion was originally given: AssertSMTLIB2String
	// and AssertSMTLIB2File segments are kept verbatim, and Assert(AST)
	// segments are individually printed. This is deliberately not the same
	// as mirror's Z3_solver_to_string output: parsing text into mirror via
	// Z3's C API and reprinting it does not preserve define-fun structure
	// sharing (macros are inlined at parse time and never reconstructed),
	// which has been observed to turn formulas the z3 binary solves
	// instantly on the original text into ones that take orders of
	// magnitude longer when reprinted. Sending rawSegments instead keeps
	// SolverCLI's whole premise intact: reproducing the z3 executable's own
	// default behavior on the formula as originally written.
	rawSegments []string
	// scopeStack records len(rawSegments) at each Push, mirroring how
	// mirror tracks its own scopes, so Pop can drop exactly the raw
	// segments asserted since the corresponding Push.
	scopeStack []int

	// astDeclNames collects the name of every uninterpreted symbol ever
	// passed to Assert(AST), across all scopes. Unlike AssertSMTLIB2String/
	// File, whose text already carries its own declare-fun commands,
	// Assert(AST) only ever prints the assertion term itself (see rawSegments'
	// doc comment on why reprinting a full solver dump instead isn't safe),
	// so the subprocess - a brand-new z3 process that has seen none of
	// mirror's declarations - would otherwise be asked to assert a formula
	// over undeclared symbols. CheckContext cross-references this set
	// against what's actually live in mirror right now (liveSymbols) and
	// synthesizes "(declare-fun ...)" commands for the overlap; this needs
	// no separate Push/Pop bookkeeping of its own because mirror's own scope
	// tracking already decides what's live, and a name popped out of mirror
	// simply stops appearing there even though it stays in this set.
	astDeclNames map[string]bool

	lastModel        *Model
	lastModelBuilt   bool // whether lastModel has been (attempted to be) reconstructed for the current sat result
	lastDeclScript   string
	lastGetValueOut  string
	lastReason       string
	lastModelPartial bool
}

// NewSolverCLI creates a SolverCLI attached to ctx that invokes "z3"
// resolved from PATH.
func (ctx *Context) NewSolverCLI() *SolverCLI {
	return ctx.NewSolverCLIPath("z3")
}

// NewSolverCLIPath creates a SolverCLI attached to ctx that invokes the z3
// executable at the given path (a bare name such as "z3" is resolved via
// PATH at Check time).
func (ctx *Context) NewSolverCLIPath(path string) *SolverCLI {
	return &SolverCLI{ctx: ctx, path: path, mirror: ctx.NewSimpleSolver()}
}

// Assert adds a constraint, mirroring Solver.Assert. The AST must have been
// created in the same context as the solver.
func (s *SolverCLI) Assert(a AST) {
	s.mirror.Assert(a)
	s.recordASTDeclNames(a)
	s.rawSegments = append(s.rawSegments, fmt.Sprintf("(assert %s)", a.String()))
}

// recordASTDeclNames walks a's subtree collecting the name of every
// uninterpreted function/constant symbol it uses into s.astDeclNames (see
// that field's doc comment), so CheckContext knows to synthesize a
// declaration for it. This is a raw cgo walk rather than AST.Walk/AST.Child
// for the same ref-counting reason liveSymbols uses one (see its doc
// comment): a's own children are already kept alive by a for the duration
// of this synchronous read-only walk.
func (s *SolverCLI) recordASTDeclNames(a AST) {
	if a.a == nil {
		return
	}
	if s.astDeclNames == nil {
		s.astDeclNames = make(map[string]bool)
	}
	stack := []C.Z3_ast{a.a}
	for len(stack) > 0 {
		node := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if node == nil || !bool(C.Z3_is_app(s.ctx.c, node)) {
			continue
		}
		app := C.Z3_to_app(s.ctx.c, node)
		numArgs := int(C.Z3_get_app_num_args(s.ctx.c, app))
		decl := C.Z3_get_app_decl(s.ctx.c, app)
		if C.Z3_get_decl_kind(s.ctx.c, decl) == C.Z3_OP_UNINTERPRETED {
			if name := symbolToString(s.ctx, C.Z3_get_decl_name(s.ctx.c, decl)); name != "" {
				s.astDeclNames[name] = true
			}
		}
		for i := 0; i < numArgs; i++ {
			stack = append(stack, C.Z3_get_app_arg(s.ctx.c, app, C.uint(i)))
		}
	}
}

// AssertSMTLIB2String parses an SMT-LIB2 string and asserts the resulting
// commands, mirroring Solver.AssertSMTLIB2String. The original input text is
// also kept verbatim (see rawSegments) and is what actually gets sent to the
// z3 subprocess on Check.
func (s *SolverCLI) AssertSMTLIB2String(input string) error {
	if err := s.mirror.AssertSMTLIB2String(input); err != nil {
		return err
	}
	s.rawSegments = append(s.rawSegments, stripControlCommands(input))
	return nil
}

// AssertSMTLIB2File mirrors Solver.AssertSMTLIB2File. The file's contents are
// also kept verbatim (see rawSegments) and are what actually get sent to the
// z3 subprocess on Check.
func (s *SolverCLI) AssertSMTLIB2File(path string) error {
	if err := s.mirror.AssertSMTLIB2File(path); err != nil {
		return err
	}
	content, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	s.rawSegments = append(s.rawSegments, stripControlCommands(string(content)))
	return nil
}

// SetOption records an SMT-LIB "(set-option :name value)" command to run
// ahead of the script on every Check. Unlike Solver.SetOption there is no
// shared process/global state for this to leak into: every Check spawns a
// brand-new z3 subprocess with its own memory.
func (s *SolverCLI) SetOption(name string, value any) error {
	var valStr string
	switch v := value.(type) {
	case string:
		valStr = v
	case bool:
		if v {
			valStr = "true"
		} else {
			valStr = "false"
		}
	case int, int32, int64, uint, uint32, uint64:
		valStr = fmt.Sprintf("%d", v)
	case float32, float64:
		valStr = fmt.Sprintf("%v", v)
	default:
		return fmt.Errorf("unsupported option value type %T", v)
	}
	s.options = append(s.options, fmt.Sprintf("(set-option :%s %s)", name, valStr))
	return nil
}

// Push creates a new solver scope, mirroring Solver.Push.
func (s *SolverCLI) Push() {
	s.mirror.Push()
	s.scopeStack = append(s.scopeStack, len(s.rawSegments))
}

// Pop removes solver scopes, mirroring Solver.Pop.
func (s *SolverCLI) Pop(n uint) {
	s.mirror.Pop(n)
	for i := uint(0); i < n && len(s.scopeStack) > 0; i++ {
		mark := s.scopeStack[len(s.scopeStack)-1]
		s.scopeStack = s.scopeStack[:len(s.scopeStack)-1]
		s.rawSegments = s.rawSegments[:mark]
	}
}

// Close releases the resources backing this solver (including its
// last-computed Model, if any). Safe to call multiple times.
func (s *SolverCLI) Close() {
	if s == nil {
		return
	}
	if s.lastModel != nil {
		s.lastModel.Close()
		s.lastModel = nil
	}
	if s.mirror != nil {
		s.mirror.Close()
	}
}

func (s *SolverCLI) resetLastModelState() {
	if s.lastModel != nil {
		s.lastModel.Close()
		s.lastModel = nil
	}
	s.lastModelBuilt = false
	s.lastDeclScript = ""
	s.lastGetValueOut = ""
}

// Check runs the accumulated assertions through the z3 executable, mirroring
// Solver.Check's signature. It is equivalent to CheckContext(context.Background(), 0).
func (s *SolverCLI) Check() (CheckResult, error) {
	return s.CheckContext(context.Background(), 0)
}

// ReasonUnknown returns the z3 subprocess's own reason-unknown text from the
// most recent Check, or an empty string if unavailable.
func (s *SolverCLI) ReasonUnknown() string {
	return s.lastReason
}

// liveSymbols walks the real ASTs via Z3_solver_get_assertions directly with
// raw cgo calls rather than through AST.Walk/AST.Child: those helpers call
// Z3_inc_ref on every visited child with no matching Z3_dec_ref anywhere,
// which is fine for their existing single-shot callers but would leak an
// unbounded number of Z3-internal references here, since CheckContext calls
// this on every single Check (including repeated Checks around Push/Pop). A
// child AST is already kept alive by its parent's own internal
// representation for the duration of this synchronous, read-only walk, so no
// inc_ref is needed at all.
//
// It walks mirror's currently asserted formulas (respecting
// whatever Push/Pop scope mirror is in right now) collecting: names, the
// 0-ary constants eligible for "(get-value ...)"; hasArityFuncs, whether any
// uninterpreted application with real arity (whose value this package cannot
// reconstruct into a model, see the type doc comment) was also found; and
// declCmds, synthesized "(declare-fun ...)" commands for every live symbol
// - of any arity - whose name is in s.astDeclNames, i.e. one that was
// introduced via Assert(AST) and so has no declaration of its own anywhere
// in rawSegments (see astDeclNames' doc comment). A name not in
// astDeclNames came from AssertSMTLIB2String/File instead, whose verbatim
// text in rawSegments already declares it, so it's deliberately skipped here
// to avoid sending a duplicate declaration the subprocess would reject.
func (s *SolverCLI) liveSymbols() (names []string, hasArityFuncs bool, declCmds []string) {
	vec := C.Z3_solver_get_assertions(s.ctx.c, s.mirror.s)
	if vec == nil {
		return nil, false, nil
	}
	C.Z3_ast_vector_inc_ref(s.ctx.c, vec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.c, vec)

	seen := make(map[string]bool)     // names already added to `names`
	declared := make(map[string]bool) // names already added to `declCmds`
	var stack []C.Z3_ast
	n := int(C.Z3_ast_vector_size(s.ctx.c, vec))
	for i := 0; i < n; i++ {
		stack = append(stack, C.Z3_ast_vector_get(s.ctx.c, vec, C.uint(i)))
	}
	for len(stack) > 0 {
		node := stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		if node == nil || !bool(C.Z3_is_app(s.ctx.c, node)) {
			continue
		}
		app := C.Z3_to_app(s.ctx.c, node)
		numArgs := int(C.Z3_get_app_num_args(s.ctx.c, app))
		decl := C.Z3_get_app_decl(s.ctx.c, app)
		if C.Z3_get_decl_kind(s.ctx.c, decl) == C.Z3_OP_UNINTERPRETED {
			name := symbolToString(s.ctx, C.Z3_get_decl_name(s.ctx.c, decl))
			if numArgs == 0 {
				if name != "" && !seen[name] {
					seen[name] = true
					names = append(names, name)
				}
			} else {
				hasArityFuncs = true
			}
			if name != "" && !declared[name] && s.astDeclNames[name] {
				declared[name] = true
				if q, ok := quoteSMTLIBSymbol(name); ok {
					var domain []string
					for i := 0; i < numArgs; i++ {
						domain = append(domain, (Sort{ctx: s.ctx, s: C.Z3_get_domain(s.ctx.c, decl, C.uint(i))}).String())
					}
					rng := (Sort{ctx: s.ctx, s: C.Z3_get_range(s.ctx.c, decl)}).String()
					declCmds = append(declCmds, fmt.Sprintf("(declare-fun %s (%s) %s)", q, strings.Join(domain, " "), rng))
				}
			}
		}
		for i := 0; i < numArgs; i++ {
			stack = append(stack, C.Z3_get_app_arg(s.ctx.c, app, C.uint(i)))
		}
	}
	return names, hasArityFuncs, declCmds
}

// smtlibSimpleSymbolChar reports whether r is legal in an unquoted SMT-LIB2
// "simple symbol" token.
func smtlibSimpleSymbolChar(r rune) bool {
	if unicode.IsLetter(r) || unicode.IsDigit(r) {
		return true
	}
	switch r {
	case '~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.', '?', '/':
		return true
	}
	return false
}

// quoteSMTLIBSymbol renders name as a valid SMT-LIB2 symbol token, adding
// |...| quoting when needed. Reports ok=false if name can't be safely
// represented (e.g. it contains a literal '|' or '\\', which quoted symbols
// cannot escape).
func quoteSMTLIBSymbol(name string) (quoted string, ok bool) {
	if name == "" {
		return "", false
	}
	simple := !unicode.IsDigit(rune(name[0]))
	for _, r := range name {
		if !smtlibSimpleSymbolChar(r) {
			simple = false
			break
		}
	}
	if simple {
		return name, true
	}
	if strings.ContainsAny(name, "|\\") {
		return "", false
	}
	return "|" + name + "|", true
}

// CheckContext behaves like Check but bounds the subprocess by ctx and, if
// timeout > 0, by that timeout too (via z3's own "-T:<seconds>" flag as well
// as a hard subprocess-kill deadline, so a z3 build that ignores -T: still
// cannot hang the caller).
func (s *SolverCLI) CheckContext(ctx context.Context, timeout time.Duration) (CheckResult, error) {
	s.resetLastModelState()
	s.lastReason = ""
	s.lastModelPartial = false

	full := strings.Join(s.rawSegments, "\n")
	rawNames, hasArityFuncs, declCmds := s.liveSymbols()

	var names []string
	for _, n := range rawNames {
		if q, ok := quoteSMTLIBSymbol(n); ok {
			names = append(names, q)
		} else {
			hasArityFuncs = true // can't be safely retrieved either; model will be partial
		}
	}

	var script strings.Builder
	// Vanilla z3 produces models by default in "-in" mode without being
	// asked, but z3-noodler does not: without this, its "(get-value ...)"
	// response is just an error ("model is not available, did you forget to
	// enable model generation with 'model=true'?") and Model() silently
	// returns nil. Writing it unconditionally ahead of the caller's own
	// options is a no-op for vanilla z3 and keeps SolverCLI working
	// identically against either; a caller that explicitly wants models off
	// can still override it since s.options (via SetOption) is written
	// after and SMT-LIB2 options apply in order.
	script.WriteString("(set-option :produce-models true)\n")
	for _, opt := range s.options {
		script.WriteString(opt)
		script.WriteByte('\n')
	}
	// Declares symbols introduced via Assert(AST) ahead of the assertions
	// that use them (see astDeclNames' and liveSymbols' doc comments) - the
	// subprocess is a brand-new z3 process that has never seen mirror's
	// declarations, only whatever text rawSegments carries.
	for _, cmd := range declCmds {
		script.WriteString(cmd)
		script.WriteByte('\n')
	}
	script.WriteString(full)
	script.WriteString("(check-sat)\n")
	if len(names) > 0 {
		fmt.Fprintf(&script, "(get-value (%s))\n", strings.Join(names, " "))
	}

	args := []string{"-in"}
	if timeout > 0 {
		secs := int(timeout / time.Second)
		if secs < 1 {
			secs = 1
		}
		args = append(args, fmt.Sprintf("-T:%d", secs))
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, timeout+5*time.Second)
		defer cancel()
	}

	cmd := exec.CommandContext(ctx, s.path, args...)
	cmd.Stdin = strings.NewReader(script.String())
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	runErr := cmd.Run()

	out := strings.TrimRight(stdout.String(), "\n")

	// The result of (check-sat) is not necessarily the first line of
	// stdout: z3 prints diagnostics for a bad preceding (set-option ...) or
	// other command to stdout (not stderr), and still runs check-sat
	// afterward. Scan every line for the actual sat/unsat/unknown response
	// instead of assuming it's the first one, so a rejected option upstream
	// doesn't cause a solved query's result to be discarded.
	lines := strings.Split(out, "\n")
	resultLine := -1
	var res CheckResult
	for i, ln := range lines {
		switch strings.TrimSpace(ln) {
		case "sat":
			res, resultLine = Sat, i
		case "unsat":
			res, resultLine = Unsat, i
		case "unknown":
			res, resultLine = Unknown, i
		default:
			continue
		}
		break
	}

	if resultLine == -1 {
		if ctx.Err() != nil {
			return Unknown, fmt.Errorf("z3 subprocess did not finish in time: %w", ctx.Err())
		}
		if runErr != nil {
			msg := strings.TrimSpace(stderr.String())
			if msg == "" {
				msg = strings.TrimSpace(out)
			}
			if msg == "" {
				msg = runErr.Error()
			}
			return Unknown, fmt.Errorf("z3 subprocess failed: %s", msg)
		}
		if out == "" {
			return Unknown, errors.New("z3 subprocess produced no output")
		}
		return Unknown, fmt.Errorf("unrecognized z3 output: %q", out)
	}

	rest := strings.Join(lines[resultLine+1:], "\n")
	if res == Unknown {
		s.lastReason = strings.TrimSpace(rest)
	}

	if res == Sat && len(names) > 0 {
		// Reconstruction is deferred to Model(): it replays get-value's
		// response against the declarations by running a native Check() of
		// its own (see reconstructModel), which hits the very tactic-based
		// Solver slowness SolverCLI exists to route around. Most callers
		// only need the sat/unsat/unknown status, so paying that cost on
		// every sat result - rather than only when a caller actually asks
		// for the model - turned "check instantly, don't need a witness"
		// queries into multi-second ones for no benefit.
		// declCmds isn't part of full (Assert(AST) deliberately keeps
		// rawSegments to just the assertion text - see astDeclNames' doc
		// comment), but reconstructModel needs it: it extracts declarations
		// from lastDeclScript to replay get-value's response against a
		// fresh native solver, and a symbol Assert(AST) introduced has no
		// declaration anywhere else.
		if len(declCmds) > 0 {
			s.lastDeclScript = strings.Join(declCmds, "\n") + "\n" + full
		} else {
			s.lastDeclScript = full
		}
		s.lastGetValueOut = rest
	}
	s.lastModelPartial = res == Sat && hasArityFuncs
	return res, nil
}

// Model returns the model reconstructed from the most recent sat Check, or
// nil - mirroring Solver.Model's signature and its convention of returning
// nil when no model is available. The returned model must be closed by the
// caller (or allowed to leak for GC finalization), same as Solver.Model.
//
// Reconstruction happens lazily on first call (see CheckContext) and is
// cached until the next Check/CheckContext or Close.
func (s *SolverCLI) Model() *Model {
	if !s.lastModelBuilt {
		s.lastModelBuilt = true
		if s.lastGetValueOut != "" {
			s.lastModel = reconstructModel(s.ctx, s.lastDeclScript, s.lastGetValueOut)
		}
	}
	return s.lastModel
}

// ModelIncomplete reports whether the most recent sat Check's model is known
// to be missing entries: either a real-arity uninterpreted function (which
// this package cannot reconstruct, see the type doc comment) was present in
// the formula, or a declared constant's name couldn't be safely represented
// as an SMT-LIB2 symbol and so its value was never requested. Callers that
// need a guarantee the model is complete should check this rather than
// assuming a non-nil Model() covers every declaration.
func (s *SolverCLI) ModelIncomplete() bool {
	return s.lastModelPartial
}
