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
	"os/exec"
	"strings"
	"time"
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
// symbols natively (walking the real ASTs via Z3_solver_get_assertions and
// AST.Walk/Decl, not by scanning printed text), asks the subprocess for
// their values via SMT-LIB's (get-value ...), and feeds those values -
// unparsed, exactly as z3 printed them - straight into Z3's own
// Z3_parse_smtlib2_string as equality assertions against a fresh, trivial
// native solver, which is what actually interprets them into a genuine
// *Model. The only custom code involved is a small top-level-paren splitter
// that locates the boundaries between values in the subprocess's response
// text (needed because that response isn't itself valid SMT-LIB command
// syntax Z3's parser can consume directly) - it never interprets what a
// value means. Function symbols with real arity are not reconstructed and
// will simply be absent from the resulting model. If reconstruction fails
// for any reason, Model() returns nil, the same as it would for a Solver
// that hasn't found a model.
//
// SolverCLI is not safe for concurrent use by multiple goroutines.
type SolverCLI struct {
	ctx    *Context
	path   string
	mirror *Solver // tracks declarations/assertions for CLI serialization only
	// unusedOptions are relayed to the subprocess script but never applied to
	// mirror, since mirror is never itself checked against the real formula.
	options []string

	lastModel  *Model
	lastReason string
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
}

// AssertSMTLIB2String parses an SMT-LIB2 string and asserts the resulting
// commands, mirroring Solver.AssertSMTLIB2String.
func (s *SolverCLI) AssertSMTLIB2String(input string) error {
	return s.mirror.AssertSMTLIB2String(input)
}

// AssertSMTLIB2File mirrors Solver.AssertSMTLIB2File.
func (s *SolverCLI) AssertSMTLIB2File(path string) error {
	return s.mirror.AssertSMTLIB2File(path)
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
}

// Pop removes solver scopes, mirroring Solver.Pop.
func (s *SolverCLI) Pop(n uint) {
	s.mirror.Pop(n)
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

// constantNames returns the names of every 0-ary (constant) function
// application reachable from mirror's currently asserted formulas, found by
// walking their real ASTs via Z3_solver_get_assertions/AST.Walk/Decl -
// rather than by text-scanning the printed script for "declare-fun" forms.
func (s *SolverCLI) constantNames() []string {
	vec := C.Z3_solver_get_assertions(s.ctx.c, s.mirror.s)
	if vec == nil {
		return nil
	}
	C.Z3_ast_vector_inc_ref(s.ctx.c, vec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.c, vec)

	seen := make(map[string]bool)
	var names []string
	n := int(C.Z3_ast_vector_size(s.ctx.c, vec))
	for i := 0; i < n; i++ {
		root := AST{ctx: s.ctx, a: C.Z3_ast_vector_get(s.ctx.c, vec, C.uint(i))}
		root.Walk(func(node AST) bool {
			if node.IsApp() && node.NumChildren() == 0 && node.Decl().Kind() == DeclOpUninterpreted {
				name := node.Decl().Name()
				if name != "" && !seen[name] {
					seen[name] = true
					names = append(names, name)
				}
			}
			return true
		})
	}
	return names
}

// CheckContext behaves like Check but bounds the subprocess by ctx and, if
// timeout > 0, by that timeout too (via z3's own "-T:<seconds>" flag as well
// as a hard subprocess-kill deadline, so a z3 build that ignores -T: still
// cannot hang the caller).
func (s *SolverCLI) CheckContext(ctx context.Context, timeout time.Duration) (CheckResult, error) {
	if s.lastModel != nil {
		s.lastModel.Close()
		s.lastModel = nil
	}
	s.lastReason = ""

	full := C.GoString(C.Z3_solver_to_string(s.ctx.c, s.mirror.s))
	names := s.constantNames()

	var script strings.Builder
	for _, opt := range s.options {
		script.WriteString(opt)
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
	firstLine, rest, _ := strings.Cut(out, "\n")
	firstLine = strings.TrimSpace(firstLine)

	var res CheckResult
	switch firstLine {
	case "sat":
		res = Sat
	case "unsat":
		res = Unsat
	case "unknown":
		res = Unknown
		s.lastReason = strings.TrimSpace(rest)
	default:
		if ctx.Err() != nil {
			return Unknown, fmt.Errorf("z3 subprocess did not finish in time: %w", ctx.Err())
		}
		if runErr != nil {
			msg := strings.TrimSpace(stderr.String())
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

	if res == Sat && len(names) > 0 {
		s.lastModel = reconstructModel(s.ctx, full, rest)
	}
	return res, nil
}

// Model returns the model reconstructed from the most recent sat Check, or
// nil - mirroring Solver.Model's signature and its convention of returning
// nil when no model is available. The returned model must be closed by the
// caller (or allowed to leak for GC finalization), same as Solver.Model.
func (s *SolverCLI) Model() *Model {
	return s.lastModel
}
