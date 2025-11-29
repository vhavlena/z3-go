//go:build cgo
// +build cgo

package z3

/*
#include <stdlib.h>
#include "z3.h"
*/
import "C"

import (
	"errors"
	"fmt"
	"runtime"
	"unsafe"
)

// Solver wraps a Z3_solver handle and provides a Go-friendly API for building
// and checking verification problems tied to the owning Context.
type Solver struct {
	ctx *Context
	s   C.Z3_solver
}

// CheckResult captures the outcome of a solver check.
type CheckResult int

const (
	// Unknown indicates the solver could not determine satisfiability.
	Unknown CheckResult = iota
	// Sat indicates the problem is satisfiable.
	Sat
	// Unsat indicates the problem is unsatisfiable.
	Unsat
)

// NewSolver creates a fresh solver attached to the context. The returned
// solver automatically tracks a Go finalizer so leaked solver handles are
// still released when the GC runs.
func (ctx *Context) NewSolver() *Solver {
	s := &Solver{ctx, C.Z3_mk_solver(ctx.c)}
	C.Z3_solver_inc_ref(ctx.c, s.s)
	runtime.SetFinalizer(s, func(x *Solver) { x.Close() })
	return s
}

// Close releases the underlying Z3 solver reference. Repeated calls are safe
// and become no-ops once the solver handle has been cleared.
func (s *Solver) Close() {
	if s != nil && s.s != nil {
		C.Z3_solver_dec_ref(s.ctx.c, s.s)
		s.s = nil
	}
}

// SetGlobalParam sets a global Z3 parameter such as "timeout". Global
// parameters must be configured before creating contexts and affect every
// solver in the current process.
func SetGlobalParam(key, value string) {
	k := C.CString(key)
	v := C.CString(value)
	C.Z3_set_param_value(nil, k, v)
	C.free(unsafe.Pointer(k))
	C.free(unsafe.Pointer(v))
}

// Assert adds a constraint to the solver without copying it. The AST must have
// been created in the same context as the solver.
func (s *Solver) Assert(a AST) {
	C.Z3_solver_assert(s.ctx.c, s.s, a.a)
}

// SetOption applies an SMT-LIB (set-option) command on the solver instance by
// constructing a tiny SMT-LIB snippet and parsing it through Z3. This keeps the
// API surface small while still exposing every solver tuning knob.
func (s *Solver) SetOption(name string, value interface{}) error {
	if s == nil || s.s == nil {
		return errors.New("nil solver")
	}
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
	case int, int32, int64:
		valStr = fmt.Sprintf("%d", v)
	case uint, uint32, uint64:
		valStr = fmt.Sprintf("%d", v)
	case float32, float64:
		valStr = fmt.Sprintf("%v", v)
	default:
		return fmt.Errorf("unsupported option value type %T", v)
	}
	cmd := fmt.Sprintf("(set-option :%s %s)", name, valStr)
	return s.AssertSMTLIB2String(cmd)
}

// Push creates a new solver scope, allowing constraints to be added and later
// discarded with a matching Pop.
func (s *Solver) Push() {
	C.Z3_solver_push(s.ctx.c, s.s)
}

// Pop removes the given number of solver scopes. Passing 0 leaves scopes
// untouched, while passing a value larger than the number of scopes panics (per
// Z3 semantics).
func (s *Solver) Pop(n uint) {
	C.Z3_solver_pop(s.ctx.c, s.s, C.uint(n))
}

// Check runs the solver with the currently asserted constraints and returns the
// Z3 check result. Unknown results are surfaced with the textual reason from
// Z3 when available.
func (s *Solver) Check() (CheckResult, error) {
	r := C.Z3_solver_check(s.ctx.c, s.s)
	switch r {
	case C.Z3_L_TRUE:
		return Sat, nil
	case C.Z3_L_FALSE:
		return Unsat, nil
	default:
		rstr := C.Z3_solver_get_reason_unknown(s.ctx.c, s.s)
		if rstr != nil {
			return Unknown, errors.New(C.GoString(rstr))
		}
		return Unknown, errors.New("unknown")
	}
}

// ReasonUnknown returns Z3's explanation for an "unknown" result, or an empty
// string if the solver has not been queried or the last result was decisive.
func (s *Solver) ReasonUnknown() string {
	if s == nil || s.s == nil {
		return ""
	}
	rstr := C.Z3_solver_get_reason_unknown(s.ctx.c, s.s)
	if rstr == nil {
		return ""
	}
	return C.GoString(rstr)
}

// Model retrieves the current model if available. The returned model must be
// closed by the caller (or allowed to leak for GC finalization) to avoid
// accumulating references inside Z3.
func (s *Solver) Model() *Model {
	m := C.Z3_solver_get_model(s.ctx.c, s.s)
	if m == nil {
		return nil
	}
	C.Z3_model_inc_ref(s.ctx.c, m)
	mod := &Model{s.ctx, m}
	runtime.SetFinalizer(mod, func(x *Model) { x.Close() })
	return mod
}

// AssertSMTLIB2String parses an SMT-LIB2 string and asserts resulting commands
// into the solver. Any declarations found in the script are also recorded in
// the owning Context so later helpers (ConstDecl, FuncDeclByName) keep working.
func (s *Solver) AssertSMTLIB2String(input string) error {
	cstr := C.CString(input)
	defer C.free(unsafe.Pointer(cstr))
	vec := C.Z3_parse_smtlib2_string(s.ctx.c, cstr, 0, nil, nil, 0, nil, nil)
	if code := C.Z3_get_error_code(s.ctx.c); code != C.Z3_OK {
		msg := C.Z3_get_error_msg(s.ctx.c, code)
		if msg != nil {
			return errors.New(C.GoString(msg))
		}
		return errors.New("SMT-LIB2 parse error")
	}
	if vec == nil {
		return nil
	}
	C.Z3_ast_vector_inc_ref(s.ctx.c, vec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.c, vec)
	n := int(C.Z3_ast_vector_size(s.ctx.c, vec))
	for i := 0; i < n; i++ {
		a := C.Z3_ast_vector_get(s.ctx.c, vec, C.uint(i))
		if a != nil {
			s.ctx.recordSortsFromAST(AST{ctx: s.ctx, a: a})
			C.Z3_solver_assert(s.ctx.c, s.s, a)
		}
	}
	return nil
}

// AssertSMTLIB2File parses an SMT-LIB2 file and asserts resulting commands,
// mirroring AssertSMTLIB2String but sourcing the input from disk.
func (s *Solver) AssertSMTLIB2File(path string) error {
	cpath := C.CString(path)
	defer C.free(unsafe.Pointer(cpath))
	vec := C.Z3_parse_smtlib2_file(s.ctx.c, cpath, 0, nil, nil, 0, nil, nil)
	if code := C.Z3_get_error_code(s.ctx.c); code != C.Z3_OK {
		msg := C.Z3_get_error_msg(s.ctx.c, code)
		if msg != nil {
			return errors.New(C.GoString(msg))
		}
		return errors.New("SMT-LIB2 parse error")
	}
	if vec == nil {
		return nil
	}
	C.Z3_ast_vector_inc_ref(s.ctx.c, vec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.c, vec)
	n := int(C.Z3_ast_vector_size(s.ctx.c, vec))
	for i := 0; i < n; i++ {
		a := C.Z3_ast_vector_get(s.ctx.c, vec, C.uint(i))
		if a != nil {
			s.ctx.recordSortsFromAST(AST{ctx: s.ctx, a: a})
			C.Z3_solver_assert(s.ctx.c, s.s, a)
		}
	}
	return nil
}

// SolveSMTLIB2String asserts SMT-LIB2 commands from a string and immediately
// runs Check, making it convenient for one-off satisfiability queries.
func (s *Solver) SolveSMTLIB2String(input string) (CheckResult, error) {
	if err := s.AssertSMTLIB2String(input); err != nil {
		return Unknown, err
	}
	return s.Check()
}

// SolveSMTLIB2File asserts SMT-LIB2 commands from a file and immediately runs
// Check, mirroring SolveSMTLIB2String for file-based workflows.
func (s *Solver) SolveSMTLIB2File(path string) (CheckResult, error) {
	if err := s.AssertSMTLIB2File(path); err != nil {
		return Unknown, err
	}
	return s.Check()
}
