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
	"math"
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

// NewSolver creates a fresh solver attached to the context, backed by Z3's
// general-purpose combined solver (Z3_mk_solver). This solver runs Z3's
// tactic-based preprocessing pipeline (simplification, macro-finding, logic
// auto-detection, etc.) before falling back to the core engine, which is a
// net win for most problems. However, for some quantified formulas —
// particularly those mixing quantifiers over datatype-sorted variables with
// Seq/String theory reasoning — the selected tactic can be dramatically
// slower (or fail to terminate in practice) than the same assertions run on
// the plain incremental core. If a formula that should be fast hangs or
// times out under NewSolver, try NewSimpleSolver on the same assertions
// before concluding the formula itself is hard.
//
// The returned solver automatically tracks a Go finalizer so leaked solver
// handles are still released when the GC runs.
func (ctx *Context) NewSolver() *Solver {
	s := &Solver{ctx, C.Z3_mk_solver(ctx.c)}
	C.Z3_solver_inc_ref(ctx.c, s.s)
	runtime.SetFinalizer(s, func(x *Solver) { x.Close() })
	return s
}

// NewSimpleSolver creates a fresh solver attached to the context, backed by
// Z3's basic incremental core (Z3_mk_simple_solver). Unlike NewSolver, it
// skips the tactic-based preprocessing pipeline and asserts formulas more
// directly against the core engine. This can avoid pathological slowdowns
// that NewSolver's tactic selection occasionally hits on certain quantified
// formulas (see NewSolver's doc comment), but it also loses the
// simplifications that make NewSolver faster on many other problems. Prefer
// NewSolver by default; reach for NewSimpleSolver when a specific query is
// known to hang or time out under the combined solver.
//
// The returned solver automatically tracks a Go finalizer so leaked solver
// handles are still released when the GC runs.
func (ctx *Context) NewSimpleSolver() *Solver {
	s := &Solver{ctx, C.Z3_mk_simple_solver(ctx.c)}
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

// SetOption sets a tuning parameter on this solver only. Deliberately does
// NOT go through SMT-LIB2's textual (set-option ...) command: parsing that
// via Z3_parse_smtlib2_string applies it to Z3's process-global parameter
// table rather than scoping it to one solver, so it silently leaks into
// every other Context/Solver created afterward in the same process (this was
// observed to poison unrelated tests - and would equally poison unrelated
// production solvers - with e.g. a 5ms global timeout). Instead this builds
// a Z3_params object and applies it with Z3_solver_set_params, which Z3
// documents as scoped to the receiving solver.
//
// The Z3_params value kind is chosen from value's Go type rather than looked
// up via Z3_solver_get_param_descrs: that descriptor table only enumerates a
// solver's own top-level options (timeout, unsat_core, ...) and reports
// Z3_PK_INVALID for legitimate module-prefixed options like "smt.mbqi" or
// "smt.random_seed", even though Z3_solver_set_params accepts them fine.
//
// Before applying, the built Z3_params is run through Z3_params_validate
// against the solver's own descriptor table. Despite Z3_param_descrs_get_kind
// reporting Z3_PK_INVALID for a module-prefixed name looked up directly (the
// reason this function can't use it to pick a Z3_params kind up front),
// Z3_params_validate resolves module-prefixed names against their owning
// module's own descriptors and does raise an error for both a misspelled
// option (top-level or module-prefixed) and a wrong-kind value for a
// legitimate one - e.g. passing a Go int for the double-valued
// "smt.qi.eager_threshold" is rejected here, so double-valued module options
// must be set with a float32/float64.
func (s *Solver) SetOption(name string, value any) error {
	if s == nil || s.s == nil {
		return errors.New("nil solver")
	}

	nameC := C.CString(name)
	defer C.free(unsafe.Pointer(nameC))
	key := C.Z3_mk_string_symbol(s.ctx.c, nameC)

	params := C.Z3_mk_params(s.ctx.c)
	C.Z3_params_inc_ref(s.ctx.c, params)
	defer C.Z3_params_dec_ref(s.ctx.c, params)

	switch v := value.(type) {
	case bool:
		C.Z3_params_set_bool(s.ctx.c, params, key, C.bool(v))
	case int:
		u, err := int64ToParamUint(int64(v))
		if err != nil {
			return fmt.Errorf("option %q: %w", name, err)
		}
		C.Z3_params_set_uint(s.ctx.c, params, key, u)
	case int32:
		u, err := int64ToParamUint(int64(v))
		if err != nil {
			return fmt.Errorf("option %q: %w", name, err)
		}
		C.Z3_params_set_uint(s.ctx.c, params, key, u)
	case int64:
		u, err := int64ToParamUint(v)
		if err != nil {
			return fmt.Errorf("option %q: %w", name, err)
		}
		C.Z3_params_set_uint(s.ctx.c, params, key, u)
	case uint:
		u, err := uint64ToParamUint(uint64(v))
		if err != nil {
			return fmt.Errorf("option %q: %w", name, err)
		}
		C.Z3_params_set_uint(s.ctx.c, params, key, u)
	case uint32:
		C.Z3_params_set_uint(s.ctx.c, params, key, C.unsigned(v))
	case uint64:
		u, err := uint64ToParamUint(v)
		if err != nil {
			return fmt.Errorf("option %q: %w", name, err)
		}
		C.Z3_params_set_uint(s.ctx.c, params, key, u)
	case float32:
		C.Z3_params_set_double(s.ctx.c, params, key, C.double(v))
	case float64:
		C.Z3_params_set_double(s.ctx.c, params, key, C.double(v))
	case string:
		strC := C.CString(v)
		defer C.free(unsafe.Pointer(strC))
		C.Z3_params_set_symbol(s.ctx.c, params, key, C.Z3_mk_string_symbol(s.ctx.c, strC))
	default:
		return fmt.Errorf("unsupported option value type %T", v)
	}

	descrs := C.Z3_solver_get_param_descrs(s.ctx.c, s.s)
	C.Z3_param_descrs_inc_ref(s.ctx.c, descrs)
	C.Z3_params_validate(s.ctx.c, params, descrs)
	C.Z3_param_descrs_dec_ref(s.ctx.c, descrs)
	if code := C.Z3_get_error_code(s.ctx.c); code != C.Z3_OK {
		msg := C.Z3_get_error_msg(s.ctx.c, code)
		if msg != nil {
			return errors.New(C.GoString(msg))
		}
		return fmt.Errorf("invalid option %q", name)
	}

	C.Z3_solver_set_params(s.ctx.c, s.s, params)
	if code := C.Z3_get_error_code(s.ctx.c); code != C.Z3_OK {
		msg := C.Z3_get_error_msg(s.ctx.c, code)
		if msg != nil {
			return errors.New(C.GoString(msg))
		}
		return fmt.Errorf("failed to set option %q", name)
	}
	return nil
}

// int64ToParamUint range-checks v against Z3_params_set_uint's 32-bit
// unsigned parameter, rather than silently truncating/sign-wrapping it.
func int64ToParamUint(v int64) (C.unsigned, error) {
	if v < 0 || v > math.MaxUint32 {
		return 0, fmt.Errorf("value %d out of range for a uint32 option", v)
	}
	return C.unsigned(v), nil
}

// uint64ToParamUint range-checks v against Z3_params_set_uint's 32-bit
// unsigned parameter, rather than silently truncating it.
func uint64ToParamUint(v uint64) (C.unsigned, error) {
	if v > math.MaxUint32 {
		return 0, fmt.Errorf("value %d out of range for a uint32 option", v)
	}
	return C.unsigned(v), nil
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
