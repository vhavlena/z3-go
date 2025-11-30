//go:build cgo
// +build cgo

package z3

/*
#include "z3.h"
int model_eval_wrap(Z3_context c, Z3_model m, Z3_ast a, int model_completion, Z3_ast* out);
*/
import "C"

// Model wraps a reference-counted Z3_model handle produced by Solver.Model and
// exposes helpers for evaluating expressions back into the model.
type Model struct {
	ctx *Context
	m   C.Z3_model
}

// Close decrements the reference count held by the Go wrapper. It is safe to
// call multiple times and becomes a no-op once the handle is cleared.
func (m *Model) Close() {
	if m != nil && m.m != nil {
		C.Z3_model_dec_ref(m.ctx.c, m.m)
		m.m = nil
	}
}

// Eval evaluates an AST in the model, optionally requesting model completion so
// Z3 synthesizes default values for underspecified symbols. The returned AST
// inherits the model's context and carries an increased reference count.
func (m *Model) Eval(a AST, modelCompletion bool) AST {
	var out C.Z3_ast
	mc := C.int(0)
	if modelCompletion {
		mc = C.int(1)
	}
	ok := C.model_eval_wrap(m.ctx.c, m.m, a.a, mc, &out)
	if ok == 0 || out == nil {
		return AST{m.ctx, nil}
	}
	C.Z3_inc_ref(m.ctx.c, out)
	return AST{m.ctx, out}
}

// String returns the textual SMT-LIB representation of the model, which is
// useful for debugging or writing golden-model tests.
func (m *Model) String() string {
	if m == nil || m.m == nil {
		return "<nil-model>"
	}
	s := C.Z3_model_to_string(m.ctx.c, m.m)
	if s == nil {
		return "<invalid-model>"
	}
	return C.GoString(s)
}
