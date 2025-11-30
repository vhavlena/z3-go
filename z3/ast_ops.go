//go:build cgo
// +build cgo

package z3

/*
#include "z3.h"
*/
import "C"

import "unsafe"

// Not returns the logical negation of the AST.
func (t AST) Not() AST {
	a := C.Z3_mk_not(t.ctx.c, t.a)
	C.Z3_inc_ref(t.ctx.c, a)
	return AST{t.ctx, a}
}

// And builds a conjunction over all provided ASTs.
func And(args ...AST) AST {
	if len(args) == 0 {
		panic("And requires at least one arg")
	}
	ctx := args[0].ctx
	cargs := make([]C.Z3_ast, len(args))
	for i, a := range args {
		cargs[i] = a.a
	}
	a := C.Z3_mk_and(ctx.c, C.uint(len(cargs)), (*C.Z3_ast)(unsafe.Pointer(&cargs[0])))
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Or builds a disjunction over all provided ASTs.
func Or(args ...AST) AST {
	if len(args) == 0 {
		panic("Or requires at least one arg")
	}
	ctx := args[0].ctx
	cargs := make([]C.Z3_ast, len(args))
	for i, a := range args {
		cargs[i] = a.a
	}
	a := C.Z3_mk_or(ctx.c, C.uint(len(cargs)), (*C.Z3_ast)(unsafe.Pointer(&cargs[0])))
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Eq builds an equality between two ASTs.
func Eq(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_eq(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Add sums all provided numeric ASTs.
func Add(args ...AST) AST {
	if len(args) == 0 {
		panic("Add requires at least one arg")
	}
	ctx := args[0].ctx
	cargs := make([]C.Z3_ast, len(args))
	for i, a := range args {
		cargs[i] = a.a
	}
	a := C.Z3_mk_add(ctx.c, C.uint(len(cargs)), (*C.Z3_ast)(unsafe.Pointer(&cargs[0])))
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Sub subtracts subsequent ASTs from the first argument.
func Sub(args ...AST) AST {
	if len(args) == 0 {
		panic("Sub requires at least one arg")
	}
	ctx := args[0].ctx
	cargs := make([]C.Z3_ast, len(args))
	for i, a := range args {
		cargs[i] = a.a
	}
	a := C.Z3_mk_sub(ctx.c, C.uint(len(cargs)), (*C.Z3_ast)(unsafe.Pointer(&cargs[0])))
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Mul multiplies all provided numeric ASTs.
func Mul(args ...AST) AST {
	if len(args) == 0 {
		panic("Mul requires at least one arg")
	}
	ctx := args[0].ctx
	cargs := make([]C.Z3_ast, len(args))
	for i, a := range args {
		cargs[i] = a.a
	}
	a := C.Z3_mk_mul(ctx.c, C.uint(len(cargs)), (*C.Z3_ast)(unsafe.Pointer(&cargs[0])))
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Le builds the constraint x <= y.
func Le(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_le(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Lt builds the constraint x < y.
func Lt(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_lt(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Ge builds the constraint x >= y.
func Ge(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_ge(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Gt builds the constraint x > y.
func Gt(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_gt(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Select builds an array select expression.
func Select(array AST, index AST) AST {
	ctx := array.ctx
	a := C.Z3_mk_select(ctx.c, array.a, index.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Implies builds the implication x => y.
func Implies(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_implies(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Ite builds an if-then-else over c, t, and e.
func Ite(c, t, e AST) AST {
	ctx := c.ctx
	a := C.Z3_mk_ite(ctx.c, c.a, t.a, e.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Distinct enforces that all provided ASTs take pairwise different values.
func Distinct(args ...AST) AST {
	if len(args) == 0 {
		panic("Distinct requires at least one arg")
	}
	ctx := args[0].ctx
	cargs := make([]C.Z3_ast, len(args))
	for i, a := range args {
		cargs[i] = a.a
	}
	a := C.Z3_mk_distinct(ctx.c, C.uint(len(cargs)), (*C.Z3_ast)(unsafe.Pointer(&cargs[0])))
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Concat concatenates the provided sequence (string) ASTs.
func Concat(args ...AST) AST {
	if len(args) == 0 {
		panic("Concat requires at least one arg")
	}
	ctx := args[0].ctx
	cargs := make([]C.Z3_ast, len(args))
	for i, a := range args {
		cargs[i] = a.a
	}
	a := C.Z3_mk_seq_concat(ctx.c, C.uint(len(cargs)), (*C.Z3_ast)(unsafe.Pointer(&cargs[0])))
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Length returns the sequence length as an Int AST.
func Length(s AST) AST {
	ctx := s.ctx
	a := C.Z3_mk_seq_length(ctx.c, s.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Contains builds the predicate (contains s t).
func Contains(s, t AST) AST {
	ctx := s.ctx
	a := C.Z3_mk_seq_contains(ctx.c, s.a, t.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// App applies a function declaration to the provided arguments and returns the resulting AST.
func (ctx *Context) App(f FuncDecl, args ...AST) AST {
	var a C.Z3_ast
	if len(args) == 0 {
		a = C.Z3_mk_app(ctx.c, f.d, 0, nil)
	} else {
		cargs := make([]C.Z3_ast, len(args))
		for i, v := range args {
			cargs[i] = v.a
		}
		a = C.Z3_mk_app(ctx.c, f.d, C.uint(len(cargs)), (*C.Z3_ast)(unsafe.Pointer(&cargs[0])))
	}
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}
