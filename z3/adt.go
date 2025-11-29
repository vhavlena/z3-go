//go:build cgo
// +build cgo

package z3

/*
#include <stdlib.h>
#include "z3.h"
*/
import "C"

import "unsafe"

// Constructor is a temporary helper used while declaring algebraic datatypes.
// Instances are short-lived descriptors that feed into MkDatatype.
type Constructor struct {
	ctx *Context
	c   C.Z3_constructor
	n   int
}

// ADTField describes a constructor field with a concrete sort. Recursive fields
// are expressed by setting Sort to the datatype sort after MkDatatype returns.
type ADTField struct {
	Name string
	Sort Sort
}

// ADTConstructorDecl collects the callable declarations extracted from a
// constructor, including the constructor function itself, its recognizer, and
// each accessor.
type ADTConstructorDecl struct {
	Constructor FuncDecl
	Recognizer  FuncDecl
	Accessors   []FuncDecl
}

// MkConstructor creates a constructor descriptor with the provided recognizer
// and fields. The descriptor must eventually be consumed by MkDatatype, which
// also takes care of freeing the underlying Z3 constructor object.
func (ctx *Context) MkConstructor(name, recognizer string, fields []ADTField) *Constructor {
	symName := ctx.StringSymbol(name)
	symRec := ctx.StringSymbol(recognizer)

	n := len(fields)
	var fieldSyms *C.Z3_symbol
	var fieldSorts *C.Z3_sort
	var sortRefs *C.uint
	if n > 0 {
		syms := make([]C.Z3_symbol, n)
		sorts := make([]C.Z3_sort, n)
		refs := make([]C.uint, n)
		for i, f := range fields {
			cstr := C.CString(f.Name)
			syms[i] = C.Z3_mk_string_symbol(ctx.c, cstr)
			C.free(unsafe.Pointer(cstr))
			sorts[i] = f.Sort.s
			refs[i] = 0 // non-recursive fields
		}
		fieldSyms = (*C.Z3_symbol)(unsafe.Pointer(&syms[0]))
		fieldSorts = (*C.Z3_sort)(unsafe.Pointer(&sorts[0]))
		sortRefs = (*C.uint)(unsafe.Pointer(&refs[0]))
	}
	c := C.Z3_mk_constructor(ctx.c, symName, symRec, C.uint(n), fieldSyms, fieldSorts, sortRefs)
	return &Constructor{ctx: ctx, c: c, n: n}
}

// MkDatatype turns constructor descriptors into a datatype sort and concrete
// declarations. The returned sort is recorded on the context so it can be
// rediscovered later via NamedSort.
func (ctx *Context) MkDatatype(name string, ctors []*Constructor) (Sort, []ADTConstructorDecl) {
	sym := ctx.StringSymbol(name)
	n := len(ctors)
	var arr *C.Z3_constructor
	if n > 0 {
		carr := make([]C.Z3_constructor, n)
		for i, k := range ctors {
			carr[i] = k.c
		}
		arr = (*C.Z3_constructor)(unsafe.Pointer(&carr[0]))
	}
	srt := C.Z3_mk_datatype(ctx.c, sym, C.uint(n), arr)
	decls := make([]ADTConstructorDecl, n)
	for i := 0; i < n; i++ {
		k := ctors[i]
		nf := k.n
		var fdecl C.Z3_func_decl
		var rdecl C.Z3_func_decl
		var acc *C.Z3_func_decl
		if nf > 0 {
			accArr := make([]C.Z3_func_decl, nf)
			acc = (*C.Z3_func_decl)(unsafe.Pointer(&accArr[0]))
			C.Z3_query_constructor(ctx.c, k.c, C.uint(nf), &fdecl, &rdecl, acc)
			accOut := make([]FuncDecl, nf)
			for j := 0; j < nf; j++ {
				accOut[j] = FuncDecl{ctx, accArr[j]}
			}
			decls[i] = ADTConstructorDecl{Constructor: FuncDecl{ctx, fdecl}, Recognizer: FuncDecl{ctx, rdecl}, Accessors: accOut}
		} else {
			C.Z3_query_constructor(ctx.c, k.c, 0, &fdecl, &rdecl, nil)
			decls[i] = ADTConstructorDecl{Constructor: FuncDecl{ctx, fdecl}, Recognizer: FuncDecl{ctx, rdecl}, Accessors: nil}
		}
		C.Z3_del_constructor(ctx.c, k.c)
	}
	sort := Sort{ctx, srt}
	ctx.rememberSort(sort)
	return sort, decls
}
