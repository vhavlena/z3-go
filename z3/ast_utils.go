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
	"math/big"
	"strconv"
	"unsafe"
)

// ASTKind mirrors Z3_ast_kind.
type ASTKind int

// Enumeration of supported AST kinds.
const (
	ASTKindNumeral    ASTKind = ASTKind(C.Z3_NUMERAL_AST)
	ASTKindApp        ASTKind = ASTKind(C.Z3_APP_AST)
	ASTKindVar        ASTKind = ASTKind(C.Z3_VAR_AST)
	ASTKindQuantifier ASTKind = ASTKind(C.Z3_QUANTIFIER_AST)
	ASTKindSort       ASTKind = ASTKind(C.Z3_SORT_AST)
	ASTKindFuncDecl   ASTKind = ASTKind(C.Z3_FUNC_DECL_AST)
	ASTKindUnknown    ASTKind = ASTKind(C.Z3_UNKNOWN_AST)
)

var astKindNames = map[ASTKind]string{
	ASTKindNumeral:    "numeral",
	ASTKindApp:        "app",
	ASTKindVar:        "var",
	ASTKindQuantifier: "quantifier",
	ASTKindSort:       "sort",
	ASTKindFuncDecl:   "func-decl",
	ASTKindUnknown:    "unknown",
}

func (k ASTKind) String() string {
	if s, ok := astKindNames[k]; ok {
		return s
	}
	return "ASTKind(" + strconv.Itoa(int(k)) + ")"
}

// DeclKind mirrors Z3_decl_kind for common operators.
type DeclKind int

const (
	DeclOpTrue          DeclKind = DeclKind(C.Z3_OP_TRUE)
	DeclOpFalse         DeclKind = DeclKind(C.Z3_OP_FALSE)
	DeclOpEq            DeclKind = DeclKind(C.Z3_OP_EQ)
	DeclOpDistinct      DeclKind = DeclKind(C.Z3_OP_DISTINCT)
	DeclOpIte           DeclKind = DeclKind(C.Z3_OP_ITE)
	DeclOpAnd           DeclKind = DeclKind(C.Z3_OP_AND)
	DeclOpOr            DeclKind = DeclKind(C.Z3_OP_OR)
	DeclOpNot           DeclKind = DeclKind(C.Z3_OP_NOT)
	DeclOpAdd           DeclKind = DeclKind(C.Z3_OP_ADD)
	DeclOpSub           DeclKind = DeclKind(C.Z3_OP_SUB)
	DeclOpMul           DeclKind = DeclKind(C.Z3_OP_MUL)
	DeclOpDiv           DeclKind = DeclKind(C.Z3_OP_DIV)
	DeclOpIDiv          DeclKind = DeclKind(C.Z3_OP_IDIV)
	DeclOpRem           DeclKind = DeclKind(C.Z3_OP_REM)
	DeclOpMod           DeclKind = DeclKind(C.Z3_OP_MOD)
	DeclOpLE            DeclKind = DeclKind(C.Z3_OP_LE)
	DeclOpGE            DeclKind = DeclKind(C.Z3_OP_GE)
	DeclOpLT            DeclKind = DeclKind(C.Z3_OP_LT)
	DeclOpGT            DeclKind = DeclKind(C.Z3_OP_GT)
	DeclOpConcat        DeclKind = DeclKind(C.Z3_OP_CONCAT)
	DeclOpSeqLength     DeclKind = DeclKind(C.Z3_OP_SEQ_LENGTH)
	DeclOpSeqContains   DeclKind = DeclKind(C.Z3_OP_SEQ_CONTAINS)
	DeclOpUninterpreted DeclKind = DeclKind(C.Z3_OP_UNINTERPRETED)
)

var declKindNames = map[DeclKind]string{
	DeclOpTrue:          "true",
	DeclOpFalse:         "false",
	DeclOpEq:            "eq",
	DeclOpDistinct:      "distinct",
	DeclOpIte:           "ite",
	DeclOpAnd:           "and",
	DeclOpOr:            "or",
	DeclOpNot:           "not",
	DeclOpAdd:           "add",
	DeclOpSub:           "sub",
	DeclOpMul:           "mul",
	DeclOpDiv:           "div",
	DeclOpIDiv:          "idiv",
	DeclOpRem:           "rem",
	DeclOpMod:           "mod",
	DeclOpLE:            "le",
	DeclOpGE:            "ge",
	DeclOpLT:            "lt",
	DeclOpGT:            "gt",
	DeclOpConcat:        "concat",
	DeclOpSeqLength:     "seq.length",
	DeclOpSeqContains:   "seq.contains",
	DeclOpUninterpreted: "uninterpreted",
}

func (k DeclKind) String() string {
	if s, ok := declKindNames[k]; ok {
		return s
	}
	return "DeclKind(" + strconv.Itoa(int(k)) + ")"
}

// Kind returns the low-level Z3 kind for the AST.
func (a AST) Kind() ASTKind {
	if a.ctx == nil || a.a == nil {
		return ASTKindUnknown
	}
	return ASTKind(C.Z3_get_ast_kind(a.ctx.c, a.a))
}

// IsApp reports whether the AST is an application node.
func (a AST) IsApp() bool {
	if a.ctx == nil || a.a == nil {
		return false
	}
	return bool(C.Z3_is_app(a.ctx.c, a.a))
}

// NumChildren returns the number of immediate child ASTs.
func (a AST) NumChildren() int {
	if !a.IsApp() {
		return 0
	}
	app := C.Z3_to_app(a.ctx.c, a.a)
	return int(C.Z3_get_app_num_args(a.ctx.c, app))
}

// Child returns the ith child AST.
func (a AST) Child(i int) AST {
	if !a.IsApp() || i < 0 || i >= a.NumChildren() {
		return AST{}
	}
	app := C.Z3_to_app(a.ctx.c, a.a)
	child := C.Z3_get_app_arg(a.ctx.c, app, C.uint(i))
	if child == nil {
		return AST{}
	}
	C.Z3_inc_ref(a.ctx.c, child)
	return AST{ctx: a.ctx, a: child}
}

// Children returns a slice with all direct child ASTs.
func (a AST) Children() []AST {
	n := a.NumChildren()
	if n == 0 {
		return nil
	}
	res := make([]AST, 0, n)
	for i := 0; i < n; i++ {
		res = append(res, a.Child(i))
	}
	return res
}

// Decl returns the function declaration for an application AST.
func (a AST) Decl() FuncDecl {
	if !a.IsApp() {
		return FuncDecl{}
	}
	app := C.Z3_to_app(a.ctx.c, a.a)
	decl := C.Z3_get_app_decl(a.ctx.c, app)
	return FuncDecl{ctx: a.ctx, d: decl}
}

// Kind returns the declaration kind.
func (d FuncDecl) Kind() DeclKind {
	if d.ctx == nil || d.d == nil {
		return DeclKind(0)
	}
	return DeclKind(C.Z3_get_decl_kind(d.ctx.c, d.d))
}

// Arity returns the number of arguments for the declaration.
func (d FuncDecl) Arity() int {
	if d.ctx == nil || d.d == nil {
		return 0
	}
	return int(C.Z3_get_arity(d.ctx.c, d.d))
}

// Name returns the symbol name for the declaration.
func (d FuncDecl) Name() string {
	if d.ctx == nil || d.d == nil {
		return ""
	}
	sym := C.Z3_get_decl_name(d.ctx.c, d.d)
	return symbolToString(d.ctx, sym)
}

func symbolToString(ctx *Context, sym C.Z3_symbol) string {
	if ctx == nil || ctx.c == nil || sym == nil {
		return ""
	}
	switch C.Z3_get_symbol_kind(ctx.c, sym) {
	case C.Z3_INT_SYMBOL:
		v := int(C.Z3_get_symbol_int(ctx.c, sym))
		return "#" + strconv.Itoa(v)
	case C.Z3_STRING_SYMBOL:
		return C.GoString(C.Z3_get_symbol_string(ctx.c, sym))
	default:
		return ""
	}
}

// ASTVisitFunc controls AST traversal; returning false skips visiting the node's children.
type ASTVisitFunc func(AST) bool

// Walk performs a depth-first traversal over the AST.
func (a AST) Walk(fn ASTVisitFunc) {
	if fn == nil || a.ctx == nil || a.a == nil {
		return
	}
	stack := []AST{a}
	for len(stack) > 0 {
		idx := len(stack) - 1
		node := stack[idx]
		stack = stack[:idx]
		if !fn(node) {
			continue
		}
		children := node.Children()
		for i := len(children) - 1; i >= 0; i-- {
			stack = append(stack, children[i])
		}
	}
}

// BoolValue attempts to interpret the AST as a boolean literal.
func (a AST) BoolValue() (bool, bool) {
	if a.ctx == nil || a.a == nil {
		return false, false
	}
	val := C.Z3_get_bool_value(a.ctx.c, a.a)
	switch val {
	case C.Z3_L_TRUE:
		return true, true
	case C.Z3_L_FALSE:
		return false, true
	default:
		return false, false
	}
}

// AsInt64 tries to read the AST as an Int numeral.
func (a AST) AsInt64() (int64, bool) {
	if a.ctx == nil || a.a == nil {
		return 0, false
	}
	if a.Kind() != ASTKindNumeral {
		return 0, false
	}
	var out C.longlong
	if bool(C.Z3_get_numeral_int64(a.ctx.c, a.a, &out)) {
		return int64(out), true
	}
	text := a.NumeralString()
	if text == "" {
		return 0, false
	}
	if i, err := strconv.ParseInt(text, 10, 64); err == nil {
		return i, true
	}
	rat := new(big.Rat)
	if _, ok := rat.SetString(text); ok && rat.IsInt() {
		num := rat.Num()
		if num.IsInt64() {
			return num.Int64(), true
		}
	}
	return 0, false
}

// AsStringLiteral returns the Go string represented by a Z3 string literal.
func (a AST) AsStringLiteral() (string, bool) {
	if a.ctx == nil || a.a == nil {
		return "", false
	}
	if !bool(C.Z3_is_string(a.ctx.c, a.a)) {
		return "", false
	}
	s := C.Z3_get_string(a.ctx.c, a.a)
	if s == nil {
		return "", false
	}
	return C.GoString(s), true
}

// ParseSMTLIB2String parses the SMT-LIB2 script and returns the asserted ASTs.
func (ctx *Context) ParseSMTLIB2String(input string) ([]AST, error) {
	if ctx == nil || ctx.c == nil {
		return nil, errors.New("nil context")
	}
	cstr := C.CString(input)
	defer C.free(unsafe.Pointer(cstr))
	vec := C.Z3_parse_smtlib2_string(ctx.c, cstr, 0, nil, nil, 0, nil, nil)
	if code := C.Z3_get_error_code(ctx.c); code != C.Z3_OK {
		msg := C.Z3_get_error_msg(ctx.c, code)
		if msg != nil {
			return nil, errors.New(C.GoString(msg))
		}
		return nil, errors.New("SMT-LIB2 parse error")
	}
	if vec == nil {
		return nil, nil
	}
	C.Z3_ast_vector_inc_ref(ctx.c, vec)
	defer C.Z3_ast_vector_dec_ref(ctx.c, vec)
	n := int(C.Z3_ast_vector_size(ctx.c, vec))
	out := make([]AST, 0, n)
	for i := 0; i < n; i++ {
		a := C.Z3_ast_vector_get(ctx.c, vec, C.uint(i))
		if a == nil {
			continue
		}
		C.Z3_inc_ref(ctx.c, a)
		out = append(out, AST{ctx: ctx, a: a})
	}
	return out, nil
}
