//go:build !cgo
// +build !cgo

package z3

import "errors"

// ASTKind is a placeholder when cgo is disabled.
type ASTKind int

const (
	ASTKindNumeral ASTKind = iota
	ASTKindApp
	ASTKindVar
	ASTKindQuantifier
	ASTKindSort
	ASTKindFuncDecl
	ASTKindUnknown
)

func (k ASTKind) String() string { return "ast-kind" }

// ASTVisitFunc is available for build consistency when cgo is disabled.
type ASTVisitFunc func(AST) bool

// DeclKind is a placeholder when cgo is disabled.
type DeclKind int

const (
	DeclOpTrue DeclKind = iota
	DeclOpFalse
	DeclOpEq
	DeclOpDistinct
	DeclOpIte
	DeclOpAnd
	DeclOpOr
	DeclOpNot
	DeclOpAdd
	DeclOpSub
	DeclOpMul
	DeclOpDiv
	DeclOpIDiv
	DeclOpRem
	DeclOpMod
	DeclOpLE
	DeclOpGE
	DeclOpLT
	DeclOpGT
	DeclOpConcat
	DeclOpSeqLength
	DeclOpSeqContains
	DeclOpUninterpreted
)

func (k DeclKind) String() string { return "decl-kind" }

func (a AST) Kind() ASTKind           { return ASTKindUnknown }
func (a AST) IsApp() bool             { return false }
func (a AST) NumChildren() int        { return 0 }
func (a AST) Child(int) AST           { return AST{} }
func (a AST) Children() []AST         { return nil }
func (a AST) Walk(ASTVisitFunc)       {}
func (a AST) BoolValue() (bool, bool) { return false, false }
func (a AST) AsInt64() (int64, bool)  { return 0, false }
func (a AST) AsStringLiteral() (string, bool) {
	return "", false
}

func (d FuncDecl) Kind() DeclKind { return DeclOpUninterpreted }
func (d FuncDecl) Arity() int     { return 0 }
func (d FuncDecl) Name() string   { return "" }

var errNoCgo = errors.New("z3: cgo support is required")

func (ctx *Context) ParseSMTLIB2String(string) ([]AST, error) { return nil, errNoCgo }
