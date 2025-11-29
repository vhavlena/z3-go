//go:build cgo
// +build cgo

// Package z3 provides a minimal Go binding to Z3's C API.
// Prototype: limited functions for context, basic ASTs, solver, and model.
package z3

/*
// cgo headers (linker flags are provided via separate build-tagged files).
#include <stdlib.h>
#include "z3.h"

int model_eval_wrap(Z3_context c, Z3_model m, Z3_ast a, int model_completion, Z3_ast* out) {
	return Z3_model_eval(c, m, a, model_completion, out);
}

// Install a no-op error handler so Z3 doesn't abort on errors; we'll query errors from Go.
void go_z3_error_handler(Z3_context c, Z3_error_code e) {
	// no-op
}
static void z3_set_noop_error_handler(Z3_context c) {
	Z3_set_error_handler(c, go_z3_error_handler);
}
*/
import "C"
import (
	"runtime"
	"strconv"
	"unsafe"
)

// Context wraps Z3_context.
type Context struct {
	c          C.Z3_context
	namedSorts map[string]Sort
	declSorts  map[string]Sort
	funcDecls  map[string]FuncDecl
}

// Config wraps Z3_config.
type Config struct{ cfg C.Z3_config }

// NewConfig creates a default config and enables model construction so that
// solver models can be queried without additional configuration. Callers can
// mutate the returned Config via SetParam before NewContext consumes it.
func NewConfig() *Config {
	cfg := &Config{cfg: C.Z3_mk_config()}
	// Ensure models are constructed by default so Model() and Eval() are meaningful.
	k := C.CString("model")
	v := C.CString("true")
	C.Z3_set_param_value(cfg.cfg, k, v)
	C.free(unsafe.Pointer(k))
	C.free(unsafe.Pointer(v))
	// Enable auto configuration similar to command-line default.
	k2 := C.CString("auto_config")
	v2 := C.CString("true")
	C.Z3_set_param_value(cfg.cfg, k2, v2)
	C.free(unsafe.Pointer(k2))
	C.free(unsafe.Pointer(v2))
	return cfg
}

// SetParam sets a configuration parameter before creating a context. Z3 only
// consults these parameters at context creation time, so mutating the config
// after NewContext has been called has no effect on existing contexts.
func (cfg *Config) SetParam(key, value string) {
	if cfg == nil || cfg.cfg == nil {
		return
	}
	k := C.CString(key)
	v := C.CString(value)
	C.Z3_set_param_value(cfg.cfg, k, v)
	C.free(unsafe.Pointer(k))
	C.free(unsafe.Pointer(v))
}

// Close frees the config. It is safe to call multiple times or on a nil
// receiver.
func (cfg *Config) Close() {
	if cfg != nil && cfg.cfg != nil {
		C.Z3_del_config(cfg.cfg)
		cfg.cfg = nil
	}
}

// NewContext creates a new Z3 context with the given config (optional). When no
// config is provided a temporary config is created under the hood. Contexts
// install a no-op error handler so Z3 surfaces errors through Go return values
// instead of aborting the process.
func NewContext(cfg *Config) *Context {
	var c C.Z3_context
	if cfg != nil {
		c = C.Z3_mk_context(cfg.cfg)
	} else {
		tmp := C.Z3_mk_config()
		c = C.Z3_mk_context(tmp)
		C.Z3_del_config(tmp)
	}
	// Ensure errors are reported via error codes/messages instead of aborting.
	C.z3_set_noop_error_handler(c)
	ctx := &Context{c: c, namedSorts: make(map[string]Sort), declSorts: make(map[string]Sort), funcDecls: make(map[string]FuncDecl)}
	runtime.SetFinalizer(ctx, func(x *Context) { x.Close() })
	return ctx
}

// Close deletes the context and clears the bookkeeping caches (named sorts,
// declarations, recorded function declarations). After Close returns the
// context must not be used.
func (ctx *Context) Close() {
	if ctx != nil && ctx.c != nil {
		C.Z3_del_context(ctx.c)
		ctx.c = nil
	}
	if ctx != nil {
		ctx.namedSorts = nil
		ctx.declSorts = nil
		ctx.funcDecls = nil
	}
}

// Sort wraps Z3_sort.
type Sort struct {
	ctx *Context
	s   C.Z3_sort
}

// AST wraps Z3_ast.
type AST struct {
	ctx *Context
	a   C.Z3_ast
}

// FuncDecl wraps Z3_func_decl.
type FuncDecl struct {
	ctx *Context
	d   C.Z3_func_decl
}

// BoolSort returns the boolean sort and records it so later NamedSort lookups
// can rediscover the same handle.
func (ctx *Context) BoolSort() Sort {
	s := Sort{ctx, C.Z3_mk_bool_sort(ctx.c)}
	ctx.rememberSort(s)
	return s
}

// IntSort returns the integer sort representing mathematical integers.
func (ctx *Context) IntSort() Sort {
	s := Sort{ctx, C.Z3_mk_int_sort(ctx.c)}
	ctx.rememberSort(s)
	return s
}

// RealSort returns the real-number sort.
func (ctx *Context) RealSort() Sort {
	s := Sort{ctx, C.Z3_mk_real_sort(ctx.c)}
	ctx.rememberSort(s)
	return s
}

// StringSort returns the Z3 string sort (sequence of unicode characters).
func (ctx *Context) StringSort() Sort {
	s := Sort{ctx, C.Z3_mk_string_sort(ctx.c)}
	ctx.rememberSort(s)
	return s
}

// NamedSort returns a previously recorded sort reference by its symbolic name
// or printed form. Sorts are recorded automatically when created via helpers or
// when parsing SMT-LIB.
func (ctx *Context) NamedSort(name string) (Sort, bool) {
	if ctx == nil || name == "" {
		return Sort{}, false
	}
	if ctx.namedSorts == nil {
		return Sort{}, false
	}
	s, ok := ctx.namedSorts[name]
	return s, ok
}

// ConstDecl recreates a constant with the given name using a recorded sort. This
// is useful for SMT-LIB inputs where the declaration occurs in parsed scripts
// and the Go program needs to reference that declaration later.
func (ctx *Context) ConstDecl(name string) (AST, bool) {
	if ctx == nil || ctx.c == nil || name == "" {
		return AST{}, false
	}
	if ctx.declSorts == nil {
		return AST{}, false
	}
	s, ok := ctx.declSorts[name]
	if !ok || s.s == nil {
		return AST{}, false
	}
	return ctx.Const(name, s), true
}

// StringSymbol creates a Z3 symbol from the provided Go string.
func (ctx *Context) StringSymbol(name string) C.Z3_symbol {
	cstr := C.CString(name)
	defer C.free(unsafe.Pointer(cstr))
	return C.Z3_mk_string_symbol(ctx.c, cstr)
}

// Const creates a constant with the given name and sort, recording the mapping
// so ConstDecl/NamedSort can rediscover it later.
func (ctx *Context) Const(name string, s Sort) AST {
	sym := ctx.StringSymbol(name)
	a := C.Z3_mk_const(ctx.c, sym, s.s)
	C.Z3_inc_ref(ctx.c, a)
	ctx.rememberSort(s)
	ctx.rememberDeclSort(name, s)
	return AST{ctx, a}
}

func (ctx *Context) rememberDeclSort(name string, s Sort) {
	if ctx == nil || s.s == nil || name == "" {
		return
	}
	if ctx.declSorts == nil {
		ctx.declSorts = make(map[string]Sort)
	}
	if _, exists := ctx.declSorts[name]; !exists {
		ctx.declSorts[name] = s
	}
}

func (ctx *Context) rememberSort(s Sort) {
	if ctx == nil || s.s == nil {
		return
	}
	ctx.storeSortByKey(s, s.Name())
	ctx.storeSortByKey(s, s.String())
}

func (ctx *Context) storeSortByKey(s Sort, key string) {
	if ctx == nil || s.s == nil || key == "" {
		return
	}
	if ctx.namedSorts == nil {
		ctx.namedSorts = make(map[string]Sort)
	}
	if _, exists := ctx.namedSorts[key]; !exists {
		ctx.namedSorts[key] = s
	}
}

func (ctx *Context) recordSortsFromASTs(nodes []AST) {
	for _, node := range nodes {
		ctx.recordSortsFromAST(node)
	}
}

func (ctx *Context) recordSortsFromAST(root AST) {
	if ctx == nil || root.ctx == nil || root.a == nil {
		return
	}
	root.Walk(func(node AST) bool {
		if node.ctx == nil || node.a == nil {
			return true
		}
		s := node.Sort()
		ctx.rememberSort(s)
		if node.IsApp() && node.NumChildren() == 0 {
			ctx.rememberDeclSort(node.Decl().Name(), s)
		}
		if node.IsApp() {
			decl := node.Decl()
			name := decl.Name()
			if name != "" {
				if ctx.funcDecls == nil {
					ctx.funcDecls = make(map[string]FuncDecl)
				}
				if _, ok := ctx.funcDecls[name]; !ok {
					ctx.funcDecls[name] = decl
				}
			}
		}
		return true
	})
}

// FuncDeclByName returns a previously encountered function declaration by name.
func (ctx *Context) FuncDeclByName(name string) (FuncDecl, bool) {
	if ctx == nil || name == "" || ctx.funcDecls == nil {
		return FuncDecl{}, false
	}
	decl, ok := ctx.funcDecls[name]
	return decl, ok
}

// IntVal creates an integer numeral AST from the provided value.
func (ctx *Context) IntVal(v int64) AST {
	// Use string-based numeral creation to avoid platform-dependent C integer types.
	s := strconv.FormatInt(v, 10)
	cstr := C.CString(s)
	defer C.free(unsafe.Pointer(cstr))
	a := C.Z3_mk_numeral(ctx.c, cstr, ctx.IntSort().s)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// RealVal creates a real numeral from a string like "1/3" or "2". Z3 accepts
// rational literals, so callers should pass fractions in textual form.
func (ctx *Context) RealVal(num string) AST {
	cstr := C.CString(num)
	defer C.free(unsafe.Pointer(cstr))
	a := C.Z3_mk_numeral(ctx.c, cstr, ctx.RealSort().s)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// StringVal creates a string literal AST.
func (ctx *Context) StringVal(s string) AST {
	cstr := C.CString(s)
	defer C.free(unsafe.Pointer(cstr))
	a := C.Z3_mk_string(ctx.c, cstr)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// BoolVal creates a boolean constant true/false.
func (ctx *Context) BoolVal(b bool) AST {
	var a C.Z3_ast
	if b {
		a = C.Z3_mk_true(ctx.c)
	} else {
		a = C.Z3_mk_false(ctx.c)
	}
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// String returns an SMT-LIB-like textual representation of the AST.
func (a AST) String() string {
	if a.a == nil {
		return "<nil>"
	}
	s := C.Z3_ast_to_string(a.ctx.c, a.a)
	if s == nil {
		return "<invalid>"
	}
	return C.GoString(s)
}

// String returns an SMT-LIB-like textual representation of the sort.
func (s Sort) String() string {
	if s.ctx == nil || s.s == nil {
		return ""
	}
	str := C.Z3_sort_to_string(s.ctx.c, s.s)
	if str == nil {
		return "<invalid-sort>"
	}
	return C.GoString(str)
}

// Name returns the symbolic name of the sort if available.
func (s Sort) Name() string {
	if s.ctx == nil || s.s == nil {
		return ""
	}
	sym := C.Z3_get_sort_name(s.ctx.c, s.s)
	return symbolToString(s.ctx, sym)
}

// NumeralString returns a textual numeral if the AST is numeric.
func (a AST) NumeralString() string {
	if a.a == nil {
		return ""
	}
	s := C.Z3_get_numeral_string(a.ctx.c, a.a)
	if s == nil {
		return ""
	}
	return C.GoString(s)
}
