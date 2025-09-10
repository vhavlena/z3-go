//go:build cgo
// +build cgo

// Package z3 provides a minimal Go binding to Z3's C API.
// Prototype: limited functions for context, basic ASTs, solver, and model.
package z3

/*
// cgo headers (linker flags are provided via separate build-tagged files).
#include <stdlib.h>
#include "z3.h"

static Z3_symbol mk_str_symbol(Z3_context c, const char* s) {
	return Z3_mk_string_symbol(c, s);
}

// Wrap Z3_model_eval to avoid referencing Z3_bool / Z3_TRUE macros in cgo.
static int model_eval_wrap(Z3_context c, Z3_model m, Z3_ast a, int model_completion, Z3_ast* out) {
	return Z3_model_eval(c, m, a, model_completion, out);
}
*/
import "C"
import (
	"errors"
	"runtime"
	"unsafe"
)

// Context wraps Z3_context.
type Context struct{ c C.Z3_context }

// Config wraps Z3_config.
type Config struct{ cfg C.Z3_config }

// NewConfig creates a default config and enables model construction by default.
func NewConfig() *Config {
	cfg := &Config{cfg: C.Z3_mk_config()}
	// Ensure models are constructed by default so Model() and Eval() are meaningful.
	k := C.CString("model")
	v := C.CString("true")
	C.Z3_set_param_value(cfg.cfg, k, v)
	C.free(unsafe.Pointer(k))
	C.free(unsafe.Pointer(v))
	return cfg
}

// SetParam sets a configuration parameter before creating a context.
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

// Close frees the config.
func (cfg *Config) Close() {
	if cfg != nil && cfg.cfg != nil {
		C.Z3_del_config(cfg.cfg)
		cfg.cfg = nil
	}
}

// NewContext creates a new Z3 context with the given config (optional).
func NewContext(cfg *Config) *Context {
	var c C.Z3_context
	if cfg != nil {
		c = C.Z3_mk_context(cfg.cfg)
	} else {
		tmp := C.Z3_mk_config()
		c = C.Z3_mk_context(tmp)
		C.Z3_del_config(tmp)
	}
	ctx := &Context{c: c}
	runtime.SetFinalizer(ctx, func(x *Context) { x.Close() })
	return ctx
}

// Close deletes the context.
func (ctx *Context) Close() {
	if ctx != nil && ctx.c != nil {
		C.Z3_del_context(ctx.c)
		ctx.c = nil
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

// Solver wraps Z3_solver.
type Solver struct {
	ctx *Context
	s   C.Z3_solver
}

// Model wraps Z3_model.
type Model struct {
	ctx *Context
	m   C.Z3_model
}

// BoolSort returns the boolean sort.
func (ctx *Context) BoolSort() Sort { return Sort{ctx, C.Z3_mk_bool_sort(ctx.c)} }

// IntSort returns the integer sort.
func (ctx *Context) IntSort() Sort { return Sort{ctx, C.Z3_mk_int_sort(ctx.c)} }

// RealSort returns the real sort.
func (ctx *Context) RealSort() Sort { return Sort{ctx, C.Z3_mk_real_sort(ctx.c)} }

// StringSort returns the string sort (sequence of characters).
func (ctx *Context) StringSort() Sort { return Sort{ctx, C.Z3_mk_string_sort(ctx.c)} }

// StringSymbol creates a symbol from string.
func (ctx *Context) StringSymbol(name string) C.Z3_symbol {
	cstr := C.CString(name)
	defer C.free(unsafe.Pointer(cstr))
	return C.mk_str_symbol(ctx.c, cstr)
}

// Const creates a constant with given name and sort.
func (ctx *Context) Const(name string, s Sort) AST {
	sym := ctx.StringSymbol(name)
	a := C.Z3_mk_const(ctx.c, sym, s.s)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// IntVal creates an integer numeral.
func (ctx *Context) IntVal(v int64) AST {
	a := C.Z3_mk_int64(ctx.c, C.longlong(v), ctx.IntSort().s)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// RealVal creates a real numeral from a string like "1/3" or "2".
func (ctx *Context) RealVal(num string) AST {
	cstr := C.CString(num)
	defer C.free(unsafe.Pointer(cstr))
	a := C.Z3_mk_numeral(ctx.c, cstr, ctx.RealSort().s)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// StringVal creates a string literal.
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

// Not, And, Or, Eq, Add, Le, Lt, Ge, Gt
func (t AST) Not() AST {
	a := C.Z3_mk_not(t.ctx.c, t.a)
	C.Z3_inc_ref(t.ctx.c, a)
	return AST{t.ctx, a}
}

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

func Eq(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_eq(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

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

// Sub subtracts a list of arguments.
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

// Mul multiplies a list of arguments.
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

func Le(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_le(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}
func Lt(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_lt(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}
func Ge(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_ge(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}
func Gt(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_gt(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Implies builds (x => y).
func Implies(x, y AST) AST {
	ctx := x.ctx
	a := C.Z3_mk_implies(ctx.c, x.a, y.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Ite builds if-then-else (c ? t : e).
func Ite(c, t, e AST) AST {
	ctx := c.ctx
	a := C.Z3_mk_ite(ctx.c, c.a, t.a, e.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Distinct builds (distinct a1 a2 ... an).
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

// String/Sequence ops
// Concat concatenates sequences (e.g., strings) variadically.
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

// Length returns the length of a sequence (string) as an Int AST.
func Length(s AST) AST {
	ctx := s.ctx
	a := C.Z3_mk_seq_length(ctx.c, s.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Contains returns (contains s t).
func Contains(s, t AST) AST {
	ctx := s.ctx
	a := C.Z3_mk_seq_contains(ctx.c, s.a, t.a)
	C.Z3_inc_ref(ctx.c, a)
	return AST{ctx, a}
}

// Solver API
func (ctx *Context) NewSolver() *Solver {
	s := &Solver{ctx, C.Z3_mk_solver(ctx.c)}
	C.Z3_solver_inc_ref(ctx.c, s.s)
	runtime.SetFinalizer(s, func(x *Solver) { x.Close() })
	return s
}

func (s *Solver) Close() {
	if s != nil && s.s != nil {
		C.Z3_solver_dec_ref(s.ctx.c, s.s)
		s.s = nil
	}
}

func (s *Solver) Assert(a AST) { C.Z3_solver_assert(s.ctx.c, s.s, a.a) }

// Push creates a new solver scope.
func (s *Solver) Push() { C.Z3_solver_push(s.ctx.c, s.s) }

// Pop removes n scopes.
func (s *Solver) Pop(n uint) { C.Z3_solver_pop(s.ctx.c, s.s, C.uint(n)) }

// App applies a function declaration to arguments, producing an AST.
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

// ADT (algebraic data type) support

// Constructor is a temporary object used when creating datatypes.
type Constructor struct {
	ctx *Context
	c   C.Z3_constructor
}

// ADTField describes a field name and sort for a constructor (non-recursive).
type ADTField struct {
	Name string
	Sort Sort
}

// MkConstructor creates a constructor descriptor with explicit recognizer and fields.
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
			syms[i] = C.mk_str_symbol(ctx.c, cstr)
			C.free(unsafe.Pointer(cstr))
			sorts[i] = f.Sort.s
			refs[i] = 0 // non-recursive fields
		}
		fieldSyms = (*C.Z3_symbol)(unsafe.Pointer(&syms[0]))
		fieldSorts = (*C.Z3_sort)(unsafe.Pointer(&sorts[0]))
		sortRefs = (*C.uint)(unsafe.Pointer(&refs[0]))
	}
	c := C.Z3_mk_constructor(ctx.c, symName, symRec, C.uint(n), fieldSyms, fieldSorts, sortRefs)
	return &Constructor{ctx: ctx, c: c}
}

// ADTConstructorDecl contains the usable function declarations extracted from a constructor.
type ADTConstructorDecl struct {
	Constructor FuncDecl
	Recognizer  FuncDecl
	Accessors   []FuncDecl
}

// MkDatatype creates a datatype sort from constructors, and returns the sort and per-constructor declarations.
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
	// Query constructor declarations
	decls := make([]ADTConstructorDecl, n)
	for i := 0; i < n; i++ {
		k := ctors[i]
		// get number of fields
		nf := int(C.Z3_constructor_num_fields(ctx.c, k.c))
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
		// release constructor descriptor
		C.Z3_del_constructor(ctx.c, k.c)
	}
	// Increase ref to returned sort
	// Note: Z3_mk_datatype returns a sort associated with the context; no extra inc needed for sort objects.
	return Sort{ctx, srt}, decls
}

type CheckResult int

const (
	Unknown CheckResult = iota
	Sat
	Unsat
)

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

func (m *Model) Close() {
	if m != nil && m.m != nil {
		C.Z3_model_dec_ref(m.ctx.c, m.m)
		m.m = nil
	}
}

// Eval evaluates an AST in the model.
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

// String returns an SMT-LIB-like textual representation of the model.
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

// String helpers
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

func (s Sort) String() string {
	str := C.Z3_sort_to_string(s.ctx.c, s.s)
	if str == nil {
		return "<invalid-sort>"
	}
	return C.GoString(str)
}

// NumeralString returns a textual numeral if the AST is numeric; otherwise a string form.
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

// SMT-LIB2 parsing and solving helpers
// AssertSMTLIB2String parses an SMT-LIB2 command sequence from a string and asserts
// the resulting assertions into the solver.
func (s *Solver) AssertSMTLIB2String(input string) error {
	cstr := C.CString(input)
	defer C.free(unsafe.Pointer(cstr))
	vec := C.Z3_parse_smtlib2_string(s.ctx.c, cstr, 0, nil, nil, 0, nil, nil)
	// If parser errored, get error message
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
	// manage vector refs while iterating
	C.Z3_ast_vector_inc_ref(s.ctx.c, vec)
	defer C.Z3_ast_vector_dec_ref(s.ctx.c, vec)
	n := int(C.Z3_ast_vector_size(s.ctx.c, vec))
	for i := 0; i < n; i++ {
		a := C.Z3_ast_vector_get(s.ctx.c, vec, C.uint(i))
		if a != nil {
			C.Z3_solver_assert(s.ctx.c, s.s, a)
		}
	}
	return nil
}

// AssertSMTLIB2File parses an SMT-LIB2 file and asserts the resulting
// assertions into the solver.
func (s *Solver) AssertSMTLIB2File(path string) error {
	cpath := C.CString(path)
	defer C.free(unsafe.Pointer(cpath))
	vec := C.Z3_parse_smtlib2_file(s.ctx.c, cpath, 0, nil, nil, 0, nil, nil)
	// If parser errored, get error message
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
			C.Z3_solver_assert(s.ctx.c, s.s, a)
		}
	}
	return nil
}

// SolveSMTLIB2String parses assertions from SMT-LIB2 string and checks satisfiability.
func (s *Solver) SolveSMTLIB2String(input string) (CheckResult, error) {
	if err := s.AssertSMTLIB2String(input); err != nil {
		return Unknown, err
	}
	return s.Check()
}

// SolveSMTLIB2File parses assertions from SMT-LIB2 file and checks satisfiability.
func (s *Solver) SolveSMTLIB2File(path string) (CheckResult, error) {
	if err := s.AssertSMTLIB2File(path); err != nil {
		return Unknown, err
	}
	return s.Check()
}
