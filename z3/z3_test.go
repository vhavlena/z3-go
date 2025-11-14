//go:build cgo
// +build cgo

package z3

import (
	"os"
	"path/filepath"
	"testing"
)

func TestIntArithmeticAndModel(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	x := ctx.Const("x", ctx.IntSort())
	y := ctx.Const("y", ctx.IntSort())

	s := ctx.NewSolver()
	defer s.Close()

	s.Assert(Ge(x, ctx.IntVal(0)))
	s.Assert(Ge(y, ctx.IntVal(0)))
	s.Assert(Gt(Add(x, y), ctx.IntVal(5)))

	res, err := s.Check()
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}

	m := s.Model()
	if m == nil {
		t.Fatalf("no model")
	}
	defer m.Close()

	xv := m.Eval(x, true)
	yv := m.Eval(y, true)
	if xv.a == nil || yv.a == nil {
		t.Fatalf("model eval nil")
	}
}

func TestStrings(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s1 := ctx.Const("s1", ctx.StringSort())
	s2 := ctx.Const("s2", ctx.StringSort())

	s := ctx.NewSolver()
	defer s.Close()

	s.Assert(Contains(Concat(s1, ctx.StringVal("abc"), s2), ctx.StringVal("b")))
	res, err := s.Check()
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}
}

func TestADTOptionInt(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	// Define Option[Int] = None | Some(value:Int)
	someCtor := ctx.MkConstructor("Some", "is-Some", []ADTField{{Name: "val", Sort: ctx.IntSort()}})
	noneCtor := ctx.MkConstructor("None", "is-None", nil)
	optSort, decls := ctx.MkDatatype("OptionInt", []*Constructor{someCtor, noneCtor})

	// get decls
	some := decls[0]
	none := decls[1]

	// variable o : OptionInt
	o := ctx.Const("o", optSort)

	// Constrain o = Some(10)
	ten := ctx.IntVal(10)
	someApp := ctx.App(some.Constructor, ten)

	s := ctx.NewSolver()
	defer s.Close()
	s.Assert(Eq(o, someApp))
	// guide model completion
	s.Assert(ctx.App(some.Recognizer, o))

	// Check and query recognizer and accessor
	if res, err := s.Check(); err != nil || res != Sat {
		t.Fatalf("expected sat, got %v err %v", res, err)
	}
	m := s.Model()
	defer m.Close()
	if m == nil {
		t.Fatalf("no model")
	}

	// is-Some(o) should be true
	isSome := ctx.App(some.Recognizer, o)
	b := m.Eval(isSome, true)
	if b.String() != "true" {
		t.Fatalf("expected is-Some(o) to be true, got %s", b.String())
	}

	// Access value: val(o) == 10
	if len(some.Accessors) != 1 {
		t.Fatalf("expected 1 accessor")
	}
	val := ctx.App(some.Accessors[0], o)
	// additionally assert the value to guide the model
	s.Push()
	s.Assert(Eq(val, ten))
	if res, err := s.Check(); err != nil || res != Sat {
		t.Fatalf("expected sat after value assert, got %v err %v", res, err)
	}
	m2 := s.Model()
	defer m2.Close()
	v := m2.Eval(val, true)
	if v.NumeralString() != "10" {
		t.Fatalf("expected value 10, got %s", v.NumeralString())
	}

	// is-None(o) should be false
	isNone := ctx.App(none.Recognizer, o)
	b2 := m.Eval(isNone, true)
	if b2.String() != "false" {
		t.Fatalf("expected is-None(o) to be false, got %s", b2.String())
	}
}

func TestSMTLIB2FromString(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	smt := `
	(set-logic ALL)
	(declare-fun x () Int)
	(declare-fun y () Int)
	(assert (>= x 0))
	(assert (>= y 0))
	(assert (> (+ x y) 5))
	`

	if err := s.AssertSMTLIB2String(smt); err != nil {
		t.Fatalf("parse/assert smtlib2 string: %v", err)
	}
	res, err := s.Check()
	if err != nil || res != Sat {
		t.Fatalf("expected sat, got %v err %v", res, err)
	}

	// also via convenience method
	s2 := ctx.NewSolver()
	defer s2.Close()
	if res2, err := s2.SolveSMTLIB2String(smt); err != nil || res2 != Sat {
		t.Fatalf("SolveSMTLIB2String expected sat, got %v err %v", res2, err)
	}
}

func TestSMTLIB2FromFile(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	dir := t.TempDir()
	path := filepath.Join(dir, "example.smt2")
	content := `
	(set-logic QF_ALIA)
	(declare-fun a () (Array Int Int))
	(declare-fun i () Int)
	(assert (>= i 0))
	(assert (= (select a i) 42))
	(assert (= (select a i) 42))
	`
	if err := os.WriteFile(path, []byte(content), 0644); err != nil {
		t.Fatalf("write smt2: %v", err)
	}

	if err := s.AssertSMTLIB2File(path); err != nil {
		t.Fatalf("parse/assert smtlib2 file: %v", err)
	}
	res, err := s.Check()
	if err != nil || res != Sat {
		t.Fatalf("expected sat, got %v err %v", res, err)
	}

	// convenience method
	s2 := ctx.NewSolver()
	defer s2.Close()
	if res2, err := s2.SolveSMTLIB2File(path); err != nil || res2 != Sat {
		t.Fatalf("SolveSMTLIB2File expected sat, got %v err %v", res2, err)
	}
}

func TestSetOptionQuantifiers(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	if err := s.SetOption("smt.mbqi", true); err != nil {
		t.Fatalf("SetOption smt.mbqi: %v", err)
	}
	if err := s.SetOption("smt.qi.eager_threshold", 0); err != nil {
		t.Fatalf("SetOption smt.qi.eager_threshold: %v", err)
	}

	smt := `
		(set-logic AUFLIA)
		(declare-fun f (Int) Int)
		(assert (forall ((x Int)) (= (f x) x)))
		(assert (exists ((y Int)) (= (f y) 5)))
	`

	if err := s.AssertSMTLIB2String(smt); err != nil {
		t.Fatalf("assert quantified smtlib2: %v", err)
	}
	res, err := s.Check()
	if err != nil {
		t.Fatalf("check quantified formula: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}
}

func TestModelGenerationCases(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	cases := []struct {
		name  string
		build func(*Context) (*Solver, func(*testing.T, *Model))
	}{
		{
			name: "IntEquality",
			build: func(ctx *Context) (*Solver, func(*testing.T, *Model)) {
				x := ctx.Const("model_case_int_x", ctx.IntSort())
				s := ctx.NewSolver()
				s.Assert(Eq(x, ctx.IntVal(5)))
				return s, func(t *testing.T, m *Model) {
					t.Helper()
					val := m.Eval(x, true)
					if val.a == nil {
						t.Fatalf("model evaluation for x returned nil")
					}
					if v := val.NumeralString(); v != "5" {
						t.Fatalf("expected x == 5, got %s", v)
					}
				}
			},
		},
		{
			name: "BoolImplication",
			build: func(ctx *Context) (*Solver, func(*testing.T, *Model)) {
				a := ctx.Const("model_case_bool_a", ctx.BoolSort())
				b := ctx.Const("model_case_bool_b", ctx.BoolSort())
				s := ctx.NewSolver()
				s.Assert(Implies(a, b))
				s.Assert(a)
				return s, func(t *testing.T, m *Model) {
					t.Helper()
					aa := m.Eval(a, true)
					bb := m.Eval(b, true)
					if aa.a == nil || bb.a == nil {
						t.Fatalf("model evaluation for boolean vars returned nil")
					}
					if aa.String() != "true" {
						t.Fatalf("expected a == true, got %s", aa.String())
					}
					if bb.String() != "true" {
						t.Fatalf("expected b == true, got %s", bb.String())
					}
				}
			},
		},
		{
			name: "IntAddition",
			build: func(ctx *Context) (*Solver, func(*testing.T, *Model)) {
				x := ctx.Const("model_case_add_x", ctx.IntSort())
				y := ctx.Const("model_case_add_y", ctx.IntSort())
				s := ctx.NewSolver()
				s.Assert(Eq(Add(x, y), ctx.IntVal(10)))
				s.Assert(Eq(x, ctx.IntVal(3)))
				return s, func(t *testing.T, m *Model) {
					t.Helper()
					xVal := m.Eval(x, true)
					yVal := m.Eval(y, true)
					if xVal.a == nil || yVal.a == nil {
						t.Fatalf("model evaluation for addition vars returned nil")
					}
					if xv := xVal.NumeralString(); xv != "3" {
						t.Fatalf("expected x == 3, got %s", xv)
					}
					if yv := yVal.NumeralString(); yv != "7" {
						t.Fatalf("expected y == 7, got %s", yv)
					}
				}
			},
		},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			solver, check := tc.build(ctx)
			if solver == nil {
				t.Fatalf("nil solver from build")
			}
			if check == nil {
				t.Fatalf("nil checker for test case")
			}
			defer solver.Close()
			res, err := solver.Check()
			if err != nil {
				t.Fatalf("check error: %v", err)
			}
			if res != Sat {
				t.Fatalf("expected sat, got %v", res)
			}
			model := solver.Model()
			if model == nil {
				t.Fatalf("expected model, got nil")
			}
			defer model.Close()
			check(t, model)
		})
	}
}
