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
