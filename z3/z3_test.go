//go:build cgo
// +build cgo

package z3

import (
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"
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
	if err := s.SetOption("smt.qi.eager_threshold", 0.0); err != nil {
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

func TestDistinctBuilderUnsat(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	x := ctx.Const("distinct_x", ctx.IntSort())
	s := ctx.NewSolver()
	defer s.Close()
	s.Assert(Distinct(x, x))

	res, err := s.Check()
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Unsat {
		t.Fatalf("expected unsat due to distinct(x, x), got %v", res)
	}
}

func TestSequenceLengthAndContains(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s1 := ctx.Const("seq_s1", ctx.StringSort())
	s := ctx.NewSolver()
	defer s.Close()

	s.Assert(Eq(Length(s1), ctx.IntVal(5)))
	s.Assert(Contains(s1, ctx.StringVal("ab")))
	s.Assert(Contains(s1, ctx.StringVal("cd")))

	res, err := s.Check()
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}
	m := s.Model()
	if m == nil {
		t.Fatalf("expected model")
	}
	defer m.Close()

	lenAST := Length(s1)
	lenVal := m.Eval(lenAST, true)
	if v, ok := lenVal.AsInt64(); !ok || v != 5 {
		t.Fatalf("expected length 5, got %s (ok=%v)", lenVal.String(), ok)
	}

	containsAB := m.Eval(Contains(s1, ctx.StringVal("ab")), true)
	if val, ok := containsAB.BoolValue(); !ok || !val {
		t.Fatalf("expected contains \"ab\" to be true, got %s", containsAB.String())
	}
	containsCD := m.Eval(Contains(s1, ctx.StringVal("cd")), true)
	if val, ok := containsCD.BoolValue(); !ok || !val {
		t.Fatalf("expected contains \"cd\" to be true, got %s", containsCD.String())
	}
}

func TestSolverSetOptionUnsupportedType(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	if err := s.SetOption("timeout", 5); err != nil {
		t.Fatalf("SetOption timeout int failed: %v", err)
	}
	if err := s.SetOption("timeout", struct{}{}); err == nil {
		t.Fatalf("expected SetOption to reject unsupported value type")
	}
}

// TestSolverSetOptionWrongKindRejected is a regression test for SetOption
// silently no-op'ing when a value's Go type maps to the wrong Z3_params kind
// for the target option: "timeout" is a uint-kind solver option, so setting
// it with a bool must be rejected rather than silently ignored.
func TestSolverSetOptionWrongKindRejected(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	if err := s.SetOption("timeout", true); err == nil {
		t.Fatalf("expected SetOption to reject a bool value for the uint-kind \"timeout\" option")
	}
}

// TestSolverSetOptionUnknownNameRejected is a regression test for SetOption
// silently no-op'ing on a misspelled/nonexistent option name instead of
// returning an error.
func TestSolverSetOptionUnknownNameRejected(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	if err := s.SetOption("totally_bogus_option_name_xyz", true); err == nil {
		t.Fatalf("expected SetOption to reject an unknown option name")
	}
}

// TestSolverSetOptionUintOutOfRange is a regression test for int64/uint64
// option values being silently truncated (and sign-wrapped, for negatives)
// into Z3_params_set_uint's 32-bit unsigned parameter instead of erroring.
func TestSolverSetOptionUintOutOfRange(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	if err := s.SetOption("timeout", int64(-1)); err == nil {
		t.Fatalf("expected SetOption to reject a negative timeout instead of wrapping it to a huge uint32")
	}
	if err := s.SetOption("timeout", int64(5_000_000_000)); err == nil {
		t.Fatalf("expected SetOption to reject a timeout value that overflows uint32 instead of truncating it")
	}
}

// TestNewSimpleSolverBasicSat checks that NewSimpleSolver behaves like
// NewSolver on an ordinary quantifier-free problem: same API, same correct
// result.
func TestNewSimpleSolverBasicSat(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	x := ctx.Const("x", ctx.IntSort())
	y := ctx.Const("y", ctx.IntSort())

	s := ctx.NewSimpleSolver()
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

// TestNewSimpleSolverQuantifiedSeqDatatypeRegression is a regression test for
// a real formula (extracted from VeriRego's SMT generation for a Rego policy
// with two independent `some x; input.arr[x]` wildcards) that hangs under
// NewSolver's combined/tactic-based solver but is solved quickly by
// NewSimpleSolver's plain incremental core; see NewSolver's doc comment for
// the general caveat this test guards against regressing.
//
// This test previously appeared flaky across platforms/CI - occasionally
// failing with "(incomplete quantifiers)" or "timeout" - which looked like
// Z3's quantifier-instantiation search order being platform-dependent. The
// actual cause was unrelated to this formula: Solver.SetOption used to apply
// options by parsing an SMT-LIB2 "(set-option ...)" string, which Z3 treats
// as a process-global parameter change rather than a per-solver one. A
// different test earlier in this file (TestSolverSetOptionUnsupportedType)
// sets "timeout" to 5ms that way, which leaked into every solver created
// afterward in the same test binary - including this one - starving it of
// time regardless of solver construction or random seed. SetOption now uses
// Z3_solver_set_params, which is genuinely solver-scoped, so a plain,
// direct check is sufficient here again.
func TestNewSimpleSolverQuantifiedSeqDatatypeRegression(t *testing.T) {
	content, err := os.ReadFile(filepath.Join("testdata", "quantified_seq_datatype_regression.smt2"))
	if err != nil {
		t.Fatalf("read testdata: %v", err)
	}

	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSimpleSolver()
	defer s.Close()

	if err := s.AssertSMTLIB2String(string(content)); err != nil {
		t.Fatalf("assert smtlib2: %v", err)
	}

	done := make(chan struct{})
	var res CheckResult
	var checkErr error
	start := time.Now()
	go func() {
		defer close(done)
		res, checkErr = s.Check()
	}()

	select {
	case <-done:
	case <-time.After(10 * time.Second):
		ctx.Interrupt()
		<-done
		t.Fatalf("NewSimpleSolver did not finish within 10s; this formula is expected to solve in milliseconds")
	}
	elapsed := time.Since(start)

	if checkErr != nil {
		t.Fatalf("check error: %v", checkErr)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}
	t.Logf("NewSimpleSolver solved in %v", elapsed)
}

// TestSolverCLIQuantifiedSeqDatatypeRegression drives the same formula as
// TestNewSimpleSolverQuantifiedSeqDatatypeRegression through the actual "z3"
// executable (skipping if it isn't on PATH) rather than the C API, matching
// the manual `z3 testdata/....smt2` runs used earlier to diagnose that test.
func TestSolverCLIQuantifiedSeqDatatypeRegression(t *testing.T) {
	if _, err := exec.LookPath("z3"); err != nil {
		t.Skip("z3 executable not found on PATH")
	}

	content, err := os.ReadFile(filepath.Join("testdata", "quantified_seq_datatype_regression.smt2"))
	if err != nil {
		t.Fatalf("read testdata: %v", err)
	}

	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolverCLI()
	defer s.Close()
	if err := s.AssertSMTLIB2String(string(content)); err != nil {
		t.Fatalf("assert smtlib2: %v", err)
	}

	start := time.Now()
	res, err := s.CheckContext(context.Background(), 10*time.Second)
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}
	t.Logf("SolverCLI solved in %v", time.Since(start))

	m := s.Model()
	if m == nil {
		t.Fatalf("expected a reconstructed model")
	}
	defer m.Close()
}

// TestSolverCLIBasic exercises SolverCLI's sat/unsat parsing, model
// reconstruction, and error handling on small formulas, independent of the
// regression formula above.
func TestSolverCLIBasic(t *testing.T) {
	if _, err := exec.LookPath("z3"); err != nil {
		t.Skip("z3 executable not found on PATH")
	}

	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	t.Run("sat", func(t *testing.T) {
		s := ctx.NewSolverCLI()
		defer s.Close()
		if err := s.AssertSMTLIB2String("(declare-fun x () Int)\n(assert (> x 0))\n(assert (< x 10))\n"); err != nil {
			t.Fatalf("assert: %v", err)
		}
		res, err := s.Check()
		if err != nil {
			t.Fatalf("check error: %v", err)
		}
		if res != Sat {
			t.Fatalf("expected sat, got %v", res)
		}
		m := s.Model()
		if m == nil {
			t.Fatalf("expected a reconstructed model")
		}
		defer m.Close()

		x := ctx.Const("x", ctx.IntSort())
		v := m.Eval(x, true)
		if v.a == nil {
			t.Fatalf("model eval for x returned nil")
		}
		n, ok := v.AsInt64()
		if !ok || n <= 0 || n >= 10 {
			t.Fatalf("expected 0 < x < 10, got %s (ok=%v)", v.String(), ok)
		}
	})

	t.Run("unsat", func(t *testing.T) {
		s := ctx.NewSolverCLI()
		defer s.Close()
		if err := s.AssertSMTLIB2String("(declare-fun y () Int)\n(assert (> y 0))\n(assert (< y 0))\n"); err != nil {
			t.Fatalf("assert: %v", err)
		}
		res, err := s.Check()
		if err != nil {
			t.Fatalf("check error: %v", err)
		}
		if res != Unsat {
			t.Fatalf("expected unsat, got %v", res)
		}
		if m := s.Model(); m != nil {
			m.Close()
			t.Fatalf("expected no model for unsat")
		}
	})

	t.Run("bad executable path", func(t *testing.T) {
		s := ctx.NewSolverCLIPath(filepath.Join(t.TempDir(), "no-such-z3-binary"))
		defer s.Close()
		if _, err := s.Check(); err == nil {
			t.Fatalf("expected an error for a nonexistent z3 executable")
		}
	})
}

// TestSolverCLISurvivesRejectedOption is a regression test for CheckContext
// only looking at the first line of the subprocess's stdout: an invalid
// SetOption command makes z3 print an "(error ...)" line (on stdout, not
// stderr) before it still runs check-sat and solves the query, and that sat
// result must not be discarded as a generic subprocess failure.
func TestSolverCLISurvivesRejectedOption(t *testing.T) {
	if _, err := exec.LookPath("z3"); err != nil {
		t.Skip("z3 executable not found on PATH")
	}

	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolverCLI()
	defer s.Close()

	if err := s.SetOption("totally_bogus_option_name_xyz", true); err != nil {
		t.Fatalf("SetOption: %v", err)
	}
	if err := s.AssertSMTLIB2String("(declare-fun x () Int)\n(assert (> x 0))\n(assert (< x 10))\n"); err != nil {
		t.Fatalf("assert: %v", err)
	}

	res, err := s.Check()
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat despite the rejected option, got %v", res)
	}
}

// TestSolverCLIQuotesSpecialConstantNames is a regression test for constant
// names being spliced into the "(get-value (...))" request without SMT-LIB2
// |...| quoting: a declared symbol containing a space must still have its
// value retrieved and reconstructed into the model.
func TestSolverCLIQuotesSpecialConstantNames(t *testing.T) {
	if _, err := exec.LookPath("z3"); err != nil {
		t.Skip("z3 executable not found on PATH")
	}

	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolverCLI()
	defer s.Close()

	if err := s.AssertSMTLIB2String("(declare-fun |my var| () Int)\n(assert (> |my var| 0))\n(assert (< |my var| 10))\n"); err != nil {
		t.Fatalf("assert: %v", err)
	}

	res, err := s.Check()
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}
	m := s.Model()
	if m == nil {
		t.Fatalf("expected a reconstructed model covering the quoted symbol")
	}
	defer m.Close()
}

// TestSolverCLIModelIncompleteForArityFunctions is a regression test for
// SolverCLI.Model() silently omitting uninterpreted functions with real
// arity with no way for the caller to detect the gap: ModelIncomplete must
// report true whenever such a function was present in a sat formula.
func TestSolverCLIModelIncompleteForArityFunctions(t *testing.T) {
	if _, err := exec.LookPath("z3"); err != nil {
		t.Skip("z3 executable not found on PATH")
	}

	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolverCLI()
	defer s.Close()

	if err := s.AssertSMTLIB2String("(declare-fun f (Int) Int)\n(assert (= (f 0) 1))\n"); err != nil {
		t.Fatalf("assert: %v", err)
	}

	res, err := s.Check()
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}
	if !s.ModelIncomplete() {
		t.Fatalf("expected ModelIncomplete to report true for a formula using an arity-1 function")
	}
}
