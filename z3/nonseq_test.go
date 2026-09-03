//go:build cgo
// +build cgo

package z3

import (
	"os/exec"
	"strings"
	"testing"
)

// This file holds a table of SMT-LIB2 queries that stay entirely outside the
// sequence/string theory, together with drivers that run the whole table
// through Solver (the cgo-linked library) and SolverCLI (the "z3"
// executable).
//
// Its purpose is regression coverage for the *rest* of the solver when the
// string theory is replaced: the package is also built and tested against
// Z3-Noodler (see z3_flags_noodler.go), a Z3 fork that swaps out the seq/str
// decision procedure for an automata-based one. Changes to that theory are
// not supposed to affect arithmetic, bit-vectors, arrays, uninterpreted
// functions, datatypes, floating-point or quantifier reasoning at all, and
// this table is what makes that "not supposed to" checkable: `go test` on a
// vanilla-Z3 build pins down the expected answers, and `go test -tags
// noodler` (plus TestNoodlerNonSeqFormulasCLI in z3_noodler_test.go, which
// drives the same table through a noodler executable) asserts the fork
// agrees on every one of them.
//
// The queries deliberately avoid (set-logic ...), so that no case can be
// answered from a declared logic's restrictions instead of the theory
// reasoning it is meant to exercise, and so that appending an entailment
// check's extra assertion (see nonSeqFormula.entailed) stays valid text -
// it is that concatenated text that the SolverCLI driver forwards verbatim
// to the z3 subprocess (see solver_cli.go's rawSegments).

// nonSeqFormula is one seq-free SMT-LIB2 query plus everything the drivers
// need to validate a solver's answer on it.
type nonSeqFormula struct {
	// name identifies the case as a subtest, prefixed with the theory it
	// exercises.
	name string
	// smt is the query: declarations and assertions only, no set-logic and
	// no control commands.
	smt string
	// want is the expected Check result.
	want CheckResult
	// entailed lists formulas that hold in *every* model of smt, each
	// checked by re-asserting smt together with that formula's negation on a
	// fresh solver and requiring unsat. This is what turns a bare "sat" -
	// which a solver can return for the wrong reasons - into a check that
	// the solver actually derived the intended consequences, without
	// depending on model reconstruction (which SolverCLI only supports for
	// 0-ary symbols) or on which of several models a solver happens to pick.
	//
	// The negation is appended to smt's own text rather than asserted as a
	// second segment on the same solver: AssertSMTLIB2String hands each
	// string to Z3_parse_smtlib2_string separately, and that parser starts
	// from an empty symbol table every time, so a follow-up segment cannot
	// refer to declarations made by an earlier one. Only meaningful for
	// want == Sat.
	entailed []string
}

// nonSeqFormulas covers each non-seq theory with both a sat case whose
// consequences are pinned down by entailed, and an unsat case that requires
// the theory's own reasoning (rather than propositional conflict) to refute.
var nonSeqFormulas = []nonSeqFormula{
	{
		// Unique solution: x<3 and x>0 leaves x=1 (no integer y) and x=2.
		name: "lia/sat_unique_solution",
		smt: `
			(declare-fun x () Int)
			(declare-fun y () Int)
			(assert (= (+ (* 3 x) (* 2 y)) 12))
			(assert (> x 0))
			(assert (> y 0))
			(assert (< x 3))
		`,
		want:     Sat,
		entailed: []string{"(= x 2)", "(= y 3)"},
	},
	{
		// Needs integrality, not just linear-real reasoning: 2x=7 has a
		// rational solution but no integer one.
		name: "lia/unsat_parity",
		smt: `
			(declare-fun x () Int)
			(assert (= (* 2 x) 7))
		`,
		want: Unsat,
	},
	{
		// Farkas-style refutation: (a+b>=4) and (a+2b<=5) give b<=1.
		name: "lra/unsat_farkas",
		smt: `
			(declare-fun a () Real)
			(declare-fun b () Real)
			(assert (>= (+ a b) 4.0))
			(assert (<= (+ a (* 2.0 b)) 5.0))
			(assert (>= b 2.0))
		`,
		want: Unsat,
	},
	{
		name: "int/sat_div_mod",
		smt: `
			(declare-fun x () Int)
			(assert (= (mod x 5) 3))
			(assert (> x 10))
			(assert (< x 16))
		`,
		want:     Sat,
		entailed: []string{"(= x 13)", "(= (div x 5) 2)"},
	},
	{
		// Nonlinear integer arithmetic: the only factorization of 91 with
		// 1 < x < y.
		name: "nia/sat_factorization",
		smt: `
			(declare-fun x () Int)
			(declare-fun y () Int)
			(assert (= (* x y) 91))
			(assert (> x 1))
			(assert (> y x))
		`,
		want:     Sat,
		entailed: []string{"(= x 7)", "(= y 13)"},
	},
	{
		// 2 is not a perfect square, so no integer x in (0,5) squares to it.
		name: "nia/unsat_no_integer_root",
		smt: `
			(declare-fun x () Int)
			(assert (= (* x x) 2))
			(assert (> x 0))
			(assert (< x 5))
		`,
		want: Unsat,
	},
	{
		// Real algebraic reasoning: r must be the irrational sqrt(2), which
		// the entailment bounds without naming it.
		name: "nra/sat_sqrt_two",
		smt: `
			(declare-fun r () Real)
			(assert (= (* r r) 2.0))
			(assert (> r 0.0))
		`,
		want:     Sat,
		entailed: []string{"(> r 1.414)", "(< r 1.4143)"},
	},
	{
		name: "mixed/sat_int_real_coercions",
		smt: `
			(declare-fun n () Int)
			(declare-fun r () Real)
			(assert (= r (/ 7.0 2.0)))
			(assert (= n (to_int r)))
		`,
		want:     Sat,
		entailed: []string{"(= n 3)", "(> r (to_real n))"},
	},
	{
		// (xor a b c) with a=b reduces to c.
		name: "bool/sat_xor_chain",
		smt: `
			(declare-fun a () Bool)
			(declare-fun b () Bool)
			(declare-fun c () Bool)
			(assert (xor a b c))
			(assert (= a b))
		`,
		want:     Sat,
		entailed: []string{"c"},
	},
	{
		// Purely propositional: three pigeons, two holes.
		name: "bool/unsat_pigeonhole",
		smt: `
			(declare-fun p1h1 () Bool)
			(declare-fun p1h2 () Bool)
			(declare-fun p2h1 () Bool)
			(declare-fun p2h2 () Bool)
			(declare-fun p3h1 () Bool)
			(declare-fun p3h2 () Bool)
			(assert (or p1h1 p1h2))
			(assert (or p2h1 p2h2))
			(assert (or p3h1 p3h2))
			(assert (not (and p1h1 p2h1)))
			(assert (not (and p1h1 p3h1)))
			(assert (not (and p2h1 p3h1)))
			(assert (not (and p1h2 p2h2)))
			(assert (not (and p1h2 p3h2)))
			(assert (not (and p2h2 p3h2)))
		`,
		want: Unsat,
	},
	{
		name: "ite/sat_branch_selection",
		smt: `
			(declare-fun x () Int)
			(declare-fun y () Int)
			(assert (= y (ite (> x 0) (* 2 x) (- x))))
			(assert (= y 6))
			(assert (< x 0))
		`,
		want:     Sat,
		entailed: []string{"(= x (- 6))"},
	},
	{
		// Pigeonhole through arithmetic instead of propositional structure:
		// three pairwise-distinct integers cannot all fit in {1,2}.
		name: "ite/unsat_distinct_range",
		smt: `
			(declare-fun x () Int)
			(declare-fun y () Int)
			(declare-fun z () Int)
			(assert (distinct x y z))
			(assert (and (<= 1 x) (<= x 2)))
			(assert (and (<= 1 y) (<= y 2)))
			(assert (and (<= 1 z) (<= z 2)))
		`,
		want: Unsat,
	},
	{
		// EUF over an uninterpreted sort: c is one of two distinct elements
		// and not the first, so it is the second.
		name: "euf/sat_uninterpreted_sort",
		smt: `
			(declare-sort U 0)
			(declare-fun p () U)
			(declare-fun q () U)
			(declare-fun c () U)
			(assert (distinct p q))
			(assert (or (= c p) (= c q)))
			(assert (not (= c p)))
		`,
		want:     Sat,
		entailed: []string{"(= c q)"},
	},
	{
		// Congruence closure: equal arguments force equal results.
		name: "euf/unsat_congruence",
		smt: `
			(declare-fun f (Int) Int)
			(declare-fun x () Int)
			(declare-fun y () Int)
			(assert (= x y))
			(assert (not (= (f x) (f y))))
		`,
		want: Unsat,
	},
	{
		// The store/select axiom: reading back a written index yields the
		// written value, so its negation is unsatisfiable for every a, i, v.
		name: "array/unsat_store_select_axiom",
		smt: `
			(declare-fun a () (Array Int Int))
			(declare-fun i () Int)
			(declare-fun v () Int)
			(assert (not (= (select (store a i v) i) v)))
		`,
		want: Unsat,
	},
	{
		name: "array/sat_store_preserves_other_indices",
		smt: `
			(declare-fun a () (Array Int Int))
			(declare-fun k () Int)
			(assert (= (select a 1) 10))
			(assert (= k (select (store a 2 20) 1)))
		`,
		want:     Sat,
		entailed: []string{"(= k 10)", "(= (select (store a 2 20) 2) 20)"},
	},
	{
		// Array extensionality: equal arrays must agree at every index.
		name: "array/unsat_extensionality",
		smt: `
			(declare-fun a () (Array Int Int))
			(declare-fun b () (Array Int Int))
			(assert (= a (store b 1 5)))
			(assert (not (= (select a 1) 5)))
		`,
		want: Unsat,
	},
	{
		// Bit-vector wraparound: the only 8-bit x with x+1 = 0 is 0xff.
		name: "bv/sat_wraparound",
		smt: `
			(declare-fun x () (_ BitVec 8))
			(assert (= (bvadd x #x01) #x00))
		`,
		want:     Sat,
		entailed: []string{"(= x #xff)"},
	},
	{
		// bvand and bvor agreeing forces x = y = that value bitwise.
		name: "bv/sat_bitwise_agreement",
		smt: `
			(declare-fun x () (_ BitVec 8))
			(declare-fun y () (_ BitVec 8))
			(assert (= (bvand x y) #x0f))
			(assert (= (bvor x y) #x0f))
		`,
		want:     Sat,
		entailed: []string{"(= x #x0f)", "(= y #x0f)"},
	},
	{
		name: "bv/sat_shift",
		smt: `
			(declare-fun x () (_ BitVec 32))
			(assert (= (bvshl x (_ bv3 32)) (_ bv40 32)))
			(assert (bvult x (_ bv16 32)))
		`,
		want:     Sat,
		entailed: []string{"(= x (_ bv5 32))"},
	},
	{
		// Unsigned overflow is not an ordering: 0xff + 1 wraps to 0x00, so
		// x < x+1 fails exactly at the maximum.
		name: "bv/unsat_overflow_not_increasing",
		smt: `
			(declare-fun x () (_ BitVec 8))
			(assert (bvult x (bvadd x #x01)))
			(assert (= x #xff))
		`,
		want: Unsat,
	},
	{
		name: "array_bv/sat_combined_theories",
		smt: `
			(declare-fun m () (Array (_ BitVec 4) (_ BitVec 8)))
			(declare-fun k () (_ BitVec 8))
			(assert (= (select m #x1) #xaa))
			(assert (= k (select (store m #x2 #xbb) #x1)))
		`,
		want:     Sat,
		entailed: []string{"(= k #xaa)"},
	},
	{
		// Recursive datatype (a list, i.e. the shape a seq is often modeled
		// with, but decided by the datatype solver rather than the string
		// one), plus tester and accessor reasoning.
		name: "datatype/sat_list_shape",
		smt: `
			(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
			(declare-fun l () Lst)
			(assert ((_ is cons) l))
			(assert (= (hd l) 7))
			(assert (= (tl l) nil))
		`,
		want:     Sat,
		entailed: []string{"(= l (cons 7 nil))", "(not ((_ is nil) l))"},
	},
	{
		// Datatypes are acyclic, so no list equals its own tail extension.
		name: "datatype/unsat_occurs_check",
		smt: `
			(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
			(declare-fun l () Lst)
			(assert (= l (cons 1 l)))
		`,
		want: Unsat,
	},
	{
		name: "quant/sat_forall_uf",
		smt: `
			(declare-fun f (Int) Int)
			(assert (forall ((x Int)) (= (f x) (+ x 1))))
		`,
		want:     Sat,
		entailed: []string{"(= (f 3) 4)", "(> (f 0) 0)"},
	},
	{
		name: "quant/sat_forall_array",
		smt: `
			(declare-fun a () (Array Int Int))
			(declare-fun j () Int)
			(assert (forall ((i Int)) (= (select a i) 0)))
		`,
		want:     Sat,
		entailed: []string{"(= (select a j) 0)"},
	},
	{
		// A universally quantified positivity claim contradicted by one
		// instance.
		name: "quant/unsat_instance_conflict",
		smt: `
			(declare-fun f (Int) Int)
			(assert (forall ((x Int)) (> (f x) 0)))
			(assert (= (f 5) (- 1)))
		`,
		want: Unsat,
	},
	{
		// Floating point is not the reals: 0.1+0.2 is strictly greater than
		// 0.3 in Float64 (it rounds to 0.30000000000000004), so the solver
		// has to model rounding rather than treat these as rationals. Note
		// that this needs double precision - in Float32 the two rounded
		// values do coincide.
		name: "fp/sat_rounding",
		smt: `
			(declare-fun x () Float64)
			(assert (= x (fp.add roundNearestTiesToEven
				((_ to_fp 11 53) roundNearestTiesToEven 0.1)
				((_ to_fp 11 53) roundNearestTiesToEven 0.2))))
		`,
		want: Sat,
		entailed: []string{
			"(not (= x ((_ to_fp 11 53) roundNearestTiesToEven 0.3)))",
			"(fp.gt x ((_ to_fp 11 53) roundNearestTiesToEven 0.3))",
			"(= x ((_ to_fp 11 53) roundNearestTiesToEven 0.30000000000000004))",
		},
	},
	{
		// NaN is not fp.eq to itself.
		name: "fp/unsat_nan_not_equal_to_itself",
		smt: `
			(declare-fun x () Float32)
			(assert (fp.isNaN x))
			(assert (fp.eq x x))
		`,
		want: Unsat,
	},
}

// nonSeqSolver is the part of Solver/SolverCLI the table drivers below use,
// so a single driver can validate the same formulas through the cgo-linked
// library and through a z3 executable.
type nonSeqSolver interface {
	AssertSMTLIB2String(string) error
	Check() (CheckResult, error)
	Close()
}

var (
	_ nonSeqSolver = (*Solver)(nil)
	_ nonSeqSolver = (*SolverCLI)(nil)
)

// runNonSeqFormulas runs the whole table against solvers produced by
// newSolver, one fresh solver per query (rather than one solver reused
// across queries) so that declarations from different cases - and from a
// case's own entailment checks - cannot collide.
func runNonSeqFormulas(t *testing.T, newSolver func() nonSeqSolver) {
	t.Helper()

	// check asserts one self-contained query on a fresh solver and returns
	// its result.
	check := func(t *testing.T, smt string) CheckResult {
		t.Helper()
		s := newSolver()
		defer s.Close()
		if err := s.AssertSMTLIB2String(smt); err != nil {
			t.Fatalf("assert smtlib2: %v\n%s", err, smt)
		}
		res, err := s.Check()
		if err != nil {
			t.Fatalf("check error: %v\n%s", err, smt)
		}
		return res
	}

	for _, f := range nonSeqFormulas {
		f := f
		t.Run(f.name, func(t *testing.T) {
			if res := check(t, f.smt); res != f.want {
				t.Fatalf("expected %v, got %v", f.want, res)
			}
			if f.want != Sat {
				return
			}
			for _, e := range f.entailed {
				query := f.smt + "\n(assert (not " + e + "))\n"
				if res := check(t, query); res != Unsat {
					t.Fatalf("expected %s to be entailed (negation unsat), got %v", e, res)
				}
			}
		})
	}
}

// TestNonSeqFormulasNative validates the table through the cgo-linked
// library, i.e. against noodler itself when built with -tags noodler.
func TestNonSeqFormulasNative(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	runNonSeqFormulas(t, func() nonSeqSolver { return ctx.NewSolver() })
}

// TestNonSeqFormulasSimpleSolver validates the table through
// NewSimpleSolver's plain incremental core rather than NewSolver's
// tactic-based construction; the two can differ in what they solve (see
// NewSolver's doc comment), and every formula here is meant to be easy for
// both.
func TestNonSeqFormulasSimpleSolver(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	runNonSeqFormulas(t, func() nonSeqSolver { return ctx.NewSimpleSolver() })
}

// TestNonSeqFormulasCLI validates the table through the "z3" executable on
// PATH. Under -tags noodler that executable is whatever plain "z3" resolves
// to, which need not be a noodler build - see
// TestNoodlerNonSeqFormulasCLI in z3_noodler_test.go for the variant pinned
// to a noodler binary via Z3_NOODLER_BIN.
func TestNonSeqFormulasCLI(t *testing.T) {
	if _, err := exec.LookPath("z3"); err != nil {
		t.Skip("z3 executable not found on PATH")
	}

	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	runNonSeqFormulas(t, func() nonSeqSolver { return ctx.NewSolverCLI() })
}

// TestNonSeqFormulasAreSeqFree guards the table's whole premise: a formula
// added here that quietly reaches into the string/sequence/regex theory
// would make its result depend on exactly the solver component this table is
// supposed to hold fixed.
func TestNonSeqFormulasAreSeqFree(t *testing.T) {
	// Substrings, not whole tokens, so that e.g. "str.++" or "(Seq Int)" is
	// caught regardless of how it's spelled.
	banned := []string{"String", "str.", "seq.", "Seq ", "re.", "RegLan", `"`, "char."}

	for _, f := range nonSeqFormulas {
		texts := append([]string{f.smt}, f.entailed...)
		for _, text := range texts {
			for _, b := range banned {
				if strings.Contains(text, b) {
					t.Errorf("formula %q uses sequence-theory construct %q: %s", f.name, b, text)
				}
			}
		}
	}
}
