//go:build cgo && noodler
// +build cgo,noodler

package z3

import (
	"os"
	"os/exec"
	"testing"
)

// These tests only build under -tags noodler, i.e. when the package has been
// cgo-linked against a z3-noodler build (see z3_flags_noodler.go) instead of
// vanilla Z3. They exist to catch the two failure modes that plain linking
// doesn't: a header/library version mismatch (Z3-Noodler, unlike vanilla Z3,
// does not reserve a fixed sentinel value for Z3_OP_UNINTERPRETED - it's
// wherever that entry falls in the Z3_decl_kind enum, which shifts if the
// noodler fork has added/removed op kinds since the linked library was
// built, silently breaking every uninterpreted-symbol check in this package,
// e.g. SolverCLI's constantNames - so CGO_CFLAGS and CGO_LDFLAGS/
// DYLD_LIBRARY_PATH/LD_LIBRARY_PATH must point at the same noodler build),
// and confirmation that the string theory itself is actually being
// exercised (as opposed to accidentally linking vanilla Z3 under the
// noodler tag).

// TestNoodlerNativeStringConstraint drives a native (non-CLI) Solver through
// a string constraint that requires actual string-theory reasoning
// (length + membership-shaped equalities via concatenation), exercising the
// cgo-linked noodler libz3 directly.
func TestNoodlerNativeStringConstraint(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	x := ctx.Const("x", ctx.StringSort())
	s.Assert(Eq(Length(x), ctx.IntVal(3)))
	s.Assert(Eq(Concat(ctx.StringVal("ab"), x), ctx.StringVal("abxyz")))

	res, err := s.Check()
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}

	m := s.Model()
	if m == nil {
		t.Fatal("expected a model")
	}
	defer m.Close()

	v := m.Eval(x, true)
	got, ok := v.AsStringLiteral()
	if !ok {
		t.Fatalf("expected a string literal, got %s", v.String())
	}
	if got != "xyz" {
		t.Fatalf("expected x = %q, got %q", "xyz", got)
	}
}

// TestNoodlerNativeStringConstraintUnsat is the unsat counterpart to
// TestNoodlerNativeStringConstraint, checking that noodler's string theory
// correctly rejects a contradictory length constraint.
func TestNoodlerNativeStringConstraintUnsat(t *testing.T) {
	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolver()
	defer s.Close()

	x := ctx.Const("x", ctx.StringSort())
	s.Assert(Eq(Concat(ctx.StringVal("ab"), x), ctx.StringVal("abxyz")))
	s.Assert(Eq(Length(x), ctx.IntVal(1)))

	res, err := s.Check()
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Unsat {
		t.Fatalf("expected unsat, got %v", res)
	}
}

// noodlerCLIPath resolves the z3-noodler executable to use for SolverCLI
// tests, so they exercise the same noodler flavor as the native cgo link
// rather than whatever unrelated "z3" happens to be first on PATH (see
// solver_cli.go's own doc comment: a vanilla-z3 subprocess paired with a
// noodler-linked native Context is a supported but different combination
// from testing noodler-through-SolverCLI, which is what these tests want).
// Set Z3_NOODLER_BIN to the noodler build's z3 executable to run them;
// otherwise they skip.
func noodlerCLIPath(t *testing.T) string {
	t.Helper()
	path := os.Getenv("Z3_NOODLER_BIN")
	if path == "" {
		t.Skip("Z3_NOODLER_BIN not set; skipping SolverCLI-against-noodler test")
	}
	if _, err := exec.LookPath(path); err != nil {
		t.Skipf("z3-noodler executable %q not found: %v", path, err)
	}
	return path
}

// TestNoodlerSolverCLI drives the same string constraint as
// TestNoodlerNativeStringConstraint through SolverCLI pointed at a
// z3-noodler executable, exercising the subprocess path (including model
// reconstruction) end-to-end against noodler rather than the native C API.
func TestNoodlerSolverCLI(t *testing.T) {
	path := noodlerCLIPath(t)

	cfg := NewConfig()
	defer cfg.Close()
	ctx := NewContext(cfg)
	defer ctx.Close()

	s := ctx.NewSolverCLIPath(path)
	defer s.Close()

	x := ctx.Const("x", ctx.StringSort())
	s.Assert(Eq(Length(x), ctx.IntVal(3)))
	s.Assert(Eq(Concat(ctx.StringVal("ab"), x), ctx.StringVal("abxyz")))

	res, err := s.Check()
	if err != nil {
		t.Fatalf("check error: %v", err)
	}
	if res != Sat {
		t.Fatalf("expected sat, got %v", res)
	}

	m := s.Model()
	if m == nil {
		t.Fatal("expected a reconstructed model")
	}
	defer m.Close()

	v := m.Eval(x, true)
	got, ok := v.AsStringLiteral()
	if !ok {
		t.Fatalf("expected a string literal, got %s", v.String())
	}
	if got != "xyz" {
		t.Fatalf("expected x = %q, got %q", "xyz", got)
	}
}
