//go:build cgo
// +build cgo

package main

import (
	"fmt"
	"strings"

	z3 "github.com/vhavlena/z3-go/z3"
)

func main() {
	cfg := z3.NewConfig()
	defer cfg.Close()
	ctx := z3.NewContext(cfg)
	defer ctx.Close()

	x := ctx.Const("x", ctx.IntSort())
	y := ctx.Const("y", ctx.IntSort())
	three := ctx.IntVal(3)
	zero := ctx.IntVal(0)

	formula := z3.And(
		z3.Ge(x, zero),
		z3.Ge(y, zero),
		z3.Eq(z3.Add(x, three), y),
	)

	fmt.Println("Formula (SMT-LIB):")
	fmt.Println(formula)
	fmt.Println()

	fmt.Println("AST structure:")
	dumpAST(formula, 0)

	solver := ctx.NewSolver()
	defer solver.Close()
	solver.Assert(formula)

	res, err := solver.Check()
	if err != nil {
		fmt.Println("solver error:", err)
		return
	}
	if res != z3.Sat {
		fmt.Println("formula result:", res)
		return
	}

	m := solver.Model()
	if m == nil {
		fmt.Println("no model returned")
		return
	}
	defer m.Close()

	xVal := m.Eval(x, true)
	yVal := m.Eval(y, true)
	fmt.Println()
	fmt.Println("Model values:")
	fmt.Printf("  x = %s\n", numeralOrString(xVal))
	fmt.Printf("  y = %s\n", numeralOrString(yVal))

	fmt.Println("\nTraversing x-value AST:")
	xVal.Walk(func(node z3.AST) bool {
		fmt.Println("  ", describe(node))
		return true
	})
}

func dumpAST(a z3.AST, depth int) {
	indent := strings.Repeat("  ", depth)
	fmt.Printf("%s- %s\n", indent, describe(a))
	for i := 0; i < a.NumChildren(); i++ {
		dumpAST(a.Child(i), depth+1)
	}
}

func describe(a z3.AST) string {
	if !a.IsApp() {
		return a.String()
	}
	return fmt.Sprintf("%s (%s)", a.Decl().Name(), a.Kind())
}

func numeralOrString(a z3.AST) string {
	if v, ok := a.AsInt64(); ok {
		return fmt.Sprintf("%d", v)
	}
	if s, ok := a.AsStringLiteral(); ok {
		return fmt.Sprintf("%q", s)
	}
	return a.String()
}
