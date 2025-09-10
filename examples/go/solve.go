//go:build cgo
// +build cgo

package main

import (
	"fmt"

	z3 "github.com/vhavlena/z3-go/z3"
)

func main() {
	cfg := z3.NewConfig()
	defer cfg.Close()
	ctx := z3.NewContext(cfg)
	defer ctx.Close()

	x := ctx.Const("x", ctx.IntSort())
	y := ctx.Const("y", ctx.IntSort())

	s := ctx.NewSolver()
	defer s.Close()

	// x + y > 5, x >= 0, y >= 0
	five := ctx.IntVal(5)
	zero := ctx.IntVal(0)
	s.Assert(z3.Gt(z3.Add(x, y), five))
	s.Assert(z3.Ge(x, zero))
	s.Assert(z3.Ge(y, zero))

	res, err := s.Check()
	if err != nil {
		fmt.Println("check:", err)
	}
	switch res {
	case z3.Sat:
		m := s.Model()
		defer m.Close()
		fmt.Println("sat")
		fmt.Println("x =", m.Eval(x, true))
		fmt.Println("y =", m.Eval(y, true))
	case z3.Unsat:
		fmt.Println("unsat")
	default:
		fmt.Println("unknown")
	}
}
