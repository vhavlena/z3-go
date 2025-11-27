//go:build !cgo
// +build !cgo

package main

import (
	"fmt"

	z3 "github.com/vhavlena/z3-go/z3"
)

func main() {
	// Using the stub types because cgo is disabled.
	_ = z3.Unknown
	fmt.Println("Go Z3 examples require cgo. Enable CGO_ENABLED=1 and install Z3, then run `go run ./examples/solve/solve.go` or `go run ./examples/ast/main.go`.")
}
