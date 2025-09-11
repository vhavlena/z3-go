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
	fmt.Println("Go Z3 example. Enable cgo (CGO_ENABLED=1) and have Z3 installed to run the real solver.")
}
