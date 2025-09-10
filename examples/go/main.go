//go:build !cgo
// +build !cgo

package main

import (
	"fmt"

	z3 "github.com/vhavlena/z3-go/z3"
)

func main() {
	// Using the stub types unless built with -tags z3binding
	_ = z3.Unknown
	fmt.Println("Go Z3 prototype example. Build with -tags z3binding to run real solver.")
}
