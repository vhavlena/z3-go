//go:build !cgo
// +build !cgo

package main

import "fmt"

func main() {
	fmt.Println("AST example requires cgo and a local Z3 installation.")
}
