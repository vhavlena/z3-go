//go:build !cgo
// +build !cgo

// Package z3 provides a minimal Go binding to Z3's C API.
// This stub allows the package to build without cgo available.
// Install Z3 and enable cgo to use the real binding.
package z3

// Placeholder types for documentation-only builds (no functionality).

type Context struct{}

type Config struct{}

type Sort struct{}

type AST struct{}

type Solver struct{}

type Model struct{}

type CheckResult int

const (
	Unknown CheckResult = iota
	Sat
	Unsat
)
