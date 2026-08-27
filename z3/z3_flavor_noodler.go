//go:build cgo && noodler
// +build cgo,noodler

package z3

// isNoodlerBuild reports whether this package was cgo-linked against
// z3-noodler (via -tags noodler) rather than vanilla Z3. A few regression
// tests are tuned to vanilla Z3's own tactic/quantifier-instantiation
// behavior on formulas outside what z3-noodler targets (quantifier-free
// string constraints); this lets them skip themselves under -tags noodler
// instead of asserting a vanilla-Z3-specific outcome against a genuinely
// different solver.
const isNoodlerBuild = true
