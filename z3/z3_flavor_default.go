//go:build cgo && !noodler
// +build cgo,!noodler

package z3

// isNoodlerBuild reports whether this package was cgo-linked against
// z3-noodler (via -tags noodler) rather than vanilla Z3. See the noodler
// build's version of this constant (z3_flavor_noodler.go) for why tests
// check it.
const isNoodlerBuild = false
