//go:build cgo && z3pc && !noodler
// +build cgo,z3pc,!noodler

package z3

// Excluded from -tags noodler builds: `pkg-config z3` resolves to whatever
// vanilla Z3 install is registered on the system, not a z3-noodler build
// (which has no pkg-config file of its own and isn't packaged anywhere), and
// mixing that -L/-l set with a noodler one on the same link line risks
// silently resolving against the wrong libz3 (Z3-Noodler is an ABI-compatible
// fork exporting the same C symbol names). See z3_flags_noodler.go.

/*
#cgo pkg-config: z3
*/
import "C"
