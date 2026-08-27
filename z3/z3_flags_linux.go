//go:build cgo && linux && !noodler
// +build cgo,linux,!noodler

package z3

/*
// Default linker flag to pull in z3. On Linux CI (Ubuntu), libz3 is typically in a default linker path
// when installed via apt (libz3-dev). If not, callers can provide CGO_LDFLAGS/CGO_CFLAGS.
//
// Excluded from -tags noodler builds: apt only ships vanilla Z3, and its
// libz3 exports the same C symbol names as a z3-noodler libz3 (Z3-Noodler is
// an ABI-compatible fork), so letting both -L/-l sets land on the same link
// line risks silently resolving against the wrong library. See
// z3_flags_noodler.go for the noodler-specific build.
#cgo LDFLAGS: -lz3
*/
import "C"
