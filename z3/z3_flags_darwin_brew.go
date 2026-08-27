//go:build cgo && darwin && !noodler
// +build cgo,darwin,!noodler

package z3

/*
// Default Homebrew locations on macOS (Apple Silicon and Intel). These paths are
// added unconditionally; missing directories are harmless.
//
// Excluded from -tags noodler builds: Homebrew only ships vanilla Z3, and its
// libz3 exports the same C symbol names as a z3-noodler libz3 (Z3-Noodler is
// an ABI-compatible fork), so letting both -L/-l sets land on the same link
// line risks silently resolving against the wrong library. See
// z3_flags_noodler.go for the noodler-specific build.
#cgo CFLAGS: -I/opt/homebrew/include -I/usr/local/include
#cgo LDFLAGS: -L/opt/homebrew/lib -L/usr/local/lib -lz3
*/
import "C"
