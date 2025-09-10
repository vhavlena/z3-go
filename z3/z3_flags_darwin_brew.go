//go:build cgo && darwin
// +build cgo,darwin

package z3

/*
// Default Homebrew locations on macOS (Apple Silicon and Intel). These paths are
// added unconditionally; missing directories are harmless.
#cgo CFLAGS: -I/opt/homebrew/include -I/usr/local/include
#cgo LDFLAGS: -L/opt/homebrew/lib -L/usr/local/lib -lz3
*/
import "C"
