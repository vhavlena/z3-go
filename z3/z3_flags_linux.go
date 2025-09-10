//go:build cgo && linux
// +build cgo,linux

package z3

/*
// Default linker flag to pull in z3. On Linux CI (Ubuntu), libz3 is typically in a default linker path
// when installed via apt (libz3-dev). If not, callers can provide CGO_LDFLAGS/CGO_CFLAGS.
#cgo LDFLAGS: -lz3
*/
import "C"
