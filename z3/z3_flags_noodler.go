//go:build cgo && noodler
// +build cgo,noodler

package z3

// Z3-Noodler (https://github.com/VeriFIT/z3-noodler) is a fork of Z3 that
// replaces its string theory solver with one backed by the Mata automata
// library. It re-exports the same C API under the same symbol names
// (Z3_mk_context, Z3_mk_solver, ...) as vanilla Z3 - the fork adds no new
// C API surface - so the rest of this package works against it unmodified.
// That symbol-for-symbol overlap is exactly why it can't be linked into the
// same binary as vanilla libz3: whichever one the linker resolves first wins
// for every call. Building with -tags noodler switches the package's cgo
// flags to target a noodler build instead of vanilla Z3 (see
// z3_flags_darwin_brew.go, z3_flags_linux.go, z3_flags_pkgconfig.go, all of
// which exclude themselves under this tag for that reason). To run both
// flavors from the same process instead, use SolverCLI/NewSolverCLIPath
// pointed at a noodler "z3" executable as a subprocess alongside a normal
// (non-noodler) cgo-linked Solver - see solver_cli.go.
//
// Z3-Noodler isn't packaged by any OS package manager or available via
// pkg-config, and its build tree has no fixed install location, so unlike
// the vanilla-Z3 flags files this one has no defaults to fall back on.
// Point the build at your own noodler checkout with CGO_CFLAGS/CGO_LDFLAGS,
// e.g. after building it per https://github.com/VeriFIT/z3-noodler#building-and-running:
//
//	export CGO_CFLAGS="-I/path/to/z3-noodler/src/api"
//	export CGO_LDFLAGS="-L/path/to/z3-noodler/build -lz3"
//	go build -tags noodler ./...
//
// At runtime the resulting binary needs to find libz3 the same way any
// non-standard-location Z3 build does:
//
//	export DYLD_LIBRARY_PATH="/path/to/z3-noodler/build:${DYLD_LIBRARY_PATH}"   # macOS
//	export LD_LIBRARY_PATH="/path/to/z3-noodler/build:${LD_LIBRARY_PATH}"      # Linux
//
// Mata itself needs no separate CGO_LDFLAGS entry: z3-noodler's own CMake
// build fetches and statically links it into libz3, so nothing beyond that
// one -lz3 is required here.

/*
#include <stdlib.h>
*/
import "C"
