# z3-go

[![CI](https://img.shields.io/github/actions/workflow/status/vhavlena/z3-go/ci.yml?branch=main&label=CI)](https://github.com/vhavlena/z3-go/actions)
[![tag](https://img.shields.io/github/v/tag/vhavlena/z3-go?label=tag)](https://github.com/vhavlena/z3-go/releases)

Full-featured Go binding for the Z3 SMT solver.

Originally conceived as a tiny wrapper, the module now covers a broad slice of the Z3 C API (config/context management, solver/model helpers, AST utilities, and examples) while staying idiomatic to Go.

## Layout
- `z3/` — Go package `z3`
- `examples/go` — tiny solver example (cgo)
- `examples/go/ast` — AST creation/traversal demo (cgo)

## Requirements
- Go 1.20+
- Z3 installed with headers and libraries discoverable by pkg-config.
  - macOS: `brew install z3`
  - Ubuntu/Debian: `sudo apt-get install -y libz3-dev`
  - From source: build Z3 and ensure `pkg-config` can find `z3.pc` (set `PKG_CONFIG_PATH` if needed).

The cgo binding is enabled by default when cgo is available. A tiny stub is used when building with `CGO_ENABLED=0`.

## Usage

Add the module to your project and import the `z3` package. With Go modules enabled you can add it with:

```bash
go get github.com/vhavlena/z3-go
```

Then import and use the binding in your code:

```go
package main

import (
  "fmt"
  "github.com/vhavlena/z3-go/z3"
)

func main() {
  cfg := z3.NewConfig()
  defer cfg.Close()

  ctx := z3.NewContext(cfg)
  defer ctx.Close()

  s := ctx.NewSolver()
  defer s.Close()

  x := ctx.Const("x", ctx.IntSort())
  y := ctx.Const("y", ctx.IntSort())

  s.Assert(z3.Ge(x, ctx.IntVal(0)))
  s.Assert(z3.Ge(y, ctx.IntVal(0)))
  s.Assert(z3.Gt(z3.Add(x, y), ctx.IntVal(5)))

  res, err := s.Check()
  if err != nil {
    fmt.Println("check error:", err)
    return
  }
  switch res {
  case z3.Sat:
    m := s.Model()
    if m != nil {
      defer m.Close()
      fmt.Println("sat model:\n", m.String())
    }
  case z3.Unsat:
    fmt.Println("unsat")
  default:
    fmt.Println("unknown")
  }
}
```

Notes:
- The binding uses cgo to call the Z3 C API. Ensure Z3 is installed and discoverable via `pkg-config` (see Requirements above).
- If you build with `CGO_ENABLED=0` the package falls back to a small stub (useful for tests or build environments without Z3).

## Build and test

Run tests:

```bash
go test ./z3 -v
```

Run the solver example:

```bash
go run ./examples/solve/solve.go
```

## AST helpers & example

The package exposes helpers for inspecting `z3.AST` values (`Kind`, `Decl`, `Children`, `Walk`, `AsInt64`, `AsStringLiteral`, etc.).
To see them in action, run the AST demo (requires cgo and a local Z3 install):

```bash
go run ./examples/ast
```

The program builds a small arithmetic formula, prints its tree structure, checks it with a solver, and walks the model value of `x` to show how to recover concrete numerals/strings from the resulting ASTs.

### Troubleshooting linking
- If Z3 is installed but not found, check `pkg-config --libs z3` works. If not, set `PKG_CONFIG_PATH` to include the directory with `z3.pc`.
- As a last resort, you can override via env vars:

```bash
export CGO_CFLAGS="-I/path/to/z3/src/api"
export CGO_LDFLAGS="-L/path/to/z3/build -lz3"
```

On macOS, when running binaries that link to libz3.dylib in a non-standard location, you may need:

```bash
export DYLD_LIBRARY_PATH="/path/to/z3/build:${DYLD_LIBRARY_PATH}"
```

## Z3-Noodler support

[Z3-Noodler](https://github.com/VeriFIT/z3-noodler) is a fork of Z3 that replaces its string theory solver with one backed by the [Mata](https://github.com/VeriFIT/mata) automata library. It re-exports the same C API under the same symbol names as vanilla Z3 (no new API surface), so this package works against it unmodified - but that symbol-for-symbol overlap also means a noodler build can't be cgo-linked into the same binary as vanilla libz3: whichever one the linker resolves first wins for every call. There are two ways to use it, and they can be combined:

**Native cgo linking**, for the lowest-overhead path when your whole process only ever needs one flavor: build z3-noodler yourself (it isn't packaged by any OS package manager or available via pkg-config - see its own [build instructions](https://github.com/VeriFIT/z3-noodler#building-and-running)), then build this package against it with the `noodler` tag:

```bash
export CGO_CFLAGS="-I/path/to/z3-noodler/src/api"
export CGO_LDFLAGS="-L/path/to/z3-noodler/build -lz3"
go build -tags noodler ./...
export DYLD_LIBRARY_PATH="/path/to/z3-noodler/build:${DYLD_LIBRARY_PATH}"   # macOS
export LD_LIBRARY_PATH="/path/to/z3-noodler/build:${LD_LIBRARY_PATH}"      # Linux
```

The `noodler` tag also disables this package's vanilla-Z3 default flags (Homebrew paths, apt's default linker path, `pkg-config z3`) so they can't collide with the noodler `-L`/`-l` on the same link line. Mata itself needs no separate linker entry: z3-noodler's own CMake build fetches and statically links it into libz3.

Because CGO_CFLAGS and CGO_LDFLAGS must point at the exact library that was actually built, mismatching them (e.g. building against a newer noodler checkout's headers than the linked libz3) silently breaks correctness rather than failing to link: unlike vanilla Z3, z3-noodler does not reserve a fixed sentinel value for `Z3_OP_UNINTERPRETED` in its C API, so its numeric value shifts whenever the fork's `Z3_decl_kind` enum changes, and a mismatch will make every uninterpreted-symbol check in this package (e.g. `SolverCLI`'s constant discovery) quietly find nothing.

**SolverCLI as a subprocess**, for using both flavors from the same process: point `NewSolverCLIPath` at a noodler `z3` executable to run it as a subprocess alongside a normal (non-noodler) cgo-linked `Solver`, with no build tag needed:

```go
noodler := ctx.NewSolverCLIPath("/path/to/z3-noodler/build/z3")
```

`go test -tags noodler ./z3/...` also picks up a small set of noodler-specific regression tests (`z3_noodler_test.go`); set `Z3_NOODLER_BIN` to a noodler `z3` executable to include the ones that exercise `SolverCLI` against it.

