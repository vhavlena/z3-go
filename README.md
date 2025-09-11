# z3-go

[![CI](https://img.shields.io/github/actions/workflow/status/vhavlena/z3-go/ci.yml?branch=main&label=CI)](https://github.com/vhavlena/z3-go/actions)
[![tag](https://img.shields.io/github/v/tag/vhavlena/z3-go?label=tag)](https://github.com/vhavlena/z3-go/releases)

Minimal Go binding for the Z3 SMT solver.

This aims to be a small, idiomatic wrapper over the Z3 C API, suitable to be used as a standalone module.

## Layout
- `z3/` — Go package `z3`
- `examples/go` — tiny example program

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

Run the example:

```bash
go run ./examples/go
```

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

