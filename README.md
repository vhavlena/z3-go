# z3-go

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

