# AutoQ in the browser (WebAssembly)

`wasm/build.sh` compiles the AutoQ command-line tool to WebAssembly with
[Emscripten](https://emscripten.org). The result, `autoq.js` and `autoq.wasm`,
powers the playground at `site/playground/`, which runs AutoQ entirely in the
browser. It is the same `main()` as the native CLI, so it accepts the same
arguments and files and prints the same output.

## Building

You need an activated [emsdk](https://emscripten.org/docs/getting_started/downloads.html)
(tested with 6.0.12), `git`, `python3`, and the Boost headers (for example
`apt install libboost-dev`).

```sh
git clone https://github.com/emscripten-core/emsdk.git ~/emsdk
~/emsdk/emsdk install 6.0.12 && ~/emsdk/emsdk activate 6.0.12
source ~/emsdk/emsdk_env.sh

wasm/build.sh            # writes site/playground/autoq.js and autoq.wasm
```

The first run builds Z3 4.12.5 and the ANTLR 4.13.2 C++ runtime as static
WebAssembly libraries in `build-wasm/deps/` and takes a while. Later runs reuse
them and only rebuild AutoQ. Both versions match the headers bundled in
`include/z3` and `include/antlr4-runtime`.

Environment variables: `AUTOQ_WASM_DEPS` (dependency cache, default
`build-wasm/deps`), `AUTOQ_WASM_BUILD` (AutoQ build directory, default
`build-wasm/autoq`), `BOOST_INCLUDE_DIR` (default `/usr/include`) and `JOBS`.
An optional argument sets the output directory.

## Trying it locally

```sh
python3 -m http.server -d site 8000
# open http://localhost:8000/playground/
```

The page needs to be served over HTTP: browsers don't load module workers
from `file://` URLs.

## Checking it against the native build

```sh
node wasm/compare.mjs build/cli/autoq site/playground
```

This runs every playground example (`site/playground/examples.js`) with the
native `autoq` and with the WebAssembly build and checks that both print the
same output and exit code, ignoring the timing and memory figures. Set
`VERBOSE=1` to see the outputs.

## How it fits together

- **CMake.** When configured with `emcmake`, the root `CMakeLists.txt` takes
  Boost from `AUTOQ_WASM_BOOST_INCLUDE` (only header-only parts are used) and
  skips the unit tests; `src/CMakeLists.txt` links the prebuilt Z3 and ANTLR
  libraries; `cli/CMakeLists.txt` links `autoq` as an ES module that exports
  `createAutoQ()` and does not run `main()` on load. The native build is
  unchanged.
- **The page.** `site/playground/worker.js` compiles `autoq.wasm` once, then
  creates a fresh instance for every run (`main()` keeps global state), writes
  the files into the in-memory file system and calls `main()` through
  `callMain([...args])`. The page itself never blocks, and Stop simply
  terminates the worker.
- **Deployment.** `.github/workflows/pages.yml` installs emsdk, restores the
  cached Z3 and ANTLR build, runs `wasm/build.sh` and deploys `site/`. The
  generated `autoq.js` and `autoq.wasm` are not committed.

## Differences from the native build

- WebAssembly has no floating-point traps, so the `feenableexcept()` call in
  `cli/autoq.cc` is skipped: an arithmetic error that stops the native tool
  with `SIGFPE` produces `inf` or `NaN` here instead.
- The reported memory usage is the size of the WebAssembly heap, which only
  grows; Emscripten does not report a resident set size.
- Runs are single-threaded and limited to the memory a browser grants a page
  (at most 4 GB), so the largest benchmarks are better run natively.
- Source paths in error messages are relative to the repository root.

## Patches to Z3

`wasm/build.sh` patches three lines of Z3 4.12.5 after cloning it. They are
uses of nonexistent members (`get`, `m_low_bound`,
`get_value_of_column_cell`) in templates that are never instantiated; GCC and
older clang accept them, the clang in current Emscripten does not. Later Z3
releases contain the same fixes. Drop the patches if you move to a newer Z3,
and update `Z3_TAG` together with `include/z3`.
