#!/usr/bin/env bash
# Build AutoQ for WebAssembly with Emscripten.
#
# Usage:   wasm/build.sh [OUT_DIR]          (default OUT_DIR: site/playground)
# Needs:   an activated emsdk (emcc/emcmake on PATH; tested with 6.0.12), git, python3, and the
#          Boost headers (BOOST_INCLUDE_DIR, default /usr/include).
# Env:     AUTOQ_WASM_DEPS   where Z3 and ANTLR are built and cached
#                            (default: build-wasm/deps)
#          AUTOQ_WASM_BUILD  build directory for AutoQ (default: build-wasm/autoq)
#          JOBS              parallel build jobs
#
# Z3 and the ANTLR runtime are built once as static WebAssembly libraries and
# reused on later runs. Everything is compiled with native WebAssembly
# exceptions (-fwasm-exceptions), which all current browsers support.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
DEPS=${AUTOQ_WASM_DEPS:-$ROOT/build-wasm/deps}
BUILD=${AUTOQ_WASM_BUILD:-$ROOT/build-wasm/autoq}
OUT=${1:-$ROOT/site/playground}
BOOST_INCLUDE_DIR=${BOOST_INCLUDE_DIR:-/usr/include}
JOBS=${JOBS:-$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 2)}

# Keep these in sync with the bundled headers in include/z3 and include/antlr4-runtime.
Z3_TAG=z3-4.12.5
ANTLR_TAG=4.13.2
EH_FLAGS="-fwasm-exceptions"

command -v emcmake >/dev/null || { echo "error: emcmake not found; install and activate emsdk first" >&2; exit 1; }
[ -d "$BOOST_INCLUDE_DIR/boost" ] || { echo "error: Boost headers not found in $BOOST_INCLUDE_DIR" >&2; exit 1; }
mkdir -p "$DEPS"

# Boost: header-only parts only. Expose just the boost/ directory so that no
# other host headers leak into the Emscripten build.
mkdir -p "$DEPS/boost-include"
ln -sfn "$BOOST_INCLUDE_DIR/boost" "$DEPS/boost-include/boost"

# Z3
if [ ! -f "$DEPS/z3/libz3.a" ]; then
  [ -d "$DEPS/z3-src" ] || git clone --depth 1 --branch "$Z3_TAG" https://github.com/Z3Prover/z3.git "$DEPS/z3-src"
  # Recent clang rejects references to nonexistent members inside
  # uninstantiated templates. This Z3 release has three such leftovers from
  # renames; later Z3 releases contain the same fixes.
  sed -i.orig 's/v\.m_matrix\.get(v\.m_row, v\.m_col)/v.m_matrix.get_elem(v.m_row, v.m_col)/' \
    "$DEPS/z3-src/src/math/lp/static_matrix.h"
  sed -i.orig 's/c\.m_low_bound)/c.m_lower_bound)/' "$DEPS/z3-src/src/math/lp/column_info.h"
  sed -i.orig 's/A\.get_value_of_column_cell(col)/A.get_val(col)/' "$DEPS/z3-src/src/math/lp/static_matrix_def.h"
  emcmake cmake -S "$DEPS/z3-src" -B "$DEPS/z3-build" \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_CXX_FLAGS="$EH_FLAGS" \
    -DZ3_SINGLE_THREADED=ON \
    -DZ3_BUILD_LIBZ3_SHARED=OFF \
    -DZ3_BUILD_EXECUTABLE=OFF \
    -DZ3_BUILD_TEST_EXECUTABLES=OFF \
    -DZ3_ENABLE_EXAMPLE_TARGETS=OFF \
    -DZ3_BUILD_PYTHON_BINDINGS=OFF \
    -DZ3_BUILD_DOCUMENTATION=OFF
  cmake --build "$DEPS/z3-build" --target libz3 -j "$JOBS"
  mkdir -p "$DEPS/z3"
  cp "$DEPS/z3-build/libz3.a" "$DEPS/z3/libz3.a"
fi

# ANTLR4 C++ runtime
if [ ! -f "$DEPS/antlr4/libantlr4-runtime.a" ]; then
  [ -d "$DEPS/antlr4-src" ] || git clone --depth 1 --branch "$ANTLR_TAG" https://github.com/antlr/antlr4.git "$DEPS/antlr4-src"
  emcmake cmake -S "$DEPS/antlr4-src/runtime/Cpp" -B "$DEPS/antlr4-build" \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_CXX_FLAGS="$EH_FLAGS" \
    -DANTLR_BUILD_CPP_TESTS=OFF \
    -DANTLR_BUILD_SHARED=OFF \
    -DANTLR_BUILD_STATIC=ON \
    -DWITH_DEMO=OFF
  cmake --build "$DEPS/antlr4-build" --target antlr4_static -j "$JOBS"
  mkdir -p "$DEPS/antlr4"
  cp "$(find "$DEPS/antlr4-build" -name 'libantlr4-runtime.a' | head -n 1)" "$DEPS/antlr4/libantlr4-runtime.a"
fi

# AutoQ
# -ffile-prefix-map keeps the build machine's paths out of error messages.
emcmake cmake -S "$ROOT" -B "$BUILD" \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_CXX_FLAGS="$EH_FLAGS -ffile-prefix-map=$ROOT/=" \
  -DAUTOQ_WASM_BOOST_INCLUDE="$DEPS/boost-include" \
  -DAUTOQ_WASM_Z3_LIB="$DEPS/z3/libz3.a" \
  -DAUTOQ_WASM_ANTLR4_LIB="$DEPS/antlr4/libantlr4-runtime.a"
cmake --build "$BUILD" --target autoq -j "$JOBS"

mkdir -p "$OUT"
cp "$BUILD/cli/autoq.js" "$BUILD/cli/autoq.wasm" "$OUT/"
echo "Wrote $OUT/autoq.js and $OUT/autoq.wasm"
