#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tests="$root/build/unit_tests"
export LD_LIBRARY_PATH="$tests:${LD_LIBRARY_PATH:-}"
export DYLD_LIBRARY_PATH="$tests:${DYLD_LIBRARY_PATH:-}"
export AUTOQ_TEST_CLI="$root/build/cli/autoq"
chmod +x "$AUTOQ_TEST_CLI"
cd "$tests"
# Preserve the existing test invocation and add both new targets.
# Run binaries directly: downloaded artifacts have relocated CTest paths.
for test in explicit_tree_aut_test span_inclusion_test span_inclusion_cli_test; do
    chmod +x "./$test"
    echo "=== Running $test ==="
    "./$test" --report_level=detailed
done
