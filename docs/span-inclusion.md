# Fixed-depth span inclusion

## CLI

`./build/cli/autoq span-inclusion A.lsta B.lsta --qubits 5`

Input files use existing `.aut`, `.lsta`, or `.hsl` readers and must describe concrete automata in the same computational-basis order. Symbolic/predicate inputs return UnsupportedInput. File parsing errors retain the existing AutoQ error path. The command does not execute a circuit, infer a different qubit ordering, or change existing language-inclusion operations.

Exit codes: 0 Included; 2 NotIncluded; 3 ResourceLimit; 4 UnsupportedInput. File/parser errors use the existing exit code 1; CLI syntax errors retain CLI11 exit codes. A status line includes run, basis, tuple, equation and enumeration-step counts.

Options: `--max-runs` (applied separately to A/B), `--max-basis-runs`, `--max-tuple-states`, `--max-equations`, `--max-search-steps` (default 1000000), `--max-depth` (default 512). Zero disables a configurable limit. Other counters default to unlimited. These are not complete memory/time/bit-complexity bounds. Large reachable layers may still consume recursion stack and memory. A resource stop is not a non-inclusion proof.

## Library and semantics

Include `autoq/span/inclusion.hh` and call `AUTOQ::Span::check_inclusion(a, b, options)` with concrete automata and `options.qubits = n`. Inputs are not modified. The result distinguishes Included, NotIncluded, ResourceLimit and UnsupportedInput. A NotIncluded result owns a compressed witness; the CLI reports the outcome but does not serialize that witness.

The language slice consists of perfect binary trees of depth n whose internal layer d carries explicit qubit label d+1. Transitions ending at other depths or with a different layer label do not belong to that slice. Zero-choice transitions are ignored. Positive choices must be disjoint for each top state. Explicit nonpositive/wildcard qubit labels and malformed transition arities are unsupported. Cycles terminate under the fixed-depth restriction.

Accepted runs are owning maps Gamma=[gamma_0,...,gamma_n]. The root is the unique key of gamma_0. Each selected transition has exactly one ordered child vector. The global intersection of choices is checked separately in every layer of each run. No cross-run choice synchronization is imposed.

B is enumerated to retain an independent subset of accepted vectors. A is enumerated without constructing its own basis. Membership propagates aligned tuples over common coordinate directions, deduplicates tuples and checks shared-coefficient equations. No position lists, multiplicities, dense vectors or Gram matrices are used in production. Enumeration and basis size can be exponential.

Elimination is division-free: row <- pivot_value*row - coefficient*pivot_row. Pivots are visited in ascending column order. A contradiction is an all-zero coefficient row with nonzero RHS. Equations are over C; coefficients need not be representable by the amplitude type (e.g. 3c=1). Supported exact representations are FiveTuple and nTuple with N=4; other nTuple parameters and numerical amplitudes are not supported.

## Tests and CI

Core tests live in `unit_tests/span_inclusion_test.cc`, with an independent rational dense oracle in `span_test_util.hh`. CLI tests live in `span_inclusion_cli_test.cc`; they generate temporary `.aut` fixtures, invoke the actual binary and check exit status/output. They also check help, missing arguments and the existing print command.

Locally: `ctest --test-dir build -R '^span_inclusion(_cli)?_test$' --output-on-failure`, with project library paths configured. Build CLI tests depends on the autoq target.

All six existing artifact-based test jobs call `bash unit_tests/run_ci_tests.sh`. It preserves execution of explicit_tree_aut_test and adds span_inclusion_test and span_inclusion_cli_test. It restores executable bits, sets absolute shared-library search paths and exports AUTOQ_TEST_CLI pointing to the extracted CLI binary. CLI tests use that override rather than stale compile-time paths. The previously separately registered qasm_parsing_inclusion_cli_test is not newly added to this runner because its existing absolute fixture/executable paths require separate relocation work.

This wiring is not evidence that tests have passed: inspect the actual CI logs for the specific commit. No full local AutoQ compilation or test execution is claimed in this change.
