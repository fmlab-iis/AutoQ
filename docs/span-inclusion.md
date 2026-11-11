# Fixed-depth span inclusion: library core

This commit introduces the library core and Boost.Test target. CLI integration and execution in the existing GitHub CI test jobs are not included yet. CMake test registration alone does not cause the current artifact-based CI test jobs to execute this test. No local full AutoQ build is claimed.

Include `autoq/span/inclusion.hh` and call `AUTOQ::Span::check_inclusion(a, b, options)` with concrete automata. Set `options.qubits = n`. Inputs are not modified. The result distinguishes Included, NotIncluded, ResourceLimit and UnsupportedInput. A NotIncluded result owns a compressed witness.

The language slice consists of perfect binary trees of depth n whose internal layer d carries explicit qubit label d+1. Transitions ending at other depths or with a different layer label do not belong to that slice. Zero-choice transitions are ignored. Positive choices must be disjoint for each top state. Explicit nonpositive/wildcard qubit labels and malformed transition arities are unsupported. Cycles terminate under the fixed-depth restriction.

Accepted runs are represented by owning maps Gamma=[gamma_0,...,gamma_n]. The root is recoverable from the unique key of gamma_0. Each selected transition has exactly one ordered child vector, not a set of alternatives. The global intersection of choices is checked separately in every layer of each run. No cross-run choice synchronization is imposed.

B is enumerated to retain an independent subset of its accepted vectors. A is then enumerated without constructing its own basis. Membership propagates aligned tuples over the same coordinate directions, deduplicates tuples, and checks shared-coefficient leaf equations. No position lists, multiplicities, dense vectors, or Gram matrices are used in production.

Elimination is division-free: row <- pivot_value*row - coefficient*pivot_row. Pivots are visited in ascending column order even if rows arrive out of order. A contradiction is an all-zero coefficient row with nonzero RHS. Equations are over C; a valid coefficient need not be representable by AutoQ's amplitude type (e.g. 3c=1). Supported exact representations are FiveTuple and nTuple with N=4. Other nTuple parameters are deliberately rejected because syntactic zero tests are not generally faithful for redundant cyclotomic representations. Numerical amplitudes are not supported.

Limits count runs separately for A/B; tuple visits, equations, and search steps cumulatively across the whole check. Basis size limits retained generators. Zero disables a configurable limit. Default search_steps=1000000 and depth=512 guard enumeration and recursion; these are not complete memory/time/bit-complexity bounds. Large reachable layers may still consume recursion stack and memory. Enumeration of runs and basis size can be exponential.

Tests: `ctest --test-dir build -R '^span_inclusion_test$' --output-on-failure` in the original build location, or run `build/unit_tests/span_inclusion_test` with project shared-library paths configured. Tests include an independent rational dense oracle, non-dyadic solutions, out-of-order pivots, complex/algebraic coefficients, global synchronization, stored-run ownership, cross-run choices, fixed-depth cycles, limits, and a width-one depth-80 case built without dense coordinates.
