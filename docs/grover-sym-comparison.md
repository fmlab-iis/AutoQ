# Manual GroverSym set/span comparison

Standalone executable only: no unit-test registration or automatic execution. Existing tests, GroverSym fixtures and scaling workflows are unchanged. Build with the project's normal configuration and run from its root:

```sh
make release
./build/unit_tests/grover_sym_benchmark --qubits 4
./build/unit_tests/grover_sym_benchmark --qubits 4 --method set
./build/unit_tests/grover_sym_benchmark --qubits 4 --method span
./build/unit_tests/grover_sym_benchmark --qubits 4 --method original
./build/unit_tests/grover_sym_benchmark --help
```

Default method is `both`: set then span, once each. There is no repeat option, automatic qubit sweep or circuit generation. `--qubits N` means SEARCH qubits; the existing GroverSym layout uses 2*N-1 total qubits. Thus 4 means case 04 with seven total qubits. N must be in [3,65536], but this is only an argument cap: the corresponding `benchmarks/all/GroverSym/NN` directory with pre.hsl, circuit.qasm and post.hsl must already exist. Use `--repo-root PATH` from another working directory. Use the normal AutoQ shared-library environment.

The tool validates the original post expression against the expected alternating-bit answer and fixed auxiliary suffix. It uses the original precondition and executes the actual existing circuit, not a formula-derived Grover output. Case 04's pre is concrete all-zero (c1:=1 is a constant).

- `set`: original symbolic set-inclusion algorithm, using the plane expression with only tautological constraints. pH and pL have no imposed real/imaginary-part or magnitude restrictions.
- `span`: exact span-inclusion algorithm, using two concrete compressed generators: answer and sum of non-answers, with the same fixed auxiliary suffix. Target rank is two. There are O(N) states per generator, two runs, and no dense coordinate expansion. Coefficients are internal membership unknowns, not symbolic inputs.
- `both`: run both plane checks, once each, with fresh inputs.
- `original`: check the stronger original symbolic post, including its real/magnitude constraints; this is not the equivalent baseline.

Compare plane_set versus plane_span for the same intended complex-plane predicate. Neither plane target imposes normalization or verifies success probability/rotation angle. Symbolic constraint semantics and frontend behavior require actual runtime validation; implementation alone is not a performance result. Symbolic and Concrete paths execute the same circuit separately in their native representations, not one shared output automaton.

Each GROVER_COMPARE row reports method, search_qubits, total_qubits, prepare_seconds, execute_seconds, check_seconds, total_seconds and actual outcome. Preparation includes parsing, copies and target construction. execute_seconds covers circuit execution. check_seconds covers only inclusion, including span basis discovery. total_seconds combines these three phases. Build, initial metadata validation, temporary symbolic-post creation, result printing and later object destruction are excluded. Span solver stats are printed separately; existing library messages may also appear on stdout.

For inclusion speed, compare check_seconds; for combined preparation/execution/check cost, compare total_seconds. Use the same machine and Release build. Separate invocations of set and span avoid sharing the process. Record commit, compiler and stack limits. One observation does not establish a stable performance advantage.

There is no built-in timeout or address-space budget; OS limits still apply. Exit codes: 0 requested checks passed/help; 1 non-inclusion, unexpected rank, unsupported/missing fixture or runtime error; 3 caught allocation failure; 4 invalid CLI. Both mode continues after a normal non-inclusion result, but an exception/crash may prevent the second method from running. This harness is not an automatic negative-control regression suite. Original source fixtures are never modified; the temporary symbolic plane post is removed on normal scope exit.
