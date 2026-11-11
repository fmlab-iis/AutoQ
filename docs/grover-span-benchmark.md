# Grover span benchmarks

These are formula-derived inclusion obligations, not quantum circuit execution or end-to-end Grover verification.

## Automated probability-one scenario

Normal platform/configuration regression jobs run `grover_paper_probability_one` at n=3. The separate Ubuntu Release scaling workflow tests n=2,3,4,... until the first timeout or failure. Each case gets its own 300-second wall-clock budget (fixture construction and positive/negative controls included, build excluded) and 4 GiB child address-space limit. There is no custom overall job timeout; GitHub platform limits still apply. Results are in the `grover-span-results` artifact.

Here N=2^n, M=N/4 solutions are all strings beginning with 00, and R=1 Grover iteration gives success probability one. The target is the full solution subspace of dimension 2^(n-2), not just the uniform solution ray. Current basis enumeration can therefore become expensive despite the compact fixture. A failed process is not automatically a timeout or a mathematical counterexample: inspect its log.

## Manual plane scenario

Build using the project's normal configuration, for example:

```sh
make release
./build/unit_tests/grover_plane_benchmark --qubits 7965
./build/unit_tests/grover_plane_benchmark --help
```

This is a standalone executable, not a Boost unit test and not registered with CTest. CI can build it but does not run it. It accepts exactly one qubit count in [2,65536] (a fixture implementation cap), has no automatic sweep, and imposes no built-in wall-clock or memory budget. Apply external limits if needed. Use the same runtime shared-library environment as other AutoQ executables on your platform.

It uses M=1 and checks formula-derived iterates j=0,1,2 against span{alpha,beta}, plus a single-coordinate leakage negative control. For n<=4 it additionally runs an independent dense oracle. This plane has fixed dimension two; large n does not imply that arbitrary high-dimensional subspaces are easy.

Each `GROVER` line reports the actual inclusion outcome and a_runs, b_runs, basis, tuples, equations, search_steps. An expected `NotIncluded` for the leakage control is a success. The final `SUMMARY` line reports qubits, overall status, and steady-clock elapsed seconds including fixture construction, both controls, and the small dense oracle when applicable; parsing and build are excluded. Exit codes: 0 all checks passed/help, 1 failed check or other exception, 3 caught allocation failure, 4 invalid arguments. An external kill cannot produce a final summary. Inclusion outcomes such as ResourceLimit or UnsupportedInput remain visible in the per-check output and cause a nonzero exit.
