# Optional B basis reduction

Span inclusion retains all enumerated B runs by default. Pass the bare flag
`--reduce-b-basis` to discard linearly dependent generators before checking A.
No yes/no argument is required.

```sh
autoq span-inclusion A.lsta B.lsta --qubits 5
autoq span-inclusion A.lsta B.lsta --qubits 5 --reduce-b-basis
./build/unit_tests/grover_sym_benchmark --qubits 4 --method span
./build/unit_tests/grover_sym_benchmark --qubits 4 --method span --reduce-b-basis
```

The API option is `Options::reduce_b_basis`, default `false`. Both modes are
exact even for dependent, duplicated or zero generators; independence affects
performance, not correctness. B enumeration is required in both modes.

Skipping reduction saves B membership checks but can increase generator memory,
joint-tuple traversal and linear-system width during A membership. Compare
GroverSym `check_seconds`; it includes B enumeration and optional reduction.
The flag does not affect set/original checks.

For source compatibility, `Stats::basis` and `Limits::basis` keep their names.
They count/limit retained generators in either mode, not necessarily rank.
CLI and GroverSym output label the count as generators. Older benchmark output
may still call this field basis; it is rank only when reduction completed.
`--max-basis-runs` limits retained generators in either mode.

No circuit fixtures or CI workflow settings are changed. Runtime and performance
must be checked after building; this change does not assert a measured speedup.
