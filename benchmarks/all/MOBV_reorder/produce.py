#!/usr/bin/python3
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import ensure_bench_dir_for_n, write_qasm_header, parse_sizes, HSL_HEADER, write_hsl

sizes = parse_sizes(1, 1001, min_n=1)

for n in sizes:
    n_str = ensure_bench_dir_for_n(n)
    # Identity qubit index mapping: qubit_index[i] == i
    qubit_index = list(range(2 * n + 1))
    with open(n_str + "/circuit.qasm", "w") as file:
        write_qasm_header(file)
        file.write(f'qreg qubits[{2*n+1}];\n\n')
        for i in range(n, -1, -1):
            file.write(f'h qubits[{qubit_index[n+i]}];\n')
        file.write(f'z qubits[{qubit_index[n+n]}];\n')
        for i in range(0, n):
            file.write(f'ccx qubits[{qubit_index[i]}], qubits[{qubit_index[n+i]}], qubits[{qubit_index[n+n]}];\n')
        for i in range(n, -1, -1):
            file.write(f'h qubits[{qubit_index[n+i]}];\n')
    write_hsl(n_str + "/pre.hsl", f'{{c1 |i{"0" * (n+1)}> : |i|={n}}}\n')
    write_hsl(n_str + "/post.hsl", f'{{c1 |ii1> : |i|={n}}}\n')