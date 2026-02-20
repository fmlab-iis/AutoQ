#!/usr/bin/python3
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import ensure_bench_dir, write_qasm_header

# Shared HSL preamble for pre.hsl and post.hsl
HSL_HEADER = "Constants\nc1 := 1\nExtended Dirac\n"

sizes = []
if len(sys.argv) == 2:
    n = int(sys.argv[1])
    assert(n >= 1)
    sizes.append(n)
else:
    sizes = list(range(1, 1001))

for n in sizes:
    n_str = str(n).zfill(2)
    ensure_bench_dir(n_str)
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
    with open(n_str + "/pre.hsl", "w") as file:
        file.write(HSL_HEADER)
        file.write(f'{{c1 |i{"0" * (n+1)}> : |i|={n}}}\n')
    with open(n_str + "/post.hsl", "w") as file:
        file.write(HSL_HEADER)
        file.write(f'{{c1 |ii1> : |i|={n}}}\n')