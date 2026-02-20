#!/usr/bin/python3
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import ensure_bench_dir, write_qasm_header

N_STR_PADDING = 3  # zfill width for benchmark dir names
PRE_HSL_HEADER = "Constants\nc1 := 1\nExtended Dirac\n"
POST_HSL_HEADER = "Constants\ncp := 1/sqrt2\ncn := -1/sqrt2\nExtended Dirac\n"

sizes = []
if len(sys.argv) == 2:
    n = int(sys.argv[1])
    assert n >= 2
    sizes.append(n)
else:
    sizes = list(range(2, 1001))

for n in sizes:
    n_str = str(n).zfill(N_STR_PADDING)
    ensure_bench_dir(n_str)
    with open(n_str + "/circuit.qasm", "w") as file:
        write_qasm_header(file)
        file.write(f"qreg qubits[{n}];\n\n")
        file.write("h qubits[0];\n")
        for i in range(n - 1):
            file.write(f"cx qubits[{i}], qubits[{i+1}];\n")
    with open(n_str + "/pre.hsl", "w") as file:
        file.write(PRE_HSL_HEADER)
        file.write(f"{{c1 |ji> : |j|=1, |i|={n-1}}}\n")
    with open(n_str + "/post.hsl", "w") as file:
        file.write(POST_HSL_HEADER)
        file.write(f"{{cp |0i> + cp |1i'> : |i|={n-1}}} ∪\n")
        file.write(f"{{cp |0i> + cn |1i'> : |i|={n-1}}}\n")