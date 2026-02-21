#!/usr/bin/python3
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import ensure_bench_dir_for_n, write_qasm_header, write_hsl, parse_sizes

N_STR_PADDING = 3  # zfill width for benchmark dir names
PRE_HSL_HEADER = "Constants\nc1 := 1\nExtended Dirac\n"
POST_HSL_HEADER = "Constants\ncp := 1/sqrt2\ncn := -1/sqrt2\nExtended Dirac\n"

sizes = parse_sizes(2, 1001, min_n=2)

for n in sizes:
    n_str = ensure_bench_dir_for_n(n, zfill=N_STR_PADDING)
    with open(n_str + "/circuit.qasm", "w") as file:
        write_qasm_header(file)
        file.write(f"qreg qubits[{n}];\n\n")
        file.write("h qubits[0];\n")
        for i in range(n - 1):
            file.write(f"cx qubits[{i}], qubits[{i+1}];\n")
    write_hsl(n_str + "/pre.hsl", f"{{c1 |ji> : |j|=1, |i|={n-1}}}\n", header=PRE_HSL_HEADER)
    write_hsl(
        n_str + "/post.hsl",
        f"{{cp |0i> + cp |1i'> : |i|={n-1}}} ∪\n{{cp |0i> + cn |1i'> : |i|={n-1}}}\n",
        header=POST_HSL_HEADER,
    )