#!/usr/bin/python3
import sys
import shutil
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import ensure_bench_dir_for_n, write_qasm_header, write_hsl, parse_sizes

sizes = parse_sizes(3, 1001, min_n=3)

for n in sizes:
    n_str = ensure_bench_dir_for_n(n)
    w = range(n)
    a = [n + i for i in range(n - 1)]
    t = 2 * n - 1
    to_be_reversed = []
    with open(n_str + "/circuit.qasm", "w") as file:
        write_qasm_header(file)
        file.write(f'qreg qubits[{2*n}];\n\n')
        to_be_reversed.append(f'ccx qubits[{w[0]}], qubits[{w[1]}], qubits[{a[0]}];\n')
        file.write(to_be_reversed[-1])
        for i in range(2, n, 1):
            to_be_reversed.append(f'ccx qubits[{a[i-2]}], qubits[{w[i]}], qubits[{a[i-1]}];\n')
            file.write(to_be_reversed[-1])
        file.write(f'cx qubits[{a[n-2]}], qubits[{t}];\n')
        for item in reversed(to_be_reversed):
            file.write(item)
    write_hsl(n_str + "/pre.hsl", "{ c1 |i" + "0" * (n - 1) + "j> : |i|=" + str(n) + ", |j|=1 }\n")
    shutil.copy(n_str + "/pre.hsl", n_str + "/post.hsl")
    write_hsl(n_str + "/pre0.hsl", "{ c1 |i" + "0" * (n - 1) + "0> : |i|=" + str(n) + " }\n")
    write_hsl(n_str + "/pre1.hsl", "{ c1 |i" + "0" * (n - 1) + "1> : |i|=" + str(n) + " }\n")
    write_hsl(
        n_str + "/post0.hsl",
        "{ c1 |i" + "0" * (n - 1) + "0> : |i|=" + str(n) + " }\n"
        "∪ { c1 |" + "1" * n + "0" * (n - 1) + "1>}\n"
        "\\ { c1 |" + "1" * n + "0" * (n - 1) + "0>}\n"
    )
    write_hsl(
        n_str + "/post1.hsl",
        "{ c1 |i" + "0" * (n - 1) + "1> : |i|=" + str(n) + " }\n"
        "∪ { c1 |" + "1" * n + "0" * (n - 1) + "0>}\n"
        "\\ { c1 |" + "1" * n + "0" * (n - 1) + "1>}\n"
    )