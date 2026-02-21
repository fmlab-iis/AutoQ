#!/usr/bin/python3
import sys
import os
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import ensure_bench_dir_for_n, write_qasm_header, parse_sizes

sizes = parse_sizes(2, 1001, min_n=2)

for n in sizes:
    n_str = ensure_bench_dir_for_n(n, zfill=3)
    #########################################
    with open(n_str + "/circuit.qasm", "w") as file:
        write_qasm_header(file)
        file.write(f'qreg qubits[{n}];\n\n')
        file.write(f'h qubits[0];\n')
        for i in range(0, n-1):
            file.write(f'cx qubits[{i}], qubits[{i+1}];\n')
    #########################################
    with open(n_str + '/pre.hsl', 'w') as file:
        file.write('Constants\n')
        file.write(f"c1 := 1\n")
        file.write('Extended Dirac\n')
        file.write(f"{{c1 |{'0' * n}>}}\n")
    #########################################
    # with open(n_str + "/pre.lsta", "w") as file:
    #     file.write('Constants\n')
    #     file.write('c0 := 0\n')
    #     file.write('c1 := 1\n')
    #     file.write('Root States 0\n')
    #     file.write('Transitions\n')
    #     file.write(f"[{1},1]({2}, {1}) -> {0}\n")
    #     for level in range(2, n+1):
    #         file.write(f"[{level},1]({2*level - 1}, {2*level - 1}) -> {2*level - 3}\n")
    #         file.write(f"[{level},1]({2*level}, {2*level - 1}) -> {2*level - 2}\n")
    #     file.write(f"[c0,1] -> {2*n-1}\n")
    #     file.write(f"[c1,1] -> {2*n}\n")
    #########################################
    with open(n_str + '/post.hsl', 'w') as file:
        file.write('Constants\n')
        file.write(f"cp := 1/sqrt2\n")
        file.write('Extended Dirac\n')
        file.write(f"{{cp |{'0' * n}> + cp |{'1' * n}>}}\n")
    #########################################
    # with open(n_str + "/post.lsta", "w") as file:
    #     file.write('Constants\n')
    #     file.write('c0 := 0\n')
    #     file.write('c1 := 1/sqrt2\n')
    #     file.write('Root States 0\n')
    #     file.write('Transitions\n')
    #     file.write("[1,1](1, 2) -> 0\n")
    #     file.write("[2,1](4, 3) -> 1\n")
    #     file.write("[2,1](3, 5) -> 2\n")
    #     for level in range(3, n+1):
    #         file.write(f"[{level},1]({(level - 1) * 3}, {(level - 1) * 3}) -> {(level - 2) * 3}\n")
    #         file.write(f"[{level},1]({(level - 1) * 3 + 1}, {(level - 1) * 3}) -> {(level - 2) * 3 + 1}\n")
    #         file.write(f"[{level},1]({(level - 1) * 3}, {(level - 1) * 3 + 2}) -> {(level - 2) * 3 + 2}\n")
    #     file.write(f"[c0,1] -> {(n - 1) * 3}\n")
    #     file.write(f"[c1,1] -> {(n - 1) * 3 + 1}\n")
    #     file.write(f"[c1,1] -> {(n - 1) * 3 + 2}\n")
    #########################################

# cp -rl {064,128,256,384,512} ../../POPL25/GHZzero/