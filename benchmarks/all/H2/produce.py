#!/usr/bin/python3
import sys
import os
import shutil
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import ensure_bench_dir_for_n, write_qasm_header, parse_sizes

sizes = parse_sizes(1, 1001, min_n=1)

for n in sizes:
    n_str = ensure_bench_dir_for_n(n, zfill=3)
    #########################################
    with open(n_str + "/circuit.qasm", "w") as file:
        write_qasm_header(file)
        file.write(f'qreg qubits[{n}];\n\n')
        for i in range(n-1, -1, -1):
            file.write(f'h qubits[{i}];\n')
            file.write(f'h qubits[{i}];\n')
    #########################################
    with open(n_str + '/pre.hsl', 'w') as file:
        file.write('Constants\n')
        file.write('c1 := 1\n')
        file.write('Extended Dirac\n')
        file.write(f"{{c1 |i> : |i|={n}}}\n")
    shutil.copy(n_str + '/pre.hsl', n_str + '/post.hsl')
    #########################################
    # with open(n_str + "/pre.lsta", "w") as file:
    #     file.write('Constants\n')
    #     file.write('c0 := 0\n')
    #     file.write('c1 := 1\n')
    #     file.write('Root States 0\n')
    #     file.write('Transitions\n')
    #     file.write(f"[{1},1](1, 2) -> 0\n")
    #     file.write(f"[{1},2](2, 1) -> 0\n")
    #     for level in range(2, n+1):
    #         file.write(f"[{level},3]({2*level - 1}, {2*level - 1}) -> {2*level - 3}\n")
    #         file.write(f"[{level},1]({2*level - 1}, {2*level    }) -> {2*level - 2}\n")
    #         file.write(f"[{level},2]({2*level    }, {2*level - 1}) -> {2*level - 2}\n")
    #     file.write(f"[c0,1] -> {2*n-1}\n")
    #     file.write(f"[c1,1] -> {2*n}\n")
    # shutil.copy(n_str + '/pre.lsta', n_str + '/post.lsta')
    #########################################

# cp -rl {012,013,064,128,256} ../../POPL25/H2/