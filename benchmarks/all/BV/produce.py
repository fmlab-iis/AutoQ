#!/usr/bin/python3
import sys
import os
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import ensure_bench_dir_for_n, write_qasm_header, write_hsl, parse_sizes

sizes = parse_sizes(1, 1001, min_n=1)

for n in sizes:
    n_str = ensure_bench_dir_for_n(n)
    ###########################################################################
    write_hsl(n_str + '/pre.hsl', f"{{c1 |{'0' * (n+1)}>}}\n")
    ###########################################################################
    # with open(n_str + '/pre.lsta', 'w') as file:
    #     file.write('Constants\n')
    #     file.write('c0 := 0\n')
    #     file.write('c1 := 1\n')
    #     file.write('Root States 0\n')
    #     file.write('Transitions\n')
    #     file.write('[1,1](2, 1) -> 0\n')
    #     for i in range(2, n+2): # 2 <= i <= n+1
    #         file.write(f'[{i},1]({2*i-1}, {2*i-1}) -> {2*i-3}\n')
    #         file.write(f'[{i},1]({2*i  }, {2*i-1}) -> {2*i-2}\n')
    #     file.write(f'[c0,1] -> {2*n+1}\n')
    #     file.write(f'[c1,1] -> {2*n+2}\n')
    ###########################################################################
    with open(n_str + '/circuit.qasm', 'w') as file:
        write_qasm_header(file)
        file.write(f'qreg qubits[{n+1}];\n\n')
        for i in range(0, n+1):
            file.write(f'h qubits[{i}];\n')
        file.write(f'z qubits[{n}];\n')
        for i in range(0, n, 2):
            file.write(f'cx qubits[{i}], qubits[{n}];\n')
        for i in range(0, n+1):
            file.write(f'h qubits[{i}];\n')
    ###########################################################################
    # with open(n_str + '/post.lsta', 'w') as file:
    #     file.write('Constants\n')
    #     file.write('c0 := 0\n')
    #     file.write('c1 := 1\n')
    #     file.write('Root States 0\n')
    #     file.write('Transitions\n')
    #     file.write('[1,1](1, 2) -> 0\n')
    #     for i in range(2, n+1): # 2 <= i <= n
    #         file.write(f'[{i},1]({2*i-1}, {2*i-1}) -> {2*i-3}\n')
    #         if i % 2:
    #             file.write(f'[{i},1]({2*i-1}, {2*i  }) -> {2*i-2}\n')
    #         else:
    #             file.write(f'[{i},1]({2*i  }, {2*i-1}) -> {2*i-2}\n')
    #     file.write(f'[{(n+1)},1]({2*(n+1)-1}, {2*(n+1)-1}) -> {2*(n+1)-3}\n')
    #     file.write(f'[{(n+1)},1]({2*(n+1)-1}, {2*(n+1)  }) -> {2*(n+1)-2}\n')
    #     file.write(f'[c0,1] -> {2*n+1}\n')
    #     file.write(f'[c1,1] -> {2*n+2}\n')
    ###########################################################################
    write_hsl(n_str + '/post.hsl', f"{{c1 |{'10' * (n//2) + '1' * (n%2)}1>}}\n")
    ###########################################################################
