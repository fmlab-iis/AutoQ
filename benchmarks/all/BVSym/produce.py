#!/usr/bin/python3
import sys
import os

sizes = []
if len(sys.argv) == 2:
    n = int(sys.argv[1])
    assert(n >= 1)
    sizes.append(n)
else:
    sizes = list(range(1, 1001))

for n in sizes:
    n_str = str(n).zfill(2)
    if not os.path.exists(n_str):
        os.makedirs(n_str)
    ###########################################################################
    with open(n_str + '/pre.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write(f"|{'0' * (n+1)}>\n")
    ###########################################################################
    with open(n_str + '/pre.lsta', 'w') as file:
        file.write('Constants\n')
        file.write('c0 := 0\n')
        file.write('c1 := 1\n')
        file.write('Root States 0\n')
        file.write('Colored Transitions\n')
        file.write('[1,1](2, 1) -> 0\n')
        for i in range(2, n+2): # 2 <= i <= n+1
            file.write(f'[{i},1]({2*i-1}, {2*i-1}) -> {2*i-3}\n')
            file.write(f'[{i},1]({2*i  }, {2*i-1}) -> {2*i-2}\n')
        file.write(f'[c0,1] -> {2*n+1}\n')
        file.write(f'[c1,1] -> {2*n+2}\n')
    ###########################################################################
    with open(n_str + '/circuit.qasm', 'w') as file:
        file.write('OPENQASM 2.0;\n')
        file.write('include "qelib1.inc";\n')
        file.write(f'qreg qubits[{n+1}];\n\n')
        for i in range(0, n+1):
            file.write(f'h qubits[{i}];\n')
        file.write(f'z qubits[{n}];\n')
        for i in range(0, n, 2):
            file.write(f'cx qubits[{i}], qubits[{n}];\n')
        for i in range(0, n+1):
            file.write(f'h qubits[{i}];\n')
    ###########################################################################
    with open(n_str + '/post.lsta', 'w') as file:
        file.write('Predicates\n')
        file.write('p := (= $I 0)\n')
        file.write('Root States 0\n')
        file.write('Colored Transitions\n')
        file.write('[1,1](1, 2) -> 0\n')
        for i in range(2, n+1): # 2 <= i <= n
            file.write(f'[{i},1]({2*i-1}, {2*i-1}) -> {2*i-3}\n')
            if i % 2:
                file.write(f'[{i},1]({2*i-1}, {2*i  }) -> {2*i-2}\n')
            else:
                file.write(f'[{i},1]({2*i  }, {2*i-1}) -> {2*i-2}\n')
        file.write(f'[{(n+1)},1]({2*(n+1)-1}, {2*(n+1)-1}) -> {2*(n+1)-3}\n')
        file.write(f'[{(n+1)},1]({2*(n+1)-1}, {2*(n+1)  }) -> {2*(n+1)-2}\n')
        file.write(f'[p,1] -> {2*n+1}\n')
        file.write(f'[p,1] -> {2*n+2}\n')
    ###########################################################################
    with open(n_str + '/post.hsl', 'w') as file:
        file.write('Predicates\n')
        file.write('p := (= $I 0)\n')
        file.write('Extended Dirac\n')
        file.write(f"p |{'0' * (n+1)}> + p |*>\n")
    ###########################################################################