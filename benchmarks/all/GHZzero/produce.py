#!/usr/bin/python3
import sys
import os

sizes = []
if len(sys.argv) == 2:
    n = int(sys.argv[1])
    assert(n >= 2)
    sizes.append(n)
else:
    sizes = list(range(2, 1001))

for n in sizes:
    n_str = str(n).zfill(3)
    if not os.path.exists(n_str):
        os.makedirs(n_str)
    #########################################
    with open(n_str + "/circuit.qasm", "w") as file:
        file.write("OPENQASM 2.0;\n")
        file.write('include "qelib1.inc";\n')
        file.write(f'qreg qubits[{n}];\n\n')
        file.write(f'h qubits[0];\n')
        for i in range(0, n-1):
            file.write(f'cx qubits[{i}], qubits[{i+1}];\n')
    #########################################
    with open(n_str + '/pre.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write(f"{{|{'0' * n}>}}\n")
    #########################################
    with open(n_str + "/pre.lsta", "w") as file:
        file.write('Constants\n')
        file.write('c0 := 0\n')
        file.write('c1 := 1\n')
        file.write('Root States 0\n')
        file.write('Transitions\n')
        file.write(f"[{1},1]({2}, {1}) -> {0}\n")
        for level in range(2, n+1):
            file.write(f"[{level},1]({2*level - 1}, {2*level - 1}) -> {2*level - 3}\n")
            file.write(f"[{level},1]({2*level}, {2*level - 1}) -> {2*level - 2}\n")
        file.write(f"[c0,1] -> {2*n-1}\n")
        file.write(f"[c1,1] -> {2*n}\n")
    #########################################
    with open(n_str + '/post.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write(f"{{1/sqrt2 |{'0' * n}> + 1/sqrt2 |{'1' * n}>}}\n")
    #########################################
    with open(n_str + "/post.lsta", "w") as file:
        file.write('Constants\n')
        file.write('c0 := 0\n')
        file.write('c1 := 1/sqrt2\n')
        file.write('Root States 0\n')
        file.write('Transitions\n')
        file.write("[1,1](1, 2) -> 0\n")
        file.write("[2,1](4, 3) -> 1\n")
        file.write("[2,1](3, 5) -> 2\n")
        for level in range(3, n+1):
            file.write(f"[{level},1]({(level - 1) * 3}, {(level - 1) * 3}) -> {(level - 2) * 3}\n")
            file.write(f"[{level},1]({(level - 1) * 3 + 1}, {(level - 1) * 3}) -> {(level - 2) * 3 + 1}\n")
            file.write(f"[{level},1]({(level - 1) * 3}, {(level - 1) * 3 + 2}) -> {(level - 2) * 3 + 2}\n")
        file.write(f"[c0,1] -> {(n - 1) * 3}\n")
        file.write(f"[c1,1] -> {(n - 1) * 3 + 1}\n")
        file.write(f"[c1,1] -> {(n - 1) * 3 + 2}\n")
    #########################################

# cp -rl {064,128,256,384,512} ../../LSTA/GHZzero/