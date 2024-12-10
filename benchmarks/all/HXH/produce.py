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
    #########################################
    with open(n_str + "/circuit.qasm", "w") as file:
        file.write("OPENQASM 2.0;\n")
        file.write('include "qelib1.inc";\n')
        file.write(f'qreg qubits[{n}];\n\n')
        for i in range(n-1, -1, -1):
            file.write(f'h qubits[{i}];\n')
            file.write(f'x qubits[{i}];\n')
            file.write(f'h qubits[{i}];\n')
    #########################################
    with open(n_str + '/pre.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write(f"{{|i> | |i|={n}}}\n")
    #########################################
    with open(n_str + "/pre.lsta", "w") as file:
        file.write('Constants\n')
        file.write('c0 := 0\n')
        file.write('c1 := 1\n')
        file.write('Root States 0\n')
        file.write('Transitions\n')
        file.write(f"[{1},1](1, 2) -> 0\n")
        file.write(f"[{1},2](2, 1) -> 0\n")
        for level in range(2, n+1):
            file.write(f"[{level},3]({2*level - 1}, {2*level - 1}) -> {2*level - 3}\n")
            file.write(f"[{level},1]({2*level - 1}, {2*level    }) -> {2*level - 2}\n")
            file.write(f"[{level},2]({2*level    }, {2*level - 1}) -> {2*level - 2}\n")
        file.write(f"[c0,1] -> {2*n-1}\n")
        file.write(f"[c1,1] -> {2*n}\n")
    #########################################
    with open(n_str + '/post.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write(f'{{|0>, -|1>}} ^ {n}\n')
    #########################################
    with open(n_str + "/post.lsta", "w") as file:
        file.write("Constants\n")
        file.write("c0 := 0\n")
        file.write("c1 := 1\n")
        file.write("c2 := -1\n")
        file.write('Root States 0\n')
        file.write("Transitions\n")
        file.write(f"[1,1](1, 3) -> 0\n")
        file.write(f"[1,2](2, 1) -> 0\n")
        for i in range(2, n+1):
            file.write(f"[{i},3]({3*i - 2}, {3*i - 2}) -> {3*i - 5}\n")
            file.write(f"[{i},1]({3*i - 2}, {3*i    }) -> {3*i - 4}\n")
            file.write(f"[{i},2]({3*i - 1}, {3*i - 2}) -> {3*i - 4}\n")
            file.write(f"[{i},1]({3*i - 2}, {3*i - 1}) -> {3*i - 3}\n")
            file.write(f"[{i},2]({3*i    }, {3*i - 2}) -> {3*i - 3}\n")
        file.write(f"[c0,1] -> {3*n - 2}\n")
        file.write(f"[c1,1] -> {3*n - 1}\n")
        file.write(f"[c2,1] -> {3*n    }\n")
    #########################################

# cp -rl {1[0-3],99} ../../LSTA/HXH/