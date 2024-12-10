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
    id = []
    for i in range(1, n+1):
        id.append(2*i - 1 - 1)
    for i in range(n+1, 2*n+1):
        id.append(2 * (i-n) - 1)
    id.append(2*n+1 - 1)
    #########################################
    with open(n_str + "/circuit.qasm", "w") as file:
        file.write("OPENQASM 2.0;\n")
        file.write('include "qelib1.inc";\n')
        file.write(f'qreg qubits[{2*n+1}];\n\n')

        for i in range(n, -1, -1):
            file.write(f'h qubits[{id[n+i]}];\n')
        file.write(f'z qubits[{id[n+n]}];\n')
        for i in range(0, n):
            file.write(f'ccx qubits[{id[i]}], qubits[{id[n+i]}], qubits[{id[n+n]}];\n')
        for i in range(n, -1, -1):
            file.write(f'h qubits[{id[n+i]}];\n')
    #########################################
    with open(n_str + "/pre.hsl", "w") as file:
        file.write("Extended Dirac\n")
        file.write('{|i0> | |i|=1} ^ ' + f'{n}' + ' ⊗ {|0>}\n')
    #########################################
    with open(n_str + "/pre.lsta", "w") as file:
        file.write("Constants\n")
        file.write("c0 := 0\n")
        file.write("c1 := 1\n")
        file.write("Root States 0\n")
        file.write("Transitions\n")
        for i in range(1, n+1):
            if i > 1:
                file.write(f"[{2*i - 1},3]({4*i - 3}, {4*i - 3}) -> {4*i - 5}\n")
            file.write(f"[{2*i - 1},1]({4*i - 3}, {4*i - 2}) -> {4*i - 4}\n")
            file.write(f"[{2*i - 1},2]({4*i - 2}, {4*i - 3}) -> {4*i - 4}\n")
            file.write(f"[{2*i    },1]({4*i - 1}, {4*i - 1}) -> {4*i - 3}\n")
            file.write(f"[{2*i    },1]({4*i    }, {4*i - 1}) -> {4*i - 2}\n")
        file.write(f"[{2*n + 1},1]({4*n + 1}, {4*n + 1}) -> {4*n - 1}\n")
        file.write(f"[{2*n + 1},1]({4*n + 2}, {4*n + 1}) -> {4*n    }\n")
        file.write(f"[c0,1] -> {4*n + 1}\n")
        file.write(f"[c1,1] -> {4*n + 2}\n")
    #########################################

    #########################################
    with open(n_str + "/post.lsta", "w") as file:
        file.write("Constants\n")
        file.write("c0 := 0\n")
        file.write("c1 := 1\n")
        file.write("Root States 0\n")
        file.write("Transitions\n")
        for i in range(1, n+1):
            if i > 1:
                file.write(f"[{2*i - 1},3]({5*i - 4}, {5*i - 4}) -> {5*i - 6}\n")
            file.write(f"[{2*i - 1},1]({5*i - 4}, {5*i - 3}) -> {5*i - 5}\n")
            file.write(f"[{2*i - 1},2]({5*i - 2}, {5*i - 4}) -> {5*i - 5}\n")
            file.write(f"[{2*i    },3]({5*i - 1}, {5*i - 1}) -> {5*i - 4}\n")
            file.write(f"[{2*i    },1]({5*i - 1}, {5*i    }) -> {5*i - 3}\n")
            file.write(f"[{2*i    },2]({5*i    }, {5*i - 1}) -> {5*i - 2}\n")
        file.write(f"[{2*n + 1},1]({5*n + 1}, {5*n + 1}) -> {5*n - 1}\n")
        file.write(f"[{2*n + 1},1]({5*n + 1}, {5*n + 2}) -> {5*n    }\n")
        file.write(f"[c0,1] -> {5*n + 1}\n")
        file.write(f"[c1,1] -> {5*n + 2}\n")
    #########################################
    with open(n_str + "/post.hsl", "w") as file:
        file.write("Extended Dirac\n")
        file.write('{|00>, |11>} ^ ' + f'{n}' + ' ⊗ {|1>}\n')
    #########################################

# cp -rl {09,1[0-3]} ../../LSTA/MOBV_reorder/