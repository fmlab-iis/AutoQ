#!/usr/bin/python3
import os

for n in range(1, 100):
    folder = str(n).zfill(2)
    os.mkdir(folder)
    os.chdir(folder)

    id = []
    for i in range(1, n+1):
        id.append(2*i - 1 - 1)
    for i in range(n+1, 2*n+1):
        id.append(2 * (i-n) - 1)
    id.append(2*n+1 - 1)

    #########################################
    with open("circuit.qasm", "w") as file:
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

    #########################################
    with open("pre.spec", "w") as file:
        file.write("Numbers\n")
        file.write("c0 := 0\n")
        file.write("c1 := 1\n")
        file.write("Transitions\n")
        for i in range(1, n+1):
            if i > 1:
                file.write(f"[{2*i - 1}]({4*i - 3}, {4*i - 3}) -> {4*i - 5}\n")
            file.write(f"[{2*i - 1}]({4*i - 3}, {4*i - 2}) -> {4*i - 4}\n")
            file.write(f"[{2*i - 1}]({4*i - 2}, {4*i - 3}) -> {4*i - 4}\n")
            file.write(f"[{2*i    }]({4*i - 1}, {4*i - 1}) -> {4*i - 3}\n")
            file.write(f"[{2*i    }]({4*i    }, {4*i - 1}) -> {4*i - 2}\n")
        file.write(f"[{2*n + 1}]({4*n + 1}, {4*n + 1}) -> {4*n - 1}\n")
        file.write(f"[{2*n + 1}]({4*n + 2}, {4*n + 1}) -> {4*n    }\n")
        file.write(f"[c0] -> {4*n + 1}\n")
        file.write(f"[c1] -> {4*n + 2}\n")
    #########################################

    #########################################
    with open("post.spec", "w") as file:
        file.write("Numbers\n")
        file.write("c0 := 0\n")
        file.write("c1 := 1\n")
        file.write("Transitions\n")
        for i in range(1, n+1):
            if i > 1:
                file.write(f"[{2*i - 1}]({5*i - 4}, {5*i - 4}) -> {5*i - 6}\n")
            file.write(f"[{2*i - 1}]({5*i - 4}, {5*i - 3}) -> {5*i - 5}\n")
            file.write(f"[{2*i - 1}]({5*i - 2}, {5*i - 4}) -> {5*i - 5}\n")
            file.write(f"[{2*i    }]({5*i - 1}, {5*i - 1}) -> {5*i - 4}\n")
            file.write(f"[{2*i    }]({5*i - 1}, {5*i    }) -> {5*i - 3}\n")
            file.write(f"[{2*i    }]({5*i    }, {5*i - 1}) -> {5*i - 2}\n")
        file.write(f"[{2*n + 1}]({5*n + 1}, {5*n + 1}) -> {5*n - 1}\n")
        file.write(f"[{2*n + 1}]({5*n + 1}, {5*n + 2}) -> {5*n    }\n")
        file.write(f"[c0] -> {5*n + 1}\n")
        file.write(f"[c1] -> {5*n + 2}\n")
    #########################################

    os.chdir('..')