#!/usr/bin/python3
import os

for n in range(1, 100):
    folder = str(n).zfill(2)
    os.mkdir(folder)
    os.chdir(folder)

    #########################################
    with open("circuit.qasm", "w") as file:
        file.write("OPENQASM 2.0;\n")
        file.write('include "qelib1.inc";\n')
        file.write(f'qreg qubits[{2*n+1}];\n\n')

        for i in range(n, -1, -1):
            file.write(f'h qubits[{n+i}];\n')
        file.write(f'z qubits[{n+n}];\n')
        for i in range(0, n):
            file.write(f'ccx qubits[{i}], qubits[{n+i}], qubits[{n+n}];\n')
        for i in range(n, -1, -1):
            file.write(f'h qubits[{n+i}];\n')
    #########################################

    #########################################
    with open("pre.spec", "w") as file:
        file.write("Numbers\n")
        file.write("c0 := 0\n")
        file.write("c1 := 1\n")
        file.write("Transitions\n")
        for level in range(1, n+1):
            if (level >= 2):
                file.write(f"[{level}]({2*level - 1}, {2*level - 1}) -> {2*level - 3}\n")
            file.write(f"[{level}]({2*level - 1}, {2*level}) -> {2*level - 2}\n")
            file.write(f"[{level}]({2*level}, {2*level - 1}) -> {2*level - 2}\n")
        for level in range(1, n+2):
            file.write(f"[{n + level}]({2*n + 2*level-1}, {2*n + 2*level-1}) -> {2*n + 2*level-3}\n")
            file.write(f"[{n + level}]({2*n + 2*level}, {2*n + 2*level-1}) -> {2*n + 2*level-2}\n")
        file.write(f"[c0] -> {2*n + 2*(n+1)-1}\n")
        file.write(f"[c1] -> {2*n + 2*(n+1)}\n")
    #########################################

    os.chdir('..')