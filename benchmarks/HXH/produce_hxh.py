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
        file.write(f'qreg qubits[{n}];\n\n')

        for i in range(n-1, -1, -1):
            file.write(f'h qubits[{i}];\n')
            file.write(f'x qubits[{i}];\n')
            file.write(f'h qubits[{i}];\n')
    #########################################

    #########################################
    with open("pre.aut", "w") as file:
        file.write("Ops " + ' '.join(f'[{i}]:2' for i in range(1, n+1)) + ' [0,0,0,0,0]:0 [1,0,0,0,0]:0\n')
        file.write("Automaton Basis\n")
        file.write(f"States {' '.join([str(i) for i in range(2*n + 1)])}\n")
        file.write("Final States 0\n")
        file.write("Transitions\n")
        for level in range(1, n+1):
            if (level >= 2):
                file.write(f"[{level}]({2*level - 1}, {2*level - 1}) -> {2*level - 3}\n")
            file.write(f"[{level}]({2*level - 1}, {2*level}) -> {2*level - 2}\n")
            file.write(f"[{level}]({2*level}, {2*level - 1}) -> {2*level - 2}\n")
        file.write(f"[0,0,0,0,0] -> {2*n-1}\n")
        file.write(f"[1,0,0,0,0] -> {2*n}\n")
    #########################################

    os.chdir('..')