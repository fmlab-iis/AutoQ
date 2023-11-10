#!/usr/bin/python3
import os

for n in range(2, 1000):
    folder = str(n).zfill(3)
    os.mkdir(folder)
    os.chdir(folder)

    #########################################
    with open("circuit.qasm", "w") as file:
        file.write("OPENQASM 2.0;\n")
        file.write('include "qelib1.inc";\n')
        file.write(f'qreg qubits[{n}];\n\n')

        file.write(f'h qubits[0];\n')
        for i in range(0, n-1):
            file.write(f'cx qubits[{i}], qubits[{i+1}];\n')
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
        file.write(f"[c0] -> {2*n-1}\n")
        file.write(f"[c1] -> {2*n}\n")
    #########################################

    #########################################
    with open("post.spec", "w") as file:
        file.write("Numbers\n")
        file.write("c0 := 0\n")
        file.write("c1 := 1 / V2\n")
        file.write("c2 := -1 / V2\n")
        file.write("Colored Transitions\n")
        file.write(f"[1,1](1, 2) -> 0\n")
        file.write(f"[1,2](4, 3) -> 0\n")
        file.write(f"[2,1](6, 5) -> 1\n")
        file.write(f"[2,1](5, 7) -> 2\n")
        file.write(f"[2,2](7, 5) -> 1\n")
        file.write(f"[2,2](5, 6) -> 2\n")
        file.write(f"[2,4](6, 5) -> 1\n")
        file.write(f"[2,4](5, 9) -> 2\n")
        file.write(f"[2,8](7, 5) -> 1\n")
        file.write(f"[2,8](5, 8) -> 2\n")
        file.write(f"[2,1](5, 7) -> 4\n")
        file.write(f"[2,2](5, 7) -> 4\n")
        file.write(f"[2,4](5, 6) -> 4\n")
        file.write(f"[2,8](5, 6) -> 4\n")
        file.write(f"[2,1](6, 5) -> 3\n")
        file.write(f"[2,2](8, 5) -> 3\n")
        file.write(f"[2,4](7, 5) -> 3\n")
        file.write(f"[2,8](9, 5) -> 3\n")
        for i in range(3, n+1):
            file.write(f"[{i},0]({5*i - 5}, {5*i - 5}) -> {5*i - 10}\n")
            file.write(f"[{i},1]({5*i - 4}, {5*i - 5}) -> {5*i - 9}\n")
            file.write(f"[{i},2]({5*i - 3}, {5*i - 5}) -> {5*i - 9}\n")
            file.write(f"[{i},1]({5*i - 5}, {5*i - 3}) -> {5*i - 8}\n")
            file.write(f"[{i},2]({5*i - 5}, {5*i - 4}) -> {5*i - 8}\n")
            file.write(f"[{i},1]({5*i - 2}, {5*i - 5}) -> {5*i - 7}\n")
            file.write(f"[{i},2]({5*i - 1}, {5*i - 5}) -> {5*i - 7}\n")
            file.write(f"[{i},1]({5*i - 5}, {5*i - 1}) -> {5*i - 6}\n")
            file.write(f"[{i},2]({5*i - 5}, {5*i - 2}) -> {5*i - 6}\n")
        file.write(f"[c0,0] -> {5*n - 5}\n")
        file.write(f"[c1,0] -> {5*n - 4}\n")
        file.write(f"[c1,0] -> {5*n - 3}\n")
        file.write(f"[c2,0] -> {5*n - 2}\n")
        file.write(f"[c2,0] -> {5*n - 1}\n")
    #########################################

    os.chdir('..')