#!/usr/bin/python3
import os

def oracle(file, n):
    file.write(f'ccx problem[{n+1}], problem[{n+2}], problem[{0}];\n')
    for i in range(0, n-2):
        file.write(f'ccx problem[{i}], problem[{n+3+i}], problem[{i+1}];\n')
    file.write(f'cx problem[{n-2}], problem[{n}];\n')
    for i in range(n-3, -1, -1):
        file.write(f'ccx problem[{i}], problem[{n+3+i}], problem[{i+1}];\n')
    file.write(f'ccx problem[{n+1}], problem[{n+2}], problem[{0}];\n')

def E_k(file, n):
    oracle(file, n)
    file.write(f'cu problem[{n}], problem[{n-1}];\n')
    oracle(file, n)

def mcz(file, n):
    file.write(f'ccx problem[{n+1}], problem[{n+2}], problem[{0}];\n')
    for i in range(0, n-3):
        file.write(f'ccx problem[{i}], problem[{n+3+i}], problem[{i+1}];\n')
    file.write(f'cz problem[{n-3}], problem[{2*n}];\n')
    for i in range(n-4, -1, -1):
        file.write(f'ccx problem[{i}], problem[{n+3+i}], problem[{i+1}];\n')
    file.write(f'ccx problem[{n+1}], problem[{n+2}], problem[{0}];\n')

for n in range(3, 100):
    assert n >= 3
    folder = str(n).zfill(2)
    try:
        os.mkdir(folder)
    except:
        pass
    os.chdir(folder)

    #########################################
    with open("circuit.qasm", "w") as file:
        file.write("OPENQASM 3;\n")
        file.write('include "stdgates.inc";\n')
        file.write(f'qubit[{2*n+1}] problem;\n\n') # assert n >= 3
        ########
        for i in range(n+1, 2*n+1): # initial superposition
            file.write(f'h problem[{i}];\n')
        ########
        E_k(file, n)
        ########
        file.write(f'\nwhile (!measure problem[{n-1}]) ' + '{ // loop-invariant.spec\n')
        file.write(f'x problem[{n}];\n')
        file.write(f'h problem[{n}];\n')
        oracle(file, n)
        file.write(f'h problem[{n}];\n')
        file.write(f'x problem[{n}];\n')
        ######## diffusion
        for i in range(n+1, 2*n+1):
            file.write(f'h problem[{i}];\n')
        for i in range(n+1, 2*n+1):
            file.write(f'x problem[{i}];\n')
        mcz(file, n)
        for i in range(n+1, 2*n+1):
            file.write(f'x problem[{i}];\n')
        for i in range(n+1, 2*n+1):
            file.write(f'h problem[{i}];\n')
        ########
        E_k(file, n)
        ########
        file.write('} // post.spec\n')
    #########################################

    #########################################
    with open("pre.spec", "w") as file:
        file.write("Numbers\n")
        file.write("c0 := 0\n")
        file.write("c1 := 1\n")
        file.write("Transitions\n")
        file.write("[1](2, 1) -> 0\n")
        for i in range(2, 2*n+2):
            file.write(f"[{i}]({2*i - 1}, {2*i - 1}) -> {2*i - 3}\n")
            file.write(f"[{i}]({2*i    }, {2*i - 1}) -> {2*i - 2}\n")
        file.write(f"[c0] -> {2*(2*n+1) - 1}\n")
        file.write(f"[c1] -> {2*(2*n+1)    }\n")
        file.write("Constraints\n")
    #########################################

    #########################################
    with open("loop-invariant.spec", "w") as file:
        file.write("Numbers\n")
        file.write("c0 := 0\n")
        file.write("v1\n")
        file.write("v2\n")
        file.write("v3\n")
        file.write("Transitions\n")
        file.write("[1](2, 1) -> 0\n")
        for i in range(2, n):
            file.write(f"[{i}]({2*i - 1}, {2*i - 1}) -> {2*i - 3}\n")
            file.write(f"[{i}]({2*i    }, {2*i - 1}) -> {2*i - 2}\n")
        file.write(f"[{n}]({2*n - 1}, {2*n - 1}) -> {2*(n-1) - 1}\n")
        file.write(f"[{n}]({2*n    }, {2*n + 1}) -> {2*(n-1)}\n")
        file.write(f"[{n+1}]({2*n + 2}, {2*n + 2}) -> {2*n - 1}\n")
        file.write(f"[{n+1}]({2*n + 3}, {2*n + 2}) -> {2*n    }\n")
        file.write(f"[{n+1}]({2*n + 4}, {2*n + 2}) -> {2*n + 1}\n")
        file.write(f"[{n+2}]({2*(n+2) + 1}, {2*(n+2) + 1}) -> {2*(n+2) - 2}\n")
        file.write(f"[{n+2}]({2*(n+2) + 2}, {2*(n+2) + 3}) -> {2*(n+2) - 1}\n")
        file.write(f"[{n+2}]({2*(n+2) + 4}, {2*(n+2) + 5}) -> {2*(n+2)    }\n")
        for i in range(n+3, 2*n+2):
            file.write(f"[{i}]({5*i - 3*n - 5}, {5*i - 3*n - 5}) -> {5*i - 3*n - 10}\n")
            file.write(f"[{i}]({5*i - 3*n - 4}, {5*i - 3*n - 4}) -> {5*i - 3*n - 9}\n")
            file.write(f"[{i}]({5*i - 3*n - 4}, {5*i - 3*n - 3}) -> {5*i - 3*n - 8}\n")
            file.write(f"[{i}]({5*i - 3*n - 2}, {5*i - 3*n - 2}) -> {5*i - 3*n - 7}\n")
            file.write(f"[{i}]({5*i - 3*n - 2}, {5*i - 3*n - 1}) -> {5*i - 3*n - 6}\n")
        file.write(f"[c0] -> {5*(2*n+1) - 3*n - 5}\n")
        file.write(f"[v1] -> {5*(2*n+1) - 3*n - 4}\n")
        file.write(f"[v2] -> {5*(2*n+1) - 3*n - 3}\n")
        file.write(f"[c0] -> {5*(2*n+1) - 3*n - 2}\n")
        file.write(f"[v3] -> {5*(2*n+1) - 3*n - 1}\n")
        file.write("Constraints\n")
        file.write("(declare-fun v1 () Real)(declare-fun v2 () Real)(declare-fun v3 () Real)\n")
    #########################################

    #########################################
    with open("post.spec", "w") as file:
        file.write("Numbers\n")
        file.write("c0 := 0\n")
        file.write("c1 := 1\n")
        file.write("Transitions\n")
        file.write("[1](2, 1) -> 0\n")
        for i in range(2, n):
            file.write(f"[{i}]({2*i - 1}, {2*i - 1}) -> {2*i - 3}\n")
            file.write(f"[{i}]({2*i    }, {2*i - 1}) -> {2*i - 2}\n")
        file.write(f"[{n}]({2*n - 1}, {2*n - 1}) -> {2*(n-1) - 1}\n")
        file.write(f"[{n}]({2*n    }, {2*n + 1}) -> {2*(n-1)}\n")
        file.write(f"[{n+1}]({2*n + 2}, {2*n + 2}) -> {2*n - 1}\n")
        file.write(f"[{n+1}]({2*n + 3}, {2*n + 2}) -> {2*n    }\n")
        file.write(f"[{n+1}]({2*n + 4}, {2*n + 2}) -> {2*n + 1}\n")
        file.write(f"[{n+2}]({2*(n+2) + 1}, {2*(n+2) + 1}) -> {2*(n+2) - 2}\n")
        file.write(f"[{n+2}]({2*(n+2) + 2}, {2*(n+2) + 3}) -> {2*(n+2) - 1}\n")
        file.write(f"[{n+2}]({2*(n+2) + 4}, {2*(n+2) + 5}) -> {2*(n+2)    }\n")
        for i in range(n+3, 2*n+2):
            file.write(f"[{i}]({5*i - 3*n - 5}, {5*i - 3*n - 5}) -> {5*i - 3*n - 10}\n")
            file.write(f"[{i}]({5*i - 3*n - 4}, {5*i - 3*n - 4}) -> {5*i - 3*n - 9}\n")
            file.write(f"[{i}]({5*i - 3*n - 4}, {5*i - 3*n - 3}) -> {5*i - 3*n - 8}\n")
            file.write(f"[{i}]({5*i - 3*n - 2}, {5*i - 3*n - 2}) -> {5*i - 3*n - 7}\n")
            file.write(f"[{i}]({5*i - 3*n - 2}, {5*i - 3*n - 1}) -> {5*i - 3*n - 6}\n")
        file.write(f"[c0] -> {5*(2*n+1) - 3*n - 5}\n")
        file.write(f"[c0] -> {5*(2*n+1) - 3*n - 4}\n")
        file.write(f"[c0] -> {5*(2*n+1) - 3*n - 3}\n")
        file.write(f"[c0] -> {5*(2*n+1) - 3*n - 2}\n")
        file.write(f"[c1] -> {5*(2*n+1) - 3*n - 1}\n")
    #########################################

    os.chdir('..')