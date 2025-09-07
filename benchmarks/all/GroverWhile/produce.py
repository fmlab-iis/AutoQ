#!/usr/bin/python3
import os

def oracle(file, n):
    file.write(f'ccx qb[{n+1}], qb[{n+2}], qb[{0}];\n')
    for i in range(0, n-2):
        file.write(f'ccx qb[{i}], qb[{n+3+i}], qb[{i+1}];\n')
    file.write(f'cx qb[{n-2}], qb[{n}];\n')
    for i in range(n-3, -1, -1):
        file.write(f'ccx qb[{i}], qb[{n+3+i}], qb[{i+1}];\n')
    file.write(f'ccx qb[{n+1}], qb[{n+2}], qb[{0}];\n')

def E_k(file, n):
    oracle(file, n)
    file.write(f'ck qb[{n}], qb[{n-1}];\n')
    oracle(file, n)

def mcz(file, n):
    file.write(f'ccx qb[{n+1}], qb[{n+2}], qb[{0}];\n')
    for i in range(0, n-3):
        file.write(f'ccx qb[{i}], qb[{n+3+i}], qb[{i+1}];\n')
    file.write(f'cz qb[{n-3}], qb[{2*n}];\n')
    for i in range(n-4, -1, -1):
        file.write(f'ccx qb[{i}], qb[{n+3+i}], qb[{i+1}];\n')
    file.write(f'ccx qb[{n+1}], qb[{n+2}], qb[{0}];\n')

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
        file.write(f'qubit[{2*n+1}] qb;\n') # assert n >= 3
        file.write(f'bit[{2*n+1}] outcome;\n\n')
        file.write('''/******************************************************/
// Users should be notified that all gate definitions
// in this circuit file are simply ignored by AutoQ 2.0.
// These definitions are intended for this circuit file
// to be readable by qiskit.
gate k q {
    U(0.190332413, 0, 0) q;
}
gate ck q1, q2 {
    ctrl @ k q1, q2;
}
/******************************************************/
\n''')
        ########
        for i in range(n+1, 2*n+1): # initial superposition
            file.write(f'h qb[{i}];\n')
        ########
        E_k(file, n)
        ########
        file.write(f'\noutcome[{n-1}] = measure qb[{n-1}];\n')
        file.write(f'while (!outcome[{n-1}]) ' + '{ // loop-invariant.hsl\n')
        file.write(f'x qb[{n}];\n')
        file.write(f'h qb[{n}];\n')
        oracle(file, n)
        # file.write(f'x qb[{n}];\n') # prevent a global phase flip in the diffuser circuit
        file.write(f'h qb[{n}];\n')
        file.write(f'x qb[{n}];\n')
        ######## diffusion
        for i in range(n+1, 2*n+1):
            file.write(f'h qb[{i}];\n')
        for i in range(n+1, 2*n+1):
            file.write(f'x qb[{i}];\n')
        mcz(file, n)
        for i in range(n+1, 2*n+1):
            file.write(f'x qb[{i}];\n')
        for i in range(n+1, 2*n+1):
            file.write(f'h qb[{i}];\n')
        ########
        E_k(file, n)
        ########
        file.write(f'outcome[{n-1}] = measure qb[{n-1}];\n')
        file.write('}\n')
        file.write('\n// outcome = measure qb;\n')
    #########################################

    #########################################
    with open("pre.hsl", "w") as file:
        file.write("Constants\n")
        file.write("c1 := 1\n")
        file.write("Extended Dirac\n")
        file.write("{c1 |" + ('0'*(2*n+1)) + ">}\n")
    #########################################

    #########################################
    with open("loop-invariant.hsl", "w") as file:
        # file.write("v1\n")
        # file.write("v2\n")
        # file.write("v3\n")
        file.write(f"Extended Dirac\n")
        file.write("{v1 ∑|i|=" + str(n) + ",i≠" + ('1'*n) + " |" + ('0'*(n+1)+'i') + "> + v2 |" + ('0'*(n+1)+'1'*n) + "> + v3 |" + ('0'*(n-1)+'10'+'1'*n) + ">}\n")
        file.write(f"Constraints\n")
        file.write(f"imag(v1) = 0\n")
        file.write(f"imag(v2) = 0\n")
        file.write(f"imag(v3) = 0\n")
        # file.write(f'(and (not (= v3 0)) (and (> v1 0) (> v2 0) (<= v2 v1)))')
    #########################################

    #########################################
    with open("post.hsl", "w") as file:
        file.write("Constants\n")
        file.write("c1 := 1\n")
        file.write("Extended Dirac\n")
        file.write("{c1 |" + ('0'*(n-1)+'10'+'1'*n) + ">}\n")
    #########################################

    os.chdir('..')
