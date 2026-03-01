#!/usr/bin/python3
import os
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import ensure_bench_dir, write_hsl

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
    ensure_bench_dir(folder)
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
    write_hsl("pre.hsl", "{c1 |" + ('0'*(2*n+1)) + ">}\n")
    #########################################

    #########################################
    loop_body = ("{v1 ∑|i|=" + str(n) + ",i≠" + ('1'*n) + " |" + ('0'*(n+1)+'i') + "> + v2 |" + ('0'*(n+1)+'1'*n) + "> + v3 |" + ('0'*(n-1)+'10'+'1'*n) + ">}\n"
                 "Constraints\n"
                 "imag(v1) = 0\n"
                 "imag(v2) = 0\n"
                 "imag(v3) = 0\n")
    write_hsl("loop-invariant.hsl", loop_body, header="Extended Dirac\n")
    #########################################

    #########################################
    write_hsl("post.hsl", "{c1 |" + ('0'*(n-1)+'10'+'1'*n) + ">}\n")
    #########################################

    os.chdir('..')
