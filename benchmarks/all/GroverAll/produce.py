#!/usr/bin/python3
import sys
import os
import math

sizes = []
if len(sys.argv) == 2:
    n = int(sys.argv[1])
    assert(n >= 3)
    sizes.append(n)
else:
    sizes = list(range(3, 12))

for n in sizes:
    q = 3 * n - 1
    n_str = str(n).zfill(2)
    if not os.path.exists(n_str):
        os.makedirs(n_str)
    ###########################################################################
    with open(n_str + '/pre.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write('{|s' + '0'*(2*n-1) + '> : |s|=' + str(n) + '}\n')
    ###########################################################################
    with open(n_str + '/pre.hslsym', 'w') as file:
        file.write(f'|i|={n} i:1,0,0,0,0 *:0,0,0,0,0 # {'0'*(2*n-1)}:1,0,0,0,0 *:0,0,0,0,0\n')
    ###########################################################################
    # with open(n_str + "/pre.lsta", "w") as file:
    #     file.write('Constants\n')
    #     file.write('c0 := 0\n')
    #     file.write('c1 := 1\n')
    #     file.write('Root States 0\n')
    #     file.write('Transitions\n')
    #     file.write(f"[1,1](1, 2) -> 0\n")
    #     file.write(f"[1,2](2, 1) -> 0\n")
    #     for i in range(2, n+1):
    #         file.write(f"[{i},3]({2*i - 1}, {2*i - 1}) -> {2*i - 3}\n")
    #         file.write(f"[{i},1]({2*i - 1}, {2*i    }) -> {2*i - 2}\n")
    #         file.write(f"[{i},2]({2*i    }, {2*i - 1}) -> {2*i - 2}\n")
    #     for i in range(n+1, q+1):
    #         file.write(f"[{i},1]({2*i - 1}, {2*i - 1}) -> {2*i - 3}\n")
    #         file.write(f"[{i},1]({2*i    }, {2*i - 1}) -> {2*i - 2}\n")
    #     file.write(f"[c0,1] -> {2*q-1}\n")
    #     file.write(f"[c1,1] -> {2*q}\n")
    ###########################################################################
    with open(n_str + '/circuit.qasm', 'w') as file:
        s = range(n) # [0] + list(range(2, 3*n-3, 3)) # 0, 2, 5, 8, ..., 3n-4
        w = [n + i for i in range(n)] # [1] + list(range(3, 3*n-2, 3)) # 1, 3, 6, 9, ..., 3n-3
        a = ['nan'] + [2*n + i for i in range(n-2)] # list(range(4, 3*n-4, 3)) # 4, 7, 10, ..., 3n-5
        t = 3*n - 2 # w[-1] + 1 # 3n-2
        ###########################################################
        file.write('OPENQASM 2.0;\n')
        file.write('include "qelib1.inc";\n')
        file.write(f'qreg qubits[{q}];\n')
        file.write(f'x qubits[{t}];\n\n')
        for i in s:
            file.write(f'x qubits[{i}];\n')
        for i in w:
            file.write(f'h qubits[{i}];\n')
        file.write(f'h qubits[{t}];\n\n')
        for _ in range(math.floor(math.pi / (4 * math.asin(1 / pow(2, n/2))))):
            for i in range(0, n):
                file.write(f'cx qubits[{s[i]}], qubits[{w[i]}];\n')
            myList = [f'ccx qubits[{w[0]}], qubits[{w[1]}], qubits[{a[1]}];\n']
            for i in range(2, n-1): # 2 <= i <= n-2
                myList.append(f'ccx qubits[{a[i-1]}], qubits[{w[i]}], qubits[{a[i]}];\n')
            for line in myList:
                file.write(line)
            file.write(f'cz qubits[{a[n-2]}], qubits[{w[n-1]}];\n')
            for line in reversed(myList):
                file.write(line)
            for i in range(0, n):
                file.write(f'cx qubits[{s[i]}], qubits[{w[i]}];\n')
            ###################################
            for i in range(n):
                file.write(f'h qubits[{w[i]}];\n')
            for i in range(n):
                file.write(f'x qubits[{w[i]}];\n')
            for line in myList:
                file.write(line)
            file.write(f'cz qubits[{a[n-2]}], qubits[{w[n-1]}];\n')
            for line in reversed(myList):
                file.write(line)
            for i in range(n):
                file.write(f'x qubits[{w[i]}];\n')
            for i in range(n):
                file.write(f'h qubits[{w[i]}];\n')
            file.write(f'x qubits[{t}];\n\n')
        for i in s:
            file.write(f'x qubits[{i}];\n')
        file.write(f'h qubits[{t}];\n')
    ###########################################################################
    if n <= 2: continue
    ###########################################################################
    # with open(n_str + '/post.lsta', 'w') as file:
    #     file.write('Constants\n')
    #     file.write(f'aH := {aH[n]}\n')
    #     file.write(f'aL := {aL[n]}\n')
    #     file.write('c0 := 0\n')
    #     file.write('Root States 0\n')
    #     file.write('Transitions\n')
    #     file.write('[1,1](2, 1) -> 0\n')
    #     file.write('[2,1](3, 3) -> 1\n')
    #     file.write('[2,1](3, 4) -> 2\n')
    #     file.write('[3,1](6, 5) -> 3\n')
    #     file.write('[3,1](7, 5) -> 4\n')
    #     for i in range(4, 2*n-1, 2): # maximum 2n-2
    #         file.write(f'[{i  },1]({3*(i-4)+ 8}, {3*(i-4)+ 8}) -> {3*(i-4)+ 5}\n')
    #         file.write(f'[{i  },1]({3*(i-4)+ 9}, {3*(i-4)+ 9}) -> {3*(i-4)+ 6}\n')
    #         if (i // 2) % 2:
    #             file.write(f'[{i},1]({3*(i-4)+9}, {3*(i-4)+10}) -> {3*(i-4)+ 7}\n')
    #         else:
    #             file.write(f'[{i},1]({3*(i-4)+10}, {3*(i-4)+9}) -> {3*(i-4)+ 7}\n')
    #         file.write(f'[{i+1},1]({3*(i-4)+11}, {3*(i-4)+11}) -> {3*(i-4)+ 8}\n')
    #         file.write(f'[{i+1},1]({3*(i-4)+12}, {3*(i-4)+11}) -> {3*(i-4)+ 9}\n')
    #         file.write(f'[{i+1},1]({3*(i-4)+13}, {3*(i-4)+11}) -> {3*(i-4)+10}\n')
    #     file.write(f'[{2*n-1+1},1]({3*(2*n-1-4)+11}, {3*(2*n-1-4)+11}) -> {3*(2*n-1-4)+ 8}\n')
    #     file.write(f'[{2*n-1+1},1]({3*(2*n-1-4)+11}, {3*(2*n-1-4)+12}) -> {3*(2*n-1-4)+ 9}\n')
    #     file.write(f'[{2*n-1+1},1]({3*(2*n-1-4)+11}, {3*(2*n-1-4)+13}) -> {3*(2*n-1-4)+10}\n')
    #     file.write(f'[c0,1] -> {3*(2*n-1-4)+11}\n')
    #     file.write(f'[aL,1] -> {3*(2*n-1-4)+12}\n')
    #     file.write(f'[aH,1] -> {3*(2*n-1-4)+13}')
    ###########################################################################
    with open(n_str + '/post.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write('{' + f'pH |ss{"0" * (n-2)}1> + pL ∑ |i|={n}, i≠s |si{"0" * (n-2)}1>' + ' : |s|=' + str(n) + '}\n')
        file.write('Constraints\n')
        file.write('real(pL) * real(pL) < 1/8\n')
        file.write('imag(pL) = 0\n')
        file.write('real(pH) * real(pH) > 7/8\n')
        file.write('imag(pH) = 0\n')
    ###########################################################################
    with open(n_str + '/post.hslsym', 'w') as file:
        file.write(f'|i|={n} i:1,0,0,0,0 *:0,0,0,0,0 # i:pH *:pL # {"0" * (n-2)}1:1,0,0,0,0 *:0,0,0,0,0\n')
        file.write('Constraints\n')
        file.write('real(pL) * real(pL) < 1/8\n')
        file.write('imag(pL) = 0\n')
        file.write('real(pH) * real(pH) > 7/8\n')
        file.write('imag(pH) = 0\n')
    ###########################################################################
    # [(and (< (* $a $a) 0.1) (= $b 0) (= $c 0) (= $d 0))] -> 2470
    # [(and (= $a 0) (= $b 0) (= $c 0) (= $d 0))] -> 2469
    # [(and (> (* $a $a) 0.9) (= $b 0) (= $c 0) (= $d 0))] -> 2471

# cp -rl 0{3,8,9} ../../CAV23/MOGroverSym/