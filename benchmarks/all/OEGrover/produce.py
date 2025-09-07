#!/usr/bin/python3
import sys
import os

sizes = []
if len(sys.argv) == 2:
    n = int(sys.argv[1])
    assert(n >= 3)
    sizes.append(n)
else:
    sizes = list(range(3, 101))

for n in sizes:
    n_str = str(n).zfill(2)
    if not os.path.exists(n_str):
        os.makedirs(n_str)
    ###########################################################################
    with open(n_str + '/pre.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write('{' + f'b |{"01" * (n//2) + "0" * (n % 2)}{"0" * (n-2)}1> + a ∑ |i|={n}, i≠{"01" * (n//2) + "0" * (n % 2)} |i{"0" * (n-2)}1>' + '}\n')
        # file.write('where\n')
        # file.write('b ⊗ b = b\n')
        # file.write('b ⊗ a = a\n')
        # file.write('a ⊗ b = a\n')
        # file.write('a ⊗ a = a\n')
        file.write('Constraints\n')
        file.write(f'{2 ** n - 1} * real(a) > real(b)\n')
        file.write('real(a) > 0\n')
        file.write('real(b) > 0\n')
        file.write('imag(a) = 0\n')
        file.write('imag(b) = 0\n')
    ###########################################################################
    # with open(n_str + '/pre.lsta', 'w') as file:
    #     file.write('Constants\n')
    #     file.write('c0 := 0\n')
    #     file.write('Root States 0\n')
    #     file.write('Transitions\n')
    #     file.write('[1,1](2, 1) -> 0\n')
    #     for i in range(2, n+1): # 2 <= i <= n
    #         file.write(f'[{i},1]({2*i-1}, {2*i-1}) -> {2*i-3}\n')
    #         if i % 2:
    #             file.write(f'[{i},1]({2*i}, {2*i-1}) -> {2*i-2}\n')
    #         else:
    #             file.write(f'[{i},1]({2*i-1}, {2*i}) -> {2*i-2}\n')
    #     file.write(f'[{n+1},1]({2*(n+1)-1}, {2*(n+1)}) -> {2*(n+1)-3}\n')
    #     file.write(f'[{n+1},1]({2*(n+1)-1}, {2*(n+1)+1}) -> {2*(n+1)-2}\n')
    #     for i in range(n+2, 2*n+1): # n+2 <= i <= 2n
    #         file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)  }, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)-1}\n')
    #         file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)+1}, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)  }\n')
    #         file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)+2}, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)+1}\n')
    #     file.write(f'[c0,1] -> {2*(n+2)+3*(i-n-2)}\n')
    #     file.write(f'[a,1] -> {2*(n+2)+3*(i-n-2)+1}\n')
    #     file.write(f'[b,1] -> {2*(n+2)+3*(i-n-2)+2}\n')
    #     file.write('Constraints\n')
    #     file.write(f'{2 ** n - 1} * real(a) > real(b)\n')
    #     file.write('real(a) > 0\n')
    #     file.write('real(b) > 0\n')
    #     file.write('imag(a) = 0\n')
    #     file.write('imag(b) = 0\n')
    ###########################################################################
    with open(n_str + '/circuit.qasm', 'w') as file:
        w = range(n) # [0] + list(range(1, 2*n-2, 2)) # 0, 1, 3, 5, ..., 2n-3
        a = ['nan'] + [i + len(w) for i in range(n-2)] # list(range(2, 2*n-3, 2)) # 2, 4, 6, ..., 2n-4
        t = 2*n - 2 # w[-1] + 1 # 2n-2
        ###########################################################
        file.write('OPENQASM 2.0;\n')
        file.write('include "qelib1.inc";\n')
        file.write(f'qreg qubits[{2 * n - 1}];\n\n')
        for i in range(0, n, 2):
            file.write(f'x qubits[{w[i]}];\n')
        myList = [f'ccx qubits[{w[0]}], qubits[{w[1]}], qubits[{a[1]}];\n']
        for i in range(2, n-1): # 2 <= i <= n-2
            myList.append(f'ccx qubits[{a[i-1]}], qubits[{w[i]}], qubits[{a[i]}];\n')
        for line in myList:
            file.write(line)
        file.write(f'cz qubits[{a[n-2]}], qubits[{w[n-1]}];\n')
        for line in reversed(myList):
            file.write(line)
        for i in range(0, n, 2):
            file.write(f'x qubits[{w[i]}];\n')
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
        file.write(f'z qubits[{t}];\n')
    ###########################################################################
    # with open(n_str + '/post.lsta', 'w') as file:
    #     file.write('Predicates\n')
    #     file.write('p1 := (and (= real($) 0) (= imag($) 0))\n')
    #     file.write('p2 := (and (< (* real($) real($)) (* real(a) real(a))) (= imag($) 0))\n')
    #     file.write('p3 := (and (> (* real($) real($)) (* real(b) real(b))) (= imag($) 0))\n')
    #     file.write('Root States 0\n')
    #     file.write('Transitions\n')
    #     file.write('[1,1](2, 1) -> 0\n')
    #     for i in range(2, n+1): # 2 <= i <= n
    #         file.write(f'[{i},1]({2*i-1}, {2*i-1}) -> {2*i-3}\n')
    #         if i % 2:
    #             file.write(f'[{i},1]({2*i}, {2*i-1}) -> {2*i-2}\n')
    #         else:
    #             file.write(f'[{i},1]({2*i-1}, {2*i}) -> {2*i-2}\n')
    #     file.write(f'[{n+1},1]({2*(n+1)-1}, {2*(n+1)}) -> {2*(n+1)-3}\n')
    #     file.write(f'[{n+1},1]({2*(n+1)-1}, {2*(n+1)+1}) -> {2*(n+1)-2}\n')
    #     for i in range(n+2, 2*n+1): # n+2 <= i <= 2n
    #         file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)  }, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)-1}\n')
    #         file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)+1}, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)  }\n')
    #         file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)+2}, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)+1}\n')
    #     file.write(f'[p1,1] -> {2*(n+2)+3*(i-n-2)}\n')
    #     file.write(f'[p2,1] -> {2*(n+2)+3*(i-n-2)+1}\n')
    #     file.write(f'[p3,1] -> {2*(n+2)+3*(i-n-2)+2}')
    ###########################################################################
    with open(n_str + '/post.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write('{' + f'pH |{"01" * (n//2) + "0" * (n % 2)}{"0" * (n-2)}1> + pL ∑ |i|={n}, i≠{"01" * (n//2) + "0" * (n % 2)} |i{"0" * (n-2)}1>' + '}\n')
        file.write('Constraints\n')
        file.write('real(pL) * real(pL) < real(a) * real(a)\n')
        file.write('imag(pL) = 0\n')
        file.write('real(pH) * real(pH) > real(b) * real(b)\n')
        file.write('imag(pH) = 0\n')
        # file.write('where\n')
        # file.write('pH ⊗ pH = pH\n')
        # file.write('pH ⊗ pL = pL\n')
        # file.write('pL ⊗ pH = pL\n')
        # file.write('pL ⊗ pL = pL\n')
    ###########################################################################

# cp -rl {02,18,50,75,100} ../../POPL25/OEGrover/
# cp -rl {02,18,50,75,100} ../../CAV23/OEGrover/