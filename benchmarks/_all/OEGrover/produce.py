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
        file.write(f"b |{'01' * (n//2) + '0' * (n%2)}> + a |*> # |1{'0' * (n-1)}>\n")
        file.write('Constraints\n')
        file.write(f'{2 ** n - 1} * real(a) > real(b)\n')
        file.write('real(a) > 0\n')
        file.write('real(b) > 0\n')
        file.write('imag(a) = 0\n')
        file.write('imag(b) = 0\n')
    ###########################################################################
    with open(n_str + '/pre.spec', 'w') as file:
        file.write('Constants\n')
        file.write('c0 := 0\n')
        file.write('Root States 0\n')
        file.write('Colored Transitions\n')
        file.write('[1,1](2, 1) -> 0\n')
        for i in range(2, n+1): # 2 <= i <= n
            file.write(f'[{i},1]({2*i-1}, {2*i-1}) -> {2*i-3}\n')
            if i % 2:
                file.write(f'[{i},1]({2*i}, {2*i-1}) -> {2*i-2}\n')
            else:
                file.write(f'[{i},1]({2*i-1}, {2*i}) -> {2*i-2}\n')
        file.write(f'[{n+1},1]({2*(n+1)-1}, {2*(n+1)}) -> {2*(n+1)-3}\n')
        file.write(f'[{n+1},1]({2*(n+1)-1}, {2*(n+1)+1}) -> {2*(n+1)-2}\n')
        for i in range(n+2, 2*n+1): # n+2 <= i <= 2n
            file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)  }, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)-1}\n')
            file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)+1}, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)  }\n')
            file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)+2}, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)+1}\n')
        file.write(f'[c0,1] -> {2*(n+2)+3*(i-n-2)}\n')
        file.write(f'[a,1] -> {2*(n+2)+3*(i-n-2)+1}\n')
        file.write(f'[b,1] -> {2*(n+2)+3*(i-n-2)+2}\n')
        file.write('Constraints\n')
        file.write(f'{2 ** n - 1} * real(a) > real(b)\n')
        file.write('real(a) > 0\n')
        file.write('real(b) > 0\n')
        file.write('imag(a) = 0\n')
        file.write('imag(b) = 0\n')
    ###########################################################################
    with open(n_str + '/circuit.qasm', 'w') as file:
        file.write('OPENQASM 2.0;\n')
        file.write('include "qelib1.inc";\n')
        file.write(f'qreg qubits[{2 * n}];\n\n')
        for i in range(0, n, 2):
            file.write(f'x qubits[{i}];\n')
        file.write(f'ccx qubits[{0}], qubits[{1}], qubits[{n+1}];\n')
        for i in range(2, n-1): # 2 <= i <= n-2
            file.write(f'ccx qubits[{i}], qubits[{i+(n-1)}], qubits[{i+n}];\n')
        file.write(f'cz qubits[{2*(n-1)}], qubits[{n-1}];\n')
        for i in range(n-2, 1, -1): # n-2 >= i >= 2
            file.write(f'ccx qubits[{i}], qubits[{i+(n-1)}], qubits[{i+n}];\n')
        file.write(f'ccx qubits[{0}], qubits[{1}], qubits[{n+1}];\n')
        for i in range(0, n, 2):
            file.write(f'x qubits[{i}];\n')
        for i in range(n):
            file.write(f'h qubits[{i}];\n')
        for i in range(n):
            file.write(f'x qubits[{i}];\n')
        file.write(f'ccx qubits[{0}], qubits[{1}], qubits[{n+1}];\n')
        for i in range(2, n-1): # 2 <= i <= n-2
            file.write(f'ccx qubits[{i}], qubits[{i+(n-1)}], qubits[{i+n}];\n')
        file.write(f'cz qubits[{2*(n-1)}], qubits[{n-1}];\n')
        for i in range(n-2, 1, -1): # n-2 >= i >= 2
            file.write(f'ccx qubits[{i}], qubits[{i+(n-1)}], qubits[{i+n}];\n')
        file.write(f'ccx qubits[{0}], qubits[{1}], qubits[{n+1}];\n')
        for i in range(n):
            file.write(f'x qubits[{i}];\n')
        for i in range(n):
            file.write(f'h qubits[{i}];\n')
        file.write(f'z qubits[{n}];\n')
    ###########################################################################
    with open(n_str + '/post.spec', 'w') as file:
        file.write('Predicates\n')
        file.write('p1 := (and (= real($) 0) (= imag($) 0))\n')
        file.write('p2 := (and (< (* real($) real($)) (* real(a) real(a))) (= imag($) 0))\n')
        file.write('p3 := (and (> (* real($) real($)) (* real(b) real(b))) (= imag($) 0))\n')
        file.write('Root States 0\n')
        file.write('Colored Transitions\n')
        file.write('[1,1](2, 1) -> 0\n')
        for i in range(2, n+1): # 2 <= i <= n
            file.write(f'[{i},1]({2*i-1}, {2*i-1}) -> {2*i-3}\n')
            if i % 2:
                file.write(f'[{i},1]({2*i}, {2*i-1}) -> {2*i-2}\n')
            else:
                file.write(f'[{i},1]({2*i-1}, {2*i}) -> {2*i-2}\n')
        file.write(f'[{n+1},1]({2*(n+1)-1}, {2*(n+1)}) -> {2*(n+1)-3}\n')
        file.write(f'[{n+1},1]({2*(n+1)-1}, {2*(n+1)+1}) -> {2*(n+1)-2}\n')
        for i in range(n+2, 2*n+1): # n+2 <= i <= 2n
            file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)  }, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)-1}\n')
            file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)+1}, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)  }\n')
            file.write(f'[{i},1]({2*(n+2)+3*(i-n-2)+2}, {2*(n+2)+3*(i-n-2)}) -> {2*(n+1)+3*(i-n-2)+1}\n')
        file.write(f'[p1,1] -> {2*(n+2)+3*(i-n-2)}\n')
        file.write(f'[p2,1] -> {2*(n+2)+3*(i-n-2)+1}\n')
        file.write(f'[p3,1] -> {2*(n+2)+3*(i-n-2)+2}')
    ###########################################################################
    with open(n_str + '/post.hsl', 'w') as file:
        file.write('Predicates\n')
        # file.write('p1 := (and (= real($) 0) (= imag($) 0))\n')
        # file.write('p2 := (and (< (* real($) real($)) (* real(a) real(a))) (= imag($) 0))\n')
        file.write('p := (and (> (* real($) real($)) (* real(b) real(b))) (= imag($) 0))\n')
        file.write('Extended Dirac\n')
        file.write(f"p |{'01' * (n//2) + '0' * (n%2)}1{'0' * (n-1)}>\n")
    ###########################################################################