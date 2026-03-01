#!/usr/bin/python3
import sys
import os
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from common import ensure_bench_dir_for_n, write_qasm_header, write_hsl, parse_sizes

sizes = parse_sizes(3, 101, min_n=3)

for n in sizes:
    n_str = ensure_bench_dir_for_n(n)
    ###########################################################################
    pre_body = ('{' + f'b |{"01" * (n//2) + "0" * (n % 2)}{"0" * (n-2)}1> + a ∑ |i|={n}, i≠{"01" * (n//2) + "0" * (n % 2)} |i{"0" * (n-2)}1>' + '}\n'
                'Constraints\n'
                f'{2 ** n - 1} * real(a) > real(b)\n'
                'real(a) > 0\n'
                'real(b) > 0\n'
                'imag(a) = 0\n'
                'imag(b) = 0\n')
    write_hsl(n_str + '/pre.hsl', pre_body, header='Extended Dirac\n')
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
        write_qasm_header(file)
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
    post_body = ('{' + f'pH |{"01" * (n//2) + "0" * (n % 2)}{"0" * (n-2)}1> + pL ∑ |i|={n}, i≠{"01" * (n//2) + "0" * (n % 2)} |i{"0" * (n-2)}1>' + '}\n'
                 'Constraints\n'
                 'real(pL) * real(pL) < real(a) * real(a)\n'
                 'imag(pL) = 0\n'
                 'real(pH) * real(pH) > real(b) * real(b)\n'
                 'imag(pH) = 0\n')
    write_hsl(n_str + '/post.hsl', post_body, header='Extended Dirac\n')
    ###########################################################################

# cp -rl {02,18,50,75,100} ../../POPL25/OEGrover/
# cp -rl {02,18,50,75,100} ../../CAV23/OEGrover/