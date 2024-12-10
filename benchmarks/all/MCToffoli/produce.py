#!/usr/bin/python3
from typing import Optional, Any
import sys
import os
import shutil

context = """Constants
c0 := 0
c1 := 1
Root States 0
Transitions
"""

def tr(top: int, bot: list[int], sym: Any, color: set[int]) -> str:
    tag = sum(1 << (c-1) for c in color)
    bott = ",".join(map(str, bot))
    if bott:
        bott = f"({bott})"

    return f"[{sym},{tag}]{bott} -> {top}"


def gen_toff_prelsta(n: int, last_is_one: bool = True):
    def q(lv: int, x: Optional[str] = None) -> int:
        ind = -1
        if x is None:
            ind = 2*lv
        elif x == "0":
            ind = 2*lv - 1
        return ind

    trans: list[str] = [
        # level 1
        tr(q(0), [q(1, "0"), q(1)], 1, {1}),
        tr(q(0), [q(1), q(1, "0")], 1, {2}),
    ]
    last_bot = [q(2*n, "0"), q(2*n)] if last_is_one else [q(2*n), q(2*n, "0")]

    # level 2 to 2n-1
    for i in range(2, 2*n, 2):
        trans.extend([
            # level i
            tr(q(i-1), [q(i), q(i, "0")], i, {1}),
            tr(q(i-1), [q(i, "0"), q(i)], i, {2}),
            tr(q(i-1, "0"), [q(i, "0"), q(i, "0")], i, {1, 2}),
            # level i+1
            tr(q(i), [q(i+1), q(i+1, "0")], i+1, {1}),
            tr(q(i, "0"), [q(i+1, "0"), q(i+1, "0")], i+1, {1}),
        ])
    trans.extend([
        # level 2n
        tr(q(2*n-1), last_bot, 2*n, {1}),
        tr(q(2*n-1, "0"), [q(2*n, "0"), q(2*n, "0")], 2*n, {1}),
        # leafs
        tr(q(2*n), [], "c1", {1}),
        tr(q(2*n, "0"), [], "c0", {1}),
    ])

    return context + "\n".join(trans)


def gen_toff_postlsta(n: int, last_is_one: bool) -> str:
    def q(lv: int, x: Optional[str] = None) -> int:
        if x == "T":  # even or none
            ind = 3*lv
        elif (x == "F") or (x is None):  # odd or last
            ind = 3*lv - 1
        else:  # zero
            ind = 3*lv - 2
        return ind
    trans: list[str] = [
        # level 1
        tr(q(0, "T"), [q(1, "F"), q(1, "0")], 1, {1}),
        tr(q(0, "T"), [q(1, "0"), q(1, "T")], 1, {2}),
    ]
    # level 2 to 2n-1
    for i in range(2, 2*n, 2):
        trans.extend([
            # level i
            tr(q(i-1, "T"), [q(i, "F"), q(i, "0")], i, {1}),
            tr(q(i-1, "T"), [q(i, "0"), q(i, "T")], i, {2}),
            tr(q(i-1, "F"), [q(i, "F"), q(i, "0")], i, {1}),
            tr(q(i-1, "F"), [q(i, "0"), q(i, "F")], i, {2}),
            tr(q(i-1, "0"), [q(i, "0"), q(i, "0")], i, {1, 2}),
            # level i+1
            tr(q(i, "T"), [q(i+1, "T"), q(i+1, "0")], i+1, {1}),
            tr(q(i, "F"), [q(i+1, "F"), q(i+1, "0")], i+1, {1}),
            tr(q(i, "0"), [q(i+1, "0"), q(i+1, "0")], i+1, {1}),
        ])
    last_bot = [q(2*n, "0"), q(2*n)] if last_is_one else [q(2*n), q(2*n, "0")]
    trans.extend([
        # level 2n
        tr(q(2*n-1, "T"), last_bot[::-1], 2*n, {1}),
        tr(q(2*n-1, "F"), last_bot, 2*n, {1}),
        tr(q(2*n-1, "0"), [q(2*n, "0"), q(2*n, "0")], 2*n, {1}),
        # leafs
        tr(q(2*n), [], "c1", {1}),
        tr(q(2*n, "0"), [], "c0", {1}),
    ])

    return context + "\n".join(trans)

sizes = []
if len(sys.argv) == 2:
    n = int(sys.argv[1])
    assert(n >= 3)
    sizes.append(n)
else:
    sizes = list(range(3, 1001))

for n in sizes:
    n_str = str(n).zfill(2)
    if not os.path.exists(n_str):
        os.makedirs(n_str)
    #########################################
    with open(n_str + "/circuit.qasm", "w") as file:
        file.write("OPENQASM 2.0;\n")
        file.write('include "qelib1.inc";\n')
        file.write(f'qreg qubits[{2*n}];\n\n')
        file.write('ccx qubits[0], qubits[1], qubits[2];\n')
        for i in range(4, 2*n, 2):
            file.write(f'ccx qubits[{i-1}], qubits[{i-2}], qubits[{i}];\n')
        file.write(f'cx qubits[{2*n-2}], qubits[{2*n-1}];\n')
        for i in range(2*n-2, 2, -2):
            file.write(f'ccx qubits[{i-1}], qubits[{i-2}], qubits[{i}];\n')
        file.write('ccx qubits[0], qubits[1], qubits[2];\n')
    #########################################
    with open(n_str + '/pre.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write("{|i> | |i|=2}" + ' ⊗ {|0i> | |i|=1} ^ ' + f'{n-1}\n')
    shutil.copy(n_str + '/pre.hsl', n_str + '/post.hsl')
    #########################################
    with open(n_str + "/pre.lsta", "w") as file:
        file.write('Constants\n')
        file.write('c0 := 0\n')
        file.write('c1 := 1\n')
        file.write('Root States 0\n')
        file.write('Transitions\n')
        file.write(f"[1,1](1, 2) -> 0\n")
        file.write(f"[1,2](2, 1) -> 0\n")
        file.write(f"[2,3](3, 3) -> 1\n")
        file.write(f"[2,1](3, 4) -> 2\n")
        file.write(f"[2,2](4, 3) -> 2\n")
        for i in range(n-1):
            file.write(f"[{2*i+3},1]({4*i + 5}, {4*i + 5}) -> {4*i + 3}\n")
            file.write(f"[{2*i+3},1]({4*i + 6}, {4*i + 5}) -> {4*i + 4}\n")
            file.write(f"[{2*i+4},3]({4*i + 7}, {4*i + 7}) -> {4*i + 5}\n")
            file.write(f"[{2*i+4},1]({4*i + 7}, {4*i + 8}) -> {4*i + 6}\n")
            file.write(f"[{2*i+4},2]({4*i + 8}, {4*i + 7}) -> {4*i + 6}\n")
        file.write(f"[c0,1] -> {4*(n-2) + 7}\n")
        file.write(f"[c1,1] -> {4*(n-2) + 8}\n")
    shutil.copy(n_str + '/pre.lsta', n_str + '/post.lsta')
    #########################################
    with open(n_str + '/pre0.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write("{|i> | |i|=2}" + ' ⊗ {|0i> | |i|=1} ^ ' + f'{n-2}' + ' ⊗ {|00>}\n')
    #########################################
    with open(n_str + "/pre0.lsta", "w") as file:
        file.write('Constants\n')
        file.write('c0 := 0\n')
        file.write('c1 := 1\n')
        file.write('Root States 0\n')
        file.write('Transitions\n')
        file.write(f"[1,1](1, 2) -> 0\n")
        file.write(f"[1,2](2, 1) -> 0\n")
        file.write(f"[2,3](3, 3) -> 1\n")
        file.write(f"[2,1](3, 4) -> 2\n")
        file.write(f"[2,2](4, 3) -> 2\n")
        for i in range(n-1):
            file.write(f"[{2*i+3},1]({4*i + 5}, {4*i + 5}) -> {4*i + 3}\n")
            file.write(f"[{2*i+3},1]({4*i + 6}, {4*i + 5}) -> {4*i + 4}\n")
            file.write(f"[{2*i+4},3]({4*i + 7}, {4*i + 7}) -> {4*i + 5}\n")
            file.write(f"[{2*i+4},1]({4*i + 8}, {4*i + 7}) -> {4*i + 6}\n")
            if i < n-2:
                file.write(f"[{2*i+4},2]({4*i + 7}, {4*i + 8}) -> {4*i + 6}\n")
        file.write(f"[c0,1] -> {4*(n-2) + 7}\n")
        file.write(f"[c1,1] -> {4*(n-2) + 8}\n")
    #########################################
    with open(n_str + '/pre1.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write("{|i> | |i|=2}" + ' ⊗ {|0i> | |i|=1} ^ ' + f'{n-2}' + ' ⊗ {|01>}\n')
    #########################################
    with open(n_str + "/pre1.lsta", "w") as file:
        file.write('Constants\n')
        file.write('c0 := 0\n')
        file.write('c1 := 1\n')
        file.write('Root States 0\n')
        file.write('Transitions\n')
        file.write(f"[1,1](1, 2) -> 0\n")
        file.write(f"[1,2](2, 1) -> 0\n")
        file.write(f"[2,3](3, 3) -> 1\n")
        file.write(f"[2,1](3, 4) -> 2\n")
        file.write(f"[2,2](4, 3) -> 2\n")
        for i in range(n-1):
            file.write(f"[{2*i+3},1]({4*i + 5}, {4*i + 5}) -> {4*i + 3}\n")
            file.write(f"[{2*i+3},1]({4*i + 6}, {4*i + 5}) -> {4*i + 4}\n")
            file.write(f"[{2*i+4},3]({4*i + 7}, {4*i + 7}) -> {4*i + 5}\n")
            if i < n-2:
                file.write(f"[{2*i+4},1]({4*i + 8}, {4*i + 7}) -> {4*i + 6}\n")
            file.write(f"[{2*i+4},2]({4*i + 7}, {4*i + 8}) -> {4*i + 6}\n")
        file.write(f"[c0,1] -> {4*(n-2) + 7}\n")
        file.write(f"[c1,1] -> {4*(n-2) + 8}\n")
    #########################################
    with open(n_str + '/post0.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write("{|i> | |i|=2}" + ' ⊗ {|0i> | |i|=1} ^ ' + f'{n-2}' + ' ⊗ {|00>}\n')
        file.write('U {|1' + '10' * (n-1) + '1>}\n')
        file.write('\ {|1' + '10' * (n-1) + '0>}\n')
    #########################################
    with open(n_str + "/post0.lsta", "w") as file:
        print(gen_toff_postlsta(n, False), file=file)
    #########################################
    with open(n_str + '/post1.hsl', 'w') as file:
        file.write('Extended Dirac\n')
        file.write("{|i> | |i|=2}" + ' ⊗ {|0i> | |i|=1} ^ ' + f'{n-2}' + ' ⊗ {|01>}\n')
        file.write('U {|1' + '10' * (n-1) + '0>}\n')
        file.write('\ {|1' + '10' * (n-1) + '1>}\n')
    #########################################
    with open(n_str + "/post1.lsta", "w") as file:
        print(gen_toff_postlsta(n, True), file=file)
    #########################################

# cp -rl {08,10,12,14,16} ../../LSTA/MCToffoli/
# cp -rl {08,10,12,14,16} ../../PLDI23/MCToffoli/