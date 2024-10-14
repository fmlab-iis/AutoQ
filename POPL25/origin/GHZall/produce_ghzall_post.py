#!/usr/bin/python3
import os

n = 128
folder = str(n).zfill(3)
# os.mkdir(folder)
os.chdir(folder)

#########################################
with open("post.spec", "w") as file:
    file.write(
'''Numbers
c0 := 0
c1 := 1 / V2
c2 := -1 / V2
''')
    # file.write("Ops " + ' '.join(f'[{i}]:2' for i in range(1, n+1)) + ' [0,0,0,0,0]:0 [1,0,0,0,0]:0\n')
    # file.write("Automaton Basis\n")
    # file.write(f"States {' '.join([str(i) for i in range(2*n + 1)])}\n")
    # file.write("Final States 0\n")
    file.write("Colored Transitions\n")
    file.write("[1,1](1, 2) -> 0\n")
    file.write("[2,1](4, 3) -> 1\n")
    file.write("[2,2](3, 4) -> 1\n")
    file.write("[2,1](3, 5) -> 2\n")
    file.write("[2,2](5, 3) -> 2\n")
    for L in range(3, n+1):
        file.write(f"[{L},3]({3*L-3}, {3*L-3}) -> {3*L-6}\n")
        file.write(f"[{L},1]({3*L-2}, {3*L-3}) -> {3*L-5}\n")
        file.write(f"[{L},2]({3*L-3}, {3*L-2}) -> {3*L-5}\n")
        file.write(f"[{L},1]({3*L-3}, {3*L-1}) -> {3*L-4}\n")
        file.write(f"[{L},2]({3*L-1}, {3*L-3}) -> {3*L-4}\n")
    file.write(f"[c0,3] -> {3*n-3}\n")
    file.write(f"[c1,3] -> {3*n-2}\n")
    file.write(f"[c1,1] -> {3*n-1}\n")
    file.write(f"[c2,2] -> {3*n-1}\n")
#########################################