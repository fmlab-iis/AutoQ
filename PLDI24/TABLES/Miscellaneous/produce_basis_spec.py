#!/usr/bin/python3
import re, os

for root, dirnames, filenames in sorted(os.walk('.')):
    if not (len(dirnames) == 0 and 'circuit.qasm' in filenames): continue
    print(root)
    # Define the pattern to match "qreg qubits[...];"
    pattern = r'qreg qubits\[(\d+)\];'
    # Open the file for reading
    with open(root + '/circuit.qasm', 'r') as file:
        for line in file:
            match = re.search(pattern, line)
            if match:
                # Extract the number within the square brackets
                n = int(match.group(1))
                print(f'Found qubits: {n}')
                break  # Stop after the first match

    #########################################
    with open(root + '/pre.spec', "w") as file:
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