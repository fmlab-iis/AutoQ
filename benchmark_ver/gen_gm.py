#!/usr/bin/python3
import os
import random
import re
# Regular expression pattern to match quantum gates
gate_pattern = re.compile(r"[a-z]+ +.*\[\d+\].*;")

for root, dirnames, filenames in os.walk('.'):
    if not (len(dirnames) == 0 and 'circuit.qasm' in filenames): continue

    # Read the original file
    input_file = os.path.join(root, 'circuit.qasm')
    with open(input_file, "r") as f:
        lines = f.readlines()

    # Find all quantum gates
    quantum_gates = [line for line in lines if (r'//' not in line) and (r'reg' not in line) and gate_pattern.findall(line)]

    if quantum_gates:
        # Randomly remove one quantum gate (due to Grover, we only consider the latter half of the circuit)
        random_gate_index = random.randint(len(quantum_gates) // 2, len(quantum_gates) - 1)
        del lines[lines.index(quantum_gates[random_gate_index])]

        # Write the modified content to the new file in "./gm" folder
        output_file = os.path.join(root, os.path.basename(__file__).split('.')[0].split('_')[1] + '.qasm')
        with open(output_file, "w") as f:
            f.writelines(lines)
        print(f"Processed {input_file} and saved modified content to {output_file}")
    else:
        print(f"No quantum gates found in {input_file}. Skipping.")

print("All files processed successfully!")
