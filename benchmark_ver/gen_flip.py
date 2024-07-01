#!/usr/bin/python3
import os
import random
import re
# Regular expression pattern to match CX gates
# cx qubits[2], qubits[3];
gate_pattern = re.compile(r"cx +([^\[\]]*)\[(\d+)\]([^\[\]]+)\[(\d+)\] *;")

for root, dirnames, filenames in os.walk('.'):
    if not (len(dirnames) == 0 and 'circuit.qasm' in filenames): continue

    # Read the original file
    input_file = os.path.join(root, 'circuit.qasm')
    with open(input_file, "r") as f:
        lines = f.readlines()

    # Find all quantum gates
    quantum_gates = [line for line in lines if (r'//' not in line) and gate_pattern.findall(line)]

    if quantum_gates:
        # Randomly swap one CX gate
        random_gate_index = random.randint(0, len(quantum_gates) - 1)
        input_string = quantum_gates[random_gate_index]
        match = gate_pattern.search(input_string)
        assert(match)
        str1, num1, str2, num2 = match.groups()
        lines[lines.index(input_string)] = f"cx {str1}[{num2}]{str2}[{num1}];\n"

        # Write the modified content to the new file in "./flip" folder
        output_file = os.path.join(root, os.path.basename(__file__).split('.')[0].split('_')[1] + '.qasm')
        with open(output_file, "w") as f:
            f.writelines(lines)
        print(f"Processed {input_file} and saved modified content to {output_file}")
    else:
        print(f"No quantum gates found in {input_file}. Skipping.")

print("All files processed successfully!")
