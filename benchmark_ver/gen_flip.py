#!/usr/bin/python3
import os
import random
import re
# Regular expression pattern to match CX gates
# cx qubits[2], qubits[3];
gate_pattern = re.compile(r"cx +([^\[\]]*)\[(\d+)\]([^\[\]]+)\[(\d+)\] *;")

for root, dirnames, filenames in os.walk('./origin'):
    if not (len(dirnames) == 0 and 'circuit.qasm' in filenames): continue

    # Read the original file
    input_file = os.path.join(root, 'circuit.qasm')
    with open(input_file, "r") as f:
        lines = f.readlines()

    # Find all quantum gates
    quantum_gates = [line for line in lines if (r'//' not in line) and (r'reg' not in line) and gate_pattern.findall(line)]

    if quantum_gates:
        while True:
            # Randomly swap one CX gate
            random_gate_index = random.randint(0, len(lines) - 1)
            input_string = lines[random_gate_index]
            if (r'//' not in input_string) and (r'reg' not in input_string) and gate_pattern.findall(input_string):
                match = gate_pattern.search(input_string)
                assert(match)
                str1, num1, str2, num2 = match.groups()
                lines[random_gate_index] = f"cx {str1}[{num2}]{str2}[{num1}];\n"
                break

        # Write the modified content to the new file in "./flip" folder
        output_file = os.path.join(root, 'circuit.qasm')
        output_file = output_file.replace('origin', 'flip')
        with open(output_file, "w") as f:
            f.writelines(lines)
        print(f"Processed {input_file} and saved modified content to {output_file}")
    else:
        print(f"No quantum gates found in {input_file}. Skipping.")

print("All files processed successfully!")
