#!/usr/bin/python3


import os
import random
import re

# Create the "./gm" folder if it doesn't exist
output_folder = "./gm"
os.makedirs(output_folder) #, exist_ok=True)

# Get a list of all *.qasm files in the "./origin" folder
origin_folder = "./origin"
qasm_files = [filename for filename in os.listdir(origin_folder) if filename.endswith(".qasm")]

# Regular expression pattern to match quantum gates
gate_pattern = re.compile(r"[a-z]+ +.*\[\d+\].*;")

for qasm_file in qasm_files:
    # Read the original file
    with open(os.path.join(origin_folder, qasm_file), "r") as f:
        lines = f.readlines()

    # Find all quantum gates
    quantum_gates = [line for line in lines if (r'//' not in line) and (r'reg' not in line) and gate_pattern.findall(line)]

    if quantum_gates:
        # Randomly remove one quantum gate
        random_gate_index = random.randint(0, len(quantum_gates) - 1)
        del lines[lines.index(quantum_gates[random_gate_index])]

        # Write the modified content to the new file in "./gm" folder
        output_file = os.path.join(output_folder, qasm_file)
        with open(output_file, "w") as f:
            f.writelines(lines)

        print(f"Processed {qasm_file} and saved modified content to {output_file}")
    else:
        print(f"No quantum gates found in {qasm_file}. Skipping.")

print("All files processed successfully!")
