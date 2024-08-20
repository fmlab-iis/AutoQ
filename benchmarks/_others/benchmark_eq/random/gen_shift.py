#!/usr/bin/python3


import os
import random
import re

# Create the "./shift" folder if it doesn't exist
output_folder = "./shift"
os.makedirs(output_folder) #, exist_ok=True)

# Get a list of all *.qasm files in the "./origin" folder
origin_folder = "./origin"
qasm_files = [filename for filename in os.listdir(origin_folder) if filename.endswith(".qasm")]

# Regular expression pattern to match Rx and Rz gates
# rx(pi/2) qubits[0];
gate_pattern = re.compile(r"(rx|rz)\((.+)\)(.+)\[(\d+)\] *;")

for qasm_file in qasm_files:
    # Read the original file
    with open(os.path.join(origin_folder, qasm_file), "r") as f:
        lines = f.readlines()

    # Find all quantum gates
    quantum_gates = [line for line in lines if (r'//' not in line) and gate_pattern.findall(line)]

    if quantum_gates:
        # Randomly swap one CX gate
        random_gate_index = random.randint(0, len(quantum_gates) - 1)
        input_string = quantum_gates[random_gate_index]
        match = gate_pattern.search(input_string)
        assert(match)
        gate, angle, var, qubit = match.groups()
        angle = eval(angle.replace("pi", "1")) + random.choice((-0.5, 0.5))
        lines[lines.index(input_string)] = f"{gate}({angle} * pi){var}[{qubit}];\n"

        # Write the modified content to the new file in "./shift" folder
        output_file = os.path.join(output_folder, qasm_file)
        with open(output_file, "w") as f:
            f.writelines(lines)

        print(f"Processed {qasm_file} and saved modified content to {output_file}")
    else:
        print(f"No quantum gates found in {qasm_file}. Skipping.")

print("All files processed successfully!")
