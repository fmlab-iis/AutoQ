#!/bin/bash

rm circuit.qasm
for i in {3..17..1}; do
    echo 'OPENQASM 2.0;' >> 'circuit.qasm'
    echo 'include "qelib1.inc";' >> 'circuit.qasm'
    echo -e "qreg qubits[$((2*i))];" >> 'circuit.qasm'
    echo -e "x qubits[$i];\n" >> 'circuit.qasm' # This line is used to initialize the target qubit to |1>.
    ../build/cli/vata 9 $i
    mv circuit.qasm Grover_$(printf %02d $i).qasm
done