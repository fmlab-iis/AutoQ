#!/bin/bash

rm circuit.qasm
for i in {1..100..1}; do
    echo 'OPENQASM 2.0;' >> 'circuit.qasm'
    echo 'include "qelib1.inc";' >> 'circuit.qasm'
    echo -e "qreg qubits[$((1+i))];\n" >> 'circuit.qasm'
    ../build/cli/vata 1 $i
    mv circuit.qasm Bernstein_Vazirani_$(printf %03d $i).qasm
done


