#!/bin/bash

for i in {03..300}; do
    echo "automata/$i/pre.lsta;automata/$i/circuit.qasm" >> oegrover.input
done