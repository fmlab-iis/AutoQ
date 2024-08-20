# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Feynman/tof_3/circuit.qc):
#   Qubits: 5
#   H: 6
#   T: 21
#   cnot: 18
#   Depth: 23
#   T depth: 10
# Result (0.387ms):
#   Qubits: 5
#   H: 6
#   T: 21
#   cnot: 18
#   Depth: 23
#   T depth: 10
.v 1 2 3 4 5
.i 1 2 3 4
.o 1 2 3 4 5
BEGIN 
H 5
Z 1 2 5
H 5
H 4
Z 3 5 4
H 4
H 5
Zd 1 2 5
H 5
END
