# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Feynman/barenco_tof_3/circuit.qc):
#   Qubits: 5
#   H: 8
#   T: 28
#   cnot: 24
#   Depth: 31
#   T depth: 13
# Result (0.443ms):
#   Qubits: 5
#   H: 8
#   T: 28
#   cnot: 24
#   Depth: 31
#   T depth: 13
.v 1 2 3 4 5
.i 1 2 3 4 5
.o 1 2 3 4 5
BEGIN 
H 5
Z 3 4 5
H 5
H 4
Z 1 2 4
H 4
H 5
Zd 3 4 5
H 5
H 4
Zd 1 2 4
H 4
END
