# Feynman -- quantum circuit toolkit
# Original (barenco_tof_4.qc):
#   Qubits: 7
#   H: 10
#   T: 56
#   cnot: 48
#   Depth: 61
#   T depth: 25
# Result (0.968ms):
#   Qubits: 7
#   H: 10
#   T: 56
#   cnot: 48
#   Depth: 61
#   T depth: 25
.v 1 2 3 4 5 6 7
.i 1 2 3 4 5 6 7
.o 1 2 3 4 5 6 7
BEGIN 
H 7
Z 4 6 7
H 6
Z 3 5 6
H 5
Z 1 2 5
H 5
Zd 3 5 6
H 6
Zd 4 6 7
H 7
H 6
Z 3 5 6
H 5
Zd 1 2 5
H 5
Zd 3 5 6
H 6
END
