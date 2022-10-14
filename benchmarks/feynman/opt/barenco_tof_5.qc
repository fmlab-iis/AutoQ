# Feynman -- quantum circuit toolkit
# Original (barenco_tof_5.qc):
#   Qubits: 9
#   H: 14
#   T: 84
#   cnot: 72
#   Depth: 91
#   T depth: 37
# Result (1.481ms):
#   Qubits: 9
#   H: 14
#   T: 84
#   cnot: 72
#   Depth: 91
#   T depth: 37
.v 1 2 3 4 5 6 7 8 9
.i 1 2 3 4 5 6 7 8 9
.o 1 2 3 4 5 6 7 8 9
BEGIN 
H 9
Z 5 8 9
H 8
Z 4 7 8
H 7
Z 3 6 7
H 6
Z 1 2 6
H 6
Zd 3 6 7
H 7
Zd 4 7 8
H 8
Zd 5 8 9
H 9
H 8
Z 4 7 8
H 7
Z 3 6 7
H 6
Zd 1 2 6
H 6
Zd 3 6 7
H 7
Zd 4 7 8
H 8
END
