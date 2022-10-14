# Feynman -- quantum circuit toolkit
# Original (vbe_adder_3.qc):
#   Qubits: 10
#   H: 10
#   T: 70
#   cnot: 70
#   Depth: 70
#   T depth: 29
# Result (1.019ms):
#   Qubits: 10
#   H: 10
#   T: 70
#   cnot: 70
#   Depth: 70
#   T depth: 29
.v 0 1 2 3 4 5 6 7 8 9
.i 0 1 2 3 4 5 6 7 8 9
.o 0 1 2 3 4 5 6 7 8 9
BEGIN 
H 3
H 6
H 9
Z 1 2 3
tof 1 2
Zd 0 2 3
H 3
Z 4 5 6
tof 4 5
Zd 3 5 6
H 6
Z 7 8 9
tof 7 8
Zd 6 8 9
tof 6 8
H 9
H 6
Z 3 5 6
tof 4 5
Zd 4 5 6
tof 3 5
tof 4 5
H 6
H 3
Z 0 2 3
tof 1 2
Zd 1 2 3
tof 0 2
tof 1 2
H 3
END
