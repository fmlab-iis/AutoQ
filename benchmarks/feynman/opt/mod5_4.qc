# Feynman -- quantum circuit toolkit
# Original (mod5_4.qc):
#   Qubits: 5
#   H: 6
#   T: 28
#   X: 1
#   cnot: 28
#   Depth: 36
#   T depth: 13
# Result (1.951ms):
#   Qubits: 5
#   H: 6
#   T: 28
#   X: 1
#   cnot: 28
#   Depth: 36
#   T depth: 13
.v b c d e a
.i b c d e
.o b c d e a
BEGIN 
X a
H a
Z b e a
Zd d e a
H a
tof e a
H a
Z c d a
H a
tof d a
H a
Zd b c a
H a
tof c a
tof b a
END
