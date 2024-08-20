# Feynman -- quantum circuit toolkit
# Original (/home/alan23273850/libvata2/benchmarks/Feynman/mod5_4/circuit.qc):
#   Qubits: 5
#   H: 6
#   T: 28
#   X: 1
#   cnot: 28
#   Depth: 36
#   T depth: 13
# Result (0.568ms):
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
