# Feynman -- quantum circuit toolkit
# Original (gf2^5_mult.qc):
#   Qubits: 15
#   H: 18
#   T: 175
#   cnot: 154
#   Depth: 111
#   T depth: 54
# Result (4.999ms):
#   Qubits: 15
#   H: 18
#   T: 175
#   cnot: 154
#   Depth: 111
#   T depth: 54
.v a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
.i a0 a1 a2 a3 a4 b0 b1 b2 b3 b4
.o a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 c0 c1 c2 c3 c4
BEGIN 
H c0
H c1
H c2
H c3
Z a4 b1 c0
Z a3 b2 c0
Zd a2 b3 c0
Zd a1 b4 c0
Z a4 b2 c1
Zd a3 b3 c1
Z a2 b4 c1
Z a4 b3 c2
Zd a3 b4 c2
Zd a4 b4 c3
H c0
H c1
H c2
H c3
tof c3 c0
tof c2 c4
tof c1 c3
tof c0 c2
H c0
H c1
H c2
H c3
H c4
Z a4 b0 c4
Z a3 b1 c4
Zd a2 b2 c4
Z a1 b3 c4
Z a0 b4 c4
Z a3 b0 c3
Z a2 b1 c3
Zd a1 b2 c3
Zd a0 b3 c3
Z a2 b0 c2
Zd a1 b1 c2
Z a0 b2 c2
Z a1 b0 c1
Zd a0 b1 c1
Z a0 b0 c0
H c0
H c1
H c2
H c3
H c4
END
