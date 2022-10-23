.v q0 q1 q2 q3 q4 q5
BEGIN

H q1
H q0
S q0
H q0
Z q0 q1
S q4
Z q0 q5
tof q4 q2
X q5
H q5
X q5
H q5
X q3
H q3
tof q4 q2
tof q2 q1 q3
tof q4 q5 q3
S q1
tof q5 q3 q1
tof q4 q5 q3
tof q5 q4 q2
tof q3 q2 q5
tof q5 q0 q4

END
