OPENQASM 3;
include "stdgates.inc";
qubit[1] q;

for int i in [1:3] {
    h q[0];
    t q[0];
}
