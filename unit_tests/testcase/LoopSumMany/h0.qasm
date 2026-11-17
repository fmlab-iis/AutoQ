OPENQASM 3;
include "stdgates.inc";
qubit[2] q;

for int i in [1:1] {
    h q[0];
}
