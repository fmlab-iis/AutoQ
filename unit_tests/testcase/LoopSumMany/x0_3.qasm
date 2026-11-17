OPENQASM 3;
include "stdgates.inc";
qubit[3] q;

for int i in [1:1] {
    x q[0];
}
