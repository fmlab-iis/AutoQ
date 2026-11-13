OPENQASM 3;
include "stdgates.inc";
qubit[3] q;
bit r;
r = measure q[2];
if (r) {
    x q[1];
}
