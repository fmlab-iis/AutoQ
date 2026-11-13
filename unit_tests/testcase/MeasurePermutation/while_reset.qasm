OPENQASM 3;
include "stdgates.inc";
qubit[3] q;
bit r;
r = measure q[1];
while (r) { // inv.hsl
    x q[1];
    r = measure q[1];
}
