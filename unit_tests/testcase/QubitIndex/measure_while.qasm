OPENQASM 3;
include "stdgates.inc";
qubit[1] qb;
bit[1] c;
c[0] = measure qb[1];
if (c[0]) {
    x qb[0];
}
c[0] = measure qb[0];
while (c[0]) { // inv.hsl
    c[0] = measure qb[0];
}
