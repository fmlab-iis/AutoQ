OPENQASM 3;
include "stdgates.inc";
qubit[2] qb;
bit[1] c;

x qb[1];
c[0] = measure qb[0];
while (c[0]) { // entry_inv.hsl
    x qb[0];
    c[0] = measure qb[0];
}
