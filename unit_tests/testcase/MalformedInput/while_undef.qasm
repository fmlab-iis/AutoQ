OPENQASM 3;
qubit[1] qb;
bit[1] c;
c[0] = measure qb[0];
while (d[0]) { // inv.hsl
    x qb[0];
    c[0] = measure qb[0];
}
