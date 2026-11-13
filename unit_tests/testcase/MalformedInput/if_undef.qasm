OPENQASM 3;
qubit[1] qb;
bit[1] c;
c[0] = measure qb[0];
if (d[0]) {
    x qb[0];
}
