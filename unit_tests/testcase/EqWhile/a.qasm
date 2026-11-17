OPENQASM 3;
qreg q[1];
bit r;
r = measure q[0];
while (r) { // inv.hsl
    x q[0];
    r = measure q[0];
}
