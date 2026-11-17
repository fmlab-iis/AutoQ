OPENQASM 3;
qreg q[1];
bit r;
r = measure q[0];
if (r) { x q[0]; }
