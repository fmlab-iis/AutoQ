OPENQASM 3;
include "stdgates.inc";
qubit[2] q;

for int i in [1:3] {
    y q[0];
    h q[1];
    cz q[0], q[1];
    tdg q[0];
}
