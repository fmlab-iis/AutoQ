OPENQASM 3;
include "stdgates.inc";
qubit[1] qb;
for int i in [1:3] {
  // flip the qubit
  /* then rotate */
  x qb[0]; // rx(pi/2) qb[0];
  t qb[0];
}
