OPENQASM 3;
include "stdgates.inc";
qubit[1] qb;
for int i in [1:3] {
  x qb[0];
  t qb[0];
}
