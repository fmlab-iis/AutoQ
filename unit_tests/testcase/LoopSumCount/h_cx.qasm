OPENQASM 3;
include "stdgates.inc";
qubit[2] qb;
for int i in [1:1] {
  h qb[0];
  cx qb[0], qb[1];
}
