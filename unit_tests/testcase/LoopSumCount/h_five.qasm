OPENQASM 3;
include "stdgates.inc";
qubit[1] qb;
for int i in [1:5] {
  h qb[0];
}
