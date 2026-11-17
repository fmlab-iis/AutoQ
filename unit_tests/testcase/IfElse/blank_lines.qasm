OPENQASM 3;
include "stdgates.inc";
qubit[1] qb;
bit[1] outcome;
h qb[0];
outcome[0] = measure qb[0];
if (!outcome[0])

{
    x qb[0];
}

else

{
    h qb[0];
}
