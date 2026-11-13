OPENQASM 3;
include "stdgates.inc";
qubit[2] qb;
cx qb[0], qb[1]; // rx(pi/2) qb[1];
