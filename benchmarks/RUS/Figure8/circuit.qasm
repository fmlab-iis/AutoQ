OPENQASM 3;
include "stdgates.inc";
qreg problem[2];

h problem[0];
t problem[0];
cx problem[0], problem[1];
h problem[0];
cx problem[0], problem[1];
t problem[0];
h problem[0];
x problem[0];

while (!measure problem[0]) { // loop-invariant.aut
h problem[0];
t problem[0];
cx problem[0], problem[1];
h problem[0];
cx problem[0], problem[1];
t problem[0];
h problem[0];
x problem[0];
} // post.aut
