OPENQASM 2.0;
include "qelib1.inc";
qreg q[45];
cx q[13],q[15];
cx q[2],q[15];
cx q[14],q[16];
cx q[2],q[16];
ccx q[14],q[15],q[16];
ccx q[2],q[14],q[16];
cx q[12],q[17];
cx q[2],q[17];
ccx q[12],q[16],q[17];
ccx q[2],q[12],q[17];
cx q[11],q[18];
cx q[2],q[18];
ccx q[11],q[17],q[18];
ccx q[2],q[11],q[18];
cx q[8],q[18];
x q[18];
cx q[5],q[18];
x q[18];
cx q[0],q[18];
x q[18];
cx q[7],q[18];
x q[18];
cx q[3],q[18];
x q[18];
cx q[1],q[18];
x q[18];
x q[18];
cx q[11],q[19];
cx q[17],q[19];
ccx q[2],q[11],q[19];
ccx q[11],q[17],q[19];
cx q[9],q[19];
x q[19];
cx q[8],q[19];
x q[19];
cx q[6],q[19];
x q[19];
cx q[4],q[19];
x q[19];
cx q[3],q[19];
x q[19];
cx q[1],q[19];
x q[19];
cx q[12],q[20];
cx q[16],q[20];
ccx q[2],q[12],q[20];
ccx q[12],q[16],q[20];
cx q[2],q[21];
ccx q[11],q[20],q[21];
ccx q[2],q[11],q[21];
cx q[9],q[21];
x q[21];
cx q[5],q[21];
x q[21];
cx q[7],q[21];
x q[21];
cx q[4],q[21];
x q[21];
cx q[3],q[21];
x q[21];
cx q[10],q[21];
x q[21];
cx q[20],q[22];
ccx q[2],q[11],q[22];
ccx q[11],q[20],q[22];
cx q[6],q[22];
x q[22];
cx q[0],q[22];
x q[22];
cx q[7],q[22];
x q[22];
cx q[4],q[22];
x q[22];
cx q[1],q[22];
x q[22];
cx q[10],q[22];
x q[22];
ccx q[13],q[14],q[23];
cx q[14],q[23];
ccx q[12],q[23],q[24];
cx q[12],q[24];
ccx q[11],q[24],q[25];
cx q[11],q[25];
cx q[0],q[25];
x q[25];
cx q[11],q[26];
ccx q[11],q[24],q[26];
cx q[24],q[26];
cx q[1],q[26];
x q[26];
cx q[2],q[27];
ccx q[14],q[15],q[27];
ccx q[2],q[14],q[27];
cx q[27],q[28];
ccx q[2],q[12],q[28];
ccx q[12],q[27],q[28];
cx q[2],q[29];
ccx q[11],q[28],q[29];
ccx q[2],q[11],q[29];
cx q[12],q[30];
ccx q[12],q[23],q[30];
cx q[23],q[30];
cx q[11],q[31];
ccx q[11],q[30],q[31];
cx q[30],q[31];
cx q[3],q[31];
x q[31];
ccx q[13],q[14],q[32];
cx q[13],q[32];
ccx q[12],q[32],q[33];
cx q[12],q[33];
ccx q[11],q[33],q[34];
cx q[11],q[34];
cx q[4],q[34];
x q[34];
cx q[11],q[35];
ccx q[11],q[33],q[35];
cx q[33],q[35];
cx q[5],q[35];
x q[35];
cx q[12],q[36];
ccx q[12],q[32],q[36];
cx q[32],q[36];
ccx q[11],q[36],q[37];
cx q[11],q[37];
cx q[6],q[37];
x q[37];
cx q[11],q[38];
ccx q[11],q[36],q[38];
cx q[36],q[38];
cx q[7],q[38];
x q[38];
cx q[14],q[39];
ccx q[13],q[14],q[39];
cx q[13],q[39];
ccx q[12],q[39],q[40];
cx q[12],q[40];
ccx q[11],q[40],q[41];
cx q[11],q[41];
cx q[8],q[41];
x q[41];
cx q[11],q[42];
ccx q[11],q[40],q[42];
cx q[40],q[42];
cx q[9],q[42];
x q[42];
cx q[12],q[43];
ccx q[12],q[39],q[43];
cx q[39],q[43];
ccx q[11],q[43],q[44];
cx q[11],q[44];
cx q[10],q[44];
x q[44];