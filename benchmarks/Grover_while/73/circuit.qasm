OPENQASM 3;
include "stdgates.inc";
qubit[147] qb;
bit[147] outcome;

// Define a controlled U operation using the ctrl gate modifier.
// q1 is control, q2 is target
gate custom q {
    U(0.190332413, 0, 0) q;
}
gate ccustom q1, q2 {
    ctrl @ custom q1, q2;
}

h qb[74];
h qb[75];
h qb[76];
h qb[77];
h qb[78];
h qb[79];
h qb[80];
h qb[81];
h qb[82];
h qb[83];
h qb[84];
h qb[85];
h qb[86];
h qb[87];
h qb[88];
h qb[89];
h qb[90];
h qb[91];
h qb[92];
h qb[93];
h qb[94];
h qb[95];
h qb[96];
h qb[97];
h qb[98];
h qb[99];
h qb[100];
h qb[101];
h qb[102];
h qb[103];
h qb[104];
h qb[105];
h qb[106];
h qb[107];
h qb[108];
h qb[109];
h qb[110];
h qb[111];
h qb[112];
h qb[113];
h qb[114];
h qb[115];
h qb[116];
h qb[117];
h qb[118];
h qb[119];
h qb[120];
h qb[121];
h qb[122];
h qb[123];
h qb[124];
h qb[125];
h qb[126];
h qb[127];
h qb[128];
h qb[129];
h qb[130];
h qb[131];
h qb[132];
h qb[133];
h qb[134];
h qb[135];
h qb[136];
h qb[137];
h qb[138];
h qb[139];
h qb[140];
h qb[141];
h qb[142];
h qb[143];
h qb[144];
h qb[145];
h qb[146];
ccx qb[74], qb[75], qb[0];
ccx qb[0], qb[76], qb[1];
ccx qb[1], qb[77], qb[2];
ccx qb[2], qb[78], qb[3];
ccx qb[3], qb[79], qb[4];
ccx qb[4], qb[80], qb[5];
ccx qb[5], qb[81], qb[6];
ccx qb[6], qb[82], qb[7];
ccx qb[7], qb[83], qb[8];
ccx qb[8], qb[84], qb[9];
ccx qb[9], qb[85], qb[10];
ccx qb[10], qb[86], qb[11];
ccx qb[11], qb[87], qb[12];
ccx qb[12], qb[88], qb[13];
ccx qb[13], qb[89], qb[14];
ccx qb[14], qb[90], qb[15];
ccx qb[15], qb[91], qb[16];
ccx qb[16], qb[92], qb[17];
ccx qb[17], qb[93], qb[18];
ccx qb[18], qb[94], qb[19];
ccx qb[19], qb[95], qb[20];
ccx qb[20], qb[96], qb[21];
ccx qb[21], qb[97], qb[22];
ccx qb[22], qb[98], qb[23];
ccx qb[23], qb[99], qb[24];
ccx qb[24], qb[100], qb[25];
ccx qb[25], qb[101], qb[26];
ccx qb[26], qb[102], qb[27];
ccx qb[27], qb[103], qb[28];
ccx qb[28], qb[104], qb[29];
ccx qb[29], qb[105], qb[30];
ccx qb[30], qb[106], qb[31];
ccx qb[31], qb[107], qb[32];
ccx qb[32], qb[108], qb[33];
ccx qb[33], qb[109], qb[34];
ccx qb[34], qb[110], qb[35];
ccx qb[35], qb[111], qb[36];
ccx qb[36], qb[112], qb[37];
ccx qb[37], qb[113], qb[38];
ccx qb[38], qb[114], qb[39];
ccx qb[39], qb[115], qb[40];
ccx qb[40], qb[116], qb[41];
ccx qb[41], qb[117], qb[42];
ccx qb[42], qb[118], qb[43];
ccx qb[43], qb[119], qb[44];
ccx qb[44], qb[120], qb[45];
ccx qb[45], qb[121], qb[46];
ccx qb[46], qb[122], qb[47];
ccx qb[47], qb[123], qb[48];
ccx qb[48], qb[124], qb[49];
ccx qb[49], qb[125], qb[50];
ccx qb[50], qb[126], qb[51];
ccx qb[51], qb[127], qb[52];
ccx qb[52], qb[128], qb[53];
ccx qb[53], qb[129], qb[54];
ccx qb[54], qb[130], qb[55];
ccx qb[55], qb[131], qb[56];
ccx qb[56], qb[132], qb[57];
ccx qb[57], qb[133], qb[58];
ccx qb[58], qb[134], qb[59];
ccx qb[59], qb[135], qb[60];
ccx qb[60], qb[136], qb[61];
ccx qb[61], qb[137], qb[62];
ccx qb[62], qb[138], qb[63];
ccx qb[63], qb[139], qb[64];
ccx qb[64], qb[140], qb[65];
ccx qb[65], qb[141], qb[66];
ccx qb[66], qb[142], qb[67];
ccx qb[67], qb[143], qb[68];
ccx qb[68], qb[144], qb[69];
ccx qb[69], qb[145], qb[70];
ccx qb[70], qb[146], qb[71];
cx qb[71], qb[73];
ccx qb[70], qb[146], qb[71];
ccx qb[69], qb[145], qb[70];
ccx qb[68], qb[144], qb[69];
ccx qb[67], qb[143], qb[68];
ccx qb[66], qb[142], qb[67];
ccx qb[65], qb[141], qb[66];
ccx qb[64], qb[140], qb[65];
ccx qb[63], qb[139], qb[64];
ccx qb[62], qb[138], qb[63];
ccx qb[61], qb[137], qb[62];
ccx qb[60], qb[136], qb[61];
ccx qb[59], qb[135], qb[60];
ccx qb[58], qb[134], qb[59];
ccx qb[57], qb[133], qb[58];
ccx qb[56], qb[132], qb[57];
ccx qb[55], qb[131], qb[56];
ccx qb[54], qb[130], qb[55];
ccx qb[53], qb[129], qb[54];
ccx qb[52], qb[128], qb[53];
ccx qb[51], qb[127], qb[52];
ccx qb[50], qb[126], qb[51];
ccx qb[49], qb[125], qb[50];
ccx qb[48], qb[124], qb[49];
ccx qb[47], qb[123], qb[48];
ccx qb[46], qb[122], qb[47];
ccx qb[45], qb[121], qb[46];
ccx qb[44], qb[120], qb[45];
ccx qb[43], qb[119], qb[44];
ccx qb[42], qb[118], qb[43];
ccx qb[41], qb[117], qb[42];
ccx qb[40], qb[116], qb[41];
ccx qb[39], qb[115], qb[40];
ccx qb[38], qb[114], qb[39];
ccx qb[37], qb[113], qb[38];
ccx qb[36], qb[112], qb[37];
ccx qb[35], qb[111], qb[36];
ccx qb[34], qb[110], qb[35];
ccx qb[33], qb[109], qb[34];
ccx qb[32], qb[108], qb[33];
ccx qb[31], qb[107], qb[32];
ccx qb[30], qb[106], qb[31];
ccx qb[29], qb[105], qb[30];
ccx qb[28], qb[104], qb[29];
ccx qb[27], qb[103], qb[28];
ccx qb[26], qb[102], qb[27];
ccx qb[25], qb[101], qb[26];
ccx qb[24], qb[100], qb[25];
ccx qb[23], qb[99], qb[24];
ccx qb[22], qb[98], qb[23];
ccx qb[21], qb[97], qb[22];
ccx qb[20], qb[96], qb[21];
ccx qb[19], qb[95], qb[20];
ccx qb[18], qb[94], qb[19];
ccx qb[17], qb[93], qb[18];
ccx qb[16], qb[92], qb[17];
ccx qb[15], qb[91], qb[16];
ccx qb[14], qb[90], qb[15];
ccx qb[13], qb[89], qb[14];
ccx qb[12], qb[88], qb[13];
ccx qb[11], qb[87], qb[12];
ccx qb[10], qb[86], qb[11];
ccx qb[9], qb[85], qb[10];
ccx qb[8], qb[84], qb[9];
ccx qb[7], qb[83], qb[8];
ccx qb[6], qb[82], qb[7];
ccx qb[5], qb[81], qb[6];
ccx qb[4], qb[80], qb[5];
ccx qb[3], qb[79], qb[4];
ccx qb[2], qb[78], qb[3];
ccx qb[1], qb[77], qb[2];
ccx qb[0], qb[76], qb[1];
ccx qb[74], qb[75], qb[0];
ccustom qb[73], qb[72];
ccx qb[74], qb[75], qb[0];
ccx qb[0], qb[76], qb[1];
ccx qb[1], qb[77], qb[2];
ccx qb[2], qb[78], qb[3];
ccx qb[3], qb[79], qb[4];
ccx qb[4], qb[80], qb[5];
ccx qb[5], qb[81], qb[6];
ccx qb[6], qb[82], qb[7];
ccx qb[7], qb[83], qb[8];
ccx qb[8], qb[84], qb[9];
ccx qb[9], qb[85], qb[10];
ccx qb[10], qb[86], qb[11];
ccx qb[11], qb[87], qb[12];
ccx qb[12], qb[88], qb[13];
ccx qb[13], qb[89], qb[14];
ccx qb[14], qb[90], qb[15];
ccx qb[15], qb[91], qb[16];
ccx qb[16], qb[92], qb[17];
ccx qb[17], qb[93], qb[18];
ccx qb[18], qb[94], qb[19];
ccx qb[19], qb[95], qb[20];
ccx qb[20], qb[96], qb[21];
ccx qb[21], qb[97], qb[22];
ccx qb[22], qb[98], qb[23];
ccx qb[23], qb[99], qb[24];
ccx qb[24], qb[100], qb[25];
ccx qb[25], qb[101], qb[26];
ccx qb[26], qb[102], qb[27];
ccx qb[27], qb[103], qb[28];
ccx qb[28], qb[104], qb[29];
ccx qb[29], qb[105], qb[30];
ccx qb[30], qb[106], qb[31];
ccx qb[31], qb[107], qb[32];
ccx qb[32], qb[108], qb[33];
ccx qb[33], qb[109], qb[34];
ccx qb[34], qb[110], qb[35];
ccx qb[35], qb[111], qb[36];
ccx qb[36], qb[112], qb[37];
ccx qb[37], qb[113], qb[38];
ccx qb[38], qb[114], qb[39];
ccx qb[39], qb[115], qb[40];
ccx qb[40], qb[116], qb[41];
ccx qb[41], qb[117], qb[42];
ccx qb[42], qb[118], qb[43];
ccx qb[43], qb[119], qb[44];
ccx qb[44], qb[120], qb[45];
ccx qb[45], qb[121], qb[46];
ccx qb[46], qb[122], qb[47];
ccx qb[47], qb[123], qb[48];
ccx qb[48], qb[124], qb[49];
ccx qb[49], qb[125], qb[50];
ccx qb[50], qb[126], qb[51];
ccx qb[51], qb[127], qb[52];
ccx qb[52], qb[128], qb[53];
ccx qb[53], qb[129], qb[54];
ccx qb[54], qb[130], qb[55];
ccx qb[55], qb[131], qb[56];
ccx qb[56], qb[132], qb[57];
ccx qb[57], qb[133], qb[58];
ccx qb[58], qb[134], qb[59];
ccx qb[59], qb[135], qb[60];
ccx qb[60], qb[136], qb[61];
ccx qb[61], qb[137], qb[62];
ccx qb[62], qb[138], qb[63];
ccx qb[63], qb[139], qb[64];
ccx qb[64], qb[140], qb[65];
ccx qb[65], qb[141], qb[66];
ccx qb[66], qb[142], qb[67];
ccx qb[67], qb[143], qb[68];
ccx qb[68], qb[144], qb[69];
ccx qb[69], qb[145], qb[70];
ccx qb[70], qb[146], qb[71];
cx qb[71], qb[73];
ccx qb[70], qb[146], qb[71];
ccx qb[69], qb[145], qb[70];
ccx qb[68], qb[144], qb[69];
ccx qb[67], qb[143], qb[68];
ccx qb[66], qb[142], qb[67];
ccx qb[65], qb[141], qb[66];
ccx qb[64], qb[140], qb[65];
ccx qb[63], qb[139], qb[64];
ccx qb[62], qb[138], qb[63];
ccx qb[61], qb[137], qb[62];
ccx qb[60], qb[136], qb[61];
ccx qb[59], qb[135], qb[60];
ccx qb[58], qb[134], qb[59];
ccx qb[57], qb[133], qb[58];
ccx qb[56], qb[132], qb[57];
ccx qb[55], qb[131], qb[56];
ccx qb[54], qb[130], qb[55];
ccx qb[53], qb[129], qb[54];
ccx qb[52], qb[128], qb[53];
ccx qb[51], qb[127], qb[52];
ccx qb[50], qb[126], qb[51];
ccx qb[49], qb[125], qb[50];
ccx qb[48], qb[124], qb[49];
ccx qb[47], qb[123], qb[48];
ccx qb[46], qb[122], qb[47];
ccx qb[45], qb[121], qb[46];
ccx qb[44], qb[120], qb[45];
ccx qb[43], qb[119], qb[44];
ccx qb[42], qb[118], qb[43];
ccx qb[41], qb[117], qb[42];
ccx qb[40], qb[116], qb[41];
ccx qb[39], qb[115], qb[40];
ccx qb[38], qb[114], qb[39];
ccx qb[37], qb[113], qb[38];
ccx qb[36], qb[112], qb[37];
ccx qb[35], qb[111], qb[36];
ccx qb[34], qb[110], qb[35];
ccx qb[33], qb[109], qb[34];
ccx qb[32], qb[108], qb[33];
ccx qb[31], qb[107], qb[32];
ccx qb[30], qb[106], qb[31];
ccx qb[29], qb[105], qb[30];
ccx qb[28], qb[104], qb[29];
ccx qb[27], qb[103], qb[28];
ccx qb[26], qb[102], qb[27];
ccx qb[25], qb[101], qb[26];
ccx qb[24], qb[100], qb[25];
ccx qb[23], qb[99], qb[24];
ccx qb[22], qb[98], qb[23];
ccx qb[21], qb[97], qb[22];
ccx qb[20], qb[96], qb[21];
ccx qb[19], qb[95], qb[20];
ccx qb[18], qb[94], qb[19];
ccx qb[17], qb[93], qb[18];
ccx qb[16], qb[92], qb[17];
ccx qb[15], qb[91], qb[16];
ccx qb[14], qb[90], qb[15];
ccx qb[13], qb[89], qb[14];
ccx qb[12], qb[88], qb[13];
ccx qb[11], qb[87], qb[12];
ccx qb[10], qb[86], qb[11];
ccx qb[9], qb[85], qb[10];
ccx qb[8], qb[84], qb[9];
ccx qb[7], qb[83], qb[8];
ccx qb[6], qb[82], qb[7];
ccx qb[5], qb[81], qb[6];
ccx qb[4], qb[80], qb[5];
ccx qb[3], qb[79], qb[4];
ccx qb[2], qb[78], qb[3];
ccx qb[1], qb[77], qb[2];
ccx qb[0], qb[76], qb[1];
ccx qb[74], qb[75], qb[0];

outcome[72] = measure qb[72];
while (!outcome[72]) { // loop-invariant.spec
x qb[73];
h qb[73];
ccx qb[74], qb[75], qb[0];
ccx qb[0], qb[76], qb[1];
ccx qb[1], qb[77], qb[2];
ccx qb[2], qb[78], qb[3];
ccx qb[3], qb[79], qb[4];
ccx qb[4], qb[80], qb[5];
ccx qb[5], qb[81], qb[6];
ccx qb[6], qb[82], qb[7];
ccx qb[7], qb[83], qb[8];
ccx qb[8], qb[84], qb[9];
ccx qb[9], qb[85], qb[10];
ccx qb[10], qb[86], qb[11];
ccx qb[11], qb[87], qb[12];
ccx qb[12], qb[88], qb[13];
ccx qb[13], qb[89], qb[14];
ccx qb[14], qb[90], qb[15];
ccx qb[15], qb[91], qb[16];
ccx qb[16], qb[92], qb[17];
ccx qb[17], qb[93], qb[18];
ccx qb[18], qb[94], qb[19];
ccx qb[19], qb[95], qb[20];
ccx qb[20], qb[96], qb[21];
ccx qb[21], qb[97], qb[22];
ccx qb[22], qb[98], qb[23];
ccx qb[23], qb[99], qb[24];
ccx qb[24], qb[100], qb[25];
ccx qb[25], qb[101], qb[26];
ccx qb[26], qb[102], qb[27];
ccx qb[27], qb[103], qb[28];
ccx qb[28], qb[104], qb[29];
ccx qb[29], qb[105], qb[30];
ccx qb[30], qb[106], qb[31];
ccx qb[31], qb[107], qb[32];
ccx qb[32], qb[108], qb[33];
ccx qb[33], qb[109], qb[34];
ccx qb[34], qb[110], qb[35];
ccx qb[35], qb[111], qb[36];
ccx qb[36], qb[112], qb[37];
ccx qb[37], qb[113], qb[38];
ccx qb[38], qb[114], qb[39];
ccx qb[39], qb[115], qb[40];
ccx qb[40], qb[116], qb[41];
ccx qb[41], qb[117], qb[42];
ccx qb[42], qb[118], qb[43];
ccx qb[43], qb[119], qb[44];
ccx qb[44], qb[120], qb[45];
ccx qb[45], qb[121], qb[46];
ccx qb[46], qb[122], qb[47];
ccx qb[47], qb[123], qb[48];
ccx qb[48], qb[124], qb[49];
ccx qb[49], qb[125], qb[50];
ccx qb[50], qb[126], qb[51];
ccx qb[51], qb[127], qb[52];
ccx qb[52], qb[128], qb[53];
ccx qb[53], qb[129], qb[54];
ccx qb[54], qb[130], qb[55];
ccx qb[55], qb[131], qb[56];
ccx qb[56], qb[132], qb[57];
ccx qb[57], qb[133], qb[58];
ccx qb[58], qb[134], qb[59];
ccx qb[59], qb[135], qb[60];
ccx qb[60], qb[136], qb[61];
ccx qb[61], qb[137], qb[62];
ccx qb[62], qb[138], qb[63];
ccx qb[63], qb[139], qb[64];
ccx qb[64], qb[140], qb[65];
ccx qb[65], qb[141], qb[66];
ccx qb[66], qb[142], qb[67];
ccx qb[67], qb[143], qb[68];
ccx qb[68], qb[144], qb[69];
ccx qb[69], qb[145], qb[70];
ccx qb[70], qb[146], qb[71];
cx qb[71], qb[73];
ccx qb[70], qb[146], qb[71];
ccx qb[69], qb[145], qb[70];
ccx qb[68], qb[144], qb[69];
ccx qb[67], qb[143], qb[68];
ccx qb[66], qb[142], qb[67];
ccx qb[65], qb[141], qb[66];
ccx qb[64], qb[140], qb[65];
ccx qb[63], qb[139], qb[64];
ccx qb[62], qb[138], qb[63];
ccx qb[61], qb[137], qb[62];
ccx qb[60], qb[136], qb[61];
ccx qb[59], qb[135], qb[60];
ccx qb[58], qb[134], qb[59];
ccx qb[57], qb[133], qb[58];
ccx qb[56], qb[132], qb[57];
ccx qb[55], qb[131], qb[56];
ccx qb[54], qb[130], qb[55];
ccx qb[53], qb[129], qb[54];
ccx qb[52], qb[128], qb[53];
ccx qb[51], qb[127], qb[52];
ccx qb[50], qb[126], qb[51];
ccx qb[49], qb[125], qb[50];
ccx qb[48], qb[124], qb[49];
ccx qb[47], qb[123], qb[48];
ccx qb[46], qb[122], qb[47];
ccx qb[45], qb[121], qb[46];
ccx qb[44], qb[120], qb[45];
ccx qb[43], qb[119], qb[44];
ccx qb[42], qb[118], qb[43];
ccx qb[41], qb[117], qb[42];
ccx qb[40], qb[116], qb[41];
ccx qb[39], qb[115], qb[40];
ccx qb[38], qb[114], qb[39];
ccx qb[37], qb[113], qb[38];
ccx qb[36], qb[112], qb[37];
ccx qb[35], qb[111], qb[36];
ccx qb[34], qb[110], qb[35];
ccx qb[33], qb[109], qb[34];
ccx qb[32], qb[108], qb[33];
ccx qb[31], qb[107], qb[32];
ccx qb[30], qb[106], qb[31];
ccx qb[29], qb[105], qb[30];
ccx qb[28], qb[104], qb[29];
ccx qb[27], qb[103], qb[28];
ccx qb[26], qb[102], qb[27];
ccx qb[25], qb[101], qb[26];
ccx qb[24], qb[100], qb[25];
ccx qb[23], qb[99], qb[24];
ccx qb[22], qb[98], qb[23];
ccx qb[21], qb[97], qb[22];
ccx qb[20], qb[96], qb[21];
ccx qb[19], qb[95], qb[20];
ccx qb[18], qb[94], qb[19];
ccx qb[17], qb[93], qb[18];
ccx qb[16], qb[92], qb[17];
ccx qb[15], qb[91], qb[16];
ccx qb[14], qb[90], qb[15];
ccx qb[13], qb[89], qb[14];
ccx qb[12], qb[88], qb[13];
ccx qb[11], qb[87], qb[12];
ccx qb[10], qb[86], qb[11];
ccx qb[9], qb[85], qb[10];
ccx qb[8], qb[84], qb[9];
ccx qb[7], qb[83], qb[8];
ccx qb[6], qb[82], qb[7];
ccx qb[5], qb[81], qb[6];
ccx qb[4], qb[80], qb[5];
ccx qb[3], qb[79], qb[4];
ccx qb[2], qb[78], qb[3];
ccx qb[1], qb[77], qb[2];
ccx qb[0], qb[76], qb[1];
ccx qb[74], qb[75], qb[0];
h qb[73];
x qb[73];
h qb[74];
h qb[75];
h qb[76];
h qb[77];
h qb[78];
h qb[79];
h qb[80];
h qb[81];
h qb[82];
h qb[83];
h qb[84];
h qb[85];
h qb[86];
h qb[87];
h qb[88];
h qb[89];
h qb[90];
h qb[91];
h qb[92];
h qb[93];
h qb[94];
h qb[95];
h qb[96];
h qb[97];
h qb[98];
h qb[99];
h qb[100];
h qb[101];
h qb[102];
h qb[103];
h qb[104];
h qb[105];
h qb[106];
h qb[107];
h qb[108];
h qb[109];
h qb[110];
h qb[111];
h qb[112];
h qb[113];
h qb[114];
h qb[115];
h qb[116];
h qb[117];
h qb[118];
h qb[119];
h qb[120];
h qb[121];
h qb[122];
h qb[123];
h qb[124];
h qb[125];
h qb[126];
h qb[127];
h qb[128];
h qb[129];
h qb[130];
h qb[131];
h qb[132];
h qb[133];
h qb[134];
h qb[135];
h qb[136];
h qb[137];
h qb[138];
h qb[139];
h qb[140];
h qb[141];
h qb[142];
h qb[143];
h qb[144];
h qb[145];
h qb[146];
x qb[74];
x qb[75];
x qb[76];
x qb[77];
x qb[78];
x qb[79];
x qb[80];
x qb[81];
x qb[82];
x qb[83];
x qb[84];
x qb[85];
x qb[86];
x qb[87];
x qb[88];
x qb[89];
x qb[90];
x qb[91];
x qb[92];
x qb[93];
x qb[94];
x qb[95];
x qb[96];
x qb[97];
x qb[98];
x qb[99];
x qb[100];
x qb[101];
x qb[102];
x qb[103];
x qb[104];
x qb[105];
x qb[106];
x qb[107];
x qb[108];
x qb[109];
x qb[110];
x qb[111];
x qb[112];
x qb[113];
x qb[114];
x qb[115];
x qb[116];
x qb[117];
x qb[118];
x qb[119];
x qb[120];
x qb[121];
x qb[122];
x qb[123];
x qb[124];
x qb[125];
x qb[126];
x qb[127];
x qb[128];
x qb[129];
x qb[130];
x qb[131];
x qb[132];
x qb[133];
x qb[134];
x qb[135];
x qb[136];
x qb[137];
x qb[138];
x qb[139];
x qb[140];
x qb[141];
x qb[142];
x qb[143];
x qb[144];
x qb[145];
x qb[146];
ccx qb[74], qb[75], qb[0];
ccx qb[0], qb[76], qb[1];
ccx qb[1], qb[77], qb[2];
ccx qb[2], qb[78], qb[3];
ccx qb[3], qb[79], qb[4];
ccx qb[4], qb[80], qb[5];
ccx qb[5], qb[81], qb[6];
ccx qb[6], qb[82], qb[7];
ccx qb[7], qb[83], qb[8];
ccx qb[8], qb[84], qb[9];
ccx qb[9], qb[85], qb[10];
ccx qb[10], qb[86], qb[11];
ccx qb[11], qb[87], qb[12];
ccx qb[12], qb[88], qb[13];
ccx qb[13], qb[89], qb[14];
ccx qb[14], qb[90], qb[15];
ccx qb[15], qb[91], qb[16];
ccx qb[16], qb[92], qb[17];
ccx qb[17], qb[93], qb[18];
ccx qb[18], qb[94], qb[19];
ccx qb[19], qb[95], qb[20];
ccx qb[20], qb[96], qb[21];
ccx qb[21], qb[97], qb[22];
ccx qb[22], qb[98], qb[23];
ccx qb[23], qb[99], qb[24];
ccx qb[24], qb[100], qb[25];
ccx qb[25], qb[101], qb[26];
ccx qb[26], qb[102], qb[27];
ccx qb[27], qb[103], qb[28];
ccx qb[28], qb[104], qb[29];
ccx qb[29], qb[105], qb[30];
ccx qb[30], qb[106], qb[31];
ccx qb[31], qb[107], qb[32];
ccx qb[32], qb[108], qb[33];
ccx qb[33], qb[109], qb[34];
ccx qb[34], qb[110], qb[35];
ccx qb[35], qb[111], qb[36];
ccx qb[36], qb[112], qb[37];
ccx qb[37], qb[113], qb[38];
ccx qb[38], qb[114], qb[39];
ccx qb[39], qb[115], qb[40];
ccx qb[40], qb[116], qb[41];
ccx qb[41], qb[117], qb[42];
ccx qb[42], qb[118], qb[43];
ccx qb[43], qb[119], qb[44];
ccx qb[44], qb[120], qb[45];
ccx qb[45], qb[121], qb[46];
ccx qb[46], qb[122], qb[47];
ccx qb[47], qb[123], qb[48];
ccx qb[48], qb[124], qb[49];
ccx qb[49], qb[125], qb[50];
ccx qb[50], qb[126], qb[51];
ccx qb[51], qb[127], qb[52];
ccx qb[52], qb[128], qb[53];
ccx qb[53], qb[129], qb[54];
ccx qb[54], qb[130], qb[55];
ccx qb[55], qb[131], qb[56];
ccx qb[56], qb[132], qb[57];
ccx qb[57], qb[133], qb[58];
ccx qb[58], qb[134], qb[59];
ccx qb[59], qb[135], qb[60];
ccx qb[60], qb[136], qb[61];
ccx qb[61], qb[137], qb[62];
ccx qb[62], qb[138], qb[63];
ccx qb[63], qb[139], qb[64];
ccx qb[64], qb[140], qb[65];
ccx qb[65], qb[141], qb[66];
ccx qb[66], qb[142], qb[67];
ccx qb[67], qb[143], qb[68];
ccx qb[68], qb[144], qb[69];
ccx qb[69], qb[145], qb[70];
cz qb[70], qb[146];
ccx qb[69], qb[145], qb[70];
ccx qb[68], qb[144], qb[69];
ccx qb[67], qb[143], qb[68];
ccx qb[66], qb[142], qb[67];
ccx qb[65], qb[141], qb[66];
ccx qb[64], qb[140], qb[65];
ccx qb[63], qb[139], qb[64];
ccx qb[62], qb[138], qb[63];
ccx qb[61], qb[137], qb[62];
ccx qb[60], qb[136], qb[61];
ccx qb[59], qb[135], qb[60];
ccx qb[58], qb[134], qb[59];
ccx qb[57], qb[133], qb[58];
ccx qb[56], qb[132], qb[57];
ccx qb[55], qb[131], qb[56];
ccx qb[54], qb[130], qb[55];
ccx qb[53], qb[129], qb[54];
ccx qb[52], qb[128], qb[53];
ccx qb[51], qb[127], qb[52];
ccx qb[50], qb[126], qb[51];
ccx qb[49], qb[125], qb[50];
ccx qb[48], qb[124], qb[49];
ccx qb[47], qb[123], qb[48];
ccx qb[46], qb[122], qb[47];
ccx qb[45], qb[121], qb[46];
ccx qb[44], qb[120], qb[45];
ccx qb[43], qb[119], qb[44];
ccx qb[42], qb[118], qb[43];
ccx qb[41], qb[117], qb[42];
ccx qb[40], qb[116], qb[41];
ccx qb[39], qb[115], qb[40];
ccx qb[38], qb[114], qb[39];
ccx qb[37], qb[113], qb[38];
ccx qb[36], qb[112], qb[37];
ccx qb[35], qb[111], qb[36];
ccx qb[34], qb[110], qb[35];
ccx qb[33], qb[109], qb[34];
ccx qb[32], qb[108], qb[33];
ccx qb[31], qb[107], qb[32];
ccx qb[30], qb[106], qb[31];
ccx qb[29], qb[105], qb[30];
ccx qb[28], qb[104], qb[29];
ccx qb[27], qb[103], qb[28];
ccx qb[26], qb[102], qb[27];
ccx qb[25], qb[101], qb[26];
ccx qb[24], qb[100], qb[25];
ccx qb[23], qb[99], qb[24];
ccx qb[22], qb[98], qb[23];
ccx qb[21], qb[97], qb[22];
ccx qb[20], qb[96], qb[21];
ccx qb[19], qb[95], qb[20];
ccx qb[18], qb[94], qb[19];
ccx qb[17], qb[93], qb[18];
ccx qb[16], qb[92], qb[17];
ccx qb[15], qb[91], qb[16];
ccx qb[14], qb[90], qb[15];
ccx qb[13], qb[89], qb[14];
ccx qb[12], qb[88], qb[13];
ccx qb[11], qb[87], qb[12];
ccx qb[10], qb[86], qb[11];
ccx qb[9], qb[85], qb[10];
ccx qb[8], qb[84], qb[9];
ccx qb[7], qb[83], qb[8];
ccx qb[6], qb[82], qb[7];
ccx qb[5], qb[81], qb[6];
ccx qb[4], qb[80], qb[5];
ccx qb[3], qb[79], qb[4];
ccx qb[2], qb[78], qb[3];
ccx qb[1], qb[77], qb[2];
ccx qb[0], qb[76], qb[1];
ccx qb[74], qb[75], qb[0];
x qb[74];
x qb[75];
x qb[76];
x qb[77];
x qb[78];
x qb[79];
x qb[80];
x qb[81];
x qb[82];
x qb[83];
x qb[84];
x qb[85];
x qb[86];
x qb[87];
x qb[88];
x qb[89];
x qb[90];
x qb[91];
x qb[92];
x qb[93];
x qb[94];
x qb[95];
x qb[96];
x qb[97];
x qb[98];
x qb[99];
x qb[100];
x qb[101];
x qb[102];
x qb[103];
x qb[104];
x qb[105];
x qb[106];
x qb[107];
x qb[108];
x qb[109];
x qb[110];
x qb[111];
x qb[112];
x qb[113];
x qb[114];
x qb[115];
x qb[116];
x qb[117];
x qb[118];
x qb[119];
x qb[120];
x qb[121];
x qb[122];
x qb[123];
x qb[124];
x qb[125];
x qb[126];
x qb[127];
x qb[128];
x qb[129];
x qb[130];
x qb[131];
x qb[132];
x qb[133];
x qb[134];
x qb[135];
x qb[136];
x qb[137];
x qb[138];
x qb[139];
x qb[140];
x qb[141];
x qb[142];
x qb[143];
x qb[144];
x qb[145];
x qb[146];
h qb[74];
h qb[75];
h qb[76];
h qb[77];
h qb[78];
h qb[79];
h qb[80];
h qb[81];
h qb[82];
h qb[83];
h qb[84];
h qb[85];
h qb[86];
h qb[87];
h qb[88];
h qb[89];
h qb[90];
h qb[91];
h qb[92];
h qb[93];
h qb[94];
h qb[95];
h qb[96];
h qb[97];
h qb[98];
h qb[99];
h qb[100];
h qb[101];
h qb[102];
h qb[103];
h qb[104];
h qb[105];
h qb[106];
h qb[107];
h qb[108];
h qb[109];
h qb[110];
h qb[111];
h qb[112];
h qb[113];
h qb[114];
h qb[115];
h qb[116];
h qb[117];
h qb[118];
h qb[119];
h qb[120];
h qb[121];
h qb[122];
h qb[123];
h qb[124];
h qb[125];
h qb[126];
h qb[127];
h qb[128];
h qb[129];
h qb[130];
h qb[131];
h qb[132];
h qb[133];
h qb[134];
h qb[135];
h qb[136];
h qb[137];
h qb[138];
h qb[139];
h qb[140];
h qb[141];
h qb[142];
h qb[143];
h qb[144];
h qb[145];
h qb[146];
ccx qb[74], qb[75], qb[0];
ccx qb[0], qb[76], qb[1];
ccx qb[1], qb[77], qb[2];
ccx qb[2], qb[78], qb[3];
ccx qb[3], qb[79], qb[4];
ccx qb[4], qb[80], qb[5];
ccx qb[5], qb[81], qb[6];
ccx qb[6], qb[82], qb[7];
ccx qb[7], qb[83], qb[8];
ccx qb[8], qb[84], qb[9];
ccx qb[9], qb[85], qb[10];
ccx qb[10], qb[86], qb[11];
ccx qb[11], qb[87], qb[12];
ccx qb[12], qb[88], qb[13];
ccx qb[13], qb[89], qb[14];
ccx qb[14], qb[90], qb[15];
ccx qb[15], qb[91], qb[16];
ccx qb[16], qb[92], qb[17];
ccx qb[17], qb[93], qb[18];
ccx qb[18], qb[94], qb[19];
ccx qb[19], qb[95], qb[20];
ccx qb[20], qb[96], qb[21];
ccx qb[21], qb[97], qb[22];
ccx qb[22], qb[98], qb[23];
ccx qb[23], qb[99], qb[24];
ccx qb[24], qb[100], qb[25];
ccx qb[25], qb[101], qb[26];
ccx qb[26], qb[102], qb[27];
ccx qb[27], qb[103], qb[28];
ccx qb[28], qb[104], qb[29];
ccx qb[29], qb[105], qb[30];
ccx qb[30], qb[106], qb[31];
ccx qb[31], qb[107], qb[32];
ccx qb[32], qb[108], qb[33];
ccx qb[33], qb[109], qb[34];
ccx qb[34], qb[110], qb[35];
ccx qb[35], qb[111], qb[36];
ccx qb[36], qb[112], qb[37];
ccx qb[37], qb[113], qb[38];
ccx qb[38], qb[114], qb[39];
ccx qb[39], qb[115], qb[40];
ccx qb[40], qb[116], qb[41];
ccx qb[41], qb[117], qb[42];
ccx qb[42], qb[118], qb[43];
ccx qb[43], qb[119], qb[44];
ccx qb[44], qb[120], qb[45];
ccx qb[45], qb[121], qb[46];
ccx qb[46], qb[122], qb[47];
ccx qb[47], qb[123], qb[48];
ccx qb[48], qb[124], qb[49];
ccx qb[49], qb[125], qb[50];
ccx qb[50], qb[126], qb[51];
ccx qb[51], qb[127], qb[52];
ccx qb[52], qb[128], qb[53];
ccx qb[53], qb[129], qb[54];
ccx qb[54], qb[130], qb[55];
ccx qb[55], qb[131], qb[56];
ccx qb[56], qb[132], qb[57];
ccx qb[57], qb[133], qb[58];
ccx qb[58], qb[134], qb[59];
ccx qb[59], qb[135], qb[60];
ccx qb[60], qb[136], qb[61];
ccx qb[61], qb[137], qb[62];
ccx qb[62], qb[138], qb[63];
ccx qb[63], qb[139], qb[64];
ccx qb[64], qb[140], qb[65];
ccx qb[65], qb[141], qb[66];
ccx qb[66], qb[142], qb[67];
ccx qb[67], qb[143], qb[68];
ccx qb[68], qb[144], qb[69];
ccx qb[69], qb[145], qb[70];
ccx qb[70], qb[146], qb[71];
cx qb[71], qb[73];
ccx qb[70], qb[146], qb[71];
ccx qb[69], qb[145], qb[70];
ccx qb[68], qb[144], qb[69];
ccx qb[67], qb[143], qb[68];
ccx qb[66], qb[142], qb[67];
ccx qb[65], qb[141], qb[66];
ccx qb[64], qb[140], qb[65];
ccx qb[63], qb[139], qb[64];
ccx qb[62], qb[138], qb[63];
ccx qb[61], qb[137], qb[62];
ccx qb[60], qb[136], qb[61];
ccx qb[59], qb[135], qb[60];
ccx qb[58], qb[134], qb[59];
ccx qb[57], qb[133], qb[58];
ccx qb[56], qb[132], qb[57];
ccx qb[55], qb[131], qb[56];
ccx qb[54], qb[130], qb[55];
ccx qb[53], qb[129], qb[54];
ccx qb[52], qb[128], qb[53];
ccx qb[51], qb[127], qb[52];
ccx qb[50], qb[126], qb[51];
ccx qb[49], qb[125], qb[50];
ccx qb[48], qb[124], qb[49];
ccx qb[47], qb[123], qb[48];
ccx qb[46], qb[122], qb[47];
ccx qb[45], qb[121], qb[46];
ccx qb[44], qb[120], qb[45];
ccx qb[43], qb[119], qb[44];
ccx qb[42], qb[118], qb[43];
ccx qb[41], qb[117], qb[42];
ccx qb[40], qb[116], qb[41];
ccx qb[39], qb[115], qb[40];
ccx qb[38], qb[114], qb[39];
ccx qb[37], qb[113], qb[38];
ccx qb[36], qb[112], qb[37];
ccx qb[35], qb[111], qb[36];
ccx qb[34], qb[110], qb[35];
ccx qb[33], qb[109], qb[34];
ccx qb[32], qb[108], qb[33];
ccx qb[31], qb[107], qb[32];
ccx qb[30], qb[106], qb[31];
ccx qb[29], qb[105], qb[30];
ccx qb[28], qb[104], qb[29];
ccx qb[27], qb[103], qb[28];
ccx qb[26], qb[102], qb[27];
ccx qb[25], qb[101], qb[26];
ccx qb[24], qb[100], qb[25];
ccx qb[23], qb[99], qb[24];
ccx qb[22], qb[98], qb[23];
ccx qb[21], qb[97], qb[22];
ccx qb[20], qb[96], qb[21];
ccx qb[19], qb[95], qb[20];
ccx qb[18], qb[94], qb[19];
ccx qb[17], qb[93], qb[18];
ccx qb[16], qb[92], qb[17];
ccx qb[15], qb[91], qb[16];
ccx qb[14], qb[90], qb[15];
ccx qb[13], qb[89], qb[14];
ccx qb[12], qb[88], qb[13];
ccx qb[11], qb[87], qb[12];
ccx qb[10], qb[86], qb[11];
ccx qb[9], qb[85], qb[10];
ccx qb[8], qb[84], qb[9];
ccx qb[7], qb[83], qb[8];
ccx qb[6], qb[82], qb[7];
ccx qb[5], qb[81], qb[6];
ccx qb[4], qb[80], qb[5];
ccx qb[3], qb[79], qb[4];
ccx qb[2], qb[78], qb[3];
ccx qb[1], qb[77], qb[2];
ccx qb[0], qb[76], qb[1];
ccx qb[74], qb[75], qb[0];
ccustom qb[73], qb[72];
ccx qb[74], qb[75], qb[0];
ccx qb[0], qb[76], qb[1];
ccx qb[1], qb[77], qb[2];
ccx qb[2], qb[78], qb[3];
ccx qb[3], qb[79], qb[4];
ccx qb[4], qb[80], qb[5];
ccx qb[5], qb[81], qb[6];
ccx qb[6], qb[82], qb[7];
ccx qb[7], qb[83], qb[8];
ccx qb[8], qb[84], qb[9];
ccx qb[9], qb[85], qb[10];
ccx qb[10], qb[86], qb[11];
ccx qb[11], qb[87], qb[12];
ccx qb[12], qb[88], qb[13];
ccx qb[13], qb[89], qb[14];
ccx qb[14], qb[90], qb[15];
ccx qb[15], qb[91], qb[16];
ccx qb[16], qb[92], qb[17];
ccx qb[17], qb[93], qb[18];
ccx qb[18], qb[94], qb[19];
ccx qb[19], qb[95], qb[20];
ccx qb[20], qb[96], qb[21];
ccx qb[21], qb[97], qb[22];
ccx qb[22], qb[98], qb[23];
ccx qb[23], qb[99], qb[24];
ccx qb[24], qb[100], qb[25];
ccx qb[25], qb[101], qb[26];
ccx qb[26], qb[102], qb[27];
ccx qb[27], qb[103], qb[28];
ccx qb[28], qb[104], qb[29];
ccx qb[29], qb[105], qb[30];
ccx qb[30], qb[106], qb[31];
ccx qb[31], qb[107], qb[32];
ccx qb[32], qb[108], qb[33];
ccx qb[33], qb[109], qb[34];
ccx qb[34], qb[110], qb[35];
ccx qb[35], qb[111], qb[36];
ccx qb[36], qb[112], qb[37];
ccx qb[37], qb[113], qb[38];
ccx qb[38], qb[114], qb[39];
ccx qb[39], qb[115], qb[40];
ccx qb[40], qb[116], qb[41];
ccx qb[41], qb[117], qb[42];
ccx qb[42], qb[118], qb[43];
ccx qb[43], qb[119], qb[44];
ccx qb[44], qb[120], qb[45];
ccx qb[45], qb[121], qb[46];
ccx qb[46], qb[122], qb[47];
ccx qb[47], qb[123], qb[48];
ccx qb[48], qb[124], qb[49];
ccx qb[49], qb[125], qb[50];
ccx qb[50], qb[126], qb[51];
ccx qb[51], qb[127], qb[52];
ccx qb[52], qb[128], qb[53];
ccx qb[53], qb[129], qb[54];
ccx qb[54], qb[130], qb[55];
ccx qb[55], qb[131], qb[56];
ccx qb[56], qb[132], qb[57];
ccx qb[57], qb[133], qb[58];
ccx qb[58], qb[134], qb[59];
ccx qb[59], qb[135], qb[60];
ccx qb[60], qb[136], qb[61];
ccx qb[61], qb[137], qb[62];
ccx qb[62], qb[138], qb[63];
ccx qb[63], qb[139], qb[64];
ccx qb[64], qb[140], qb[65];
ccx qb[65], qb[141], qb[66];
ccx qb[66], qb[142], qb[67];
ccx qb[67], qb[143], qb[68];
ccx qb[68], qb[144], qb[69];
ccx qb[69], qb[145], qb[70];
ccx qb[70], qb[146], qb[71];
cx qb[71], qb[73];
ccx qb[70], qb[146], qb[71];
ccx qb[69], qb[145], qb[70];
ccx qb[68], qb[144], qb[69];
ccx qb[67], qb[143], qb[68];
ccx qb[66], qb[142], qb[67];
ccx qb[65], qb[141], qb[66];
ccx qb[64], qb[140], qb[65];
ccx qb[63], qb[139], qb[64];
ccx qb[62], qb[138], qb[63];
ccx qb[61], qb[137], qb[62];
ccx qb[60], qb[136], qb[61];
ccx qb[59], qb[135], qb[60];
ccx qb[58], qb[134], qb[59];
ccx qb[57], qb[133], qb[58];
ccx qb[56], qb[132], qb[57];
ccx qb[55], qb[131], qb[56];
ccx qb[54], qb[130], qb[55];
ccx qb[53], qb[129], qb[54];
ccx qb[52], qb[128], qb[53];
ccx qb[51], qb[127], qb[52];
ccx qb[50], qb[126], qb[51];
ccx qb[49], qb[125], qb[50];
ccx qb[48], qb[124], qb[49];
ccx qb[47], qb[123], qb[48];
ccx qb[46], qb[122], qb[47];
ccx qb[45], qb[121], qb[46];
ccx qb[44], qb[120], qb[45];
ccx qb[43], qb[119], qb[44];
ccx qb[42], qb[118], qb[43];
ccx qb[41], qb[117], qb[42];
ccx qb[40], qb[116], qb[41];
ccx qb[39], qb[115], qb[40];
ccx qb[38], qb[114], qb[39];
ccx qb[37], qb[113], qb[38];
ccx qb[36], qb[112], qb[37];
ccx qb[35], qb[111], qb[36];
ccx qb[34], qb[110], qb[35];
ccx qb[33], qb[109], qb[34];
ccx qb[32], qb[108], qb[33];
ccx qb[31], qb[107], qb[32];
ccx qb[30], qb[106], qb[31];
ccx qb[29], qb[105], qb[30];
ccx qb[28], qb[104], qb[29];
ccx qb[27], qb[103], qb[28];
ccx qb[26], qb[102], qb[27];
ccx qb[25], qb[101], qb[26];
ccx qb[24], qb[100], qb[25];
ccx qb[23], qb[99], qb[24];
ccx qb[22], qb[98], qb[23];
ccx qb[21], qb[97], qb[22];
ccx qb[20], qb[96], qb[21];
ccx qb[19], qb[95], qb[20];
ccx qb[18], qb[94], qb[19];
ccx qb[17], qb[93], qb[18];
ccx qb[16], qb[92], qb[17];
ccx qb[15], qb[91], qb[16];
ccx qb[14], qb[90], qb[15];
ccx qb[13], qb[89], qb[14];
ccx qb[12], qb[88], qb[13];
ccx qb[11], qb[87], qb[12];
ccx qb[10], qb[86], qb[11];
ccx qb[9], qb[85], qb[10];
ccx qb[8], qb[84], qb[9];
ccx qb[7], qb[83], qb[8];
ccx qb[6], qb[82], qb[7];
ccx qb[5], qb[81], qb[6];
ccx qb[4], qb[80], qb[5];
ccx qb[3], qb[79], qb[4];
ccx qb[2], qb[78], qb[3];
ccx qb[1], qb[77], qb[2];
ccx qb[0], qb[76], qb[1];
ccx qb[74], qb[75], qb[0];
outcome[72] = measure qb[72];
} // post.spec

// outcome = measure qb;