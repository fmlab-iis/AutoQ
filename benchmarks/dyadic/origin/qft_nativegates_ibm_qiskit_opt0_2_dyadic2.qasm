// Benchmark was created by MQT Bench on 2023-06-29
// For more information about MQT Bench, please visit https://www.cda.cit.tum.de/mqtbench/
// MQT Bench version: v1.0.0
// Qiskit version: {'qiskit-terra': '0.24.1', 'qiskit-aer': '0.12.0', 'qiskit-ignis': None, 'qiskit-ibmq-provider': '0.20.2', 'qiskit': '0.43.1', 'qiskit-nature': '0.6.2', 'qiskit-finance': '0.3.4', 'qiskit-optimization': '0.5.0', 'qiskit-machine-learning': '0.6.1'}
// Used Gate Set: ['rz', 'rx(0.5*pi)', 'x', 'cx', 'measure']

OPENQASM 2.0;
include "qelib1.inc";
qreg q[2];


rz(pi/2) q[1];
rx(0.5*pi) q[1];
rz(pi/2) q[1];
rz(pi/4) q[1];
cx q[1],q[0];
rz(-pi/4) q[0];
cx q[1],q[0];
rz(pi/4) q[0];
rz(pi/2) q[0];
rx(0.5*pi) q[0];
rz(pi/2) q[0];
cx q[0],q[1];
cx q[1],q[0];
cx q[0],q[1];