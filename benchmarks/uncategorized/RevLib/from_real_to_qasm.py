#!/usr/bin/python3
import os
for real in os.listdir('.'):
    if not (os.path.isfile(os.path.join('.', real)) and real.endswith('.real')): continue
    qasm = open(real[:-5] + '.qasm', 'w')
    vars = dict()
    print('OPENQASM 2.0;', file=qasm)
    print('include "qelib1.inc";', file=qasm)
    for line in open(real, 'r').readlines():
        line = line.strip()
        if line.startswith('.numvars '):
            numvars = line.split()[1]
            print('qreg qubits[' + numvars + '];\n', file=qasm)
            continue
        if line.startswith('.variables '):
            variables = line.split()[1:]
            for i, var in enumerate(variables):
                vars[var] = str(i)
            continue
        if line.startswith('t1 '):
            variables = line.split()[1:]
            tmp = []
            for i, var in enumerate(variables):
                tmp.append('qubits[' + vars[var] + ']')
            tmp = ', '.join(tmp)
            print('x ' + tmp + ';', file=qasm)
            continue
        if line.startswith('t2 '):
            variables = line.split()[1:]
            tmp = []
            for i, var in enumerate(variables):
                tmp.append('qubits[' + vars[var] + ']')
            tmp = ', '.join(tmp)
            print('cx ' + tmp + ';', file=qasm)
            continue
        if line.startswith('t3 '):
            variables = line.split()[1:]
            tmp = []
            for i, var in enumerate(variables):
                tmp.append('qubits[' + vars[var] + ']')
            tmp = ', '.join(tmp)
            print('ccx ' + tmp + ';', file=qasm)
            continue
        if line.startswith('.') or line.startswith('#'):
            continue
        qasm.close()
        os.remove(qasm.name)
        break