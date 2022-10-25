#!/usr/bin/python3
import re, sys

from qiskit import QuantumCircuit, execute
from qiskit.providers.aer import Aer
aer = Aer.get_backend('aer_simulator')
aer_gates = aer.configuration().basis_gates
aer_gates.remove('rx')
aer_gates.remove('ry')
aer_gates.append('rx(pi/2)')
aer_gates.append('ry(pi/2)')

root = sys.argv[1]

if 'MCToffoli' in root:
    N = int(re.findall('[0-9]+', root)[-1]) * 2 # number of qubits
    with open(f'{root}/circuit.qasm', 'r') as file:
        data = file.read()
    total_time = 0
    p2N = pow(2, N)
    for i in range(p2N):
        tmpstr = ''
        for j in range(N):
            if (i >> j) & 1:
                tmpstr += f'x qubits[{j}]; '
        qc = re.sub(r'qreg qubits\[\d+\];', f'\g<0> {tmpstr}', data)
        qc = QuantumCircuit.from_qasm_str(qc)
        qc.save_statevector() # <--- should be disabled in SliQSimProvider!
        result = execute(qc, backend=aer, shots=1, basis_gates=aer_gates).result()
        # statevector = result.get_statevector(qc)
        # print(statevector)
        total_time += result.time_taken
    if total_time >= 60:
        print('%dm%.fs' % (int(total_time // 60), total_time % 60), end='', flush=True)
    elif total_time >= 10:
        print('%.fs' % total_time, end='', flush=True)
    else:
        print('%.1fs' % total_time, end='', flush=True)
elif 'MOGrover' in root:
    n = int(re.findall('[0-9]+', root)[-1])
    with open(f'{root}/circuit.qasm', 'r') as file:
        data = file.read()
    total_time = 0
    p2n = pow(2, n)
    for i in range(p2n):
        tmpstr = ''
        for j in range(n):
            if (i >> j) & 1:
                tmpstr += f'x qubits[{j}]; '
        qc = re.sub(r'qreg qubits\[\d+\];', f'\g<0> {tmpstr}', data)
        qc = QuantumCircuit.from_qasm_str(qc)
        qc.save_statevector() # <--- should be disabled in SliQSimProvider!
        result = execute(qc, backend=aer, shots=1, basis_gates=aer_gates).result()
        # statevector = result.get_statevector(qc)
        # print(statevector)
        total_time += result.time_taken
    if total_time >= 60:
        print('%dm%.fs' % (int(total_time // 60), total_time % 60), end='', flush=True)
    elif total_time >= 10:
        print('%.fs' % total_time, end='', flush=True)
    else:
        print('%.1fs' % total_time, end='', flush=True)
else:
    qc = QuantumCircuit.from_qasm_file(f'{root}/circuit.qasm')
    qc.save_statevector() # <--- should be disabled in SliQSimProvider!
    result = execute(qc, backend=aer, shots=1, basis_gates=aer_gates).result()
    # statevector = result.get_statevector(qc)
    # print(statevector)
    if result.time_taken >= 60:
        print('%dm%.fs' % (int(result.time_taken // 60), result.time_taken % 60), end='', flush=True)
    elif result.time_taken >= 10:
        print('%.fs' % result.time_taken, end='', flush=True)
    else:
        print('%.1fs' % result.time_taken, end='', flush=True)