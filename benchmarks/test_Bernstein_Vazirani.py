#!/usr/bin/python3

from qiskit import QuantumCircuit
from qiskit.providers.aer import Aer

for i in range(1, 101):
    text_file = open(f'Bernstein_Vazirani_{i:03}.qasm', "r")
    data = text_file.read()
    text_file.close()
    qc = QuantumCircuit.from_qasm_str(data)
    qc.save_statevector()

    simulator = Aer.get_backend('aer_simulator')
    job = simulator.run(qc, shots=1)
    result = job.result()
    # statevector = result.get_statevector(qc)
    # print(statevector)
    print(i, result.time_taken)