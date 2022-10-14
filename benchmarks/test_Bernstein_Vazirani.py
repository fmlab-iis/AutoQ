#!/usr/bin/python3
UseSliQSim = False
from qiskit import QuantumCircuit, execute
from qiskit.providers.aer import Aer
if UseSliQSim:
    from qiskit_sliqsim_provider import SliQSimProvider # <--- import the provider
    simulator = SliQSimProvider().get_backend('strong_simulator') # <--- use the provider
else: simulator = Aer.get_backend('aer_simulator')
gates = simulator.configuration().basis_gates
gates.remove('rx')
gates.remove('ry')
gates.append('rx(pi/2)')
gates.append('ry(pi/2)')

# 正確答案的順序是由上填到下，1010...
for i in range(1, 101):
    qc = QuantumCircuit.from_qasm_file(f'Bernstein_Vazirani_{i:03}.qasm')
    if not UseSliQSim: qc.save_statevector() # <--- should be disabled in SliQSimProvider!

    job = execute(qc, backend=simulator, shots=1, basis_gates=gates)
    result = job.result()
    # statevector = result.get_statevector(qc)
    # print(statevector)
    print(i, result.time_taken)