#!/usr/bin/python3
UseSliQSim = True
import concurrent, os
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
cont = False
for qasm in os.listdir('.'):
    if not (os.path.isfile(os.path.join('.', qasm)) and qasm.endswith('.qasm')): continue
    if qasm == 'sym9_317.qasm': cont = True
    if not cont: continue
    print(qasm + ' ', end='', flush=True)
    if os.fork() == 0:
        qc = QuantumCircuit.from_qasm_file(qasm)
        if not UseSliQSim: qc.save_statevector() # <--- should be disabled in SliQSimProvider!

        job = execute(qc, backend=simulator, shots=1, basis_gates=gates)
        try:
            result = job.result(timeout=600)
            # statevector = result.get_statevector(qc)
            # print(statevector)
            print(result.time_taken, end='', flush=True)
        except concurrent.futures._base.TimeoutError:
            print('TIMEOUT', end='', flush=True)
        os._exit(0)
    else:
        os.wait()
        print()