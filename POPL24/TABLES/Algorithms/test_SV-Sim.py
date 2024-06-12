#!/usr/bin/python3
import re, subprocess, sys

root = sys.argv[1]

with open(f'{root}/circuit.qasm', 'r') as file:
    data = file.read()
    match = re.search(r'qreg.*\[(\d+)\];', data)
    if match:
        q = int(match.group(1)) # Extract the number within the square brackets
if 'MOBV_reorder' in root:
    n = (q-1) // 2
    p = subprocess.run(f"python3 /home/alan23273850/SV-Sim/svsim/tool/svsim_qasm.py --input {root}/circuit.qasm --qubits '{[2*i for i in range(n)]}'", shell=True, capture_output=True, executable='/bin/bash')
elif 'GHZall' in root or 'H2' in root or 'HXH' in root:
    p = subprocess.run(f"python3 /home/alan23273850/SV-Sim/svsim/tool/svsim_qasm.py --input {root}/circuit.qasm --qubits '{list(range(q))}'", shell=True, capture_output=True, executable='/bin/bash')
elif 'MOGrover' in root:
    n = q // 3
    p = subprocess.run(f"python3 /home/alan23273850/SV-Sim/svsim/tool/svsim_qasm.py --input {root}/circuit.qasm --qubits '{list(range(n))}'", shell=True, capture_output=True, executable='/bin/bash')
elif 'MCToffoli' in root:
    n = q // 2
    p = subprocess.run(f"python3 /home/alan23273850/SV-Sim/svsim/tool/svsim_qasm.py --input {root}/circuit.qasm --qubits '{[0] + [2*i-1 for i in range(1, n+1)]}'", shell=True, capture_output=True, executable='/bin/bash')
else:
    p = subprocess.run(f"python3 /home/alan23273850/SV-Sim/svsim/tool/svsim_qasm.py --input {root}/circuit.qasm", shell=True, capture_output=True, executable='/bin/bash')
if p.returncode != 0:
    sys.exit(1)
# print(p.stdout.decode('utf-8').strip())
total_time = 0
for sub_time in re.findall(r"sim:(.*?) ms,", p.stdout.decode('utf-8').strip()):
    total_time += float(sub_time)
total_time /= 1000.0
# print(total_time)
if total_time >= 60:
    print('%dm%.fs' % (int(total_time // 60), total_time % 60), end='', flush=True)
elif total_time >= 10:
    print('%.fs' % total_time, end='', flush=True)
else:
    print('%.1fs' % total_time, end='', flush=True)