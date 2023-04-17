#!/usr/bin/python3
import os, re, subprocess, sys

root = sys.argv[1]

if 'MCToffoli' in root:
    n = int(re.findall('[0-9]+', root)[-1]) # half of the number of qubits
    with open(f'{root}/circuit.qasm', 'r') as file:
        data = file.read()
    total_time = 0
    p2n = pow(2, n)
    root2 = root[len('./'):]
    os.system(f'mkdir -p /tmp/{root2}')
    for i in range(p2n):
        tmpstr = ''
        if (i >> 0) & 1:
            tmpstr += f'x qubits[{0}]; '
        for j in range(1, n):
            if (i >> j) & 1:
                tmpstr += f'x qubits[{2*j-1}]; '
        qc = re.sub(r'qreg qubits\[\d+\];', f'\g<0> {tmpstr}', data)
        text_file = open(f'/tmp/{root2}/circuit.qasm', "w")
        text_file.write(qc)
        text_file.close()
        p = subprocess.run(f'./SliQSim --sim_qasm /tmp/{root2}/circuit.qasm --type 1 --print_info', shell=True, capture_output=True, executable='/bin/bash')
        # Assume the 1st line format - Runtime: 0.013964 seconds
        tmp = list(map(lambda x: x.decode('utf-8'), p.stdout.splitlines()))[0].strip()
        total_time += float(tmp.split(' ')[1])
    os.system(f'rm -r /tmp/{root2}')
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
    root2 = root[len('./'):]
    os.system(f'mkdir -p /tmp/{root2}')
    for i in range(p2n):
        tmpstr = ''
        for j in range(n):
            if (i >> j) & 1:
                tmpstr += f'x qubits[{j}]; '
        qc = re.sub(r'qreg qubits\[\d+\];', f'\g<0> {tmpstr}', data)
        text_file = open(f'/tmp/{root2}/circuit.qasm', "w")
        text_file.write(qc)
        text_file.close()
        p = subprocess.run(f'./SliQSim --sim_qasm /tmp/{root2}/circuit.qasm --type 1 --print_info', shell=True, capture_output=True, executable='/bin/bash')
        # Assume the 1st line format - Runtime: 0.013964 seconds
        tmp = list(map(lambda x: x.decode('utf-8'), p.stdout.splitlines()))[0].strip()
        total_time += float(tmp.split(' ')[1])
    os.system(f'rm -r /tmp/{root2}')
    if total_time >= 60:
        print('%dm%.fs' % (int(total_time // 60), total_time % 60), end='', flush=True)
    elif total_time >= 10:
        print('%.fs' % total_time, end='', flush=True)
    else:
        print('%.1fs' % total_time, end='', flush=True)
else:
    p = subprocess.run(f'./SliQSim --sim_qasm {root}/circuit.qasm --type 1 --print_info', shell=True, capture_output=True, executable='/bin/bash')
    # Assume the 1st line format - Runtime: 0.013964 seconds
    tmp = list(map(lambda x: x.decode('utf-8'), p.stdout.splitlines()))[0].strip()
    total_time = float(tmp.split(' ')[1])
    if total_time >= 60:
        print('%dm%.fs' % (int(total_time // 60), total_time % 60), end='', flush=True)
    elif total_time >= 10:
        print('%.fs' % total_time, end='', flush=True)
    else:
        print('%.1fs' % total_time, end='', flush=True)