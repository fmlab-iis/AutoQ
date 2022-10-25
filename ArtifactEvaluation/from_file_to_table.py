#!/usr/bin/python3
import sys
from qiskit import QuantumCircuit

print(r'\begin{table}')
print(r'\begin{tabular}{|c||c|c||c|c|c|c|c|c||c|c|c|c|c|c||c||c|}\hline')
current_benchmark = ''
lst = []

file = open(sys.argv[1], 'r')
for line in file.readlines():
    # If AutoQ-P timeout, print #q and #G from the qasm file.
    if r'\multicolumn{8}{c||}{TO}' in line:
        qc = QuantumCircuit.from_qasm_file(f"{line.split(' & ')[0]}/circuit.qasm")
        line = line.replace(r'\multicolumn{8}{c||}{TO}', f'{qc.num_qubits} & {qc.size()} & ' + r'\multicolumn{6}{c||}{TO}')
    line = line.strip().replace('_', r'\_').replace('^', r'\textasciicircum').replace('Equal (took ', '').replace('s)', 's')
    # Process Feynman format
    last = line.split(' & ')[-1]
    if last.endswith('s'):
        last = float(last[:-1])
        if last >= 60:
            last = '%dm%.fs' % (int(last // 60), last % 60)
        elif last >= 10:
            last = '%.fs' % last
        else:
            last = '%.1fs' % last
        line = ' & '.join(line.split(' & ')[:-1]) + ' & ' + last
    if len(lst) > 0 and (line[:len('./Random/--')] not in lst[0][1]):
        lst.sort()
        print(lst[0][1].split('/')[2][:2] + '-min' + '/'.join(lst[0][1].split('/')[2:])[3:], end='\\\\\hline\n')
        print(lst[5][1].split('/')[2][:2] + '-med' + '/'.join(lst[5][1].split('/')[2:])[3:], end='\\\\\hline\n')
        print(lst[-1][1].split('/')[2][:2] + '-max' + '/'.join(lst[-1][1].split('/')[2:])[3:], end='\\\\\hline\n')
        lst = []
    if line.split('/')[1] != current_benchmark:
        current_benchmark = line.split('/')[1]
        print(r'\hline\multicolumn{17}{|c|}{\textbf{' + current_benchmark + '}}', end='\\\\\hline\n')
        print('\\textbf{Problem} & \\textbf{\#q} & \\textbf{\#G} & \\textbf{P-sb} & \\textbf{P-sa} & \\textbf{P-tb} & \\textbf{P-ta} & \\textbf{P-simT} & \\textbf{P-verT} \
& \\textbf{C-sb} & \\textbf{C-sa} & \\textbf{C-tb} & \\textbf{C-ta} & \\textbf{C-simT} & \\textbf{C-verT} \
& \\textbf{qiskitT} & \\textbf{feynmanT}', end='\\\\\hline\n')
    if './Random/' in line:
        cols = line.split(' & ')
        t = 0; i = 15 if './Random/35' in line else 7
        # for i in (7, 8, 13, 14, 15, 16):
        if cols[i].endswith('s'):
            cols[i] = cols[i][:-1]
            if 'm' in cols[i]:
                t += int(cols[i].split('m')[0]) * 60 + float(cols[i].split('m')[1])
            else:
                t += float(cols[i])
        lst.append((t, line))
    else:
        print('/'.join(line.split('/')[2:]), end='\\\\\hline\n')

print(r'\end{tabular}')
print(r'\end{table}')