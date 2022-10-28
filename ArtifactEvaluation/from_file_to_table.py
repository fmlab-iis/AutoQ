#!/usr/bin/python3
import sys
from qiskit import QuantumCircuit

print(r'\begin{table}')
print(r'\resizebox{\textwidth}{!}{')
print(r'\begin{tabular}{|c||c|c||c|c|c|c|c|c||c|c|c|c|c|c||c||c|}\hline')
current_benchmark = ''
lst = []
bm = {'BernsteinVazirani': 'Bernstein-Vazirani\'s algorithm with single oracle',  'Feynman': 'Feynman',
    'Grover': 'Grover\'s algorithm with single oracle', 'MCToffoli': 'Multi-controlled Toffoli gate',
    'MOGrover': 'Grover\'s algorithm with all possible oracles', 'Random': 'Random gates',
    'RevLib': 'RevLib'}

file = open(sys.argv[1], 'r')
for line in file.readlines():
    # If AutoQ-P timeout, print #q and #G from the qasm file.
    if r'\multicolumn{8}{c||}{TO}' in line:
        qc = QuantumCircuit.from_qasm_file(f"{line.split(' & ')[0]}/circuit.qasm")
        line = line.replace(r'\multicolumn{8}{c||}{TO}', f'{qc.num_qubits} & {qc.size()} & ' + r'\multicolumn{6}{c||}{\textbf{TO}}')
    else:
        line = ' & '.join(line.split(' & ')[:7] + [r'\textbf{' + line.split(' & ')[7] + '}'] + line.split(' & ')[8:])
        if r'\multicolumn{6}{c||}{TO}' not in line:
            line = ' & '.join(line.split(' & ')[:13] + [r'\textbf{' + line.split(' & ')[13] + '}'] + line.split(' & ')[14:])
    line = line.replace(r'\multicolumn{6}{c||}{TO}', r'\multicolumn{6}{c||}{\textbf{TO}}')
    line = ' & '.join(line.split(' & ')[:-2] + [r'\textbf{' + line.split(' & ')[-2] + '}'] + line.split(' & ')[-1:])
    line = line.strip().replace('_', r'\_').replace('^', r'\textasciicircum').replace('Equal (took ', '').replace('s)', 's')
    line = line.replace('TO', r'$>$ 12m')
    line = line.replace('ERR', 'ERROR')
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
        print(r'\hline\multicolumn{17}{|c|}{\textbf{' + bm[current_benchmark] + '}}', end='\\\\\hline\n')
        print('\\textbf{Problem} & \\textbf{\#q} & \\textbf{\#G} & \\textbf{P-sb} & \\textbf{P-sa} & \\textbf{P-tb} & \\textbf{P-ta} & \\textbf{P-exeT} & \\textbf{P-verT} \
& \\textbf{C-sb} & \\textbf{C-sa} & \\textbf{C-tb} & \\textbf{C-ta} & \\textbf{C-exeT} & \\textbf{C-verT} \
& \\textbf{qiskitT} & \\textbf{feynmanT}', end='\\\\\hline\n')
    if './Random/' in line:
        cols = line.split(' & ')
        t = 0; i = 15 if './Random/35' in line else 7
        # for i in (7, 8, 13, 14, 15, 16):
        cell = cols[i][8:-1]
        if cell.endswith('s'):
            cell = cell[:-1]
            if 'm' in cell:
                t += int(cell.split('m')[0]) * 60 + float(cell.split('m')[1])
            else:
                t += float(cell)
        lst.append((t, line))
    else:
        print('/'.join(line.split('/')[2:]), end='\\\\\hline\n')

print(r'\end{tabular}}')
print(r'\end{table}')