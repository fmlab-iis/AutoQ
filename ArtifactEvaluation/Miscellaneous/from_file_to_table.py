#!/usr/bin/python3
import sys
from qiskit import QuantumCircuit

print(r'\begin{tabular}{|c||c|c||c|c||c|c||c|c|}\hline')
current_benchmark = ''
# lst = []
bm = {'BernsteinVazirani': 'Bernstein-Vazirani\'s algorithm with one hidden string',  'Feynman': 'Feynman',
    'Grover': 'Grover\'s algorithm with one oracle', 'MCToffoli': 'Multi-controlled Toffoli gate',
    'MOGrover': 'Grover\'s algorithm with all possible oracles', 'Random': 'Random gates',
    'RevLib': 'RevLib'}

file = open(sys.argv[1], 'r')
for line in file.readlines():
    # Ignore the row where all tools are timeout or fail.
    line = line.replace('{AutoQ_composition}', '{2}')
    line = line.replace('{Feynman}', '{2}')
    if (r'\multicolumn{AutoQ_permutation}{c||}{TO} & \multicolumn{2}{c||}{TO}' in line) and line.endswith('\multicolumn{Feynman}{c|}{TO}\n'):
        continue
    # If AutoQ-P timeout, print #q and #G from the qasm file.
    if r'\multicolumn{AutoQ_permutation}{c||}{TO}' in line:
        qc = QuantumCircuit.from_qasm_file(f"{line.split(' & ')[0]}/bug.qasm")
        line = line.replace(r'\multicolumn{AutoQ_permutation}{c||}{TO}', f'{qc.num_qubits} & {qc.size()} & ' + r'\multicolumn{2}{c||}{\textbf{TO}}')
    # else:
    #     line = ' & '.join(line.split(' & ')[:3] + [r'\textbf{' + line.split(' & ')[3] + '}'] + line.split(' & ')[4:])
    #     if r'\multicolumn{6}{c||}{TO}' not in line:
    #         line = ' & '.join(line.split(' & ')[:5] + [r'\textbf{' + line.split(' & ')[5] + '}'] + line.split(' & ')[6:])
    # line = line.replace(r'\multicolumn{2}{c||}{TO}', r'\multicolumn{2}{c||}{\textbf{TO}}')
    # line = ' & '.join(line.split(' & ')[:-2] + [r'\textbf{' + line.split(' & ')[-2] + '}'] + line.split(' & ')[-1:])
    line = line.strip().replace('_', r'\_').replace('^', r'\textasciicircum')#.replace('Equal (took ', '').replace('s)', 's')
    line = line.replace('TO', r'$>$ 30m')
    line = line.replace('ERR', 'ERROR')
    # Process Feynman format
    last = line.split(' & ')[-2]
    if last.endswith('s'):
        last = float(last[:-1])
        if last >= 60:
            last = '%dm%.fs' % (int(last // 60), last % 60)
        elif last >= 10:
            last = '%.fs' % last
        else:
            last = '%.1fs' % last
        line = ' & '.join(line.split(' & ')[:-2]) + ' & ' + last + ' & ' + line.split(' & ')[-1]
    # if len(lst) > 0 and (line[:len('./Random/--')] not in lst[0][1]):
    #     lst.sort()
    #     print(lst[0][1].split('/')[2][:2] + '-min' + '/'.join(lst[0][1].split('/')[2:])[3:], end='\\\\\hline\n')
    #     print(lst[5][1].split('/')[2][:2] + '-med' + '/'.join(lst[5][1].split('/')[2:])[3:], end='\\\\\hline\n')
    #     print(lst[-1][1].split('/')[2][:2] + '-max' + '/'.join(lst[-1][1].split('/')[2:])[3:], end='\\\\\hline\n')
    #     lst = []
    if line.split('/')[1] != current_benchmark:
        current_benchmark = line.split('/')[1]
        print(r'\hline\multicolumn{9}{|c|}{\textbf{' + bm[current_benchmark] + '}}', end='\\\\\hline\n')
        print('\\textbf{Problem} & \\textbf{\#q} & \\textbf{\#G} & \\textbf{P-time} & \\textbf{P-bug} \
& \\textbf{C-time} & \\textbf{C-bug} \
& \\textbf{F-time} & \\textbf{F-bug}', end='\\\\\hline\n')
    print('/'.join(line.split('/')[2:]), end='\\\\\hline\n')

print(r'\end{tabular}')