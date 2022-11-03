#!/usr/bin/python3
import os
# Suggested Command: 2>&1 ./artifact_evaluation.py | tee /dev/tty > output.txt

timeout1 = 'XXX'
timeout2 = 'XXX'
timeout3 = 'XXX'
timeout4 = 'XXX'

for root, dirnames, filenames in sorted(os.walk('.')):
    if len(dirnames) == 0 and 'post.aut' in filenames:
        print(root, end=' & ', flush=True)# , dirnames, filenames)
        ###################################
        # Tool 1 - AutoQ w.r.t. permutation
        if timeout1 in root:
            ret = 124
        else:
            ret = os.system(f'VATA_PATH=/home/alan23273850/libvata/build/cli/vata timeout 720 ./permutation {root}/pre.aut {root}/circuit.qasm /tmp/automata.aut {root}/post.aut')
            ret = (ret >> 8) & 0xff
        if ret == 0:
            print('', end=' & ', flush=True)
        elif ret == 124:
            if ('Feynman' not in root) and ('RevLib' not in root):
                timeout1 = '/'.join(root.split('/')[:-1])
            print('\multicolumn{8}{c||}{TO}', end=' & ', flush=True)
        else:
            print('\multicolumn{8}{c||}{ERR}', end=' & ', flush=True)
        ###################################
        # Tool 2 - AutoQ w.r.t. composition
        if timeout2 in root:
            ret = 124
        else:
            ret = os.system(f'VATA_PATH=/home/alan23273850/libvata/build/cli/vata timeout 720 ./composition {root}/pre.aut {root}/circuit.qasm /tmp/automata.aut {root}/post.aut')
            ret = (ret >> 8) & 0xff
        if ret == 0:
            print('', end=' & ', flush=True)
        elif ret == 124:
            if ('Feynman' not in root) and ('RevLib' not in root):
                timeout2 = '/'.join(root.split('/')[:-1])
            print('\multicolumn{6}{c||}{TO}', end=' & ', flush=True)
        else:
            print('\multicolumn{6}{c||}{ERR}', end=' & ', flush=True)
        ###################################
        # Tool 3 - Qiskit
        if timeout3 in root:
            ret = 124
        else:
            ret = os.system(f'timeout 720 ./test_qiskit.py {root}')
            ret = (ret >> 8) & 0xff
        if ret == 0:
            print('', end=' & ', flush=True)
        elif ret == 124:
            if ('Feynman' not in root) and ('RevLib' not in root):
                timeout3 = '/'.join(root.split('/')[:-1])
            print('TO', end=' & ', flush=True)
        else:
            print('ERR', end=' & ', flush=True)
        ###################################
        # Tool 4 - Feynman
        if timeout4 in root:
            ret = 124
        else:
            ret = os.system(f'timeout 720 /home/alan23273850/feynman/feynver {root}/circuit.qc {root}/opt.qc')
            ret = (ret >> 8) & 0xff
        if ret == 124:
            if ('Feynman' not in root) and ('RevLib' not in root):
                timeout4 = '/'.join(root.split('/')[:-1])
            print('TO', flush=True)
        elif ret != 0:
            print('ERR', flush=True)
        ###################################