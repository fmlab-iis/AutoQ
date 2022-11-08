#!/usr/bin/python3
import os

for root, dirnames, filenames in sorted(os.walk('.')):
    if len(dirnames) == 0 and 'circuit.qasm' in filenames:
        os.system(f'/home/alan23273850/feynman/feynopt {root}/circuit.qasm > {root}/opt.qasm')
    # if len(dirnames) == 0 and 'circuit.qc' in filenames:
    #     os.system(f'/home/alan23273850/feynman/feynopt {root}/circuit.qc > {root}/opt.qc')
