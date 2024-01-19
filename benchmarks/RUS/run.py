#!/usr/bin/python3
import os, re, subprocess
from ctypes import c_wchar_p
from multiprocessing import Manager, Process, Semaphore, Lock

# name = 'Table2.tex'
TIMEOUT = 30000000
NUM_OF_THREADS = 100
TA_EXE = '../../build/cli/autoq_cav24_concrete'

processes = []
def kill_processes():
    for pid in processes:
        if pid != 0: # This line is very important!!!!
            try:
                os.killpg(os.getpgid(pid), signal.SIGKILL)  # Send the signal to all the process groups
            except: # in case this handler is called multiple times
                pass
def handle_sigint(*_):
    kill_processes()
    exit(1)
import signal
signal.signal(signal.SIGINT, handle_sigint)

def TA(root, stR, semaphore, lock, counter):
    with semaphore:
        # p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        # q = p.stdout.splitlines()[0].decode('utf-8')
        # p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(pi/2\) |ry\(pi/2\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        # G = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'timeout {TIMEOUT} {TA_EXE} {root}/pre.spec {root}/circuit.qasm {root}/post.spec', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 0:
            stR.value = p.stdout.splitlines()[-1].decode('utf-8')
            # v = stR.value.split(' & ')
            # v[3], v[4] = v[4], v[3]
            # stR.value = ' & '.join(v)
        elif ret == 124:
            stR.value = '' #q + ' & ' + G + ' & ' + r'\multicolumn{6}{c}{\timeout}'
        else:
            stR.value = '' #q + ' & ' + G + ' & ' + r'\multicolumn{6}{c}{error}'
        # stR.value = ' & '.join(stR.value.split(' & ')[2:])
        lock.acquire()
        counter.value+=1; print(f'{counter.value}/--:', root + ' & ' + stR.value, )
        lock.release()

semaphore = Semaphore(NUM_OF_THREADS)
manager = Manager()
counter = manager.Value('i', 0)
process_pool_large = []
string_pool_large = []
lock = Lock()
for root, dirnames, filenames in sorted(os.walk('.')):
    # pattern = re.compile(r'^\.\/[0-9][0-9]')
    # if not pattern.match(root): continue
    if len(dirnames) == 0 and 'pre.spec' in filenames:
        process_pool_small = []
        string_pool_small = [manager.Value(c_wchar_p, root)]
        for func in (TA, ):
            semaphore.acquire(); semaphore.release()
            string_pool_small.append(manager.Value(c_wchar_p, ''))
            p = Process(target=func, args=(root, string_pool_small[-1], semaphore, lock, counter))
            p.start()
            processes.append(p.pid)
            process_pool_small.append(p)
        process_pool_large.append((len(process_pool_large), process_pool_small))
        string_pool_large.append(string_pool_small)

while len(process_pool_large) > 0:
    for i, pps in enumerate(process_pool_large):
        all_finish = True
        for p in pps[1]:
            if p.is_alive():
                all_finish = False
                break
        if all_finish:
            # print(' & '.join(map(lambda x: x.value, string_pool_large[pps[0]])), flush=True)
            process_pool_large.pop(i)
            break

# content = []
# for row in string_pool_large:
#     content.append(list(map(lambda x: x.value, row)))
# content.sort(key = lambda x: x[0])

# print(content)

# for i in range(len(content)):
#     content[i][0] = content[i][0].split('/')[-1]
#     content[i].insert(0, '')
#     content[i] = ' & '.join(content[i])

# contents = dict()
# contents['bvsingbench'] = ''.join(content[i] + '\\\\\n' for i in range(0, 5))
# contents['ghzmultbench'] = ''.join(content[i] + '\\\\\n' for i in range(5, 10))
# contents['ghzsingbench'] = ''.join(content[i] + '\\\\\n' for i in range(10, 15))
# contents['groversingbench'] = ''.join(content[i] + '\\\\\n' for i in range(15, 20))
# contents['hhbench'] = ''.join(content[i] + '\\\\\n' for i in range(20, 25))
# contents['hxhbench'] = ''.join(content[i] + '\\\\\n' for i in range(25, 30))
# contents['mctoffolibench'] = ''.join(content[i] + '\\\\\n' for i in range(30, 35))
# contents['bvmultbench'] = ''.join(content[i] + '\\\\\n' for i in range(35, 40))
# contents['grovermultbench'] = ''.join(content[i] + '\\\\\n' for i in range(40, 45))

# f = open(name, 'w')
# print(r'''\documentclass{article}

# \usepackage{booktabs}
# \usepackage{xspace}
# \usepackage{multicol}
# \usepackage{multirow}
# \usepackage{graphicx}
# \usepackage{colortbl}
# \usepackage{xcolor}

# % tool names
# \newcommand{\autoq}[0]{\textsc{AutoQ}\xspace}
# \newcommand{\sliqsim}[0]{\textsc{SliQSim}\xspace}
# \newcommand{\feynman}[0]{\textsc{Feynman}\xspace}
# \newcommand{\feynopt}[0]{\textsc{Feynopt}\xspace}
# \newcommand{\qcec}[0]{\textsc{Qcec}\xspace}
# \newcommand{\qbricks}[0]{\textsc{Qbricks}\xspace}
# \newcommand{\qiskit}[0]{\textsc{Qiskit}\xspace}
# \newcommand{\vata}[0]{\textsc{Vata}\xspace}
# \newcommand{\cta}[0]{\textsc{CTA}\xspace}
# \newcommand{\ta}[0]{\textsc{TA}\xspace}
# \newcommand{\correct}[0]{T\xspace}
# \newcommand{\wrong}[0]{F\xspace}
# \newcommand{\unknown}[0]{---\xspace}
# \newcommand{\nacell}[0]{\cellcolor{black!20}}
# \newcommand{\timeout}[0]{\nacell timeout}
# %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

# % benchmarks
# \newcommand{\bvsingbench}[0]{\small\textsc{BV-Sing}\xspace}
# \newcommand{\bvmultbench}[0]{\small\textsc{BV-All}\xspace}
# \newcommand{\ghzsingbench}[0]{\small\textsc{GHZ-Sing}\xspace}
# \newcommand{\ghzmultbench}[0]{\small\textsc{GHZ-All}\xspace}
# \newcommand{\groversingbench}[0]{\small\textsc{Grover-Sing}\xspace}
# \newcommand{\grovermultbench}[0]{\small\textsc{Grover-All}\xspace}
# \newcommand{\hhbench}[0]{\small\textsc{H2}\xspace}
# \newcommand{\hxhbench}[0]{\small\textsc{HXH}\xspace}
# \newcommand{\mctoffolibench}[0]{\small\textsc{MCToffoli}\xspace}
# \newcommand{\randombench}[0]{\textsc{Random}\xspace}
# \newcommand{\revlibbench}[0]{\textsc{RevLib}\xspace}
# \newcommand{\feynmanbench}[0]{\textsc{FeynmanBench}\xspace}
# %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

# \begin{document}\pagenumbering{gobble}

# %\scalebox{0.8}
# {\hspace{-100pt}
# \begin{tabular}{crrrrrrrrrrrrrrr}\hline
# \toprule
#   &&&& \multicolumn{6}{c}{\autoq-\cta} & \multicolumn{6}{c}{\autoq-\ta} \\
#   \cmidrule(lr){5-10} \cmidrule(lr){11-16}
#   & \multicolumn{1}{c}{$n$} & \multicolumn{1}{c}{\textbf{\#q}} & \multicolumn{1}{c}{\textbf{\#G}} & \multicolumn{2}{c}{\textbf{before}} & \multicolumn{2}{c}{\textbf{after}} & \multicolumn{1}{c}{\textbf{analysis}} & \multicolumn{1}{c}{$=$} & \multicolumn{2}{c}{\textbf{before}} & \multicolumn{2}{c}{\textbf{after}} & \multicolumn{1}{c}{\textbf{analysis}} & \multicolumn{1}{c}{$=$}\\
# \midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\bvsingbench}}
# ''' +
#   contents['bvsingbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\bvmultbench}}
# ''' +
#   contents['bvmultbench'] +
# r'''\midrule
# \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\ghzsingbench}}
# ''' +
#   contents['ghzsingbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\ghzmultbench}}
# ''' +
#   contents['ghzmultbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\groversingbench}}
# ''' +
#   contents['groversingbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\grovermultbench}}
# ''' +
#   contents['grovermultbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\hhbench}}
# ''' +
#   contents['hhbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\hxhbench}}
# ''' +
#   contents['hxhbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\mctoffolibench}}
# ''' +
#   contents['mctoffolibench'] +
# r'''\bottomrule
# \end{tabular}
# }

# \end{document}'''
# , file=f)

# f.close()

# os.system(f'pdflatex {name}')