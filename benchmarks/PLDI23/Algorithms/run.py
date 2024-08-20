#!/usr/bin/python3
import os, subprocess
from ctypes import c_wchar_p
from multiprocessing import Manager, Process, Semaphore, Lock

name = 'Table2.tex'
TIMEOUT = 720
NUM_OF_THREADS = 4 #80

def AutoQ_permutation(root, stR, semaphore, lock, counter):
    with semaphore:
        another = root.replace('.', '').replace('/', '') + 'permutation'
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(pi/2\) |ry\(pi/2\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'VATA_PATH=../vata timeout {TIMEOUT} ./permutation_af2b8852fd02393800ca61a25087b4f71559c2cd {root}/pre.aut {root}/circuit.qasm /tmp/{another}.aut {root}/post.aut', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 0:
            stR.value = p.stdout.splitlines()[0].decode('utf-8')
        elif ret == 124:
            stR.value = q + ' & ' + G + ' & ' + r'\multicolumn{6}{c}{\timeout}'
        else:
            stR.value = q + ' & ' + G + ' & ' + r'\multicolumn{6}{c}{error}'
        if os.path.exists(f'/tmp/{another}.aut'):
            os.system(f'rm /tmp/{another}.aut')
        lock.acquire()
        counter.value+=1; print(counter.value, '/ 80')
        lock.release()
def AutoQ_composition(root, stR, semaphore, lock, counter):
    with semaphore:
        another = root.replace('.', '').replace('/', '') + 'composition'
        p = subprocess.run(f'VATA_PATH=../vata timeout {TIMEOUT} ./composition_3e0cd35efc2b8963615c9ebff543c2d70e63df14 {root}/pre.aut {root}/circuit.qasm /tmp/{another}.aut {root}/post.aut', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 0:
            stR.value = p.stdout.splitlines()[0].decode('utf-8')
        elif ret == 124:
            stR.value = r'\multicolumn{6}{c}{\timeout}'
        else:
            stR.value = r'\multicolumn{6}{c}{error}'
        if os.path.exists(f'/tmp/{another}.aut'):
            os.system(f'rm /tmp/{another}.aut')
        lock.acquire()
        counter.value+=1; print(counter.value, '/ 80')
        lock.release()
def SliQSim(root, stR, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'timeout {TIMEOUT} ./test_SliQSim.py {root}', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 124:
            stR.value = 'timeout'
        elif ret != 0:
            stR.value = 'error'
        else:
            stR.value = p.stdout.splitlines()[0].decode('utf-8').strip()
        lock.acquire()
        counter.value+=1; print(counter.value, '/ 80')
        lock.release()
def Feynman(root, stR, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'timeout {TIMEOUT} ../feynver {root}/circuit.qc {root}/opt.qc', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 124:
            stR.value = r'\multicolumn{2}{c}{\timeout}'
        elif ret != 0:
            stR.value = r'\multicolumn{2}{c}{error}'
        else:
            tmp = p.stdout.splitlines()[0].decode('utf-8')
            ts = tmp.split(' (took ')[1].split(')')[0]
            time_in_seconds = float(ts[:-1])
            rounded_time = round(time_in_seconds, 1)
            ts = f"{rounded_time}s"
            stR.value = tmp.split(' (took ')[0] + ' & ' + ts
        lock.acquire()
        counter.value+=1; print(counter.value, '/ 80')
        lock.release()

semaphore = Semaphore(NUM_OF_THREADS)
manager = Manager()
counter = manager.Value('i', 0)
process_pool_large = []
string_pool_large = []
lock = Lock()
for root, dirnames, filenames in sorted(os.walk('.')):
    if len(dirnames) == 0 and 'post.aut' in filenames:
        process_pool_small = []
        string_pool_small = [manager.Value(c_wchar_p, root)]
        for func in (AutoQ_permutation, AutoQ_composition, SliQSim, Feynman):
            semaphore.acquire(); semaphore.release()
            string_pool_small.append(manager.Value(c_wchar_p, ''))
            p = Process(target=func, args=(root, string_pool_small[-1], semaphore, lock, counter))
            p.start()
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
            print(' & '.join(map(lambda x: x.value, string_pool_large[pps[0]])), flush=True)
            process_pool_large.pop(i)
            break

os.system('pkill -9 -f permutation; pkill -9 -f composition; pkill -9 -f SliQSim; pkill -9 -f feynver; pkill -9 -f autoq; pkill -9 -f vata')

content = []
for row in string_pool_large:
    content.append(list(map(lambda x: x.value, row)))
content.sort(key = lambda x: x[0])

# print(content)

for i in range(len(content)):
    content[i][0] = content[i][0].split('/')[-1]
    content[i].insert(0, '')
    content[i] = ' & '.join(content[i])

f = open(name, 'w')
print(r'''\documentclass{article}

\usepackage{booktabs}
\usepackage{xspace}
\usepackage{multicol}
\usepackage{multirow}
\usepackage{graphicx}
\usepackage{colortbl}
\usepackage{xcolor}

% tool names
\newcommand{\autoq}[0]{\textsc{AutoQ}\xspace}
\newcommand{\sliqsim}[0]{\textsc{SliQSim}\xspace}
\newcommand{\feynman}[0]{\textsc{Feynman}\xspace}
\newcommand{\feynopt}[0]{\textsc{Feynopt}\xspace}
\newcommand{\qcec}[0]{\textsc{Qcec}\xspace}
\newcommand{\qbricks}[0]{\textsc{Qbricks}\xspace}
\newcommand{\qiskit}[0]{\textsc{Qiskit}\xspace}
\newcommand{\vata}[0]{\textsc{Vata}\xspace}
\newcommand{\permutation}[0]{\textsc{Hybrid}\xspace}
\newcommand{\composition}[0]{\textsc{Composition}\xspace}
\newcommand{\correct}[0]{T\xspace}
\newcommand{\wrong}[0]{F\xspace}
\newcommand{\unknown}[0]{---\xspace}
\newcommand{\nacell}[0]{\cellcolor{black!20}}
\newcommand{\timeout}[0]{\nacell timeout}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% benchmarks
\newcommand{\bvbench}[0]{\small\textsc{BV}\xspace}
\newcommand{\groversingbench}[0]{\small\textsc{Grover-Sing}\xspace}
\newcommand{\grovermultbench}[0]{\small\textsc{Grover-All}\xspace}
\newcommand{\mctoffolibench}[0]{\small\textsc{MCToffoli}\xspace}
\newcommand{\randombench}[0]{\textsc{Random}\xspace}
\newcommand{\revlibbench}[0]{\textsc{RevLib}\xspace}
\newcommand{\feynmanbench}[0]{\textsc{FeynmanBench}\xspace}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\scalebox{0.8}{\hspace{-150pt}
\begin{tabular}{crrrrrrrrrrrrrrrrcr}\hline
\toprule
  &&&& \multicolumn{6}{c}{\autoq-\permutation} & \multicolumn{6}{c}{\autoq-\composition}& \multicolumn{1}{c}{\sliqsim}& \multicolumn{2}{c}{\feynman} \\
  \cmidrule(lr){5-10} \cmidrule(lr){11-16} \cmidrule(lr){17-17} \cmidrule(lr){18-19}
  & \multicolumn{1}{c}{$n$} & \multicolumn{1}{c}{\textbf{\#q}} & \multicolumn{1}{c}{\textbf{\#G}} & \multicolumn{2}{c}{\textbf{before}} & \multicolumn{2}{c}{\textbf{after}} & \multicolumn{1}{c}{\textbf{analysis}} & \multicolumn{1}{c}{$=$} & \multicolumn{2}{c}{\textbf{before}} & \multicolumn{2}{c}{\textbf{after}} & \multicolumn{1}{c}{\textbf{analysis}} & \multicolumn{1}{c}{$=$} & \multicolumn{1}{c}{\textbf{time}} & \multicolumn{1}{c}{\textbf{verdict}} & \multicolumn{1}{c}{\textbf{time}}\\
\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\bvbench}}
''' +
  content[0] + '\\\\\n' +
  content[1] + '\\\\\n' +
  content[2] + '\\\\\n' +
  content[3] + '\\\\\n' +
  content[4] + '\\\\\n' +
r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\groversingbench}}
''' +
  content[5] + '\\\\\n' +
  content[6] + '\\\\\n' +
  content[7] + '\\\\\n' +
  content[8] + '\\\\\n' +
  content[9] + '\\\\\n' +
r'''\midrule
\multirow{ 5}{*}{\rotatebox[origin=c]{90}{\mctoffolibench}}
''' +
  content[10] + '\\\\\n' +
  content[11] + '\\\\\n' +
  content[12] + '\\\\\n' +
  content[13] + '\\\\\n' +
  content[14] + '\\\\\n' +
r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\grovermultbench}}
''' +
  content[15] + '\\\\\n' +
  content[16] + '\\\\\n' +
  content[17] + '\\\\\n' +
  content[18] + '\\\\\n' +
  content[19] + '\\\\\n' +
r'''\bottomrule
\end{tabular}
}

\end{document}'''
, file=f)

f.close()

os.system(f'pdflatex {name}')