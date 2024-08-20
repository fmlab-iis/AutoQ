#!/usr/bin/python3
import os, subprocess, time
from ctypes import c_wchar_p
from multiprocessing import Manager, Process, Semaphore, Lock

name = 'Table3.tex'
TIMEOUT = float(1800)
NUM_OF_THREADS = 159

def AutoQ_permutation(root, stR, semaphore, lock, counter):
    with semaphore:
        another = root.replace('.', '').replace('/', '') + 'permutation'
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/bug.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(pi/2\) |ry\(pi/2\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/bug.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'VATA_PATH=../vata timeout {TIMEOUT} ./find_bug_e1dc5b30f115d44ffb69573fee29532e81626f39 {root}/bug.qasm {root}/spec.qasm {root}/post1.aut {root}/post2.aut', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 0:
            stR.value = p.stdout.splitlines()[0].decode('utf-8')
        elif ret == 124:
            stR.value = r'\multicolumn{2}{c}{\timeout}'
        else:
            stR.value = r'\multicolumn{2}{c}{error}'
        stR.value = q + ' & ' + G + ' & ' + stR.value
        if os.path.exists(f'/tmp/{another}.aut'):
            os.system(f'rm /tmp/{another}.aut')
        lock.acquire()
        counter.value+=1; print(counter.value, '/ 159')
        lock.release()
def Feynman(root, stR, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'timeout {TIMEOUT} ../feynver {root}/spec.qc {root}/bug.qc', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 124:
            stR.value = r'\multicolumn{2}{c}{\timeout}'
        elif ret != 0:
            stR.value = r'\multicolumn{2}{c}{error}'
        else:
            tmp = p.stdout.splitlines()[0].decode('utf-8')
            status = tmp.split(' (took ')[0]
            if status == 'Inconclusive':
                status = r'\unknown'
            elif status == 'Not equal':
                status = r'\correct'
            elif status == 'Equal':
                status = r'\wrong'
            else:
                stR.value = r'\multicolumn{2}{c}{error}'
                return
            ts = tmp.split(' (took ')[1].split(')')[0]
            time_in_seconds = float(ts[:-1])
            rounded_time = round(time_in_seconds, 1)
            if rounded_time >= 60:
                rounded_time = f"{rounded_time // 60:.0f}m{rounded_time % 60:.0f}"
            if status == r'\unknown':
                stR.value = r'\nacell ' + str(rounded_time) + 's & ' + r'\nacell ' + status
            elif status == r'\wrong':
                stR.value = r'\wrongcell ' + str(rounded_time) + 's & ' + r'\wrongcell ' + status
            else:
                stR.value = str(rounded_time) + 's & ' + status
        lock.acquire()
        counter.value+=1; print(counter.value, '/ 159')
        lock.release()
def QCEC(root, stR, semaphore, lock, counter):
    with semaphore:
        start_time = time.monotonic()
        p = subprocess.run(f'timeout {TIMEOUT} /usr/bin/time -f "%U+%S" ./test_QCEC.py {root}', shell=True, capture_output=True, executable='/bin/bash')
        end_time = time.monotonic()
        ret = p.returncode
        if ret == 124:
            stR.value = r'\multicolumn{2}{c}{\timeout}'
        elif ret != 0:
            stR.value = r'\nacell ' + f"{end_time - start_time:.1f}s" + ' & ' + r'\nacell \unknown'
        else:
            status = p.stdout.splitlines()[0].decode('utf-8')
            if status.startswith('probably_'):
                status = r'\unknown'
            elif status == 'not_equivalent':
                status = r'\correct'
            elif status == 'equivalent':
                status = r'\wrong'
            else:
                stR.value = r'\multicolumn{2}{c}{error}'
                return
            rounded_time = round(sum(map(float, p.stderr.splitlines()[-1].decode('utf-8').split('+'))), 1)
            if rounded_time >= 60:
                rounded_time = f"{rounded_time // 60:.0f}m{rounded_time % 60:.0f}"
            if status == r'\unknown':
                stR.value = r'\nacell ' + str(rounded_time) + 's & ' + r'\nacell ' + status
            elif status == r'\wrong':
                stR.value = r'\wrongcell ' + str(rounded_time) + 's & ' + r'\wrongcell ' + status
            else:
                stR.value = str(rounded_time) + 's & ' + status
        lock.acquire()
        counter.value+=1; print(counter.value, '/ 159')
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
        for func in (AutoQ_permutation, Feynman, QCEC):
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
            print(' & '.join(map(lambda x: x.value, string_pool_large[pps[0]])))
            process_pool_large.pop(i)
            break

os.system('pkill -9 -f find_bug; pkill -9 -f feynver; pkill -9 -f autoq; pkill -9 -f vata')

content = []
for row in string_pool_large:
    content.append(list(map(lambda x: x.value, row)))
content.sort(key = lambda x: x[0])

# print(content)

for i in range(len(content)):
    content[i][0] = content[i][0].split('/')[-1]
    # content[i].insert(0, '')
    content[i] = ' & '.join(content[i])
    content[i] = content[i].replace('_', r'\_').replace('^', r'\textasciicircum')

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
\newcommand{\wrongcell}[0]{\cellcolor{red!20}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% benchmarks
\newcommand{\bvbench}[0]{\small\textsc{BV}\xspace}
\newcommand{\groversingbench}[0]{\small\textsc{Grover-Sing}\xspace}
\newcommand{\grovermultbench}[0]{\small\textsc{Grover-All}\xspace}
\newcommand{\mctoffolibench}[0]{\small\textsc{MCToffoli}\xspace}
\newcommand{\randombench}[0]{\small\textsc{Random}\xspace}
\newcommand{\revlibbench}[0]{\small\textsc{RevLib}\xspace}
\newcommand{\feynmanbench}[0]{\small\textsc{FeynmanBench}\xspace}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\scalebox{0.7}{\hspace{-150pt}
\begin{tabular}{clrrrcrcrclrrrcrcrc}
\cmidrule[\heavyrulewidth](lr){1-10}
\cmidrule[\heavyrulewidth](lr){11-19}
  &&&& \multicolumn{2}{c}{\autoq} & \multicolumn{2}{c}{\feynman}& \multicolumn{2}{c}{\qcec}&   & &&\multicolumn{2}{c}{\autoq} & \multicolumn{2}{c}{\feynman}& \multicolumn{2}{c}{\qcec} \\
  \cmidrule(lr){5-6} \cmidrule(lr){7-8} \cmidrule(lr){9-10}
  \cmidrule(lr){14-15} \cmidrule(lr){16-17} \cmidrule(lr){18-19}
  & \multicolumn{1}{c}{\textbf{circuit}} & \multicolumn{1}{c}{\textbf{\#q}} & \multicolumn{1}{c}{\textbf{\#G}} & \multicolumn{1}{c}{\textbf{time}} & \textbf{iter} & \multicolumn{1}{c}{\textbf{time}} & \textbf{bug?} & \multicolumn{1}{c}{\textbf{time}} & \textbf{bug?}
  &\multicolumn{1}{c}{\textbf{circuit}} & \multicolumn{1}{c}{\textbf{\#q}} & \multicolumn{1}{c}{\textbf{\#G}} & \multicolumn{1}{c}{\textbf{time}} & \textbf{iter} & \multicolumn{1}{c}{\textbf{time}} & \textbf{bug?} & \multicolumn{1}{c}{\textbf{time}} & \textbf{bug?} \\

\cmidrule(lr){1-10}\cmidrule(lr){11-19}

  \multirow{ 6}{*}{\rotatebox[origin=c]{90}{\feynmanbench}}
''' +
'& ' + content[0] + ' & ' + content[5] + '\\\\\n' +
'& ' + content[1] + ' & ' + content[6] + '\\\\\n' +
'& ' + content[2] + ' & ' + content[7] + '\\\\\n' +
'& ' + content[3] + ' & ' + content[8] + '\\\\\n' +
'& ' + content[4] + ' & ' + content[10] + '\\\\\n' +
'& ' + content[9] + ' & ' + content[11] + '\\\\\n' +
r'''\cmidrule(lr){1-10}\cmidrule(lr){11-19}

\multirow{ 10}{*}{\rotatebox[origin=c]{90}{\randombench}}
''' +
'& ' + content[12] + ' & ' + content[22] + '\\\\\n' +
'& ' + content[13] + ' & ' + content[23] + '\\\\\n' +
'& ' + content[14] + ' & ' + content[24] + '\\\\\n' +
'& ' + content[15] + ' & ' + content[25] + '\\\\\n' +
'& ' + content[16] + ' & ' + content[26] + '\\\\\n' +
'& ' + content[17] + ' & ' + content[27] + '\\\\\n' +
'& ' + content[18] + ' & ' + content[28] + '\\\\\n' +
'& ' + content[19] + ' & ' + content[29] + '\\\\\n' +
'& ' + content[20] + ' & ' + content[30] + '\\\\\n' +
'& ' + content[21] + ' & ' + content[31] + '\\\\\n' +
r'''\cmidrule(lr){1-10}\cmidrule(lr){11-19}

\multirow{ 11}{*}{\rotatebox[origin=c]{90}{\revlibbench}}
''' +
'& ' + content[32] + ' & ' + content[47] + '\\\\\n' +
'& ' + content[33] + ' & ' + content[48] + '\\\\\n' +
'& ' + content[34] + ' & ' + content[49] + '\\\\\n' +
'& ' + content[35] + ' & ' + content[50] + '\\\\\n' +
'& ' + content[36] + ' & ' + content[51] + '\\\\\n' +
'& ' + content[37] + ' & ' + content[52] + '\\\\\n' +
'& ' + content[38] + ' & ' + content[41] + '\\\\\n' +
'& ' + content[39] + ' & ' + content[42] + '\\\\\n' +
'& ' + content[40] + ' & ' + content[43] + '\\\\\n' +
'& ' + content[45] + ' & ' + content[44] + '\\\\\n' +
'& ' + content[46] + '\\\\\n' +
r'''\cmidrule[\heavyrulewidth](lr){1-10}
\cmidrule[\heavyrulewidth](lr){11-19}
\end{tabular}
}

\end{document}'''
, file=f)

f.close()

os.system(f'pdflatex {name}')
