#!/usr/bin/python3
import os, re, subprocess
from ctypes import c_wchar_p
from multiprocessing import Manager, Process, Semaphore, Lock

name = 'flip.tex'
TIMEOUT = 86400
NUM_OF_CASES = 30
NUM_OF_THREADS = NUM_OF_CASES
CTA_EXE = 'autoq'
#TA_EXE = '../../autoq_pldi_ta'
#VATA_EXE = '../../vata'

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

def CTA(root, stR, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root} | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        cmd = f'timeout {TIMEOUT} {CTA_EXE} -t eq {root} ../origin/{root.split("qasm", 1)[0] + "qasm"} --latex'#; print(cmd)
        p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 0:
            stR.value = p.stdout.splitlines()[0].decode('utf-8')
            # v = stR.value.split(' & ')
            # v[3], v[4] = v[4], v[3]
            # stR.value = ' & '.join(v)
        elif ret == 124:
            stR.value = q + ' & ' + G + ' & ' + r'\multicolumn{6}{c}{\timeout}'
        else:
            stR.value = q + ' & ' + G + ' & ' + r'\multicolumn{6}{c}{\error}'
        lock.acquire()
        counter.value+=1; print(counter.value, f'/ {NUM_OF_CASES}')
        lock.release()
def TA(root, stR, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(pi/2\) |ry\(pi/2\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root} | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'VATA_PATH={VATA_EXE} timeout {TIMEOUT} {TA_EXE} {root}/pre.aut {root} {root}/post.aut', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 0:
            stR.value = p.stdout.splitlines()[0].decode('utf-8')
            v = stR.value.split(' & ')
            v[3], v[4] = v[4], v[3]
            stR.value = ' & '.join(v)
        elif ret == 124:
            stR.value = q + ' & ' + G + ' & ' + r'\multicolumn{6}{c}{\timeout}'
        else:
            stR.value = q + ' & ' + G + ' & ' + r'\multicolumn{6}{c}{\error}'
        stR.value = ' & '.join(stR.value.split(' & ')[2:])
        lock.acquire()
        counter.value+=1; print(counter.value, f'/ {NUM_OF_CASES}')
        lock.release()
def svsim(root, stR, semaphore, lock, counter):
    with semaphore:
        cmd = f'timeout {TIMEOUT} ./test_SV-Sim.py {root}'#; print(cmd)
        p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 124:
            stR.value = r'\timeout'
        elif ret != 0:
            stR.value = r'\multicolumn{1}{c}{\error}'
        else:
            stR.value = p.stdout.decode('utf-8').splitlines()[-1].strip()
        lock.acquire()
        counter.value+=1; print(counter.value, f'/ {NUM_OF_CASES}')
        lock.release()
symqvMap = {'BV': 'BVsingle', 'GHZall': 'GHZall', 'GHZzero': 'GHZsingle', 'Grover': 'GroverSingle', 'H2': 'H2all', 'HXH': 'HXHall', 'MCToffoli': 'MCXall', 'MOBV_reorder': 'BVall', 'MOGrover': 'GroverAll'}
def symqv(root, stR, semaphore, lock, counter):
    with semaphore:
        cmd = f"cd /home/alan23273850/fabianbauermarquart-symqv-fa8ec7f/PLDI24/ && source ../.venv/bin/activate && timeout {TIMEOUT} ./{symqvMap[root.split('/')[1]]}.py {int(root.split('/')[2])}"#; print(cmd)
        p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 124:
            stR.value = r'\timeout'
        elif ret != 0:
            stR.value = r'\multicolumn{1}{c}{\error}'
        else:
            # assume format: ('unsat', {}, 8.522298574447632)
            stR.value = p.stdout.decode('utf-8').splitlines()[-1].strip()
            match = re.search(r"\('unsat', {}, ([\d\.]*)\)", stR.value)
            if match:
                total_time = float(match.group(1)) # Extract the number within the square brackets
                if total_time >= 60:
                    stR.value = '%dm%.fs' % (int(total_time // 60), total_time % 60)
                elif total_time >= 10:
                    stR.value = '%.fs' % total_time
                else:
                    stR.value = '%.1fs' % total_time
            else:
                stR.value = 'Wrong Answer'
        lock.acquire()
        counter.value+=1; print(counter.value, f'/ {NUM_OF_CASES}')
        lock.release()
CaALMap = {'BV': 'BVsingle', 'GHZall': 'GHZall', 'GHZzero': 'GHZsingle', 'H2': 'H2all', 'HXH': 'HXHall', 'MCToffoli': 'MCXall', 'MOBV_reorder': 'BVall'}
# 'Grover': 'GroverSingle',
# 'MOGrover': 'GroverAll'
def CaAL(root, stR, semaphore, lock, counter):
    with semaphore:
        key = root.split('/')[1]
        if key in CaALMap:
            cmd = f"time taskset -c {semaphore.get_value()} timeout {TIMEOUT} java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar {CaALMap[key]} {int(root.split('/')[2])}"#; print(cmd)
            p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
            ret = p.returncode
            if ret == 124:
                stR.value = r'\timeout'
            elif ret != 0:
                stR.value = r'\multicolumn{1}{c}{\error}'
            else:
                # assume format:
                # Valid
                # real    0m3.143s
                # user    0m2.950s
                # sys     0m0.192s
                answer = p.stdout.decode('utf-8').splitlines()[0].strip()
                if answer == 'Valid':
                    total_time = p.stderr.decode('utf-8').splitlines()[-3].strip()
                    assert(total_time.startswith('real'))
                    stR.value = total_time.split()[-1]
                else:
                    stR.value = 'Wrong Answer'
        else:
            stR.value = r'\timeout'
        lock.acquire()
        counter.value+=1; print(counter.value, f'/ {NUM_OF_CASES}')
        lock.release()

semaphore = Semaphore(NUM_OF_THREADS)
manager = Manager()
counter = manager.Value('i', 0)
process_pool_large = []
string_pool_large = []
lock = Lock()
for root, dirnames, filenames in sorted(os.walk('.')):
    # if len(dirnames) == 0 and 'pre.spec' in filenames and 'pre.aut' in filenames: # may be .aut or .spec
    for file in filenames:
        if file.endswith('.qasm'):
            process_pool_small = []
            string_pool_small = [manager.Value(c_wchar_p, file)]
            for func in (CTA, ):#TA, svsim, symqv, CaAL):
                semaphore.acquire(); semaphore.release()
                string_pool_small.append(manager.Value(c_wchar_p, ''))
                p = Process(target=func, args=(file, string_pool_small[-1], semaphore, lock, counter))
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
            print(' & '.join(map(lambda x: x.value, string_pool_large[pps[0]])), flush=True)
            process_pool_large.pop(i)
            break

# content = []
# for row in string_pool_large:
#     content.append(list(map(lambda x: x.value, row)))
# content.sort(key = lambda x: x[0])

# # print(content)

# for i in range(len(content)):
#     content[i][0] = content[i][0].split('/')[-1].lstrip('0')
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
# \newcommand{\error}[0]{\nacell error}
# %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
# \newcommand{\post}[1]{\mathtt{post}_{#1}}

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

# %\scalebox{0.6}
# {\hspace{-100pt}
# \begin{tabular}{crrrrrrrrrrrrrrrrrr}\hline
# \toprule
#   &&&& \multicolumn{6}{c}{\cta} & \multicolumn{6}{c}{\autoq} & \multirow{2}{*}{SV-Sim} & \multirow{2}{*}{symQV} & \multirow{2}{*}{CaAL}\\
#   \cmidrule(lr){5-10} \cmidrule(lr){11-16}
#   & \multicolumn{1}{c}{$n$} & \multicolumn{1}{c}{\textbf{\#q}} & \multicolumn{1}{c}{\textbf{\#G}} & \multicolumn{2}{c}{\textbf{before}} & \multicolumn{2}{c}{\textbf{after}} & \multicolumn{1}{c}{$\post{C}$} & \multicolumn{1}{c}{$\subseteq$} & \multicolumn{2}{c}{\textbf{before}} & \multicolumn{2}{c}{\textbf{after}} & \multicolumn{1}{c}{$\post{C}$} & \multicolumn{1}{c}{$\subseteq$}\\
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