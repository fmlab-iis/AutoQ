#!/usr/bin/python3
import os, subprocess
from ctypes import c_wchar_p
from multiprocessing import Manager, Process, Semaphore, Lock

TIMEOUT = 86400
NUM_OF_THREADS = 16

def AutoQ(root, stR, semaphore, lock, counter):
    with semaphore:
        another = root.replace('.', '').replace('/', '') + 'permutation'
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(pi/2\) |ry\(pi/2\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'timeout {TIMEOUT} ../../build/cli/autoq {root}/pre.aut {root}/circuit.qasm {root}/spec.aut {root}/constraint.smt', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 0:
            stR.value = p.stdout.splitlines()[-1].decode('utf-8')
        elif ret == 124:
            stR.value = q + ' & ' + G + ' & ' + r'\multicolumn{6}{c}{\timeout}'
        else:
            stR.value = q + ' & ' + G + ' & ' + r'\multicolumn{6}{c}{error}'
        if os.path.exists(f'/tmp/{another}.aut'):
            os.system(f'rm /tmp/{another}.aut')
        lock.acquire()
        print(p.stdout.splitlines(), flush=True)
        counter.value+=1; print(root, stR.value, counter.value, '/ 16', flush=True)
        lock.release()

semaphore = Semaphore(NUM_OF_THREADS)
manager = Manager()
counter = manager.Value('i', 0)
process_pool_large = []
string_pool_large = []
lock = Lock()
for root, dirnames, filenames in sorted(os.walk('.')):
    if len(dirnames) == 0 and 'spec.aut' in filenames:
        process_pool_small = []
        string_pool_small = [manager.Value(c_wchar_p, root)]
        for func in (AutoQ, ):
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
            # print(' & '.join(map(lambda x: x.value, string_pool_large[pps[0]])), flush=True)
            process_pool_large.pop(i)
            break

os.system('pkill -9 -f autoq')