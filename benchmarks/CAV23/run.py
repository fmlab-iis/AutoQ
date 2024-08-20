#!/usr/bin/python3
import os, subprocess
from ctypes import c_wchar_p
from multiprocessing import Manager, Process, Semaphore, Lock

TIMEOUT = 86400
NUM_OF_THREADS = 4

def AutoQ(root, stR, semaphore, lock, counter, pid):
    with semaphore:
        another = root.replace('.', '').replace('/', '') + 'permutation'
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(pi/2\) |ry\(pi/2\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        # if 'Grover' not in root:
        #     p = subprocess.Popen(f'timeout {TIMEOUT} ../AutoQ/build/cli/autoq {root}/pre.hsl {root}/circuit.qasm {root}/spec.hsl {root}/constraint.smt', shell=True, executable='/bin/bash', stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid)    
        # else:
        p = subprocess.Popen(f'timeout {TIMEOUT} ../AutoQ/build/cli/autoq {root}/pre.aut {root}/circuit.qasm {root}/spec.aut {root}/constraint.smt', shell=True, executable='/bin/bash', stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=os.setsid)
        pid.value = p.pid
        pstdout, _ = p.communicate() # blocking...
        ret = p.returncode
        if ret == 0:
            stR.value = q + 'q ' + G + 'G ' + pstdout.splitlines()[-1].decode('utf-8')
        elif ret == 124:
            stR.value = q + 'q ' + G + 'G ' + 'timeout'
        else:
            stR.value = q + 'q ' + G + 'G ' + 'error'
        if os.path.exists(f'/tmp/{another}.aut'):
            os.system(f'rm /tmp/{another}.aut')
        lock.acquire()
        counter.value+=1; print(f'{counter.value}/18', root, stR.value, sep='\t', flush=True)
        lock.release()

semaphore = Semaphore(NUM_OF_THREADS)
manager = Manager()
counter = manager.Value('i', 0)
process_pool_large = []
string_pool_large = []
autoq_process = []
lock = Lock()

def kill_autoq_process():
    for pid in autoq_process:
        if pid.value != 0: # This line is very important!!!!
            try:
                os.killpg(os.getpgid(pid.value), signal.SIGKILL)  # Send the signal to all the process groups
            except: # in case this handler is called multiple times
                pass
def handle_sigint(*_):
    kill_autoq_process()
    exit(1)
import signal
signal.signal(signal.SIGINT, handle_sigint)

for root, dirnames, filenames in sorted(os.walk('.'), key=lambda self: 'BernsteinVazirani1000' in self[0]):
    if len(dirnames) == 0 and 'spec.aut' in filenames:
        process_pool_small = []
        string_pool_small = [manager.Value(c_wchar_p, root)]
        for func in (AutoQ, ):
            semaphore.acquire(); semaphore.release()
            string_pool_small.append(manager.Value(c_wchar_p, ''))
            pid = manager.Value('i', 0) # Notice that this default pid must be ignored in the signal handler...
            p = Process(target=func, args=(root, string_pool_small[-1], semaphore, lock, counter, pid))
            p.start()
            autoq_process.append(pid)
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

kill_autoq_process()