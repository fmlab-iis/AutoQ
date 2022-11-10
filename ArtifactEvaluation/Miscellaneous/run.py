#!/usr/bin/python3
import os, subprocess, sys
from ctypes import c_wchar_p
from multiprocessing import Manager, Process, Semaphore

name = sys.argv[1]

def AutoQ_permutation(root, str1, semaphore):
    with semaphore:
        another = root.replace('.', '').replace('/', '') + 'permutation'
        p = subprocess.run(f'VATA_PATH=/home/alan23273850/libvata/build/cli/vata timeout 720 ../permutation {root}/pre.aut {root}/bug.qasm /tmp/{another}.aut {root}/post.aut', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 0:
            str1.value = list(map(lambda x: x.decode('utf-8'), p.stdout.splitlines()))[0]
        elif ret == 124:
            str1.value = '\multicolumn{AutoQ_permutation}{c||}{TO}'
        else:
            str1.value = '\multicolumn{AutoQ_permutation}{c||}{ERR}'
        if os.path.exists(f'/tmp/{another}.aut'):
            os.system(f'rm /tmp/{another}.aut')
def AutoQ_composition(root, str2, semaphore):
    with semaphore:
        another = root.replace('.', '').replace('/', '') + 'composition'
        p = subprocess.run(f'VATA_PATH=/home/alan23273850/libvata/build/cli/vata timeout 720 ../composition {root}/pre.aut {root}/bug.qasm /tmp/{another}.aut {root}/post.aut', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 0:
            str2.value = list(map(lambda x: x.decode('utf-8'), p.stdout.splitlines()))[0]
        elif ret == 124:
            str2.value = '\multicolumn{AutoQ_composition}{c||}{TO}'
        else:
            str2.value = '\multicolumn{AutoQ_composition}{c||}{ERR}'
        if os.path.exists(f'/tmp/{another}.aut'):
            os.system(f'rm /tmp/{another}.aut')
def SliQSim(root, str4, semaphore):
    with semaphore:
        p = subprocess.run(f'timeout 720 ./test_SliQSim.py {root}', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 124:
            str4.value = 'TO'
        elif ret != 0:
            str4.value = 'ERR'
        else:
            str4.value = list(map(lambda x: x.decode('utf-8'), p.stdout.splitlines()))[0].strip()
def Feynman(root, str3, semaphore):
    with semaphore:
        p = subprocess.run(f'timeout 720 /home/alan23273850/feynman/feynver {root}/spec.qc {root}/bug.qc', shell=True, capture_output=True, executable='/bin/bash')
        ret = p.returncode
        if ret == 124:
            str3.value = '\multicolumn{Feynman}{c|}{TO}'
        elif ret != 0:
            str3.value = '\multicolumn{Feynman}{c|}{ERR}'
        else:
            tmp = list(map(lambda x: x.decode('utf-8'), p.stdout.splitlines()))[0]
            str3.value = tmp.split(' (took ')[0] + ' & ' + tmp.split(' (took ')[1].split(')')[0]

NUM_OF_THREADS = 240
semaphore = Semaphore(NUM_OF_THREADS)
manager = Manager()
process_pool_large = []
string_pool_large = []
for root, dirnames, filenames in sorted(os.walk('.')):
    if len(dirnames) == 0 and 'post.aut' in filenames:
        process_pool_small = []
        string_pool_small = [manager.Value(c_wchar_p, root)]
        for func in (AutoQ_permutation, AutoQ_composition, SliQSim, Feynman):
            semaphore.acquire(); semaphore.release()
            string_pool_small.append(manager.Value(c_wchar_p, ''))
            p = Process(target=func, args=(root, string_pool_small[-1], semaphore))
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

os.system('pkill -9 -f permutation; pkill -9 -f composition; pkill -9 -f SliQSim; pkill -9 -f feynver; pkill -9 -f vata')

f = open(name, 'w')
for row in string_pool_large:
    print(' & '.join(map(lambda x: x.value, row)), file=f)
f.close()