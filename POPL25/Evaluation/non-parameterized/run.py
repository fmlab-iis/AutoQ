#!/usr/bin/python3
import json, os, subprocess, sys, time
from multiprocessing import Manager, Process, Semaphore, Lock

TIMEOUT = 300
p = subprocess.run(f'find correct -type f -name "*.qasm" | wc -l', shell=True, capture_output=True, executable='/bin/bash')
TOTAL_MEMORY = 10485760 # in KB, so for now it is 10 GB.
NUM_OF_CASES = int(p.stdout.splitlines()[0].decode('utf-8'))
NUM_OF_THREADS = min(4, NUM_OF_CASES)
LSTA_EXE = '../../../../build/cli/autoq'

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

# Function to append key-value pairs to a JSON file
def append_key_value_to_json_file(json_file, new_key, new_value):
    if os.path.exists(json_file):
        # Read the existing content
        with open(json_file, 'r') as file:
            data = json.load(file)
    else:
        # If the file does not exist, initialize an empty dictionary
        data = {}

    # Ensure the data is a dictionary
    if not isinstance(data, dict):
        raise ValueError("The JSON file does not contain a dictionary.")

    # Append the new key-value pair
    data[new_key] = new_value

    # Write the updated dictionary back to the file
    with open(json_file, 'w') as file:
        json.dump(data, file, indent=4)

def LSTA(root, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(fr'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(fr'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        data = dict()
        data['q'] = q
        data['G'] = G
        cmd = ''
        if 'OEGrover' in root:
            cmd = f'ulimit -v {TOTAL_MEMORY//NUM_OF_THREADS} && timeout {TIMEOUT} {LSTA_EXE} verS {root}/pre.spec {root}/circuit.qasm {root}/post.spec {root}/constraint.smt --latex'#; print(cmd)
        else:
            cmd = f'ulimit -v {TOTAL_MEMORY//NUM_OF_THREADS} && timeout {TIMEOUT} {LSTA_EXE} verC {root}/pre.spec {root}/circuit.qasm {root}/post.spec --latex'#; print(cmd)
        begin = time.monotonic()
        p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
        end = time.monotonic()
        ret = p.returncode
        if ret == 0:
            output = ''
            try:
                output = p.stdout.splitlines()[-1].decode('utf-8')
            except:
                print(cmd, flush=True)
            v = output.split(' & ')
            if len(v) < 5:
                data['total'] = str(round(end - begin, 1))
                data['result'] = 'ERROR'
                data['read_file_time'] = '---'
            else:
                v[3], v[4] = v[4], v[3]
                data['before_state'] = v[2]
                data['before_trans'] = v[3]
                data['after_state'] = v[4]
                data['after_trans'] = v[5]
                data['total'] = v[6]
                data['result'] = v[7]
                if len(v) >= 9:
                    data['read_file_time'] = v[8]
                else:
                    data['read_file_time'] = '---'
        elif ret == 124:
            data['total'] = str(TIMEOUT)
            data['result'] = 'TIMEOUT'
            data['read_file_time'] = '---'
        else:
            data['total'] = str(round(end - begin, 1))
            data['result'] = 'ERROR'
            data['read_file_time'] = '---'
        lock.acquire()
        ##############################################
        append_key_value_to_json_file('lsta.json', root, data)
        counter.value += 1
        print(LSTA.__name__, root, data, flush=True)
        ##############################################
        lock.release()

semaphore = Semaphore(NUM_OF_THREADS)
manager = Manager()
counter = manager.Value('i', 0)
process_pool_large = []
lock = Lock()
os.chdir('correct') # origin/
tools = []
tools.append(LSTA); os.remove('lsta.json') if os.path.exists('lsta.json') else None
for root, dirnames, filenames in sorted(os.walk('.')):
    if len(dirnames) == 0 and 'circuit.qasm' in filenames:
        if 'H2' in root or 'HXH' in root or 'MCToffoli' in root:
            continue
        process_pool_small = []
        for func in tools:
            semaphore.acquire(); semaphore.release()
            p = Process(target=func, args=(root, semaphore, lock, counter))
            p.start()
            processes.append(p.pid)
            process_pool_small.append(p)
        process_pool_large.append((len(process_pool_large), process_pool_small))

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
