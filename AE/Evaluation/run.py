#!/usr/bin/python3
import json, os, subprocess, sys, time
from multiprocessing import Manager, Process, Semaphore, Lock

TIMEOUT = 300
p = subprocess.run(f'find correct -type f -name "*.qasm" | wc -l', shell=True, capture_output=True, executable='/bin/bash')
# TOTAL_MEMORY = 10485760 # in KB, so for now it is 10 GB.
NUM_OF_CASES = int(p.stdout.splitlines()[0].decode('utf-8'))
NUM_OF_THREADS = min(128, NUM_OF_CASES)
EXE = '../../../build/cli/autoq'

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

def HSL(root, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(fr'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(fr'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        data = dict()
        data['q'] = q
        data['G'] = G

        # MCToffoli logic
        suffixes = ['00', '01', '10', '11'] if 'MCToffoli' in root else ['']
        results_accum = {'before_state': [], 'before_trans': [], 'after_state': [], 'after_trans': [], 'total': [], 'result': [], 'read_file_time': []}

        for s in suffixes:
            pre_f = f"{root}/pre{s}.hsl"
            post_f = f"{root}/post{s}.hsl"

            # ulimit -v {TOTAL_MEMORY//NUM_OF_THREADS} &&
            cmd = f'timeout {TIMEOUT} {EXE} ver {pre_f} {root}/circuit.qasm {post_f} --latex'#; print(cmd)
            begin = time.monotonic()
            p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
            end = time.monotonic()
            ret = p.returncode

            res_chunk = {}
            if ret == 0:
                output = ''
                try:
                    output = p.stdout.splitlines()[-1].decode('utf-8')
                except:
                    print(cmd, flush=True)
                v = output.split(' & ')
                if len(v) < 5:
                    res_chunk['total'] = str(round(end - begin, 1))
                    res_chunk['result'] = 'ERROR'
                    res_chunk['read_file_time'] = 'ERROR'
                else:
                    v[3], v[4] = v[4], v[3]
                    res_chunk['before_state'] = v[2]
                    res_chunk['before_trans'] = v[3]
                    res_chunk['after_state'] = v[4]
                    res_chunk['after_trans'] = v[5]
                    res_chunk['total'] = v[6]
                    res_chunk['result'] = v[7]
                    if len(v) >= 9:
                        res_chunk['read_file_time'] = v[8]
                    else:
                        res_chunk['read_file_time'] = '---'
            elif ret == 124:
                res_chunk['total'] = 'TIMEOUT' #str(TIMEOUT)
                res_chunk['result'] = 'TIMEOUT'
                res_chunk['read_file_time'] = 'TIMEOUT'
            else:
                res_chunk['total'] = str(round(end - begin, 1))
                res_chunk['result'] = 'ERROR'
                res_chunk['read_file_time'] = 'ERROR'

            # Append result parts
            for k in results_accum.keys():
                results_accum[k].append(res_chunk.get(k, ''))

        # Join results with '+'
        for k, v_list in results_accum.items():
            if any(v_list): # Only add if we have data
                data[k] = "+".join(v_list)

        lock.acquire()
        ##############################################
        append_key_value_to_json_file('hsl.json', root, data)
        counter.value += 1
        print(HSL.__name__, root, data, flush=True)
        ##############################################
        lock.release()

def CAV23(root, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(fr'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(fr'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        data = dict()
        data['q'] = q
        data['G'] = G

        # Extension logic
        ext = 'hslcon'
        if 'GroverAll' in root or 'GroverIterAll' in root:
            ext = 'hslsym'

        # MCToffoli logic
        suffixes = ['00', '01', '10', '11'] if 'MCToffoli' in root else ['']
        results_accum = {'before_state': [], 'before_trans': [], 'after_state': [], 'after_trans': [], 'total': [], 'result': [], 'read_file_time': []}

        for s in suffixes:
            pre_f = f"{root}/pre{s}.{ext}"
            post_f = f"{root}/post{s}.{ext}"

            # ulimit -v {TOTAL_MEMORY//NUM_OF_THREADS} &&
            cmd = f'timeout {TIMEOUT} {EXE} ver {pre_f} {root}/circuit.qasm {post_f} --latex'#; print(cmd)

            begin = time.monotonic()
            p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
            end = time.monotonic()
            ret = p.returncode

            res_chunk = {}
            if ret == 0:
                output = ''
                try:
                    output = p.stdout.splitlines()[-1].decode('utf-8')
                except:
                    print(cmd, flush=True)
                v = output.split(' & ')
                if len(v) < 5:
                    res_chunk['total'] = str(round(end - begin, 1))
                    res_chunk['result'] = 'ERROR'
                    res_chunk['read_file_time'] = 'ERROR'
                else:
                    v[3], v[4] = v[4], v[3]
                    res_chunk['before_state'] = v[2]
                    res_chunk['before_trans'] = v[3]
                    res_chunk['after_state'] = v[4]
                    res_chunk['after_trans'] = v[5]
                    res_chunk['total'] = v[6]
                    res_chunk['result'] = v[7]
                    if len(v) >= 9:
                        res_chunk['read_file_time'] = v[8]
                    else:
                        res_chunk['read_file_time'] = '---'
            elif ret == 124:
                res_chunk['total'] = 'TIMEOUT'
                res_chunk['result'] = 'TIMEOUT'
                res_chunk['read_file_time'] = 'TIMEOUT'
            else:
                res_chunk['total'] = str(round(end - begin, 1))
                res_chunk['result'] = 'ERROR'
                res_chunk['read_file_time'] = 'ERROR'

            # Append result parts
            for k in results_accum.keys():
                results_accum[k].append(res_chunk.get(k, ''))

        # Join results with '+'
        for k, v_list in results_accum.items():
            if any(v_list): # Only add if we have data
                data[k] = "+".join(v_list)

        lock.acquire()
        ##############################################
        append_key_value_to_json_file('cav23.json', root, data)
        counter.value += 1
        print(CAV23.__name__, root, data, flush=True)
        ##############################################
        lock.release()

semaphore = Semaphore(NUM_OF_THREADS)
manager = Manager()
counter = manager.Value('i', 0)
process_pool_large = []
lock = Lock()
os.chdir('correct') # origin/
tools = []
tools.append(CAV23); os.remove('cav23.json') if os.path.exists('cav23.json') else None
tools.append(HSL); os.remove('hsl.json') if os.path.exists('hsl.json') else None
for root, dirnames, filenames in sorted(os.walk('.')):
    if len(dirnames) == 0 and ('circuit.qasm' in filenames or 'circuit.qasm' in filenames):
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