#!/usr/bin/python3
import json, os, subprocess, sys, time
from multiprocessing import Manager, Process, Semaphore, Lock

json_file = os.path.basename(__file__).split('.')[0].split('_')[1] + '.json'
TIMEOUT = 600
p = subprocess.run(f'ls -l {sys.argv[1]}*.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
NUM_OF_CASES = int(p.stdout.splitlines()[0].decode('utf-8'))
NUM_OF_THREADS = NUM_OF_CASES
EXE = '/home/alan23273850/SliQEC/SliQEC'

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
def append_key_value_to_json_file(new_key, new_value):
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

def CTA(root, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root} | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G2 = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" ../origin/{root.split("qasm", 1)[0] + "qasm"} | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        cmd = f'timeout {TIMEOUT} {EXE} --circuit1 ../origin/{root.split("qasm", 1)[0] + "qasm"} --circuit2 {root}'#; print(cmd)
        begin = time.monotonic()
        p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
        end = time.monotonic()
        ret = p.returncode
        data = dict()
        try:
            data = eval(p.stdout.splitlines()[0].decode('utf-8'))
        except:
            print(cmd, flush=True)
        if ret == 0:
            pass
            # data['total'] = round(end - begin, 1)
        elif ret == 124:
            data['total'] = TIMEOUT
            data['result'] = 'TIMEOUT'
        else:
            data['total'] = round(end - begin, 1)
            data['result'] = 'ERROR'
        data['q'] = q
        data['G'] = G
        data['G2'] = G2
        lock.acquire()
        ##############################################
        append_key_value_to_json_file(root, data)
        counter.value += 1
        print(root, data, str(counter.value) + '/' + str(NUM_OF_CASES), flush=True)
        ##############################################
        lock.release()

semaphore = Semaphore(NUM_OF_THREADS)
manager = Manager()
counter = manager.Value('i', 0)
process_pool_large = []
# string_pool_large = []
lock = Lock()
os.chdir(sys.argv[1]); os.remove(json_file) if os.path.exists(json_file) else None
for root, dirnames, filenames in sorted(os.walk('.')):
    for file in filenames:
        if file.endswith('.qasm'):
            process_pool_small = []
            # string_pool_small = [manager.Value(c_wchar_p, file)]
            for func in (CTA, ):#TA, svsim, symqv, CaAL):
                semaphore.acquire(); semaphore.release()
                # string_pool_small.append(manager.Value(c_wchar_p, ''))
                # p = Process(target=func, args=(file, string_pool_small[-1], semaphore, lock, counter))
                p = Process(target=func, args=(file, semaphore, lock, counter))
                p.start()
                processes.append(p.pid)
                process_pool_small.append(p)
            process_pool_large.append((len(process_pool_large), process_pool_small))
            # string_pool_large.append(string_pool_small)

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
