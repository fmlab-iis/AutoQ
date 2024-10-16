#!/usr/bin/python3
import json, os, re, subprocess, sys, time
from multiprocessing import Manager, Process, Semaphore, Lock

TIMEOUT = 300
p = subprocess.run(f'find {sys.argv[1]} -type f -name "*.qasm" | wc -l', shell=True, capture_output=True, executable='/bin/bash')
NUM_OF_CASES = int(p.stdout.splitlines()[0].decode('utf-8'))
NUM_OF_THREADS = min(4, NUM_OF_CASES)
LSTA_EXE = '../../../../build/cli/autoq'
TA_EXE = '../autoq_pldi'
TA_SYMBOLIC_EXE = '../autoq_symbolic'
VATA_EXE = '../vata'
SLIQSIM_EXE = '../test_SliQSim.py'
SVSIM_EXE = '../test_SV-Sim.py'

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
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        data = dict()
        data['q'] = q
        data['G'] = G
        cmd = ''
        if 'MCToffoli' in root:
            cmd = f'timeout {TIMEOUT} {LSTA_EXE} verC {root}/pre0.spec {root}/circuit.qasm {root}/post0.spec --latex'#; print(cmd)
        elif 'OEGrover' in root:
            cmd = f'timeout {TIMEOUT} {LSTA_EXE} verS {root}/pre.spec {root}/circuit.qasm {root}/post.spec {root}/constraint.smt --latex'#; print(cmd)
        else:
            cmd = f'timeout {TIMEOUT} {LSTA_EXE} verC {root}/pre.spec {root}/circuit.qasm {root}/post.spec --latex'#; print(cmd)
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
            v[3], v[4] = v[4], v[3]
            data['before_state'] = v[2]
            data['before_trans'] = v[3]
            data['after_state'] = v[4]
            data['after_trans'] = v[5]
            data['total'] = v[6]
            data['result'] = v[7]
        elif ret == 124:
            data['total'] = str(TIMEOUT)
            data['result'] = 'TIMEOUT'
        else:
            data['total'] = str(round(end - begin, 1))
            data['result'] = 'ERROR'
        if 'MCToffoli' in root:
            cmd = f'timeout {TIMEOUT} {LSTA_EXE} verC {root}/pre1.spec {root}/circuit.qasm {root}/post1.spec --latex'#; print(cmd)
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
                v[3], v[4] = v[4], v[3]
                data['before_state'] += '/' + v[2]
                data['before_trans'] += '/' +  v[3]
                data['after_state'] += '/' +  v[4]
                data['after_trans'] += '/' +  v[5]
                data['total'] += '/' +  v[6]
                data['result'] += '/' +  v[7]
            elif ret == 124:
                data['total'] += '/' +  str(TIMEOUT)
                data['result'] += '/' +  'TIMEOUT'
            else:
                data['total'] += '/' +  str(round(end - begin, 1))
                data['result'] += '/' +  'ERROR'
        lock.acquire()
        ##############################################
        append_key_value_to_json_file('lsta.json', root, data)
        counter.value += 1
        print(LSTA.__name__, root, data, str(counter.value), flush=True)
        ##############################################
        lock.release()
def TA(root, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        data = dict()
        data['q'] = q
        data['G'] = G
        cmd = ''
        if 'MCToffoli' in root:
            cmd = f'VATA_PATH={VATA_EXE} timeout {TIMEOUT} {TA_EXE} {root}/pre0.aut {root}/circuit.qasm {root}/post0.aut'
        elif 'OEGrover' in root:
            cmd = f'VATA_PATH={VATA_EXE} timeout {TIMEOUT} {TA_SYMBOLIC_EXE} {root}/pre.aut {root}/circuit.qasm {root}/post.aut {root}/constraint2.smt'
        else:
            cmd = f'VATA_PATH={VATA_EXE} timeout {TIMEOUT} {TA_EXE} {root}/pre.aut {root}/circuit.qasm {root}/post.aut'
        begin = time.monotonic()
        p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
        end = time.monotonic()
        ret = p.returncode
        if ret == 0:
            output = ''
            try:
                output = p.stdout.splitlines()[0].decode('utf-8')
            except:
                print(cmd, flush=True)
            v = output.split(' & ')
            v[3], v[4] = v[4], v[3]
            data['before_state'] = v[2]
            data['before_trans'] = v[3]
            data['after_state'] = v[4]
            data['after_trans'] = v[5]
            data['total'] = v[6]
            data['result'] = v[7]
        elif ret == 124:
            data['total'] = str(TIMEOUT)
            data['result'] = 'TIMEOUT'
        else:
            data['total'] = str(round(end - begin, 1))
            data['result'] = 'ERROR'
        if 'MCToffoli' in root:
            cmd = f'VATA_PATH={VATA_EXE} timeout {TIMEOUT} {TA_EXE} {root}/pre1.aut {root}/circuit.qasm {root}/post1.aut'
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
                v[3], v[4] = v[4], v[3]
                data['before_state'] += '/' + v[2]
                data['before_trans'] += '/' +  v[3]
                data['after_state'] += '/' +  v[4]
                data['after_trans'] += '/' +  v[5]
                data['total'] += '/' +  v[6]
                data['result'] += '/' +  v[7]
            elif ret == 124:
                data['total'] += '/' +  str(TIMEOUT)
                data['result'] += '/' +  'TIMEOUT'
            else:
                data['total'] += '/' +  str(round(end - begin, 1))
                data['result'] += '/' +  'ERROR'
        lock.acquire()
        ##############################################
        append_key_value_to_json_file('autoq.json', root, data)
        counter.value += 1
        print(TA.__name__, root, data, str(counter.value), flush=True)
        ##############################################
        lock.release()
def svsim(root, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        data = dict()
        data['q'] = q
        data['G'] = G
        cmd = f'timeout {TIMEOUT} {SVSIM_EXE} {root}'#; print(cmd)
        begin = time.monotonic()
        p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
        end = time.monotonic()
        ret = p.returncode
        if ret == 124:
            data['total'] = str(TIMEOUT)
            data['result'] = 'TIMEOUT'
        elif ret != 0:
            data['total'] = str(round(end - begin, 1))
            data['result'] = 'ERROR'
        else:
            data['total'] = p.stdout.decode('utf-8').splitlines()[-1].strip()
            data['result'] = 'O'
        lock.acquire()
        ##############################################
        append_key_value_to_json_file('svsim.json', root, data)
        counter.value += 1
        print(svsim.__name__, root, data, str(counter.value), flush=True)
        ##############################################
        lock.release()
symqvMap = {'BV': 'BVsingle', 'GHZall': 'GHZall', 'GHZzero': 'GHZsingle', 'Grover': 'GroverSingle', 'H2': 'H2all', 'HXH': 'HXHall', 'MCToffoli': 'MCXall', 'MOBV_reorder': 'BVall', 'MOGrover': 'GroverAll', 'OEGrover': 'OEGrover'}
def symqv(root, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        data = dict()
        data['q'] = q
        data['G'] = G
        cmd = f"cd /home/alan23273850/fabianbauermarquart-symqv-fa8ec7f/POPL25/ && source ../.venv/bin/activate && timeout {TIMEOUT} ./{symqvMap[root.split('/')[1]]}.py /home/alan23273850/AutoQ/POPL25/Evaluation/non-parameterized/{sys.argv[1]}/{root.split('/')[1]}/{root.split('/')[2]}/circuit.qasm"#; print(cmd)
        # print(cmd) # cd /home/alan23273850/fabianbauermarquart-symqv-fa8ec7f/POPL25 && source ../.venv/bin/activate && timeout 300 ./OEGrover.py /home/alan23273850/AutoQ/POPL25/Evaluation/non-parameterized/correct/OEGrover/02/circuit.qasm
        begin = time.monotonic()
        p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
        end = time.monotonic()
        ret = p.returncode
        if ret == 124:
            data['total'] = str(TIMEOUT)
            data['result'] = 'TIMEOUT'
        elif ret != 0:
            data['total'] = str(round(end - begin, 1))
            data['result'] = 'ERROR'
        else:
            # assume format: ('unsat', {}, 8.522298574447632)
            # also accept something like ('δ-sat with δ = 0.0001', OrderedDict([('psi_0_0', -0.0000 + 0.0000*I), ('psi_0_1', -0.0000 + -0.0000*I), ('psi_0_2', 0.0000 + 0.0000*I), ('psi_0_3', -0.0000 + 0.0000*I), ('psi_0_4', 0.5000 + 0.0000*I), ('psi_0_5', 0.3536 + 0.3536*I), ('psi_0_6', -0.0000 + -0.5000*I), ('psi_0_7', 0.3536 + -0.3536*I), ('psi_1_0', 0.5000 + 0.0000*I), ('psi_1_1', 0.3536 + 0.3536*I), ('psi_1_2', -0.0000 + -0.5000*I), ('psi_1_3', 0.3536 + -0.3536*I), ('psi_1_4', -0.0000 + 0.0000*I), ('psi_1_5', -0.0000 + -0.0000*I), ('psi_1_6', 0.0000 + 0.0000*I), ('psi_1_7', -0.0000 + 0.0000*I), ('psi_2_0', 0.5000 + 0.0000*I), ('psi_2_1', 0.3536 + 0.3536*I), ('psi_2_2', -0.0000 + -0.5000*I), ('psi_2_3', 0.3536 + -0.3536*I), ('psi_2_4', -0.0000 + 0.0000*I), ('psi_2_5', -0.0000 + -0.0000*I), ('psi_2_6', -0.0000 + -0.0000*I), ('psi_2_7', 0.0000 + -0.0000*I), ('psi_3_0', -0.0000 + 0.0000*I), ('psi_3_1', -0.0000 + -0.0000*I), ('psi_3_2', -0.0000 + -0.0000*I), ('psi_3_3', 0.0000 + -0.0000*I), ('psi_3_4', 0.5000 + 0.0000*I), ('psi_3_5', 0.3536 + 0.3536*I), ('psi_3_6', -0.0000 + -0.5000*I), ('psi_3_7', 0.3536 + -0.3536*I), ('psi_4_0', 0.3536 + 0.0000*I), ('psi_4_1', 0.2500 + 0.2500*I), ('psi_4_2', -0.0000 + -0.3536*I), ('psi_4_3', 0.2500 + -0.2500*I), ('psi_4_4', -0.3536 + 0.0000*I), ('psi_4_5', -0.2500 + -0.2500*I), ('psi_4_6', 0.0000 + 0.3536*I), ('psi_4_7', -0.2500 + 0.2500*I), ('psi_5_0', 0.2500 + -0.2500*I), ('psi_5_1', 0.3536 + -0.0000*I), ('psi_5_2', 0.2500 + 0.2500*I), ('psi_5_3', -0.0000 + 0.3536*I), ('psi_5_4', -0.2500 + 0.2500*I), ('psi_5_5', -0.3536 + -0.0000*I), ('psi_5_6', -0.2500 + -0.2500*I), ('psi_5_7', 0.0000 + -0.3536*I), ('psi_6_0', -0.2500 + 0.2500*I), ('psi_6_1', -0.3536 + -0.0000*I), ('psi_6_2', -0.2500 + -0.2500*I), ('psi_6_3', 0.0000 + -0.3536*I), ('psi_6_4', 0.2500 + -0.2500*I), ('psi_6_5', 0.3536 + -0.0000*I), ('psi_6_6', 0.2500 + 0.2500*I), ('psi_6_7', -0.0000 + 0.3536*I), ('psi_7_0', -0.2500 + -0.2500*I), ('psi_7_1', 0.0000 + -0.3536*I), ('psi_7_2', -0.2500 + 0.2500*I), ('psi_7_3', -0.3536 + -0.0000*I), ('psi_7_4', 0.2500 + 0.2500*I), ('psi_7_5', -0.0000 + 0.3536*I), ('psi_7_6', 0.2500 + -0.2500*I), ('psi_7_7', 0.3536 + -0.0000*I), ('psi_8_0', -0.2500 + -0.2500*I), ('psi_8_1', 0.0000 + -0.3536*I), ('psi_8_2', -0.2500 + 0.2500*I), ('psi_8_3', -0.3536 + -0.0000*I), ('psi_8_4', 0.2500 + 0.2500*I), ('psi_8_5', -0.0000 + 0.3536*I), ('psi_8_6', -0.2500 + 0.2500*I), ('psi_8_7', -0.3536 + 0.0000*I), ('psi_9_0', 0.2500 + 0.2500*I), ('psi_9_1', -0.0000 + 0.3536*I), ('psi_9_2', -0.2500 + 0.2500*I), ('psi_9_3', -0.3536 + 0.0000*I), ('psi_9_4', -0.2500 + -0.2500*I), ('psi_9_5', 0.0000 + -0.3536*I), ('psi_9_6', -0.2500 + 0.2500*I), ('psi_9_7', -0.3536 + -0.0000*I), ('psi_10_0', -0.2500 + 0.2500*I), ('psi_10_1', -0.3536 + 0.0000*I), ('psi_10_2', 0.2500 + 0.2500*I), ('psi_10_3', -0.0000 + 0.3536*I), ('psi_10_4', -0.2500 + 0.2500*I), ('psi_10_5', -0.3536 + -0.0000*I), ('psi_10_6', -0.2500 + -0.2500*I), ('psi_10_7', 0.0000 + -0.3536*I), ('psi_11_0', -0.3536 + 0.3536*I), ('psi_11_1', -0.5000 + 0.0000*I), ('psi_11_2', -0.0000 + 0.0000*I), ('psi_11_3', -0.0000 + 0.0000*I), ('psi_11_4', 0.0000 + 0.0000*I), ('psi_11_5', -0.0000 + 0.0000*I), ('psi_11_6', 0.3536 + 0.3536*I), ('psi_11_7', -0.0000 + 0.5000*I), ('psi_12_0', -0.3536 + 0.3536*I), ('psi_12_1', 0.5000 + -0.0000*I), ('psi_12_2', -0.0000 + 0.0000*I), ('psi_12_3', 0.0000 + -0.0000*I), ('psi_12_4', 0.0000 + 0.0000*I), ('psi_12_5', 0.0000 + -0.0000*I), ('psi_12_6', 0.3536 + 0.3536*I), ('psi_12_7', 0.0000 + -0.5000*I), ('q1', (0.7071 + 0.0000j)|0⟩ + (-0.0000 + -0.7071j)|1⟩), ('q2', (0.7071 + 0.0000j)|0⟩ + (0.5000 + 0.5000j)|1⟩), ('q0', (-0.0000 + 0.0000j)|0⟩ + (1.0000 + 0.0000j)|1⟩)]), 234.41243076324463)
            match = re.search(r"\('.*sat.*',.*, ([\d\.]*)\)", p.stdout.decode('utf-8').splitlines()[-1].strip())
            if match:
                data['result'] = 'O'
                total_time = float(match.group(1)) # Extract the number within the square brackets
                if total_time >= 60:
                    data['total'] = '%dm%.fs' % (int(total_time // 60), total_time % 60)
                elif total_time >= 10:
                    data['total'] = '%.fs' % total_time
                else:
                    data['total'] = '%.1fs' % total_time
            else:
                data['total'] = str(round(end - begin, 1))
                data['result'] = 'X'
        lock.acquire()
        ##############################################
        append_key_value_to_json_file('symqv.json', root, data)
        counter.value += 1
        print(symqv.__name__, root, data, str(counter.value), flush=True)
        ##############################################
        lock.release()
CaALMap = {'BV': 'BVsingle', 'GHZall': 'GHZall', 'GHZzero': 'GHZsingle', 'H2': 'H2all', 'HXH': 'HXHall', 'MCToffoli': 'MCXall', 'MOBV_reorder': 'BVall'}
# 'Grover': 'GroverSingle',
# 'MOGrover': 'GroverAll'
def CaAL(root, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        data = dict()
        data['q'] = q
        data['G'] = G
        key = root.split('/')[1]
        if key in CaALMap:
            cmd = f"time taskset -c {semaphore.get_value()} timeout {TIMEOUT} java -cp /home/alan23273850/princess/target/scala-2.11/Princess-assembly-2022-11-03.jar {CaALMap[key]} {int(root.split('/')[2])}"#; print(cmd)
            begin = time.monotonic()
            p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
            end = time.monotonic()
            ret = p.returncode
            if ret == 124:
                data['total'] = str(TIMEOUT)
                data['result'] = 'TIMEOUT'
            elif ret != 0:
                data['total'] = str(round(end - begin, 1))
                data['result'] = 'ERROR'
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
                    data['total'] = total_time.split()[-1]
                    data['result'] = 'O'
                else:
                    data['total'] = str(round(end - begin, 1))
                    data['result'] = 'X'
        else:
            data['total'] = str(TIMEOUT)
            data['result'] = 'TIMEOUT'
        lock.acquire()
        ##############################################
        append_key_value_to_json_file('caal.json', root, data)
        counter.value += 1
        print(CaAL.__name__, root, data, str(counter.value), flush=True)
        ##############################################
        lock.release()
def SliQSim(root, semaphore, lock, counter):
    with semaphore:
        p = subprocess.run(f'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm', shell=True, capture_output=True, executable='/bin/bash')
        q = p.stdout.splitlines()[0].decode('utf-8')
        p = subprocess.run(f'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l', shell=True, capture_output=True, executable='/bin/bash')
        G = p.stdout.splitlines()[0].decode('utf-8')
        data = dict()
        data['q'] = q
        data['G'] = G
        cmd = f'timeout {TIMEOUT} {SLIQSIM_EXE} {root}'
        begin = time.monotonic()
        p = subprocess.run(cmd, shell=True, capture_output=True, executable='/bin/bash')
        end = time.monotonic()
        ret = p.returncode
        if ret == 124:
            data['total'] = str(TIMEOUT)
            data['result'] = 'TIMEOUT'
        elif ret != 0:
            print(cmd)
            data['total'] = str(round(end - begin, 1))
            data['result'] = 'ERROR'
        else:
            data['total'] = p.stdout.splitlines()[0].decode('utf-8').strip()
            data['result'] = 'O'
        lock.acquire()
        ##############################################
        append_key_value_to_json_file('sliqsim.json', root, data)
        counter.value += 1
        print(SliQSim.__name__, root, data, str(counter.value), flush=True)
        ##############################################
        lock.release()

semaphore = Semaphore(NUM_OF_THREADS)
manager = Manager()
counter = manager.Value('i', 0)
process_pool_large = []
lock = Lock()
os.chdir(sys.argv[1]) # origin/
tools = []
tools.append(LSTA); os.remove('lsta.json') if os.path.exists('lsta.json') else None
tools.append(TA); os.remove('autoq.json') if os.path.exists('autoq.json') else None
tools.append(svsim); os.remove('svsim.json') if os.path.exists('svsim.json') else None
tools.append(symqv); os.remove('symqv.json') if os.path.exists('symqv.json') else None
tools.append(CaAL); os.remove('caal.json') if os.path.exists('caal.json') else None
tools.append(SliQSim); os.remove('sliqsim.json') if os.path.exists('sliqsim.json') else None
for root, dirnames, filenames in sorted(os.walk('.')):
    # if 'MCToffoli' not in root: continue
    if len(dirnames) == 0 and 'circuit.qasm' in filenames:
        process_pool_small = []
        for func in tools:
            if 'OEGrover' in root and func not in (LSTA, TA, symqv): continue
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
