#!/usr/bin/python3
import os, re, subprocess, sys

root = sys.argv[1]

p = subprocess.run(f'/home/alan23273850/SliQSim/SliQSim --sim_qasm {root}/bug.qasm --type 1 --print_info', shell=True, capture_output=True, executable='/bin/bash')
# Assume the 1st line format - Runtime: 0.013964 seconds
tmp = list(map(lambda x: x.decode('utf-8'), p.stdout.splitlines()))[0].strip()
total_time = float(tmp.split(' ')[1])
if total_time >= 60:
    print('%dm%.fs' % (int(total_time // 60), total_time % 60), end='', flush=True)
elif total_time >= 10:
    print('%.fs' % total_time, end='', flush=True)
else:
    print('%.1fs' % total_time, end='', flush=True)