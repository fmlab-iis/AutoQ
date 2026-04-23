#!/usr/bin/python3
import argparse
import json
import os
import signal
import subprocess
import time
from multiprocessing import Lock, Manager, Process, Semaphore

EXE = "../../build/cli/autoq"
processes = []


def append_key_value_to_json_file(json_file, new_key, new_value):
    if os.path.exists(json_file):
        with open(json_file, "r", encoding="utf-8") as file:
            data = json.load(file)
    else:
        data = {}

    if not isinstance(data, dict):
        raise ValueError("The JSON file does not contain a dictionary.")

    data[new_key] = new_value
    with open(json_file, "w", encoding="utf-8") as file:
        json.dump(data, file, indent=4)


def parse_stats_from_qasm(root):
    q_proc = subprocess.run(
        fr'grep -Po ".*qreg.*\[\K\d+(?=\];)" {root}/circuit.qasm',
        shell=True,
        capture_output=True,
        executable="/bin/bash",
    )
    g_proc = subprocess.run(
        fr'grep -P ".*(x |y |z |h |s |t |rx\(.+\) |ry\(.+\) |cx |cz |ccx |tdg |sdg |swap ).*\[\d+\];" {root}/circuit.qasm | wc -l',
        shell=True,
        capture_output=True,
        executable="/bin/bash",
    )

    q_val = q_proc.stdout.splitlines()
    g_val = g_proc.stdout.splitlines()
    q = q_val[0].decode("utf-8") if q_val else "0"
    g = g_val[0].decode("utf-8") if g_val else "0"
    return q, g


def execute_mode(root, timeout, pre_ext, post_ext):
    data = {}
    q, g = parse_stats_from_qasm(root)
    data["q"] = q
    data["G"] = g

    suffixes = ["00", "01", "10", "11"] if "MCToffoli" in root else [""]
    results_accum = {
        "before_state": [],
        "before_trans": [],
        "after_state": [],
        "after_trans": [],
        "total": [],
        "result": [],
        "read_file_time": [],
    }

    for s in suffixes:
        pre_f = f"{root}/pre{s}.{pre_ext}"
        post_f = f"{root}/post{s}.{post_ext}"
        cmd = f"timeout {timeout} {EXE} ver {pre_f} {root}/circuit.qasm {post_f} --latex"

        begin = time.monotonic()
        proc = subprocess.run(cmd, shell=True, capture_output=True, executable="/bin/bash")
        end = time.monotonic()
        ret = proc.returncode
        res_chunk = {}

        if ret == 0:
            output = ""
            try:
                output = proc.stdout.splitlines()[-1].decode("utf-8")
            except Exception:
                pass
            values = output.split(" & ")
            if len(values) < 5:
                res_chunk["total"] = str(round(end - begin, 1))
                res_chunk["result"] = "ERROR"
                res_chunk["read_file_time"] = "ERROR"
            else:
                values[3], values[4] = values[4], values[3]
                res_chunk["before_state"] = values[2]
                res_chunk["before_trans"] = values[3]
                res_chunk["after_state"] = values[4]
                res_chunk["after_trans"] = values[5]
                res_chunk["total"] = values[6]
                res_chunk["result"] = values[7]
                res_chunk["read_file_time"] = values[8] if len(values) >= 9 else "---"
        elif ret == 124:
            res_chunk["total"] = "TIMEOUT"
            res_chunk["result"] = "TIMEOUT"
            res_chunk["read_file_time"] = "TIMEOUT"
        else:
            res_chunk["total"] = str(round(end - begin, 1))
            res_chunk["result"] = "ERROR"
            res_chunk["read_file_time"] = "ERROR"

        for key in results_accum.keys():
            results_accum[key].append(res_chunk.get(key, ""))

    for key, value_list in results_accum.items():
        if any(value_list):
            data[key] = "+".join(value_list)
    return data


def run_hsl(root, timeout, semaphore, lock, progress, total_jobs):
    with semaphore:
        data = execute_mode(root=root, timeout=timeout, pre_ext="hsl", post_ext="hsl")
        with lock:
            append_key_value_to_json_file("hsl.json", root, data)
            progress.value += 1
            print(f"[{progress.value}/{total_jobs}] HSL {root}", flush=True)


def run_cav23(root, timeout, semaphore, lock, progress, total_jobs):
    with semaphore:
        ext = "hslsym" if ("GroverAll" in root or "GroverIterAll" in root) else "hslcon"
        data = execute_mode(root=root, timeout=timeout, pre_ext=ext, post_ext=ext)
        with lock:
            append_key_value_to_json_file("cav23.json", root, data)
            progress.value += 1
            print(f"[{progress.value}/{total_jobs}] CAV23 {root}", flush=True)


def kill_processes():
    for pid in processes:
        if pid != 0:
            try:
                os.killpg(os.getpgid(pid), signal.SIGKILL)
            except Exception:
                pass


def handle_sigint(*_):
    kill_processes()
    raise SystemExit(1)


def discover_roots(dataset):
    roots = []
    for root, dirnames, filenames in sorted(os.walk(dataset)):
        if len(dirnames) == 0 and "circuit.qasm" in filenames:
            roots.append(root if root.startswith(".") else f"./{root}")
    return roots


def parse_args():
    parser = argparse.ArgumentParser(description="Run full AE benchmark evaluation.")
    parser.add_argument("--dataset", default="bench", help="Dataset directory under AE/full-review.")
    parser.add_argument("--timeout", type=int, default=300, help="Timeout for each verification run in seconds.")
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="Maximum worker processes (default: 1 for memory stability).",
    )
    return parser.parse_args()


def main():
    signal.signal(signal.SIGINT, handle_sigint)
    args = parse_args()

    if not os.path.isdir(args.dataset):
        raise FileNotFoundError(f"Dataset directory not found: {args.dataset}")

    roots = discover_roots(args.dataset)
    if not roots:
        raise RuntimeError(f"No benchmark cases found under: {args.dataset}")

    for name in ("cav23.json", "hsl.json"):
        if os.path.exists(name):
            os.remove(name)

    num_cases = len(roots)
    num_threads = max(1, min(args.jobs, num_cases))
    total_jobs = num_cases * 2

    semaphore = Semaphore(num_threads)
    manager = Manager()
    progress = manager.Value("i", 0)
    lock = Lock()
    pool = []

    for root in roots:
        per_root = []
        p_cav = Process(
            target=run_cav23,
            args=(root, args.timeout, semaphore, lock, progress, total_jobs),
        )
        p_hsl = Process(
            target=run_hsl,
            args=(root, args.timeout, semaphore, lock, progress, total_jobs),
        )
        p_cav.start()
        p_hsl.start()
        processes.append(p_cav.pid)
        processes.append(p_hsl.pid)
        per_root.extend([p_cav, p_hsl])
        pool.append(per_root)

    while pool:
        for i, entries in enumerate(pool):
            if all(not proc.is_alive() for proc in entries):
                pool.pop(i)
                break
        else:
            time.sleep(0.2)

    print(f"Completed {total_jobs} jobs for dataset '{args.dataset}'.", flush=True)


if __name__ == "__main__":
    main()