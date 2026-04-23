#!/usr/bin/python3
import argparse
import json
import os
import subprocess
import time


def parse_args():
    parser = argparse.ArgumentParser(description="Run AE smoke-test on minimum benchmark sizes.")
    parser.add_argument(
        "--dataset",
        default="../full-review/bench",
        help="Path to full-review benchmark dataset.",
    )
    parser.add_argument(
        "--autoq",
        default="../../build/cli/autoq",
        help="Path to the autoq executable.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=300,
        help="Per-command timeout in seconds.",
    )
    parser.add_argument(
        "--output",
        default="smoke-results.json",
        help="Output JSON summary path.",
    )
    return parser.parse_args()


def numeric_subdirs(path):
    values = []
    for name in os.listdir(path):
        if name.isdigit() and os.path.isdir(os.path.join(path, name)):
            values.append(name)
    return sorted(values, key=lambda x: int(x))


def run_cmd(cmd, timeout):
    start = time.monotonic()
    proc = subprocess.run(
        f"timeout {timeout} {cmd}",
        shell=True,
        capture_output=True,
        text=True,
        executable="/bin/bash",
    )
    elapsed = round(time.monotonic() - start, 2)
    status = "PASS" if proc.returncode == 0 else ("TIMEOUT" if proc.returncode == 124 else "FAIL")
    return {
        "status": status,
        "returncode": proc.returncode,
        "elapsed_sec": elapsed,
        "stdout_tail": "\n".join(proc.stdout.splitlines()[-3:]),
        "stderr_tail": "\n".join(proc.stderr.splitlines()[-3:]),
    }


def smoke_commands(autoq, bench_name, case_dir):
    if bench_name == "MCToffoli":
        return [
            (
                "hsl",
                f'{autoq} ver "{case_dir}/pre00.hsl" "{case_dir}/circuit.qasm" "{case_dir}/post00.hsl"',
            ),
            (
                "cav23",
                f'{autoq} ver "{case_dir}/pre00.hslcon" "{case_dir}/circuit.qasm" "{case_dir}/post00.hslcon"',
            ),
        ]

    cav_ext = "hslsym" if bench_name in ("GroverAll", "GroverIterAll") else "hslcon"
    return [
        ("hsl", f'{autoq} ver "{case_dir}/pre.hsl" "{case_dir}/circuit.qasm" "{case_dir}/post.hsl"'),
        (
            "cav23",
            f'{autoq} ver "{case_dir}/pre.{cav_ext}" "{case_dir}/circuit.qasm" "{case_dir}/post.{cav_ext}"',
        ),
    ]


def main():
    args = parse_args()
    dataset = os.path.abspath(args.dataset)
    autoq = os.path.abspath(args.autoq)

    if not os.path.isdir(dataset):
        raise FileNotFoundError(f"Dataset not found: {dataset}")
    if not os.path.isfile(autoq):
        raise FileNotFoundError(f"autoq binary not found: {autoq}")

    benches = sorted(
        [name for name in os.listdir(dataset) if os.path.isdir(os.path.join(dataset, name))]
    )

    results = {"dataset": dataset, "autoq": autoq, "timeout_sec": args.timeout, "benchmarks": {}}
    total = 0
    passed = 0

    for bench in benches:
        sizes = numeric_subdirs(os.path.join(dataset, bench))
        if not sizes:
            continue
        min_size = sizes[0]
        case_dir = os.path.join(dataset, bench, min_size)
        print(f"[smoke] {bench} size {min_size}", flush=True)

        bench_results = {"size": min_size, "checks": {}}
        for label, cmd in smoke_commands(autoq, bench, case_dir):
            total += 1
            outcome = run_cmd(cmd, args.timeout)
            if outcome["status"] == "PASS":
                passed += 1
            bench_results["checks"][label] = outcome
            print(f"  - {label}: {outcome['status']} ({outcome['elapsed_sec']}s)", flush=True)
        results["benchmarks"][bench] = bench_results

    results["summary"] = {
        "total_checks": total,
        "passed": passed,
        "failed_or_timeout": total - passed,
        "status": "PASS" if total == passed else "FAIL",
    }

    with open(args.output, "w", encoding="utf-8") as f:
        json.dump(results, f, indent=2)

    print(
        f"[smoke] summary: {results['summary']['passed']}/{results['summary']['total_checks']} passed",
        flush=True,
    )
    raise SystemExit(0 if results["summary"]["status"] == "PASS" else 1)


if __name__ == "__main__":
    main()
