"""Shared helpers for benchmark produce.py scripts."""
import os


def ensure_bench_dir(n_str: str) -> None:
    """Create directory n_str if it does not exist."""
    os.makedirs(n_str, exist_ok=True)


def write_qasm_header(file) -> None:
    """Write OPENQASM 2.0 header lines to an open file."""
    file.write("OPENQASM 2.0;\n")
    file.write('include "qelib1.inc";\n')
