"""Shared helpers for benchmark produce.py scripts."""
import os
import sys


def ensure_bench_dir(n_str: str) -> None:
    """Create directory n_str if it does not exist."""
    os.makedirs(n_str, exist_ok=True)


def write_qasm_header(file) -> None:
    """Write OPENQASM 2.0 header lines to an open file."""
    file.write("OPENQASM 2.0;\n")
    file.write('include "qelib1.inc";\n')


def parse_sizes(default_start: int, default_end: int, *, min_n: int = None, max_n: int = None):
    """Return [n] from argv if one int given, else list(range(default_start, default_end)).
    Optional min_n/max_n are asserted when argv provides a single n."""
    if len(sys.argv) == 2:
        n = int(sys.argv[1])
        if min_n is not None:
            assert n >= min_n
        if max_n is not None:
            assert n <= max_n
        return [n]
    return list(range(default_start, default_end))


def bench_dir_name(n: int, zfill: int = 2) -> str:
    """Return benchmark subdir name for size n (e.g. 3 -> '03')."""
    return str(n).zfill(zfill)


def ensure_bench_dir_for_n(n: int, zfill: int = 2) -> str:
    """Create benchmark dir for size n; return its name (e.g. '03')."""
    name = bench_dir_name(n, zfill)
    ensure_bench_dir(name)
    return name


# Default HSL preamble used by many benchmarks.
HSL_HEADER = "Constants\nc1 := 1\nExtended Dirac\n"


def write_hsl(path: str, body: str, header: str = None) -> None:
    """Write an HSL file with optional header (default HSL_HEADER)."""
    with open(path, "w") as f:
        f.write(header if header is not None else HSL_HEADER)
        f.write(body)
