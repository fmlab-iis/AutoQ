# AutoQ Artifact for CAV 2026 AE (Docker, x86_64)

This artifact targets the CAV 2026 Artifact Evaluation process with a Docker image on `x86_64` (`linux/amd64`).

## 1) Artifact Contents

The final upload package (`.zip`) is expected to contain:

- `image.tar.gz`: exported Docker image
- `README.md`: this guide
- `LICENSE`: project license

## 2) Environment Requirements

- Linux/macOS with Docker installed
- CPU architecture: `x86_64` (or Docker with `linux/amd64` emulation)

## 3) Load Image and Start Container

Before running smoke/full-review commands, load the image into your local Docker daemon:

```bash
docker load -i image.tar.gz
```

You can verify it is available:

```bash
docker images | grep "autoq-cav26"
```

This image intentionally does not include a pre-built `autoq` binary; we require reviewers to build at runtime to maximize transparency and verify the exact build process.

After loading the image, start one reusable container session:

```bash
docker run --rm -it autoq-cav26 bash
```

`--rm` means the container is automatically removed when you exit.
If you want to keep the container after exit, run without `--rm`:

```bash
docker run -it --name autoq-ae-session autoq-cav26 bash
```

Then inside the container:

```bash
cd /opt/AutoQ
make release
```

## 4) Run Smoke Test

Smoke-test runs the minimum size for each benchmark family.

Use the single-container workflow in Section 3. After entering the container and running `make release`, run:

```bash
cd /opt/AutoQ
python3 ./AE/smoke-test/run_smoke.py --dataset ./AE/full-review/bench --autoq ./build/cli/autoq --timeout 300 --output ./AE/smoke-test/smoke-results.json
```

The smoke script is single-threaded only (no `--jobs` option); it runs one verification after another. We measured the smoke phase itself at about 14 seconds end-to-end on our server (AMD EPYC 7742 64-Core Processor, 1.5 GHz; build time excluded).

Output:

- `/opt/AutoQ/AE/smoke-test/smoke-results.json`
- Console summary with PASS/FAIL per benchmark family

Expected smoke outcome: all checks pass (`10/10 passed`, summary status `PASS`).

## 5) Run Full Review

Full-review runs all benchmark cases in `AE/full-review/bench`.

To avoid out-of-memory failures across evaluator machines, the default configuration uses `1` worker thread.

Memory note: one process can use up to about `21 GB`.
Estimate required RAM as:

`required RAM (GB) = 21 * process_count`

For example, with `--jobs 1`, plan for at least about `21 GB`.

How `21 GB` is measured:

- We ran full-review in single-process mode and recorded peak RSS via `/usr/bin/time -v`.
- Command:

```bash
cd AE/full-review
/usr/bin/time -v python3 run.py --dataset bench --timeout 300 --jobs 1
```

- Observed peak: `Maximum resident set size (kbytes): 21956220`
  (about `20.9 GiB`, rounded to `21 GB`).

Use the single-container workflow in Section 3. After entering the container and running `make release`, run:

```bash
cd /opt/AutoQ/AE/full-review
python3 run.py --dataset bench --timeout 300 --jobs 1
python3 gen_table.py --input-dir .
```

The full-review command above uses `--jobs 1` by default. We measured the review phase at about 48 minutes end-to-end on our server (AMD EPYC 7742 64-Core Processor, 1.5 GHz; `run.py`: about 47m34s, table generation: under 1 second; build time excluded). If you increase `--jobs`, runtime can be shorter, but memory usage increases proportionally.

Output:

- `/opt/AutoQ/AE/full-review/hsl.json`
- `/opt/AutoQ/AE/full-review/cav23.json`
- `/opt/AutoQ/AE/full-review/table.jpg`

The generated `table.jpg` corresponds to **Table 1** in the paper.

How to view or copy `table.jpg`:

- In VSCode, `Ctrl` + click `/opt/AutoQ/AE/full-review/table.jpg` in terminal output to open it directly.
- To copy from the host with `docker cp`, give the container a fixed name when you start it (`docker run ... --name autoq-ae-session ...`). Then you can refer to that name in:

```bash
docker cp autoq-ae-session:/opt/AutoQ/AE/full-review/table.jpg ./table.jpg
```

If your `docker run` includes `--rm`, do not exit the interactive shell until you have copied what you need: the container must still exist, so run `docker cp` from another terminal while that session stays open. Alternatively, omit `--rm` so the container remains after exit and you can copy from the stopped container later.

Progress indicator:

- `run.py` prints `[current/total]` for each completed verification task.

## 6) Reusability: Ready-to-Run and Custom Examples

We provide ready-to-run reusable examples in `AE/reusable/`:

- `AE/reusable/pass/`: 1-qubit `Z` gate, pre `{|0>, |1>}`, post `{|0>, -|1>}` (expected to verify successfully)
- `AE/reusable/fail/`: 1-qubit `Z` gate, pre `{|0>, |1>}`, post `{|0>, |1>}` (expected to fail verification)

After Section 3 (`docker run ...` + `make release`), run:

```bash
cd /opt/AutoQ

# PASS case
autoq ver ./AE/reusable/pass/pre.hsl ./AE/reusable/pass/circuit.qasm ./AE/reusable/pass/post.hsl

# FAIL case
autoq ver ./AE/reusable/fail/pre.hsl ./AE/reusable/fail/circuit.qasm ./AE/reusable/fail/post.hsl
```

How to interpret output:

- If the line contains `verification process [OK]`, the triple is proven correct.
- If the line contains `verification process [failed]`, the postcondition is not implied by the program and precondition.
- Runtime/memory numbers in the same line are performance diagnostics only.
- For automation, parse the status token (`[OK]` / `[failed]`) from stdout.

You can also run your own custom `pre/circuit/post` triple:

```bash
# inside the container after Section 3
autoq ver /path/to/pre.hsl /path/to/circuit.qasm /path/to/post.hsl
```

## 7) Build and Test Without Docker (Optional)

First, clone the source code and check out the `CAV26` branch:

```bash
git clone -b CAV26 https://github.com/fmlab-iis/AutoQ.git
cd AutoQ
```

On Ubuntu 24.04, install:

- `ca-certificates` (system CA roots for HTTPS certificate verification)
- `g++`, `make`, `cmake`, `python3`
- `libboost-filesystem-dev`, `libboost-test-dev`, `libboost-regex-dev`, `libantlr4-runtime-dev`
- `libvips-tools`

You can install all of them in one command:

```bash
sudo apt-get update && sudo apt-get install -y ca-certificates g++ make cmake python3 libboost-filesystem-dev libboost-test-dev libboost-regex-dev libantlr4-runtime-dev libvips-tools
```

Then:

```bash
make release

# smoke-test
python3 ./AE/smoke-test/run_smoke.py --dataset ./AE/full-review/bench --autoq ./build/cli/autoq --timeout 300 --output ./AE/smoke-test/smoke-results.json

# full-review
cd ./AE/full-review
python3 run.py --dataset bench --timeout 300 --jobs 1
python3 gen_table.py --input-dir .
```

This provides an alternative path beyond the packaged Docker image.

## 8) Available + Functional: Why This Artifact Satisfies Them

Reusable in CAV 2026 presumes the artifact also satisfies Available and Functional.

### Available

- The final artifact submission provides a public DOI link (e.g., Zenodo) to the exact submitted version.
- The artifact package includes `image.tar.gz`, `README.md`, and `LICENSE`.

### Functional

- Section 3 provides a complete container startup/build path from a clean machine.
- Section 4 and Section 5 provide executable reviewer workflows (smoke and full-review) with expected outputs.

## 9) Reusable Badge Criteria: Why This Artifact Satisfies Them

The CAV 2026 reusable badge follows ACM-style criteria and requires a high bar.
Below we map each reusable criterion to concrete elements in this artifact.

1. License allows reuse, repurposing, and is easy to use.

- The artifact ships a permissive `MIT` license (`LICENSE`), explicitly allowing use, copy, modify, merge, publish, distribute, sublicense, and sell.
- This directly supports downstream reuse beyond paper replication.

2. Dependencies and libraries are documented and up to date.

- Dependencies are documented in this README for both Docker and non-Docker usage.
- The Docker image is based on Ubuntu 24.04; packages are installed from Ubuntu 24.04 repositories at image build time (latest available versions at install time).

3. README explains usage beyond the paper in sufficient detail.

- In addition to smoke/full-review replication, Section 6 documents running arbitrary user-provided `pre/circuit/post` inputs.
- This makes the artifact usable for new verification tasks, not only the paper benchmarks.

4. Documented interfaces for extensions (or open source).

- How to use and extend with custom `pre/circuit/post` inputs is documented in Section 6.
- The project is open source at [https://github.com/fmlab-iis/AutoQ/](https://github.com/fmlab-iis/AutoQ/).
- The input format references are documented at [https://github.com/fmlab-iis/AutoQ/blob/CAV26/docs/hsl_description.md](https://github.com/fmlab-iis/AutoQ/blob/CAV26/docs/hsl_description.md) and [https://github.com/fmlab-iis/AutoQ/blob/CAV26/docs/qasm_description.md](https://github.com/fmlab-iis/AutoQ/blob/CAV26/docs/qasm_description.md).

5. Usable in a different environment (outside Docker / another system).

- Section 7 provides an explicit non-Docker build path on Ubuntu 24.04.
- Core command-line usage works both inside Docker and directly on host (`autoq ver ...`).
