# AutoQ Artifact for SPLASH 2026 AE (Docker, x86_64)

This is the artifact accompanying the OOPSLA/SPLASH 2026 submission on verifying repeat-until-success (RUS) quantum protocols with AutoQ. It reproduces:

- **Table 1** — individual RUS circuits and
- **Table 2** — composed RUS circuits.

Requested badges: **Available**, **Reusable** (subsuming **Functional**), **Results Reproduced**.

---

## 1. Paper Contribution & Claims Mapping

Our work is based on AutoQ, a Hoare-style quantum program verifier, built on non-deterministic finite tree automata, that checks whether a quantum program transforms a given precondition set of quantum states into an "up-to-scale" subset of a given postcondition set. We generalized set semantics to choice-sequence semantics that tracks a one-to-one input-output correspondence between elements of the precondition and those of the postcondition. We also proved a three-test theorem that reduces correctness of RUS protocols to finitely many inputs, enabling automatic invariant synthesis and decidable verification.

This artifact evaluates this enhanced verifier specifically on repeat-until-success (RUS) protocols, namely quantum circuits with a measurement-gated retry loop. To show AutoQ both accepts correct protocols and rejects incorrect ones, the benchmarks also include deliberately-buggy protocol variants.

| Claim | Location in paper | Artifact component|
|---|---|---|
| AutoQ verifies individual RUS protocols (Figures 7–10) correctly, and correctly *rejects* the buggy variants among them | Table 1 | `benchmarks/OOPSLA26/RUS/Figure{7,8,9,10a,10b,10c}` |
| AutoQ verifies composed RUS protocols (`V_i ∘ V_j`) built from the Figure 7–10 building blocks, including buggy compositions | Table 2 | `benchmarks/OOPSLA26/RUS/Figure*_ex*` |

---

## 2. Artifact Contents

The packaged submission (`autoq-oopsla26-artifact.zip`, produced by `package-artifact.sh`) contains:

- `image.tar.gz` — the Docker image (ID: `cf4867b13d7f`), saved with `docker save`
- `README.md` — this file
- `LICENSE` — AutoQ's MIT license (see §9)

---

## 3. Environment Requirements

- Docker (any recent version). Host OS: 64-bit Linux or Windows. Other host OS/architecture combinations may work but are not tested.
- Disk: ~1 GB total — the loaded image is 863 MB, plus ~60 MB for the build output produced inside the container on first run.
- RAM: 2 GB is comfortably enough. Unlike some AE artifacts, this one does **not** need tens of GB of RAM — all benchmarks are small (≤2 qubits, ≤150 gates) and each `autoq ver` call finishes in well under 200ms using ~25–30 MB.

---

## 4. Load the Image and Start the Container

```bash
docker load -i image.tar.gz
docker images | grep autoq-oopsla26

docker run --rm -it autoq-oopsla26 bash
```

Note the `--rm` flag: the container above is deleted the moment you exit the shell, so nothing inside it (including `table1.csv`/`table2.csv`) survives past that session — fine if you only need to read the output on-screen. If you want the container to persist after you exit, e.g. to `docker cp` files out afterward as shown in §6, drop `--rm` and give it a name instead:
```bash
docker run --name autoq-ae-session -it autoq-oopsla26 bash
```

No modification to the image, Dockerfile, or any file is required to run any of the steps below — these are the exact commands to use as given.

The container starts you directly in `/opt/AutoQ/AE`, which is also where `run.sh` writes its output (`table1.csv`, `table2.csv`).

The `autoq` binary is **not** pre-built into the image — by design, so that the build itself is visible to reviewers as part of running the artifact (see §7 for the non-Docker path, which uses the identical `make release`).

---

## 5. Kick-the-Tires Phase: `bash run.sh`

Because this paper's benchmark set is small, there is no separate lightweight smoke test that runs before the full evaluation — **the Kick-the-Tires step already produces the complete, paper-relevant result set covering both claims in §1.**

Just run:
```bash
bash run.sh
```

The first invocation auto-builds via `make release` (about 1–2 minutes; measured ~70s on a 64-core AMD EPYC 7742 host, expect shorter on a modest laptop); every result printed after that build is the evaluation, so there's nothing further to do for the Evaluation phase — see §6. Running all of Table 1 + Table 2 after the build takes a few seconds, so total install-to-first-result time is well under the ~30 minutes budgeted for Kick-the-Tires.

The full run reproduces the table below verbatim in terms of results, with slight variations in runtime and memory usage.
```
Table 1: Individual RUS Circuits
program   qubits  gates  result   time  memory
𝑉7             2     30    OK    116ms    27MB
𝑉8             2     17    OK     84ms    27MB
𝑉9             2     27    OK     89ms    27MB
𝑉10a_bug       2     43  failed   93ms    25MB
𝑉10a_fix       2     43    OK     97ms    27MB
𝑉10b           2     76    OK    104ms    27MB
𝑉10c_bug       2     67  failed   96ms    27MB
𝑉10c_fix       2     67    OK     95ms    27MB

Table 2: Composed RUS Circuits
program          qubits  gates  result   time  memory
𝑉7 ◦ 𝑉7               2     61    OK    121ms    27MB
𝑉7 ◦ 𝑉8               2     48    OK    167ms    26MB
𝑉8 ◦ 𝑉7               2     48    OK    137ms    26MB
𝑉8 ◦ 𝑉8               2     35    OK    106ms    27MB
𝑉8 ◦ 𝑉9               2     45    OK    133ms    27MB
𝑉9 ◦ 𝑉10a_fix         2     71    OK    127ms    27MB
𝑉9 ◦ 𝑉10a_bug         2     71  failed  146ms    27MB
𝑉10a_fix ◦ 𝑉10b       2    120    OK    114ms    27MB
𝑉10b ◦ 𝑉10c_fix       2    144    OK    129ms    27MB
𝑉10b ◦ 𝑉10c_bug       2    144  failed  154ms    26MB
```

**Some `failed` rows are expected, not bugs in the artifact**: `V10a_bug`, `V10c_bug`, `V9 ◦ V10a_bug`, and `V10b ◦ V10c_bug` are deliberately-flawed protocol variants from the paper, included specifically to demonstrate that AutoQ correctly rejects them; the `_fix` variants (`V10a_fix`, `V10c_fix`) show the fix passing.

---

## 6. Evaluation Phase: Comparing Against the Paper

Already done in §5 — `bash run.sh` *is* both the Kick-the-Tires check and the full evaluation for both claims in §1. To copy results out and compare against the paper directly:

```bash
# from your host, after `docker run --name autoq-ae-session -it autoq-oopsla26 bash`
docker cp autoq-ae-session:/opt/AutoQ/AE/table1.csv .
docker cp autoq-ae-session:/opt/AutoQ/AE/table2.csv .
```

**Expected range of deviation:**
- `result` (`OK`/`failed`) — must match the paper **exactly**, with zero tolerance. This is a decision procedure's yes/no output, not a statistical measurement, so any mismatch here would indicate a real problem.
- `time` — reported in milliseconds; varies with host CPU, but every case in Tables 1–2 completes in the tens-to-low-hundreds-of-milliseconds range (well under a second) on any machine that can run Docker.
- `memory` — should stay within the same tens-of-MB range (roughly 20–35 MB) regardless of host; this reflects the automata sizes for these specific benchmarks, not host-dependent tuning, so it should not vary much.

---

## 7. Reusability: Adapting the Artifact to New Inputs

`AE/reusable-example/` is a minimal, purpose-built triple — a single-qubit X gate with precondition `{|0>, |1>}` — with **two** postconditions, so you can see AutoQ actually discriminate rather than just reporting OK:

```bash
cd /opt/AutoQ/AE/reusable-example

# Correctly tracks which precondition element maps to which postcondition
# element under X: choice 1 (|1>) -> |0>, choice 2 (|0>) -> |1> — expect [OK]
autoq ver pre_.lsta circuit_.qasm post_pass.lsta

# Same two kets, but the choice-to-state mapping is left unchanged from
# pre_.lsta, i.e. claims X does nothing — expect [failed]
autoq ver pre_.lsta circuit_.qasm post_fail.lsta
```

`pre_.lsta` encodes the ordered set `{|1>, |0>}` as one root state `0` choosing two choice-tagged transitions: `[1,1](1, 2) -> 0` (choice 1 denotes `|1>`) and `[1,2](2, 1) -> 0` (choice 2 denotes `|0>`). `post_fail.lsta` is byte-identical to `pre_.lsta` — as an unordered set both are still `{|0>, |1>}`, but it wrongly claims that the X gate leaves each precondition element's choice tag unchanged. `post_pass.lsta` swaps the two choice tags (`[1,2](1, 2) -> 0`, `[1,1](2, 1) -> 0`), correctly reflecting that the element identified by choice 1 (`|1>`) becomes `|0>` and the element identified by choice 2 (`|0>`) becomes `|1>` after the gate. This is AutoQ's choice-sequence semantics (§1) in miniature: two postconditions can denote the exact same unordered set of kets and still be right or wrong, because what's actually checked is the per-choice correspondence between precondition and postcondition elements, not just set membership. See [`docs/lsta_description.md`](../docs/lsta_description.md) for the full grammar of these transition entries.

**Note.** In each transition \[s,C](l,r) -> t or \[s,C] -> t, the choice C is encoded as an integer that represents a set in bitwise form. For instance, if we use the i-th bit (0-indexed) to represent the element i+1, then {1,3} is encoded as \(2^0 + 2^2 = 5\) and {1,2,3} is encoded as \(2^0 + 2^1 + 2^2 = 7\).

To verify a **completely new** triple (not derived from an existing benchmark) — no script changes, config, or registration of any kind is needed:

```bash
autoq ver /path/to/pre.lsta /path/to/circuit.qasm /path/to/post.lsta
```

- `pre.lsta`/`post.lsta` — sets of quantum states encoded in level-synchronized tree automata. See [`docs/lsta_description.md`](../docs/lsta_description.md).
- `circuit.qasm` — OpenQASM 2.0/3.0 with common gates X, Y, Z, H, T, T†, S, S†, Rx(π/2), Ry(π/2), CX, CZ, CCX, SWAP. See [`docs/qasm_description.md`](../docs/qasm_description.md).

### Build and Test Without Docker

```bash
sudo apt-get update && sudo apt-get install -y \
  ca-certificates git g++ make cmake python3 \
  libboost-filesystem-dev libboost-test-dev
git clone -b OOPSLA26 https://github.com/fmlab-iis/AutoQ.git
cd AutoQ
make release
cd AE
bash run.sh
```

---

## 8. Badge Justification

We answer only the questions in the [Reviewer Guidelines](https://2026.splashcon.org/track/splash-2026-artifact-evaluation#Reviewer-Guidelines) that are required to justify our artifact's eligibility for the claimed badges.

**Q1. What is the central contribution of the paper?**
We generalized set semantics in AutoQ to choice-sequence semantics that tracks a one-to-one input-output correspondence between elements of the precondition and those of the postcondition. We also proved a three-test theorem that reduces correctness of RUS protocols to finitely many inputs, enabling automatic invariant synthesis and decidable verification. We successfully verified RUS protocols instantly with choice-sequence semantics.

**Q2. What claims do the authors make of the artifact, and how does it connect to Q1?**
AutoQ correctly verifies individual and composed RUS protocols, including correctly *rejecting* deliberately-buggy protocol variants — directly showing that the choice-sequence semantics and the three-test theorem work.

**Q3. Can you locate the specific, significant claims made in the paper (figures, tables, etc.)?**
Yes — Table 1 (Figures 7–10, individual RUS circuits) and Table 2 (composed circuits `V_i ◦ V_j`).

**Q4. Are you able to install and test the artifact as indicated in the kick-the-tires instructions?**
If everything works well, §4 (install) and §5 (test) suffice.

**Q6. For each claim in Q3, do you know how to reproduce the result using the artifact?**
Just run the single command `bash run.sh`.

**Q10. If doing follow-up research in this area, would you be able to reuse the paper as a baseline?**
Future work in this area can reuse our proposed choice-sequence semantics to specify more fine-grained properties. Moreover, the benchmark suite in `benchmarks/OOPSLA26/RUS/` can serve as a baseline set for comparing new verification approaches on the same protocols.

**Q11. Is the code released via an open source license (e.g. OSI-approved)?**
Yes — MIT (see §9). A legacy GPLv3 file (`COPYING`) and `vata` binary exist elsewhere in the wider repository but are excluded from this artifact's Docker image entirely, so this artifact is exclusively MIT-licensed.

**Q12. Does the artifact have clear installation instructions?**
Yes — §4–5 for Docker, §7 for the non-Docker native build path.

**Q13. Are you able to modify the benchmarks/artifact to run simple additional experiments?**
Yes — `reusable-example/` demonstrates editing a postcondition to flip the verification result (§7), and any new `pre/circuit/post` triple can be run directly via `autoq ver` with no script changes required.

**Q16. Does the artifact provide evidence for all the significant claims noted in Q1–3?**
Yes — both Table 1 and Table 2 claims are exercised by the single `bash run.sh` command.

**Q17. What do you expect as a reasonable range of deviation?**
`Result` (`OK`/`failed`) must match exactly, zero tolerance. `Time` is reported in milliseconds and should stay in the tens-to-low-hundreds range. `Memory` should stay within the same ~20–35 MB band. (See full detail in §6.)

---

## 9. Licensing

AutoQ's own source code (everything needed to build and run the `autoq` CLI used throughout this artifact) is released under the **MIT License** — see [`LICENSE`](../LICENSE).

The wider repository also contains a `COPYING` file (GPLv3) and a prebuilt `vata` binary at the repo root — **legacy artifacts from an earlier project increment** (AutoQ began as a fork of the VATA tree-automata library), kept for historical/legacy-comparison purposes elsewhere in the repo. Neither is on the code path exercised by this artifact — `run.sh` and `reusable-example/` only invoke `autoq`, never `vata` — and neither is copied into this artifact's Docker image at all (excluded via `.dockerignore`), so the artifact you receive is exclusively MIT-licensed.
