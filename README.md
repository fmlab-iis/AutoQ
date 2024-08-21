# AutoQ: An automata-based C++ tool for quantum program verification.

AutoQ is a command-line utility written in C++ for verifying partial correctness of quantum programs automatically based on non-deterministic finite tree automata (NFTA) along with the concept of Hoare-style proof systems. 

Consider a triple $\{$ $P$ $\}$ $C$ $\{$ $Q$ $\}$, where $P$ and $Q$ are the pre- and post-condition recognizing sets of (pure) quantum states (represented by NFTA) and $C$ is a quantum program. Let $\mathcal L(.)$ denote the mapping from a condition $x$ to the set of all quantum states satisfying $x$ (characterized by $x$). Then AutoQ essentially checks whether all the quantum states in $\mathcal L(P)$ reach some state in $\mathcal L(Q)$ after the program $C$ is executed. If we further let $C(.)$ denote the mapping from a condition $x$ to the evolution of $x$ after a program segment $C$ is executed, then AutoQ simply checks whether $\mathcal L(C(P)) \subseteq \mathcal L(Q)$.

Our program currently supports $X$, $Y$, $Z$, $H$, $T$, $T^\dagger$, $S$, $S^\dagger$, $R_x(\pi/2)$, $R_y(\pi/2)$, $CX$, $CZ$, $CCX$, $SWAP$ quantum gates. The version of OpenQASM should be 2.0.

---

## Installation and Compilation

Currently, for Linux (Ubuntu/Debian) and macOS, the dependency of AutoQ can be built using the command ./configure.sh. After configuration, please run the following command.
```
make release
make test
```
The first command compiles the source code with compiler optimizations enabled, while the second command runs several unit tests to verify the correctness of the implementation. If you need to compile the library for debugging, you can replace make release with make debug.

---

## Command-Line
There are 5 modes listed in the following help message, which can be accessed by typing their respective subcommands. Each mode (subcommand) also has its own usage instructions.
```
$ ./build/cli/autoq -h
AutoQ: An automata-based C++ tool for quantum program verification.
Usage: autoq [OPTIONS] [SUBCOMMAND]

Options:
  -h,--help                   Print this help message and exit

Subcommands:
  exC                         Concrete Execution
  verC                        Concrete Verification
  exS                         Symbolic Execution
  verS                        Symbolic Verification
  eq                          Equivalence Checking
```
```
$ ./build/cli/autoq verC benchmarks/Grover/03/pre.spec benchmarks/Grover/03/circuit.qasm benchmarks/Grover/03/post.spec
The quantum program has [6] qubits and [54] gates.
The verification process [passed] in [0.0s] with [16MB] memory usage.
```
AutoQ provides two file extensions, *.hsl and *.spec, for users to indicate the format they use to describe a set of quantum states. The simpler format is *.hsl, which does not require users to have a background in NFTA. However, since our current implementation of *.hsl has not yet been optimized, we strongly recommend using *.spec as the number of qubits increases. The detailed formats can be found in the following documents.

- [hsl format description](./docs/hsl_description.md)
- [spec format description](./docs/spec_description.md)

If you're interested in the internal structures for quantum state representation, see the file [internal_structure.md](./docs/internal_structure.md).

---




