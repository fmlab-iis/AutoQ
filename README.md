# AutoQ: An automata-based C++ tool for quantum circuit verification
<!-- [![Build Status](https://travis-ci.org/ondrik/libvata.svg?branch=master)](https://travis-ci.org/ondrik/libvata)-->

---

AutoQ is a (highly optimized?) command-line utility written in C++ for Hoare-style quantum circuit verification based on non-deterministic finite tree automata. The following figure demonstrates how we use a tree to represent a 3-qubit quantum state, so an automaton can, of course, be used to encode a set of quantum states. The symbol of each internal transition should be a positive integer $n$ indicating the $n$-th qubit, and the symbol of each leaf transition is a 5-tuple of integers $(a,b,c,d,k)$ describing the probability amplitude $(a+b\omega+c\omega^2+d\omega^3) / \sqrt2^k$ of some computational basis state, where $w = \cos(\pi/4) + i\sin(\pi/4)$.

<img width="412" alt="image" src="https://user-images.githubusercontent.com/10044077/214999182-7e3882d2-47cf-49cb-aa3e-45295072b3f8.png">

As for Hoare-style verification, there are three main components: `pre.aut`, `circuit.qasm` and `post.aut`. The first file `pre.aut` describes an automaton that encodes a set $P$ of quantum states. The second file `circuit.qasm` describes a quantum circuit $C$ in QASM format. Notice that this format is not able to initialize the initial quantum state. The last file `post.aut` describes an automaton that encodes another set $Q$ of quantum states. Finally this tool tries to check whether for each state $s$ in $P$, the output state $C(s)$ lies in the set $Q$. If the result is true, we say the specified property is correct.

This tool can also be generalized to support "symbolic" quantum states. In this case, we simply replace some entries of leaf transitions in `pre.aut` with fresh variables. File `constraint.txt` is responsible for imposing constraints on all fresh variables used in `pre.aut`. Let the output automaton produced by the quantum circuit along with input automaton `pre.aut` be `post.aut`. Then all symbols of leaf transitions in file `spec.aut`, which is used to verify `post.aut`, are predicates. Each predicate, however, has only four variables $\\\$a$, $\\\$b$, $\\\$c$ and $\\\$d$. When the predicate's truth value is evaluated for some leaf transition in `post.aut` whose computed symbol is $(a_{expr},b_{expr},c_{expr},d_{expr},k_{expr})$, these variables will be replaced by $a_{expr}/\sqrt2^{k_{expr}}$, $b_{expr}/\sqrt2^{k_{expr}}$, $c_{expr}/\sqrt2^{k_{expr}}$ and $d_{expr}/\sqrt2^{k_{expr}}$. We say the predicate is "true" for some leaf transition if it is always true under the constraint specified in `constraint.txt`; otherwise the predicate is "false." Similarly, this tool tries to check whether for each symbolic state $s$ in $P$, the output state $C(s)$ matches some tree in $Q$ such that all predicates in the tree are always true under `constraint.txt`. If the result is true, we say the specified property is correct.

---

## Prerequisites
In order to compile the library and the command-line interface to the library,<br>
the following commands need to be executed:
```
$ sudo apt install git
$ sudo apt install make
$ sudo apt install cmake
$ sudo apt install g++
$ sudo apt install libboost-filesystem-dev
$ sudo apt install libboost-test-dev
$ sudo apt install z3
```

Then in the project root directory, execute:
```
$ mkdir build
```

This project has also been tested on Ubuntu 20.04.5 LTS and Ubuntu 22.04.1 LTS.<br>
It should work on other Linux distributions as well.

---

## Compiling
For compiling the source code of the library and the command-line
interface with compiler optimizations turned on, issue the following command
in the root directory of this project:

```
  $ make release
```

In order to compile the library into a form suitable for debugging (i.e., with
optimizations turned off and some additional runtime checks enabled, issue the
following command:

```
  $ make debug
```

It is recommended to run

```
  $ make test
```

from the repository's root directory after compiling the code to run several
unit tests and check that the compiled code passes them all.

---

## Command-Line Interface
The compiled command-line interface is located in

```
$ ./build/cli/autoq
```

There are three modes: concrete probability amplitudes without specification, concrete probability amplitudes with specification, and symbolic probability amplitudes with specification. The program switches to one of this mode according to `argc`, the number of arguments.

1. Concrete probability amplitudes without specification.
```
$ ./build/cli/autoq benchmarks/BernsteinVazirani/02/pre.aut benchmarks/BernsteinVazirani/02/circuit.qasm
Ops [1]:2 [2]:2 [3]:2 [0,0,0,0,0]:0 [1,0,0,0,0]:0 
Automaton Zero
States 0 1 2 3 4 5 6 
Final States 0 
Transitions
[1](1, 2) -> 0
[2](3, 3) -> 1
[2](4, 3) -> 2
[3](5, 5) -> 3
[3](5, 6) -> 4
[0,0,0,0,0] -> 5
[1,0,0,0,0] -> 6
```
The program simply prints the resulting concrete automaton.

2. Concrete probability amplitudes with specification.
```
$ VATA_PATH=/home/alan23273850/libvata/build/cli/vata ./build/cli/autoq benchmarks/Grover/02/pre.aut benchmarks/Grover/02/circuit.qasm benchmarks/Grover/02/post.aut
Ops [1]:2 [2]:2 [3]:2 [-1,0,0,0,0]:0 [0,0,0,0,0]:0 
Automaton Zero
States 0 1 2 3 4 5 6 
Final States 0 
Transitions
[1](1, 2) -> 0
[2](3, 3) -> 2
[2](3, 4) -> 1
[3](5, 5) -> 3
[3](5, 6) -> 4
[-1,0,0,0,0] -> 6
[0,0,0,0,0] -> 5
-
0
```
```
$ VATA_PATH=/home/alan23273850/libvata/build/cli/vata ./build/cli/autoq benchmarks/BernsteinVazirani/02/pre.aut benchmarks/BernsteinVazirani/02/circuit.qasm benchmarks/BernsteinVazirani/02/post.aut
Ops [1]:2 [2]:2 [3]:2 [0,0,0,0,0]:0 [1,0,0,0,0]:0 
Automaton Zero
States 0 1 2 3 4 5 6 
Final States 0 
Transitions
[1](1, 2) -> 0
[2](3, 3) -> 1
[2](4, 3) -> 2
[3](5, 5) -> 3
[3](5, 6) -> 4
[0,0,0,0,0] -> 5
[1,0,0,0,0] -> 6
-
1
```
The program first prints the resulting concrete automaton, and then the verification result, where `1` indicates $C(P)\subseteq Q$ and `0` otherwise. We can observe that the old file `benchmarks/Grover/02/post.aut` in fact does not meet the circuit's output. Notice that in this case environment variable `VATA_PATH` locating the binary built from [this commit](https://github.com/alan23273850/libvata/commit/22ce24661a4c4b1e684961330aa54288f7eda7ca) should be provided in order for AutoQ to run the inclusion checking algorithm. I've also provided [one](https://github.com/alan23273850/AutoQ/blob/main/vata) in the project root directory.

3. Symbolic probability amplitudes with specification.
```
$ ./build/cli/autoq benchmarks/Symbolic/H2/pre.aut benchmarks/Symbolic/H2/circuit.qasm benchmarks/Symbolic/H2/spec.aut benchmarks/Symbolic/H2/constraint.txt
Ops [[1 -> 1]]:2 [[a -> 1],[b -> 1],[c -> 1],[d -> 1],[1 -> 3]]:0 [[e -> 1],[f -> 1],[g -> 1],[h -> 1],[1 -> 3]]:0 
Automaton Zero
States 0 1 2 
Final States 0 
Transitions
[[1 -> 1]](1, 2) -> 0
[[a -> 1],[b -> 1],[c -> 1],[d -> 1],[1 -> 3]] -> 1
[[e -> 1],[f -> 1],[g -> 1],[h -> 1],[1 -> 3]] -> 2
-
1
```
The program first prints the resulting symbolic automaton, where `v -> c` denotes the linear combination contains the term `c * v`, and then the verification result, where `1` indicates that the inclusion checking algorithm returns `true` and `0` indicates `false`. In this case `VATA_PATH` is no longer required since the inclusion checking algorithm for symbolic automata is different from that for concrete automata.

---

## Examples

1. Run a [1+1-qubit version of the Bernstein-Vazirani algorithm](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/BernsteinVazirani/01/circuit.qasm).

The [initial automaton](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/BernsteinVazirani/01/pre.aut) contains an initial $|00\rangle$ quantum state. Since the hidden string is $1$ (and the other qubit is auxiliary), so the [result automaton](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/BernsteinVazirani/01/post.aut) should contain exactly one quantum state $|11\rangle$.

2. [Two consecutive Hadamard gates together](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/Symbolic/H2/circuit.qasm) acts as an identity transformation.

The [initial automaton](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/Symbolic/H2/pre.aut) contains an arbitrary quantum state $(a,b,c,d,3)|0\rangle + (e,f,g,h,3)|1\rangle$. *Please be careful that in symbolic verification all k's in symbols of all leaf transitions must be the same.* Since it uses 8 variables, we should declare them in the [constraint](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/Symbolic/H2/constraint.txt). In this case, values of these variables are arbitrary, so no additional constraint is needed. The result automaton should also contain exactly one original quantum state $(a/\sqrt2^3,b/\sqrt2^3,c/\sqrt2^3,d/\sqrt2^3)|0\rangle$ $+$ $(e/\sqrt2^3,f/\sqrt2^3,g/\sqrt2^3,h/\sqrt2^3)|1\rangle$, so the [specification](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/Symbolic/H2/spec.aut) about $|0\rangle$ should be $\\$a*\sqrt2^3=a$, $\\$b*\sqrt2^3=b$, $\\$c*\sqrt2^3=c$ and $\\$d*\sqrt2^3=d$, and the [specification](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/Symbolic/H2/spec.aut) about $|1\rangle$ should be $\\$a*\sqrt2^3=e$, $\\$b*\sqrt2^3=f$, $\\$c*\sqrt2^3=g$ and $\\$d*\sqrt2^3=h$. Notice that I've implemented the function `pow_sqrt2_k n` in SMT so that a user can directly compute $\sqrt2^n$ with it.

A careful reader may have noticed that the above probability amplitudes may not satisfy $|(a,b,c,d,3)|^2 + |(e,f,g,h,3)|^2 = 1$, but it does not matter since the original constraint still contains all valid quantum states, so the verified property is still true under the real quantum world.
