# AutoQ 2.0: An automata-based C++ tool for quantum program verification
<!-- [![Build Status](https://travis-ci.org/ondrik/libvata.svg?branch=master)](https://travis-ci.org/ondrik/libvata)-->

---

AutoQ 2.0 is a command-line utility written in C++ for verifying partial correctness of quantum programs automatically based on non-deterministic finite tree automata (NFTA) along with the concept of Hoare-style proof systems. Consider a triple $\\{P\\}\ C\ \\{Q\\}$, where $P$ and $Q$ are the pre- and post-condition recognizing sets of (pure) quantum states (represented by NFTA) and $C$ is a quantum program. Let $\mathcal L(.)$ denote the mapping from a condition $x$ to the set of all quantum states satisfying $x$ (characterized by $x$). Then AutoQ 2.0 essentially checks whether all the quantum states in $\mathcal L(P)$ reach some state in $\mathcal L(Q)$ after the program $C$ is executed. If we further let $C(.)$ denote the mapping from a condition $x$ to the evolution of $x$ after a program segment $C$ is executed, then AutoQ 2.0 simply checks whether $\mathcal L(C(P)) \subseteq \mathcal L(Q)$.

The following is a mini illustration of the functionality of this tool.
```
OPENQASM 3;
include "stdgates.inc";
qubit[2] qb; // quantum bits

//    P: {|00>, 0.5|00> + 0.5|01> + 0.5|10> + 0.5|11>}
x qb[0];
//       {|10>, 0.5|10> + 0.5|11> + 0.5|00> + 0.5|01>}
x qb[1];
//       {|11>, 0.5|11> + 0.5|10> + 0.5|01> + 0.5|00>}
h qb[1];
// C(P): {|10>/√2 - |11>/√2, |10>/√2 + |00>/√2}
/******************************************************/
//   Q1: {|10>/√2 - |11>/√2, |10>/√2 + |00>/√2} -> pass
//   Q2: {|10>/√2 - |11>/√2, |10>/√2 - |00>/√2} -> fail
```
The program starts from an initial set of quantum states $\mathcal L(P)$. Right after executing each gate, AutoQ 2.0 computes and stores the evolution of these quantum states for later use. At the end of the quantum program, AutoQ 2.0 checks whether the set $\mathcal L(Q)$ contains the set $\mathcal L(C(P))$. In the above example, if we take the postcondition $Q_1 = C(P)$, the verification passes. If we take another postcondition $Q_2$ such that there is some quantum state $|10\rangle/\sqrt2 + |00\rangle/\sqrt2 \in \mathcal L(C(P))$ but $\not\in \mathcal L(Q_2)$, the verification fails.

Our program currently supports $X$, $Y$, $Z$, $H$, $T$, $T^\dagger$, $S$, $S^\dagger$, $R_x(\pi/2)$, $R_y(\pi/2)$, $CX$, $CZ$, $CCX$, $SWAP$ quantum gates. The version of OpenQASM should be 3.0.

---

## Installation and Compilation

1. Install the following dependencies via the command line.<br>
`$ sudo apt install git make cmake g++ libboost-filesystem-dev libboost-test-dev`.

2. We need the Z3 solver to solve the constraints when the NFTA contains some symbolic variables. Since the installation process of Z3 may take a lot of work, I have provided the [prebuilt shared library](https://github.com/alan23273850/AutoQ/blob/CAV24/libz3.so.4.12) of [z3-4.12.5](https://github.com/Z3Prover/z3/releases/tag/z3-4.12.5) and the corresponding [header files](https://github.com/alan23273850/AutoQ/tree/CAV24/include/z3) for users' convenience.

3. Finally, in the project's root directory, choose one of the following command to run.

    - `$ make release -j8` (with `8` replaced with the number of threads you want):<br>For compiling the source code of the library and the command-line interface with compiler optimizations turned on.
    - `$ make debug -j8` (with `8` replaced with the number of threads you want):<br>For compiling the library into a form suitable for debugging (i.e., with
optimizations turned off and some additional runtime checks enabled).

Since `$ make release -j8` will ignore assertions in source codes, one should always use `$ make release -j8` for better performance when conducting experiments.

It is recommended to run `$ make test` in the repository's root directory after compiling the source codes to run several unit tests and check that the implementation is correct. This project has also been tested on Ubuntu 22.04.3 LTS. It should work on other Linux distributions as well.

---

## Command-Line Binaries
The compiled command-line binaries are located in `${PROJECT_ROOT}/build/cli/`. The corresponding source codes are located in `${PROJECT_ROOT}/cli/`. The major one is `${PROJECT_ROOT}/cli/autoq_cav24.cc`. The others are auxiliary tools but not well-documented.

The usage is `$ ./build/cli/autoq_cav24 P.{hsl|spec} C.qasm Q.{hsl|spec}`.
```
$ ./build/cli/autoq_cav24 benchmarks/Grover_while/03/pre.spec benchmarks/Grover_while/03/circuit.qasm benchmarks/Grover_while/03/post.spec
The quantum program has [7] qubits and [50] gates.
The verification process [passed] with a running time of [0.6s] and a memory usage of [44MB].
```

This binary also supports the `-l` option, which is used for printing the statistics whose format is suitable for tables in LaTeX.

---

## How to describe a set of quantum states? `*.hsl`

AutoQ 2.0 provides two file extensions `*.hsl` and `*.spec` for users to indicate which format they use to describe a set of quantum states. The easiest one is `*.hsl`, which does not require users to have a background in NFTA. This file may contain multiple lines. Each line represents a quantum state. A quantum state is naturally described by a linear combination of computational basis states with complex coefficients. Coefficients here can be expressed in [addition `+`], [subtraction `-`], [multiplication `*`] operations on [rationals], $[e^{i2\pi(r)}\ |\ r=k/8,\ k\in\mathbb Z]$ and the [exponentiation `^`] operation with "nonnegative" exponents. Operator precedence follows the standard convention. You can also do $/\sqrt2 ^ k$ by writing `/ sqrt2 ^ k` after the above operations are already done if you wish. Nevertheless, due to the automatic scaling in the verification process, users do not need $/\sqrt2 ^ k$.

### # Extended Dirac
Here is one example.
```
Extended Dirac
(-1 + -1 * ei2pi(2/8) + -2 * ei2pi(3/8)) |10> + ei2pi(3/8) |11> - ei2pi(1/8) |01>
ei2pi(1/8) |00> + (1 + 1 * ei2pi(2/8) + -2 * ei2pi(3/8)) |11> - ei2pi(3/8) |10>
```
This file describes two quantum states $-e^{i2\pi(1/8)}\ |01\rangle + (-1 - e^{i2\pi(2/8)} - 2\cdot e^{i2\pi(3/8)})\ |10\rangle + e^{i2\pi(3/8)}\ |11\rangle$ and $e^{i2\pi(1/8)}\ |00\rangle - e^{i2\pi(3/8)}\ |10\rangle + (1 + e^{i2\pi(2/8)} - 2\cdot e^{i2\pi(3/8)})\ |11\rangle$. If there are so many states having the same amplitude, you can also use the "wildcard state" $|\*\rangle$ at the end of a line to denote all other computational basis states whose amplitudes have not been specified so far. For instance, $0.5\ |00\rangle - 0.5\ |*\rangle = 0.5\ |00\rangle - 0.5\ |01\rangle - 0.5\ |10\rangle - 0.5\ |11\rangle$.

### # Constants
For simplicity, one can define some complex constants in the *Constants* section before the *Extended Dirac* section, and the example becomes
```
Constants
c1 := ei2pi(1/8)
c2 := ei2pi(2/8)
c3 := ei2pi(3/8)
Extended Dirac
(-1 + -1 * c2 + -2 * c3) |10> + c3 |11> - c1 |01>
c1 |00> + (1 + 1 * c2 + -2 * c3) |11> - c3 |10>
```

### # Variables and Constraints
Nonconstant tokens not defined in the Constants section are automatically regarded as *free symbolic variables*. These variables may have some constraints such as being nonzero. One can impose some constraints on these variables in the *Constraints* section after the *Extended Dirac* section. For instance,
```
Constants
c0 := 0
Extended Dirac
c0 |00> + c0 |11> + v |*>
Constraints
imag(v) = 0
```
the above file describes (at least) all quantum states which are linear combinations of $|01\rangle$ and $|10\rangle$ where both of them have the same real amplitude.

The *Constraints* section may contain multiple lines. Each line consists of a boolean formula that will be automatically conjoined (with the *and* operator) eventually. Each formula is expressed in logical operations [not `!`], [and `&`], [or `|`] on boolean subformulae. These subformulae are expressed in comparison operations [greater than `>`], [less than `<`] on real numbers and the [equal `=`] operation on complex numbers. Operator precedence follows the standard convention. AutoQ 2.0 also supports two functions `real(.)` and `imag(.)` to extract the real part and the imaginary part of a complex number.

One may want to take the absolute value of a ***real*** number in some applications. Due to the branching nature of this operation, the SMT solver may not be able to solve constraints involving this operation. Please use `(.) ^ 2` as an alternative instead.

We say a description file contains a quantum state $|s\rangle$ only if $|s\rangle$ satisfies all the boolean formulae in the *Constraints* section.

### # Tensor Products and Existentially Quantified Variables
For convenience, AutoQ 2.0 also supports the ***tensor product operator*** `#`. The usage is very easy: just put `#` between two quantum states $|x\rangle$ and $|y\rangle$ in a line to denote the quantum state $|x\rangle \otimes |y\rangle$. AutoQ 2.0 also supports the ***existentially quantified variable*** `\/ |i|=n :` over all $n$-bit binary strings. This variable is used to constrain all basis states $|i\rangle$ appearing after this notation in a line. If there is some quantum state $|s\rangle$ satisfying this line for some $i$, then we say $|s\rangle$ is described in this line.

One more example to get a closer look at `*.hsl`.
```
Extended Dirac
\/ |i|=3 : |i> # vH |i> + vL |*> # |000>
Constraints
imag(vH) = 0
imag(vL) = 0
vH > vL
vL > 0
```
describes the set of states<br>
<img width="315" alt="image" src="https://user-images.githubusercontent.com/10044077/217997027-4dec8f23-811d-4747-86b3-e95d37b9ec69.png">
<br>where $v_h > v_\ell > 0$.

Finally, we should be noticed that not all strings described by `*.hsl` are valid quantum states. For instance, the sum of absolute squares of amplitudes of all computational basis states may not be $1$.

***Our current implementation of `*.hsl` has not been optimized yet. If the number of qubits is greater than 10, we strongly recommend you use `*.spec`. The explanation of `*.spec` is left in appendices.***

---

## The Extension to Quantum Programs

AutoQ 1.0 only supports quantum circuits, but AutoQ 2.0 also supports quantum programs in addition. The extension focuses on the additional support for control flow statements such as ***branching (if-else)*** and ***looping (while)***. In this section, we will introduce these two kinds of control flow statements, along with ***measurement***, which is used to decide the control flow path.

### # Measurement
```
...
qubit[1] qb; // quantum bit
bit[1] outcome; // classical bit
...
//  S: {|0>/√2 + |1>/√2}
outcome[0] = measure qb[0];
// S0: {|0>/√2}
// S1: {|1>/√2}
```
The usage of a measurement operator should be `[a classical bit: c] = measure [a quantum bit: q];`.

The evolution of the set of quantum states in AutoQ 2.0 is described as follows. Let $S$ be the set of quantum states right before the measurement operator. There are two possible outcomes `q=0` and `q=1` of this operator, so after the measurement we define one set $\displaystyle S_0 \coloneqq \\Bigg\\{\ |s'\rangle = \sum_{i\in\\{0,1\\}^n,\ i_q=0} a_i\ |i\rangle\ \Bigg|\ |s\rangle \in S,\ |s\rangle = \sum_{i\in\\{0,1\\}^n} a_i\ |i\rangle \\Bigg\\}$ and another set $\displaystyle S_1 \coloneqq \\Bigg\\{\ |s'\rangle = \sum_{i\in\\{0,1\\}^n,\ i_q=1} a_i\ |i\rangle\ \Bigg|\ |s\rangle \in S,\ |s\rangle = \sum_{i\in\\{0,1\\}^n} a_i\ |i\rangle \\Bigg\\}$. A careful reader may notice that for computational simplicity, AutoQ 2.0 does not normalize the amplitudes after measurements, but it is still reasonable since there is only one positive scaling factor that can be used to normalize an invalid quantum state. In other words, each non-normalized quantum state also represents a unique valid quantum state.

***This operator cannot be used standalone in AutoQ 2.0***, it can only be used along with ***branching (if-else)*** and ***looping (while)*** introduced below. Please refer to them for more details.

### # Branching (if-else)
```
...
qubit[1] qb; // quantum bit
bit[1] outcome; // classical bit
...
// S: {|0>/√2 + |1>/√2}
outcome[0] = measure qb[0];
if (!outcome[0]) { // S0: {|0>/√2}
    x qb[0];
} // S0': {|1>/√2}
else { // S1: {|1>/√2}
    h qb[0];
} // S1': {|0>/2 - |1>/2}
// (S0')∪(S1'): {|1>/√2, |0>/2 - |1>/2}
```
The usage of an if-else block in general should be
```
[a classical bit: c] = measure [a quantum bit: q];
if (c) {
    ...
}
else {
    ...
}
```
, but sometimes `if (c)` may be replaced with `if (!c)` and sometimes the `else {...}` block may be omitted. The reason why we need a measurement operator at the beginning is that we need to produce $S_0$ and $S_1$ explained in the *Measurement* section before entering the if-else block.

AutoQ 2.0 will execute the `if` block with $S_1$ as its initial set and produce the resulting set $S_1'$, and will execute the `else` block with $S_0$ as its initial set and produce the resulting set $S_0'$. Right after this if-else block, AutoQ 2.0 will obtain the union $(S_0')\cup(S_1')$, and the remaining execution is then continued with this set. If `if (c)` is replaced with `if (!c)`, then the `if` (resp., `else`) block will be executed with $S_0$ (resp., $S_1$) as its initial set.

If the `else` block is omitted, AutoQ 2.0 simply sees that block as an identity gate.

A subtle thing should be noticed is that the statement `else {` cannot be on the same line with the closing bracket `}` of the previous `if` block since AutoQ 2.0 needs to detect the termination of the previous `if` block. Please refer to [this example](https://github.com/alan23273850/AutoQ/tree/CAV24/benchmarks/control_mini/if-else) for its usage.

### # Looping (while)
```
...
qubit[1] qb; // quantum bit
bit[1] outcome; // classical bit
...
// S: {|0>/√2 + |1>/√2}
outcome[0] = measure qb[0];
while (outcome[0]) { // I: {|0>/√2 + |1>/√2}
    h qb[0];
    z qb[0];
    outcome[0] = measure qb[0];
}
// {|0>/√2}
```
The usage of a while loop in general should be
```
[a classical bit: c] = measure [a quantum bit: q];
while (c) { // invariant.{hsl|spec}
    ...
    c = measure q;
}
```
, but sometimes `while (c)` may be replaced with `while (!c)`.

Unlike the if-else block, the NFTA does not split into two after a while loop. Instead, AutoQ 2.0 first checks whether the set of quantum states $S$ prior to the measurement operator is included in the set of quantum states $I$ specified in the invariant file `invariant.{hsl|spec}` (i.e., $S \subseteq I$). If the answer is no, the verification of the whole quantum program fails. Otherwise, AutoQ 2.0 continues to check whether the set evolution after $\displaystyle\\Bigg\\{\ \sum_{i\in\\{0,1\\}^n,\ i_q=1} a_i\ |i\rangle\ \Bigg|\ |s\rangle \in I,\ |s\rangle = \sum_{i\in\\{0,1\\}^n} a_i\ |i\rangle \\Bigg\\}$ running through the loop body is still included in $I$. If the answer is still yes, then the verification of this loop passes and AutoQ 2.0 continues the remaining execution with $\displaystyle\\Bigg\\{\ \sum_{i\in\\{0,1\\}^n,\ i_q=0} a_i\ |i\rangle\ \Bigg|\ |s\rangle \in I,\ |s\rangle = \sum_{i\in\\{0,1\\}^n} a_i\ |i\rangle \\Bigg\\}$ after this while loop.

If `while (c)` is replaced with `while (!c)`, then $i_q=1$ and $i_q=0$ should be interchanged in the above description.

The file paths for specifying loop invariants are relative to the circuit file's location. Please refer to [this example](https://github.com/alan23273850/AutoQ/tree/CAV24/benchmarks/control_mini/while) for its usage.

---

## Appendix - Internal Structures

The following figure demonstrates how we use a tree to represent a $3$-qubit quantum state so that an NFTA can encode a set of quantum states. The symbol $000$ stores the amplitude of the computational basis state $|000\rangle$, $001$ stores the amplitude of the computational basis state $|001\rangle$, etc.

<img width="350" alt="image" src="https://user-images.githubusercontent.com/10044077/214999182-7e3882d2-47cf-49cb-aa3e-45295072b3f8.png">

Please refer to [Example 1.1.3](https://inria.hal.science/hal-03367725v1/document#page=23) for a better understanding of NFTA. In short, the only difference between NFTA and NFA is that NFAs must have a starting state, but NFTAs do not. The tree language recognition procedure checks if an NFTA $\mathcal A$ accepts a tree $T$ (not necessarily binary) by iteratively reducing each component in a tree

<img width="350" alt="image" src="https://github.com/alan23273850/AutoQ/assets/10044077/db966d58-37ad-4b0d-be40-f57febf82634">

to a (unary) state $q$ provided that the transition (rule) $f(q_1, q_2, ..., q_n) \to q$ is present in $\mathcal A$ until no further reductions can be performed. There are many ways to reduce a tree, so we say $\mathcal A$ accepts $T$ if there exists a sequence of reductions such that the eventual resulting (unary) state is an $\mathcal A$'s final state (called ***root state*** in AutoQ 2.0). Leaf symbols (amplitudes) have no children, so they can only be reduced with $0$-arity transitions.

---

## Appendix - NFTA Format `*.spec`

Since the underlying structure of a set of quantum states is still an NFTA in AutoQ 2.0, we reserve the `*.spec` format for users to describe a set of quantum states with an NFTA. The *Constants* and *Constraints* sections remain, but the *Extended Dirac* section should be replaced with two new sections *Root States* and *Transitions* now. (Unary) states in an NFTA can be arbitrary strings (no need to enclose with double quotation marks).

### # Root States
This section is responsible for specifying a set of root states. It should contain only one line starting with "Root States" and ending with a set of root states separated by whitespaces.

### # Transitions
This section is responsible for specifying a set of transitions. One transition per line. A (bottom-up) transition $f(q_1, q_2, ..., q_n) \to q$ is written as `[f](q1, q2, ..., qn) -> q`. Note that in this tool, a symbol can only be a positive integer $i$ with arity $2$ for specifying the $i$-th qubit and can be any expression describing a complex number with arity $0$ for specifying the amplitude of some computational basis states.

We close this section with the following example.
```
Constants
c0 := 0
Root States aR bR
Transitions
[1](aL1, aL1) -> aR
[2](qLow, q0) -> aL1
[1](bL1, bL1) -> bR
[2](q0, qHigh) -> bL1
[c0] -> q0
[p1] -> qLow
[p2] -> qHigh
Constraints
imag(p1) = 0
p1 ^ 2 < 1/8
imag(p2) = 0
p2 ^ 2 > 7/8
```
