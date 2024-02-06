# AutoQ 2.0: An automata-based C++ tool for quantum program verification
<!-- [![Build Status](https://travis-ci.org/ondrik/libvata.svg?branch=master)](https://travis-ci.org/ondrik/libvata)-->

---

AutoQ 2.0 is a command-line utility written in C++ for verifying partial correctness of quantum programs automatically based on non-deterministic finite tree automata (TA) along with the concept of Hoare-style proof systems. Consider a triple $\\{P\\}\ C\ \\{Q\\}$, where $P$ and $Q$ are the pre- and post-condition recognizing sets of (pure) quantum states (represented by TA) and $C$ is a quantum program. Let $\mathcal L(.)$ denote the function mapping from a condition $x$ to the set of all quantum states satisfying $x$ (characterized by $x$). Then AutoQ 2.0 essentially checks whether all the quantum states in $\mathcal L(P)$ reach some state in $\mathcal L(Q)$ after the program $C$ is executed. If we further let $C(.)$ denote the function mapping from a condition $x$ to the evolution of $x$ after a program segment $C$ is executed, then AutoQ 2.0 simply checks whether $\mathcal L(C(P)) \subseteq \mathcal L(Q)$.

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

2. We need the Z3 solver to solve the constraints when the automaton contains some symbolic variables. Since the installation process of Z3 may take a lot of work, I have provided the [prebuilt shared library](https://github.com/alan23273850/AutoQ/blob/CAV24/libz3.so.4.12) of [z3-4.12.5](https://github.com/Z3Prover/z3/releases/tag/z3-4.12.5) and the corresponding [header files](https://github.com/alan23273850/AutoQ/tree/CAV24/include/z3) for users' convenience.

3. Finally, in the project's root directory, choose one of the following command to run.

    - `$ make release -j8` (with `8` replaced with the number of threads you want):<br>For compiling the source code of the library and the command-line interface with compiler optimizations turned on.
    - `$ make debug -j8` (with `8` replaced with the number of threads you want):<br>For compiling the library into a form suitable for debugging (i.e., with
optimizations turned off and some additional runtime checks enabled).

Since `$ make release -j8` will ignore assertions in source codes, one should always use `$ make release -j8` for better performance when conducting experiments.

It is recommended to run `$ make test` in the repository's root directory after compiling the source codes to run several unit tests and check that the implementation is correct. This project has also been tested on Ubuntu 22.04.3 LTS. It should work on other Linux distributions as well.

---

## Command-Line Binaries
The compiled command-line binaries are located in `${PROJECT_ROOT}/build/cli/`. The corresponding source codes are located in `${PROJECT_ROOT}/cli/`. The major two are `${PROJECT_ROOT}/cli/autoq_cav24_concrete.cc` and `${PROJECT_ROOT}/cli/autoq_cav24_symbolic.cc`. The others are auxiliary tools but not well-documented.

1. `$ ./build/cli/autoq_cav24_concrete P.{hsl|spec} C.qasm Q.{hsl|spec}`
```
$ ./build/cli/autoq_cav24_concrete benchmarks/control_mini/if-else/pre.hsl benchmarks/control_mini/if-else/circuit.qasm benchmarks/control_mini/if-else/post.hsl
The quantum program has [2] qubits and [5] gates.
The verification process [passed] with a running time of [0.0s] and a memory usage of [14MB].
```

2. `$ ./build/cli/autoq_cav24_symbolic P.{hsl|spec} C.qasm Q.{hsl|spec}`
```
$ ./build/cli/autoq_cav24_symbolic benchmarks/Grover_while/03/pre.spec benchmarks/Grover_while/03/circuit.qasm benchmarks/Grover_while/03/post.spec
The quantum program has [7] qubits and [50] gates.
The verification process [passed] with a running time of [3.1s] and a memory usage of [14MB].
```

These two binaries both support the `-l` option, which is used for printing the statistics whose format is suitable for tables in LaTeX.

---

## How to describe a set of quantum states? `*.hsl`

AutoQ 2.0 provides two file extensions `*.hsl` and `*.spec` for users to indicate which format they use to describe a set of quantum states. The easiest one is `*.hsl`, which does not require users to have a background in tree automata. This file may contain multiple lines. Each line represents a quantum state. A quantum state is naturally described by a linear combination of computational basis states with complex coefficients. Coefficients here can be expressed in [addition `+`], [subtraction `-`], [multiplication `*`] operations on [rationals], $[e^{i2\pi(r)}\ |\ r=k/8,\ k\in\mathbb Z]$ and the [exponentiation `^`] operation with "nonnegative" exponents. Operator precedence follows the standard convention. You can also do $/\sqrt2 ^ k$ by writing `/ sqrt2 ^ k` after the above operations are already done if you wish. Nevertheless, due to the automatic scaling in the verification process, users do not need $/\sqrt2 ^ k$.

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
the above file describes (at least) all quantum states which are linear combinations of $|01\rangle$ and $|10\rangle$ where both of them have the same real amplitude. The *Constraints* section may contain multiple lines. Each line consists of a boolean formula that will be automatically conjoined (with the *and* operator) eventually. Each formula is expressed in logical operations [not `!`], [and `&`], [or `|`] on boolean subformulae. These subformulae are expressed in comparison operations [greater than `>`], [less than `<`] on real numbers and the [equal `=`] operation on complex numbers. Operator precedence follows the standard convention. AutoQ 2.0 also supports two functions `real(.)` and `imag(.)` to extract the real part and the imaginary part of a complex number. A description file contains a quantum state $|s\rangle$ only if $|s\rangle$ satisfies all the boolean formulae in the *Constraints* section.

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

The explanation of `*.spec` is left in appendices.

---

## The Extension to Quantum Programs

The extension from quantum circuits to quantum programs mainly relies on the additional support for control flow statements such as ***branching (if-else)*** and ***looping (while)***. In each case, the control flow can only be decided by the ***measurement outcome***. A measurement outcome can be read from a classical bit, on which the outcome of a ***measurement operator*** on a target qubit is stored.

### Measurement
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
Our implementation of measurement operators is relatively easy! Let $S$ be the set of quantum states right before the measurement operator. This operator will produces two sets $S_0$ and $S_1$ where $S_0$ is produced by collapsing amplitudes of all computational basis states whose target bit in their representation is $1$ to $0$ (***without*** normalizing other non-zero amplitudes) and $S_1$ is produced by collapsing amplitudes of all computational basis states whose target bit in their representation is $0$ to $0$ (***without*** normalizing other non-zero amplitudes). Denote the operator used for producing $S_0$ (resp., $S_1$) by $M[target]_0$ $\big(\text{resp., }M[target]_1\big)$ for simplicity.

An interesting thing is that not normalizing other non-zero amplitudes is reasonable since there is only one positive scaling factor that can be used to normalize an invalid quantum state. In other words, each non-normalized quantum state also represents a unique valid quantum state.

This operator can only be used along with the ***control statement*** of the following structures. Please refer to them for more details.

### Branching (if-else)
```
...
qubit[1] qb; // quantum bit
bit[1] outcome; // classical bit
...
// S: {|0>/√2 + |1>/√2}
outcome[0] = measure qb[0]; // (*)
if (!outcome[0]) { // S0: {|0>}
    x qb[0];
} // S0': {|1>}
else { // S1: {|1>}
    h qb[0];
} // S1': {|0>/√2 - |1>/√2}
// (S0')∪(S1'): {|1>, |0>/√2 - |1>/√2}
```

Before the if-else block, there is a set of quantum states $S$ up to that line. $\color{red}\text{The line (*) is mandatory for the control statement.}$ The measurement operator produces $S_0$ and $S_1$ according to the previous section. Then AutoQ 2.0 executes the if block with $S_0$ (resp., $S_1$) as its initial set, and executes the else block with $S_1$ (resp., $S_0$) as its initial set, if the variable in the control statement is (resp., not) prepended with the negation operator. At the end of this if-else block, the resulting set $(S_0')\cup(S_1')$ is the union of the two resulting sets $S_0'$ after the if block (resp., the else block) and $S_1'$ after the else block (resp., the if block). The remaining execution is then continued with this set.

Note that the statement "else {" cannot be on the same line with the closing bracket "}" of the previous if block since AutoQ 2.0 needs to detect the termination of the previous if block. Also note that the else block can be omitted. In this case, we can simply see that block as an identity gate. Please refer to [this example](https://github.com/alan23273850/AutoQ/tree/CAV24/benchmarks/control_mini/if-else) for more details.

### Looping (while)
```
...
qubit[1] qb; // quantum bit
bit[1] outcome; // classical bit
...
// S: {|0>/√2 + |1>/√2}
outcome[0] = measure qb[0]; // (*)
while (outcome[0]) { // I: {|0>/√2 + |1>/√2} (**)
    h qb[0];
    z qb[0];
    outcome[0] = measure qb[0]; // (*)
}
// M[0]_0(I): {|0>}
```

Unlike the if-else block, the automaton does not split into two when AutoQ 2.0 encounter a while loop. Let $S$ be the set of quantum states right before the while loop and $I$ be the ***loop invariant specified in a file***. $\color{red}\text{The lines (*) and (**) are still mandatory.}$ Instead, AutoQ 2.0 checks whether (1) $S \subseteq I$ and (2) $LoopBody(M[target]_0(I)) \subseteq I$ $\big(\text{resp., }LoopBody(M[target]_1(I)) \subseteq I\big)$ if the variable in the control statement is (resp., not) prepended with the negation operator. After this while loop, AutoQ 2.0 continues with the remaining execution with the set $M[target]_1(I)$ $\big(\text{resp., }M[target]_0(I)\big)$.

Please refer to [this example](https://github.com/alan23273850/AutoQ/tree/CAV24/benchmarks/control_mini/while) for more details.

---

## Appendix - Internal Structures

The following figure demonstrates how we use a tree to represent a $3$-qubit quantum state so that an automaton can encode a set of quantum states.

<img width="412" alt="image" src="https://user-images.githubusercontent.com/10044077/214999182-7e3882d2-47cf-49cb-aa3e-45295072b3f8.png">

TO BE EDITED: Briefly explain what non-deterministic finite tree automaton (TA) is and how it can be used for representing a set of quantum states.

---

## Appendix - Automata Format `*.spec`

Since the underlying structure of a set of quantum states is still a TA in AutoQ 2.0, we reserve the `*.spec` format for users to describe a set of quantum states with a TA. The *Constants* and *Constraints* sections remain, but the *Extended Dirac* section should be replaced with two new sections *Root States* and *Transitions* now. (Automaton) states in a TA can be arbitrary strings (no need to enclose with double quotation marks).

### # Root States
This section is responsible for specifying a set of root states. It should contain only one line starting with "Root States" and ending with a set of root states separated by whitespaces.

### # Transitions
This section is responsible for specifying a set of transitions. One transition per line. A (bottom-up) transition $f(q_1, q_2, ..., q_n) \to q$ is written as `[f](q_1, q_2, ..., q_n) -> q`. Note that in this tool, a symbol can only be a positive integer $i$ with arity $2$ for specifying the $i$-th qubit and can be any expression describing a complex number with arity $0$ for specifying the amplitude of some computational basis states.

We close this section with the following example.
```
Root States 0
Transitions
[1](1, 2) -> 0
[1](2, 3) -> 0
[1](2, 4) -> 0
[1](2, 5) -> 0
[1](2, 6) -> 0
[1](7, 2) -> 0
[1](8, 2) -> 0
[1](9, 2) -> 0
[2](10, 10) -> 2
[2](10, 11) -> 7
[2](10, 12) -> 4
[2](10, 13) -> 9
[2](10, 14) -> 6
[2](15, 10) -> 1
[2](16, 10) -> 3
[2](17, 10) -> 8
[2](18, 10) -> 5
[3](19, 19) -> 10
[3](19, 20) -> 17
[3](19, 21) -> 18
[3](19, 22) -> 13
[3](19, 23) -> 14
[3](24, 19) -> 15
[3](25, 19) -> 16
[3](26, 19) -> 11
[3](27, 19) -> 12
[4](28, 28) -> 19
[4](29, 30) -> 24
[4](30, 29) -> 25
[4](30, 31) -> 27
[4](30, 32) -> 21
[4](30, 33) -> 23
[4](31, 30) -> 26
[4](32, 30) -> 20
[4](33, 30) -> 22
[5](34, 34) -> 28
[5](35, 35) -> 30
[5](35, 36) -> 31
[5](35, 37) -> 33
[5](36, 35) -> 29
[5](37, 35) -> 32
[6](38, 38) -> 34
[6](39, 38) -> 35
[6](40, 38) -> 36
[6](41, 38) -> 37
[7](42, 42) -> 38
[7](43, 43) -> 39
[7](43, 44) -> 41
[7](44, 43) -> 40
[8](45, 45) -> 42
[8](46, 45) -> 43
[8](47, 45) -> 44
[9](48, 48) -> 45
[9](48, 49) -> 46
[9](48, 50) -> 47
[p1] -> 49
[p2] -> 48
[p3] -> 50
Constraints
imag(p1) = 0
real(p1) ^ 2 < 1/8
p2 = 0
imag(p3) = 0
real(p3) ^ 2 > 7/8
```
