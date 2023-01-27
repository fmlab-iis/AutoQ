# AutoQ: An automata-based C++ tool for quantum circuit verification
<!-- [![Build Status](https://travis-ci.org/ondrik/libvata.svg?branch=master)](https://travis-ci.org/ondrik/libvata)-->

---

AutoQ is a (highly optimized?) command-line utility written in C++ for Hoare-style quantum circuit verification based on non-deterministic finite tree automata. The following figure demonstrates how we use a tree to represent a 3-qubit quantum state, so an automaton can, of course, be used to encode a set of quantum states. The symbol of each internal transition should be a positive integer $n$ indicating the $n$-th qubit, and the symbol of each leaf transition is a 5-tuple of integers $(a,b,c,d,k)$ describing the probability amplitude $(a+b\omega+c\omega^2+d\omega^3) / \sqrt2^k$ of some computational basis state, where $w = \cos(\pi/4) + i\sin(\pi/4)$.

<img width="412" alt="image" src="https://user-images.githubusercontent.com/10044077/214999182-7e3882d2-47cf-49cb-aa3e-45295072b3f8.png">

As for Hoare-style verification, there are three main components: `pre.aut`, `circuit.qasm` and `post.aut`. The first file `pre.aut` describes an automaton that encodes a set $P$ of quantum states. The second file `circuit.qasm` describes a quantum circuit $C$ in QASM format. Notice that this format is not able to initialize the initial quantum state. The last file `post.aut` describes an automaton that encodes another set $Q$ of quantum states. Finally this tool tries to check whether for each state $s$ in $P$, the output state $C(s)$ lies in the set $Q$. If the result is true, we say the specified property is correct.

This tool can also be generalized to support "symbolic" quantum states. In this case, we simply replace some entries of leaf transitions in `pre.aut` with fresh variables. File `constraint.txt` is responsible for imposing constraints on all fresh variables used in `pre.aut`. Let the output automaton produced by the quantum circuit along with input automaton `pre.aut` be `post.aut`. Then all symbols of leaf transitions in file `spec.aut`, which is used to verify `post.aut`, are predicates. Each predicate, however, has only four variables $\\\$a$, $\\\$b$, $\\\$c$ and $\\\$d$. When the predicate's truth value is evaluated for some leaf transition in `post.aut` whose computed symbol is $(a_{expr},b_{expr},c_{expr},d_{expr},k_{expr})$, these variables will be replaced by $a_{expr}/\sqrt2^{k_{expr}}$, $b_{expr}/\sqrt2^{k_{expr}}$, $c_{expr}/\sqrt2^{k_{expr}}$ and $d_{expr}/\sqrt2^{k_{expr}}$. We say the predicate is "true" for some leaf transition if it is always true under the constraint specified in `constraint.txt`; otherwise the predicate is "false." Similarly, this tool tries to check whether for each symbolic state $s$ in $P$, the output state $C(s)$ matches some tree in $Q$ such that all predicates in the tree are always true under `constraint.txt`. If the result is true, we say the specified property is correct.

---

## Prerequisites
<!-- In order to compile the library and the command-line interface to the library
the following packages need to be installed on your system:

```
  git (>= 1.6.0.0)
  cmake (>= 2.8.2)
  gcc (>= 4.8.0)
  libboost-filesystem-dev (>= 1.54.0)
  libboost-system-dev (>= 1.54.0)
  libboost-test-dev (>= 1.54.0)
``` -->

---

## Compiling
For compiling the source code of the library and the command-line
interface with compiler optimizations turned on, issue the following command
in the root directory of the library:

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
$ ./build/cli/autoq benchmarks/Grover/02/pre.aut benchmarks/Grover/02/circuit.qasm
```

2. Concrete probability amplitudes with specification.
```
$ VATA_PATH=/home/alan23273850/libvata/build/cli/vata ./build/cli/autoq benchmarks/Grover/02/pre.aut benchmarks/Grover/02/circuit.qasm benchmarks/Grover/02/post.aut
```
Notice that in this case environment variable `VATA_PATH` locating the binary built from [this commit](https://github.com/alan23273850/libvata/commit/22ce24661a4c4b1e684961330aa54288f7eda7ca) should be provided in order for AutoQ to run the inclusion checking algorithm.

3. Symbolic probability amplitudes with specification.
```
$ ./build/cli/autoq benchmarks/SymbolicGrover/03/pre.aut benchmarks/SymbolicGrover/03/circuit.qasm benchmarks/SymbolicGrover/03/spec.aut benchmarks/SymbolicGrover/03/constraint.txt
```
In this case `VATA_PATH` is no longer required since the inclusion checking algorithm for symbolic automata is different from that for concrete automata.

---

## Examples

1. Run a [1+1-qubit version of the Bernstein-Vazirani algorithm](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/BernsteinVazirani/01/circuit.qasm).

The [initial automaton](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/BernsteinVazirani/01/pre.aut) contains an initial $|00\rangle$ quantum state. Since the hidden string is $1$ (and the other qubit is auxiliary), so the [result automaton](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/BernsteinVazirani/01/post.aut) should contain exactly one quantum state $|11\rangle$.

2. [Two consecutive Hadamard gates together](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/SymbolicGrover/H2/circuit.qasm) acts as an identity transformation.

The [initial automaton](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/SymbolicGrover/H2/pre.aut) contains an arbitrary quantum state $(a,b,c,d,3)|0\rangle + (e,f,g,h,3)|1\rangle$. Since it uses 8 variables, we should declare them in the [constraint](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/SymbolicGrover/H2/constraint.txt). In this case, values of these variables are arbitrary, so no additional constraint is needed. The result automaton should also contain exactly one original quantum state $(a/\sqrt2^3,b/\sqrt2^3,c/\sqrt2^3,d/\sqrt2^3)|0\rangle$ $+$ $(e/\sqrt2^3,f/\sqrt2^3,g/\sqrt2^3,h/\sqrt2^3)|1\rangle$, so the [specification](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/SymbolicGrover/H2/spec.aut) about $|0\rangle$ should be $\\$a*\sqrt2^3=a$, $\\$b*\sqrt2^3=b$, $\\$c*\sqrt2^3=c$ and $\\$d*\sqrt2^3=d$, and the [specification](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/SymbolicGrover/H2/spec.aut) about $|1\rangle$ should be $\\$a*\sqrt2^3=e$, $\\$b*\sqrt2^3=f$, $\\$c*\sqrt2^3=g$ and $\\$d*\sqrt2^3=h$. Notice that I've implemented the function `pow_sqrt2_k n` in SMT so that a user can directly compute $\sqrt2^n$ with it.

A careful reader may have noticed that the above probability amplitudes may not satisfy $|(a,b,c,d,3)|^2 + |(e,f,g,h,3)|^2 = 1$, but it does not matter since the original constraint still contains all valid quantum states, so the verified property is still true under the real quantum world.

<!--## Input Format
 AutoQ so far supports only the Timbuk format of tree automata. The format is
specified by the following grammar with the start symbol:

```
  <file>            : 'Ops' <label_list> <automaton>

  <label_list>      : <label_decl> <label_decl> ... // a list of label declarations

  <label_decl>      : string ':' int // a symbol declaration (the name and the arity)

  <automaton>       : 'Automaton' string 'States' <state_list> 'Final States' <state_list> 'Transitions' <transition_list>

  <state_list>      : <state> <state> ... // a list of states

  <state>           : string // the name of a state

  <transition_list> : <transition> <transition> ... // a list of transitions

  <transition>      : <label> '(' <state> ',' <state> ',' ... ')' '->' <state> // a transition

  <label>           : string // the name of a label
```

An example could look like this:

```
Ops a:0 b:1 c:2

Automaton A
States q0 q1 q2
Final States q2 
Transitions
a() -> q0
b(q0) -> q1
c(q1, q1) -> q1
c(q1, q1) -> q2
c(q2, q2) -> q2
``` -->

<!-- ## Acknowledgement
This work was supported by the Czech Science Foundation (within projects
P103/10/0306 and 102/09/H042), the Czech Ministry of Education (projects COST
OC10009 and MSM 0021630528), and the EU/Czech IT4Innovations Centre of
Excellence project CZ.1.05/1.1.00/02.0070. -->

<!-- ## Contact
If you have further questions, do not hesitate to contact the authors:
  * Ondrej Lengal  <lengal@fit.vutbr.cz> (corresponding author)
  * Jiri Simacek   <simacek@fit.vutbr.cz>
  * Tomas Vojnar   <vojnar@fit.vutbr.cz>
  * Martin Hruska  <ihruska@fit.vutbr.cz>
  * Lukas Holik    <holik@fit.vutbr.cz> -->
