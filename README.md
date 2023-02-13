# AutoQ: An automata-based C++ tool for quantum circuit verification
<!-- [![Build Status](https://travis-ci.org/ondrik/libvata.svg?branch=master)](https://travis-ci.org/ondrik/libvata)-->

---

AutoQ is a command-line utility written in C++ for Hoare-style quantum circuit verification based on non-deterministic finite tree automata. The following figure demonstrates how we use a tree to represent a 3-qubit quantum state, so an automaton can be used to encode a set of quantum states. The symbol of each internal transition should be a positive integer $n$ indicating the $n$-th qubit, and the symbol of each leaf transition is a 5-tuple of integers $(a,b,c,d,k)$ describing the probability amplitude $(a+b\omega+c\omega^2+d\omega^3) / \sqrt2^k$ of some computational basis state, where $w = \cos(\pi/4) + i\sin(\pi/4)$.

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
$ VATA_PATH=$PWD/vata ./build/cli/autoq benchmarks/Grover/02/pre.aut benchmarks/Grover/02/circuit.qasm benchmarks/Grover/02/post.aut
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
$ VATA_PATH=$PWD/vata ./build/cli/autoq benchmarks/BernsteinVazirani/02/pre.aut benchmarks/BernsteinVazirani/02/circuit.qasm benchmarks/BernsteinVazirani/02/post.aut
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
Ops [1]:2 [a,b,c,d,3]:0 [e,f,g,h,3]:0 
Automaton Zero
States 0 1 2 
Final States 0 
Transitions
[1](1, 2) -> 0
[a,b,c,d,3] -> 1
[e,f,g,h,3] -> 2
-
1
```
The program first prints the resulting symbolic automaton, where each entry in 5-tuples is a human-readable format of the linear combination, and then the verification result, where `1` indicates that the inclusion checking algorithm returns `true` and `0` indicates `false`. In this case `VATA_PATH` is no longer required since we use another inclusion checking algorithm for symbolic automata.

---

## Examples

1. Run a [1+1-qubit version of the Bernstein-Vazirani algorithm](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/BernsteinVazirani/01/circuit.qasm).

The [initial automaton](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/BernsteinVazirani/01/pre.aut) contains an initial $|00\rangle$ quantum state. Since the hidden string is $1$ (and the other qubit is auxiliary), so the [result automaton](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/BernsteinVazirani/01/post.aut) should contain exactly one quantum state $|11\rangle$.

2. [Two consecutive Hadamard gates together](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/Symbolic/H2/circuit.qasm) acts as an identity transformation.

The [initial automaton](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/Symbolic/H2/pre.aut) contains an arbitrary quantum state $(a,b,c,d,3)|0\rangle + (e,f,g,h,3)|1\rangle$. *Please be careful that in symbolic verification all k's in symbols of all leaf transitions must be the same.* Since it uses 8 variables, we should declare them in the [constraint](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/Symbolic/H2/constraint.txt). In this case, values of these variables are arbitrary, so no additional constraint is needed. The result automaton should also contain exactly one original quantum state $(a/\sqrt2^3,b/\sqrt2^3,c/\sqrt2^3,d/\sqrt2^3)|0\rangle$ $+$ $(e/\sqrt2^3,f/\sqrt2^3,g/\sqrt2^3,h/\sqrt2^3)|1\rangle$, so the [specification](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/Symbolic/H2/spec.aut) about $|0\rangle$ should be $\\$a*\sqrt2^3=a$, $\\$b*\sqrt2^3=b$, $\\$c*\sqrt2^3=c$ and $\\$d*\sqrt2^3=d$, and the [specification](https://github.com/alan23273850/AutoQ/blob/main/benchmarks/Symbolic/H2/spec.aut) about $|1\rangle$ should be $\\$a*\sqrt2^3=e$, $\\$b*\sqrt2^3=f$, $\\$c*\sqrt2^3=g$ and $\\$d*\sqrt2^3=h$. Notice that I've implemented the function `pow_sqrt2_k n` in SMT so that one can directly compute $\sqrt2^n$ with it.

A careful reader may have noticed that the above probability amplitudes may not satisfy $|(a,b,c,d,3)|^2 + |(e,f,g,h,3)|^2 = 1$, but it does not matter since the original constraint still contains all valid quantum states, so the verified property is still true under the real quantum world.

---

## Automata Format
AutoQ so far supports only the Timbuk format of tree automata. The format is
specified by the following grammar with the start symbol \<file\>:

```
  <file>            : 'Final States' <state_list> <newline> 'Transitions' <newline> <transition_list>

  <state_list>      : ' ' <state> ' ' <state> ... // a list of states

  <state>           : {int ≥ 0} // nonnegative state id

  <transition_list> : <transition> <transition> ... // a list of transitions

  <transition>      : <symbol> '(' <state> ',' <state> ',' ... ')' ' -> ' <state> <newline> // a transition

  <symbol>          : '[' {int > 0} ']' // a positive qubit id
                    | '[' {int} ',' {int} ',' {int} ',' {int} ',' {int} ']' // a probability amplitude

  <newline>         : '\n' // or another character acting as a newline character
```

Only final states and transitions are sufficient. In this repository some automaton files may have
other information, but in fact they are no longer required. Also notice that there are two formats
of \<symbol\>. The first format [n] indicates n-th qubit (counting from 1) of the circuit. It is an
internal transition and must have two child states. The second format [a,b,c,d,k] indicates the
probability amplitude $(a+b\omega+c\omega^2+d\omega^3) / \sqrt2^k$ of some computational basis state,
where $w = \cos(\pi/4) + i\sin(\pi/4)$. It is a leaf transition and must have no any child state.
In the whole file, all [\_,\_,\_,\_,k]'s of leaf transitions must be the same!

An example could look like this:
```
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

---

## Build an automaton from states

We also provide two binaries for the user to construct an automaton that accepts all quantum states described by the user and rejects other quantum states. The binary `build/cli/caut_from_states` is for concrete probability amplitude, and `build/cli/saut_from_states` is for symbolic probability amplitude. One can describe a set of states with the following grammar starting from \<states\>:

```
  <states>          : <state>
                    | '|i|=' {int > 0} ' ' <state>
                    | <states> <newline> <state>

  <state>           : {binary string} ':' <amplitude> ' ' ... {binary string} ':' <amplitude> ' *:' <amplitude>
                    | 'i:' <amplitude> ' *:' <amplitude>
                    | <state> ' # ' <state> // tensor product

  <amplitude>       : {int} ',' {int} ',' {int} ',' {int} ',' {int} // concrete amplitude
                    | {str} ',' {str} ',' {str} ',' {str} ',' {str} // symbolic amplitude
  
  <newline>         : '\n' // or another character acting as a newline character
```

The only thing needing to be explained is something like `|i|=3 i:1,0,0,0,0 *:0,0,0,0,0`. This statement contains each state of the format `i:1,0,0,0,0 *:0,0,0,0,0` where `i` can be `000`, `001`, `010`, ..., `111`. Since the program does not confuse this bounded variable `i` with other free variables `i` appearing in the 5-tuple, one can write something like `|i|=3 i:i,j,i,0,0 *:i,j,i,0,0`.

During program execution, the user inputs multiple lines of data and then presses `ENTER` and `CTRL+D` to notify the program to print the automaton. Please also notice that some strings generated by the above grammar may be semantically incorrect. In this case, the string cannot validly represent a set of states, so the output automaton cannot be used.

Here we give some examples. The first example contains all computational basis states in a 2-qubit quantum system.
```
$ build/cli/caut_from_states 
0:1,0,0,0,0 *:0,0,0,0,0 # 0:1,0,0,0,0 *:0,0,0,0,0
0:1,0,0,0,0 *:0,0,0,0,0 # 1:1,0,0,0,0 *:0,0,0,0,0
1:1,0,0,0,0 *:0,0,0,0,0 # 0:1,0,0,0,0 *:0,0,0,0,0
1:1,0,0,0,0 *:0,0,0,0,0 # 1:1,0,0,0,0 *:0,0,0,0,0

Ops [1]:2 [2]:2 [0,0,0,0,0]:0 [1,0,0,0,0]:0 
Automaton Union
States 0 1 2 3 4 
Final States 0 
Transitions
[1](1, 2) -> 0
[1](2, 1) -> 0
[2](3, 3) -> 2
[2](3, 4) -> 1
[2](4, 3) -> 1
[0,0,0,0,0] -> 3
[1,0,0,0,0] -> 4
```

The second example contains the set of states:<br>
<img width="315" alt="image" src="https://user-images.githubusercontent.com/10044077/217997027-4dec8f23-811d-4747-86b3-e95d37b9ec69.png">
```
$ build/cli/saut_from_states 
|i|=3 i:1,0,0,0,0 *:0,0,0,0,0 # i:vH,0,0,0,0 *:vL,0,0,0,0 # 000:1,0,0,0,0 *:0,0,0,0,0

Ops [1]:2 [2]:2 [3]:2 [4]:2 [5]:2 [6]:2 [7]:2 [8]:2 [9]:2 [0,0,0,0,0]:0 [vH,0,0,0,0]:0 [vL,0,0,0,0]:0 
Automaton Union
States 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 
Final States 0 
Transitions
[1](1, 2) -> 0
[1](1, 3) -> 0
[1](1, 4) -> 0
[1](1, 5) -> 0
[1](6, 1) -> 0
[1](7, 1) -> 0
[1](8, 1) -> 0
[1](9, 1) -> 0
[2](10, 10) -> 1
[2](10, 11) -> 2
[2](10, 12) -> 3
[2](10, 13) -> 6
[2](10, 14) -> 7
[2](15, 10) -> 4
[2](16, 10) -> 5
[2](17, 10) -> 8
[2](18, 10) -> 9
[3](19, 19) -> 10
[3](19, 20) -> 11
[3](19, 21) -> 15
[3](19, 22) -> 13
[3](19, 23) -> 17
[3](24, 19) -> 12
[3](25, 19) -> 16
[3](26, 19) -> 14
[3](27, 19) -> 18
[4](28, 28) -> 19
[4](29, 30) -> 20
[4](29, 31) -> 24
[4](29, 32) -> 21
[4](29, 33) -> 25
[4](30, 29) -> 22
[4](31, 29) -> 26
[4](32, 29) -> 23
[4](33, 29) -> 27
[5](34, 34) -> 28
[5](35, 35) -> 29
[5](35, 36) -> 30
[5](35, 37) -> 31
[5](36, 35) -> 32
[5](37, 35) -> 33
[6](38, 38) -> 34
[6](39, 39) -> 35
[6](39, 40) -> 36
[6](40, 39) -> 37
[7](41, 41) -> 38
[7](42, 41) -> 40
[7](43, 41) -> 39
[8](44, 44) -> 41
[8](45, 44) -> 42
[8](46, 44) -> 43
[9](47, 47) -> 44
[9](48, 47) -> 45
[9](49, 47) -> 46
[0,0,0,0,0] -> 47
[vH,0,0,0,0] -> 48
[vL,0,0,0,0] -> 49
```
