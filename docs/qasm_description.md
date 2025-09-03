## How to write a quantum program? `*.qasm`

Our OpenQASM parser is implemented in the `execute` function of [src/execute.cc](../src/execute.cc). It is very minimal which supports only:
* a single set of quantum bits (and hence the variable name is irrelevant),
* any number of sets of classical bits (but usable only immediately before control flow constructs),
* the following gate set: {$X$, $Y$, $Z$, $H$, $T$, $T^\dagger$, $S$, $S^\dagger$, $R_x(\pi/2)$, $R_y(\pi/2)$, $CX$, $CZ$, $CCX$, $SWAP$},
* and the control flow constructs: `if-else` and `while`.

Both version 2.0 and 3.0 should work.

---

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

---

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

---

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
