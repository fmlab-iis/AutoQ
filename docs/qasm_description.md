## How to write a quantum program? `*.qasm`

Our OpenQASM parser is implemented in the `execute` function of [src/execute.cc](../src/execute.cc). It is very minimal which supports only:
* a single set of quantum bits (and hence the variable name is irrelevant),
* any number of sets of classical bits (but usable only immediately before control flow constructs),
* the following gate set: $\\{X$, $Y$, $Z$, $H$, $T$, $T^\dagger$, $S$, $S^\dagger$, $R_x(\pi/2)$, $R_y(\pi/2)$, $CX$, $CZ$, $CCX$, $SWAP\\}$,
* and the control flow constructs: `if-else` and `while`.

Both versions 2.0 and 3.0 should work.

---

### # Measurement
The usage of a measurement operator should be `[a classical bit: c] = measure [a quantum bit: q];`, which is demonstrated below.
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
The transformation of the set of quantum states after the measurement operator is described as follows. Let $S$ be the set of quantum states right before the measurement operator. There are two possible outcomes `q=0` and `q=1` of this operator if it is applied to the qubit `q`, so after the measurement we define one set

$$\displaystyle S_0\ :=\ \\Bigg\\{\ \ket{s'} = \sum_{i\in\\{0,1\\}^n,\ i_q=0} a_i\ \ket{i}\ \ :\ \ \ket{s} \in S,\ \ket s = \sum_{i\in\\{0,1\\}^n} a_i\ \ket{i} \\Bigg\\}$$

and another set

$$\displaystyle S_1\ :=\ \\Bigg\\{\ \ket{s'} = \sum_{i\in\\{0,1\\}^n,\ i_q=1} a_i\ \ket{i}\ \ :\ \ \ket{s} \in S,\ \ket s = \sum_{i\in\\{0,1\\}^n} a_i\ \ket{i} \\Bigg\\}.$$

A careful reader may notice that AutoQ 2.0 does not normalize amplitudes after measurements. This is intentional, for reasons of computational simplicity, but remains valid after program execution because there is always a unique positive scaling factor that can normalize any non-normalized quantum state. In other words, each non-normalized state can still be restored to exactly one valid quantum state.

***This operator cannot be used standalone in AutoQ 2.0***. It can only be used with ***branching (if-else)*** and ***looping (while)***, which are introduced below. Please refer to them for more details.

---

### # Branching (if-else)
The usage of an if-else block in general should be
```
[a classical bit: c] = measure [a quantum bit: q];
// S: the set of quantum states reaching here so far
if (c) { // S_1, computed according to the measurement formula
    ... // P_1
} // S_1' := P_1(S_1), provided that P_1 is the program segment in the "if" block
else { // S_0, computed according to the measurement formula
    ... // P_0
} // S_0' := P_0(S_0), provided that P_0 is the program segment in the "else" block
// (S_0') ∪ (S_1'): the resulting set of quantum states after the if-else block
```
with `if (c)` possibly be replaced with `if (!c)` and `else {...}` possibly be omitted. The reason why we need a measurement operator at the beginning is to produce $S_0$ and $S_1$ according to the formulae introduced in the *Measurement* section before entering the `if-else` block.

AutoQ 2.0 executes the `if` block with $S_1$ as its initial set, producing the resulting set $S_1' := P_1(S_1)$, and the `else` block with $S_0$ as its initial set, producing $S_0' := P_0(S_0)$. Immediately after the `if-else` block, AutoQ 2.0 takes the union $(S_0') \cup (S_1')$, and the execution then continues with this set. If `if (c)` is replaced with `if (!c)`, the execution is equivalent to swapping `P_1` and `P_0` and restoring `if (!c)` to `if (c)`. If `else {...}` is omitted, AutoQ 2.0 simply treats the block as an identity gate.

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

One subtle point to note is that the statement `else {` must not appear on the same line as the closing bracket `}` of the preceding `if` block since AutoQ 2.0 needs to detect the termination of the previous `if` block. <!--Please refer to [this example](https://github.com/alan23273850/AutoQ/tree/CAV24/benchmarks/control_mini/if-else) for its usage.-->

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

Unlike the if-else block, the NFTA does not split into two after a while loop. Instead, AutoQ 2.0 first checks whether the set of quantum states $S$ prior to the measurement operator is included in the set of quantum states $I$ specified in the invariant file `invariant.{hsl|spec}` (i.e., $S \subseteq I$). If the answer is no, the verification of the whole quantum program fails. Otherwise, AutoQ 2.0 continues to check whether the set transformation after $\displaystyle\\Bigg\\{\ \sum_{i\in\\{0,1\\}^n,\ i_q=1} a_i\ |i\rangle\ \Bigg|\ |s\rangle \in I,\ |s\rangle = \sum_{i\in\\{0,1\\}^n} a_i\ |i\rangle \\Bigg\\}$ running through the loop body is still included in $I$. If the answer is still yes, then the verification of this loop passes and AutoQ 2.0 continues the remaining execution with $\displaystyle\\Bigg\\{\ \sum_{i\in\\{0,1\\}^n,\ i_q=0} a_i\ |i\rangle\ \Bigg|\ |s\rangle \in I,\ |s\rangle = \sum_{i\in\\{0,1\\}^n} a_i\ |i\rangle \\Bigg\\}$ after this while loop.

If `while (c)` is replaced with `while (!c)`, then $i_q=1$ and $i_q=0$ should be interchanged in the above description.

The file paths for specifying loop invariants are relative to the circuit file's location. Please refer to [this example](https://github.com/alan23273850/AutoQ/tree/CAV24/benchmarks/control_mini/while) for its usage.

