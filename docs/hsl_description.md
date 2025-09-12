## How to describe a set of quantum states? `*.hsl`

This file is divided into three sections: `Constants`, `Extended Dirac`, and `Constraints`.

* The `Constants` section allows users to predefine complex constants for convenience.
* The `Extended Dirac` section specifies the set of quantum states.
* The `Constraints` section defines conditions on variable coefficients, if such coefficients are used in the `Extended Dirac` section.

Among these, only the `Extended Dirac` section is mandatory, while the `Constants` and `Constraints` sections are optional. All three sections, if present, must be defined in the above order.

---

### # Constants
This section is intended to let users predefine complex constants for convenience. Each line must follow the format `[var] := [constant]`.
* `[var]` must be a nonempty string consisting of English letters and digits.
* `[constant]` must be constructed according to the following grammar. The `func` nonterminal supports four functions:
    - `real(c)` returns the real part of the complex number $c$,
    - `imag(c)` returns the imaginary part of the complex number $c$,
    - `eipi(r)` returns the complex number $e^{i\pi r}$,
    - `ei2pi(r)` returns the complex number $e^{i2\pi r}$.
  
  In the `eipi` function, `r` can be in any form, but it must equal a rational number with a denominator of 4. Likewise, in the `ei2pi` function, `r` can be in any form, but it must equal a rational number with a denominator of 8.
```
constant: constant "^" n=[0-9]+      // power
    | "-" constant                   // negation
    | constant ("*"|"/") constant    // multiplication or division
    | constant ("+"|"-") constant    // addition or subtraction
    | "(" constant ")"
    | func=("real"|"imag"|"eipi"|"ei2pi") "(" constant ")"
    | "sqrt2"                        // the positive square root of 2
    | n=[0-9]+                       // nonnegative integers
    ;
```
In the grammar above, the precedence of the first four operators, from top to bottom, is from highest to lowest. Defining multiple constants with the same name leads to undefined behavior. If you want to see how this is handled programmatically, check [src/ExtendedDirac/ExtendedDiracParser.g4#L74-L84](../src/ExtendedDirac/ExtendedDiracParser.g4#L74-L84). It might look a bit different from the grammar shown above, but the two are equivalent.

---

### # Extended Dirac
This section is intended to let users specify the set of quantum states. In this part, *newline characters are automatically ignored*, but the specification must still conform to the following grammar.
```
expr: tset;

tset: set
    | set "^" n=[1-9]*[1-9]+[1-9]* // apply ⊗ (n-1) times to itself
    | tset "⊗" tset
    ;

set: set "∪" set
    | "{" diracs "}"
    | "{" diracs ":" varcons "}"
    ;

diracs: dirac
    | diracs "," dirac
    ;

dirac: term
    | dirac ("+"|"-") term
    ;

term: complex? "|" VStr=([0-9a-zA-Z]|[a-z]')+ "⟩"
    | complex? "∑" varcons "|" VStr=([0-9a-zA-Z]|[a-z]')+ "⟩"
    | "-" "|" VStr=([0-9a-zA-Z]|[a-z]')+ "⟩"
    | "-" "∑" varcons "|" VStr=([0-9a-zA-Z]|[a-z]')+ "⟩"
    ;

complex: complex "^" n=[0-9]+      // power
    | "-" complex                  // negation
    | complex ("*"|"/") complex    // multiplication or division
    | complex ("+"|"-") complex    // addition or subtraction
    | "(" complex ")"
    | func=("real"|"imag"|"eipi"|"ei2pi") "(" complex ")"
    | "sqrt2"                      // the positive square root of 2
    | n=[0-9]+                     // nonnegative integers
    ;

varcons: varcon
    | varcons "," varcon
    ;

varcon: "|" V=[a-z] "|" "=" n=[1-9]*[1-9]+[1-9]* // denote the length n of the binary string variable V
    | L=[a-z] "≠" R=([a-z]|[01]+) // the variable L is not equal to another variable or binary string constant R
    ;
```
The grammar is designed to closely resemble the usual mathematical representation of sets of quantum states in Dirac notation, with a generalization of the tensor product between sets: $S_1\otimes S_2 = \\{\ket{x} \otimes \ket{y}\ |\ \ket{x}\in S_1,\ \ket{y}\in S_2\\}$. Each ket string $s$ in $\ket{s}$ may consist of not only the digits 0 and 1 but also binary string variables (each denoted by a lowercase English letter). A variable may be followed by the prime symbol `'` to indicate its bit complement. We can also insert a summation symbol `∑` followed by a summation constraint between a complex amplitude and a ket. A constraint is a sequence of variable-length indicators and inequalities, separated by commas that represent logical conjunction. Such constraints may also appear after a colon in a set representation to control global variables. Notice that you can also use `*` instead of `⊗` for the tensor product symbol, use `Σ` instead of `∑` for the summation symbol, use `>` instead of `⟩` for the right angle bracket, and use `!=` instead of `≠` for the disequal symbol.

---

### # Variables and Constraints
Nonconstant tokens appearing in amplitudes but not defined in the `Constants` section are automatically treated as *free symbolic variables*. The target set may require some constraints on these variables, so users can specify them in this section. Similarly, the constraints must adhere to the following grammar, but notice that *newline characters are not ignored* here. Each boolean formula is processed line by line and they will eventually be combined into a larger formula through conjunction.
```
predicate: complex "=" complex
    | complex "≠" complex
    | complex "<" complex
    | complex "≤" complex
    | complex ">" complex
    | complex "≥" complex
    | "¬" predicate
    | predicate "∧" predicate
    | predicate "∨" predicate
    | "(" predicate ")";
```
Note that you can also substitute symbols as follows: `!=` for `≠`, `<=` or `≦` for `≤`, `>=` or `≧` for `≥`, `!` for `¬`, `&&` for `∧`, and `||` for `∨`.

---

### # Example
The following `*.hsl` file is adapted from [benchmarks/all/GroverSym/04/post.hsl](../benchmarks/all/GroverSym/04/post.hsl). It specifies the postcondition of Grover's algorithm where the expected hidden string can be arbitrary. The specified set is<br>

$$
\begin{aligned}
\displaystyle & \\Bigg\\{a_H \ket{0101} + a_L \sum_{\substack{i\in\\{0,1\\}^4\setminus\newline\\{0101\\}}}\ket{i} \otimes \ket{001}\\Bigg\\}\ \bigcup\ \\Bigg\\{a_H \ket{s} + a_L \sum_{\substack{i\in\\{0,1\\}^4\setminus\newline\\{s\\}}}\ket{i} \otimes \ket{001}\ :\ s\in\\{0,1\\}^4\setminus\\{0101\\}\\Bigg\\} \\\\ = &\\Bigg\\{a_H \ket{s} + a_L \sum_{\substack{i\in\\{0,1\\}^4\setminus\newline\\{s\\}}}\ket{i} \otimes \ket{001}\ :\ s\in\\{0,1\\}^4\\Bigg\\}
\end{aligned}
$$

with the amplitude constraints: $\text{real}^2(a_L) < \text{1/8} \land \text{imag}(a_L) = 0 \land \text{real}^2(a_H) > \text{7/8} \land \text{imag}(a_H) = 0$.

```
Constants
c1 := 1
Extended Dirac
{aH |0101> + aL ∑ |i|=4, i≠0101 |i>} ∪ {aH |s> + aL ∑ |i|=4, i≠s |i> : |s|=4, s≠0101} ⊗ {c1 |001>}
Constraints
real(aL) * real(aL) < 1/8
imag(aL) = 0
real(aH) * real(aH) > 7/8
imag(aH) = 0
```

If you try to remove the first part `{aH |0101> + aL ∑ |i|=4, i≠0101 |i>} ∪ `, you will get the following expected result.
```
The quantum program has [7] qubits and [100] gates. The verification process [failed] in [0.2s] with [86MB] memory usage.
```

---

### # Alignment

One important mechanism of AutoQ 2.0 is the reordering of qubits according to the given precondition, postcondition and loop invariants for reducing the sizes of the constructed automata, and hence there are some requirements on these `*.hsl` files.

1. If a tensor product symbol `⊗` appears between the $i$-th and $(i+1)$-th qubits in one `*.hsl` file, then all the other `*.hsl` files must also include a tensor product symbol `⊗` separating the $i$-th and $(i+1)$-th qubit.
2. If a variable `x` or its bit complement `x'` occurs in any ket `|...x(')...⟩` on qubits $i$ through $j$ in any *.hsl file, then in the same range of qubits ($i$ to $j$), every other ket string—whether in the same `*.hsl` file or in the other `*.hsl` files—must contain either only constants (`0` and `1`), or exactly one variable (or its complement).

Violating either of the two rules above triggers the error message `There are two *.hsl files not aligned!`, prompting users to revise their `*.hsl` files to ensure alignment.


