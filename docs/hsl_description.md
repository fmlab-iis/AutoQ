## How to describe a set of quantum states? `*.hsl`

This file may contain multiple lines. Each line represents a quantum state. A quantum state is naturally described by a linear combination of computational basis states with complex coefficients. Coefficients here can be expressed in [addition `+`], [subtraction `-`], [multiplication `*`] operations on [rationals], $[e^{i2\pi(r)}\ |\ r=k/8,\ k\in\mathbb Z]$ and the [exponentiation `^`] operation with "nonnegative" exponents. Operator precedence follows the standard convention. You can also do $/\sqrt2 ^ k$ by writing `/ sqrt2 ^ k` after the above operations are already done if you wish. Nevertheless, due to the automatic scaling in the verification process, users do not need $/\sqrt2 ^ k$.

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

The *Constraints* section may contain multiple lines. Each line consists of a boolean formula that will be automatically conjoined (with the *and* operator) eventually. Each formula is expressed in logical operations [not `!`], [and `&`], [or `|`] on boolean subformulae. These subformulae are expressed in comparison operations [greater than `>`], [less than `<`] on real numbers and the [equal `=`] operation on complex numbers. Operator precedence follows the standard convention. AutoQ also supports two functions `real(.)` and `imag(.)` to extract the real part and the imaginary part of a complex number.

One may want to take the absolute value of a ***real*** number in some applications. Due to the branching nature of this operation, the SMT solver may not be able to solve constraints involving this operation. Please use `(.) ^ 2` as an alternative instead.

We say a description file contains a quantum state $|s\rangle$ only if $|s\rangle$ satisfies all the boolean formulae in the *Constraints* section.

### # Tensor Products and Existentially Quantified Variables
For convenience, AutoQ also supports the ***tensor product operator*** `#`. The usage is very easy: just put `#` between two quantum states $|x\rangle$ and $|y\rangle$ in a line to denote the quantum state $|x\rangle \otimes |y\rangle$. AutoQ also supports the ***existentially quantified variable*** `\/ |i|=n :` over all $n$-bit binary strings. This variable is used to constrain all basis states $|i\rangle$ appearing after this notation in a line. If there is some quantum state $|s\rangle$ satisfying this line for some $i$, then we say $|s\rangle$ is described in this line.

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
