## Internal Structures

The following figure demonstrates how we use a tree to represent a $3$-qubit quantum state so that an NFTA can encode a set of quantum states. The symbol $000$ stores the amplitude of the computational basis state $|000\rangle$, $001$ stores the amplitude of the computational basis state $|001\rangle$, etc.

<img width="350" alt="image" src="https://user-images.githubusercontent.com/10044077/214999182-7e3882d2-47cf-49cb-aa3e-45295072b3f8.png">

Please refer to [Example 1.1.3](https://inria.hal.science/hal-03367725v1/document#page=23) for a better understanding of NFTA. In short, the only difference between NFTA and NFA is that NFAs must have a starting state, but NFTAs do not. The tree language recognition procedure checks if an NFTA $\mathcal A$ accepts a tree $T$ (not necessarily binary) by iteratively reducing each component in a tree

<img width="350" alt="image" src="https://github.com/alan23273850/AutoQ/assets/10044077/db966d58-37ad-4b0d-be40-f57febf82634">

to a (unary) state $q$ provided that the transition (rule) $f(q_1, q_2, ..., q_n) \to q$ is present in $\mathcal A$ until no further reductions can be performed. There are many ways to reduce a tree, so we say $\mathcal A$ accepts $T$ if there exists a sequence of reductions such that the eventual resulting (unary) state is an $\mathcal A$'s final state (called ***root state*** in AutoQ). Leaf symbols (amplitudes) have no children, so they can only be reduced with $0$-arity transitions.