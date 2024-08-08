#include "autoq/aut_description.hh"
#include "autoq/complex/complex.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::uniform(int n) {
    TreeAutomata aut;
    aut.name = "Uniform";
    aut.qubitNum = n;
    for (int level=1; level<=n; level++) {
        aut.transitions[{level, 1}][level-1].insert({level, level});
    }
    aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::One().divide_by_the_square_root_of_two(n)), 1)][n].insert({{}});
    aut.finalStates.push_back(0);
    aut.stateNum = n+1;

    // aut.minimize();
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::basis(int n) {
    TreeAutomata aut;
    aut.name = "Classical";
    aut.qubitNum = n;

    for (int level=1; level<=n; level++) {
        if (level >= 2)
            aut.transitions[{level, 0b11}][2*level - 3].insert({2*level - 1, 2*level - 1});
        aut.transitions[{level, 0b01}][2*level - 2].insert({2*level - 1, 2*level});
        aut.transitions[{level, 0b10}][2*level - 2].insert({2*level, 2*level - 1});
    }
    aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::One()), 1)][2*n].insert({{}});
    aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::Zero()), 1)][2*n - 1].insert({{}});
    aut.finalStates.push_back(0);
    aut.stateNum = 2*n + 1;

    // aut.minimize();
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::prefix_basis(int n) {
    TreeAutomata aut;
    aut.name = "Prefix Basis";
    aut.qubitNum = n;

    aut.transitions[{1, 1}][0].insert({2, 3});
    aut.transitions[{1, 2}][0].insert({3, 1});
    for (int L=2; L<=n; L++) {
        aut.transitions[{L, 1}][3*L-3].insert({3*L-1, 3*L-0});
        aut.transitions[{L, 2}][3*L-3].insert({3*L-0, 3*L-2});
        aut.transitions[{L, 3}][3*L-5].insert({3*L-2, 3*L-2});
        aut.transitions[{L, 3}][3*L-4].insert({3*L-1, 3*L-1});
    }
    aut.transitions[{AUTOQ::Symbol::Concrete(Complex::Complex::One()), 1}][3*n-0].insert({{}});
    aut.transitions[{AUTOQ::Symbol::Concrete(Complex::Complex::One()), 1}][3*n-1].insert({{}});
    aut.transitions[{AUTOQ::Symbol::Concrete(Complex::Complex::Zero()), 1}][3*n-2].insert({{}});
    aut.finalStates.push_back(0);
    aut.stateNum = 3*n + 1;

    aut.reduce();
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::random(int n) {
    TreeAutomata aut;
    aut.name = "Random";
    aut.qubitNum = n;
    int pow_of_two = 1;
    State state_counter = 0;
    for (int level=1; level<=n; level++) {
        for (int i=0; i<pow_of_two; i++) {
            aut.transitions[{level, 1}][state_counter].insert({state_counter*2+1, state_counter*2+2});
            state_counter++;
        }
        pow_of_two *= 2;
    }
    for (State i=state_counter; i<=state_counter*2; i++) {
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::Rand()), 1)][i].insert({{}});
    }
    aut.finalStates.push_back(0);
    aut.stateNum = state_counter*2 + 1;

    // aut.minimize();
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::zero(int n) {
    /* Example of n = 6:
        Final States 0
        Transitions
        [1](2, 1) -> 0
        [2](3, 3) -> 1
        [2](4, 3) -> 2
        [3](5, 5) -> 3
        [3](6, 5) -> 4
        [4](7, 7) -> 5
        [4](8, 7) -> 6
        [5](9, 9) -> 7
        [5](10, 9) -> 8
        [6](11, 11) -> 9
        [6](12, 11) -> 10
        [0,0,0,0,0] -> 11
        [1,0,0,0,0] -> 12
    */
    TreeAutomata aut;
    aut.name = "Zero";
    aut.qubitNum = n;
    aut.finalStates.push_back(0);
    aut.transitions[{1,1}][0].insert({2,1});
    for (int level=2; level<=n; level++) {
        aut.transitions[{level,1}][level*2-3].insert({level*2-1, level*2-1});
        aut.transitions[{level,1}][level*2-2].insert({level*2, level*2-1});
    }
    aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::Zero()), 1)][n*2-1].insert({{}});
    aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::One()), 1)][n*2].insert({{}});
    aut.stateNum = n*2 + 1;

    // aut.minimize();
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::basis_zero_one_zero(int n) {
    TreeAutomata aut;
    assert(n >= 2);
    aut.name = "Classical_Zero_One_Zero";
    aut.qubitNum = n + (n+1) + (n>=3) * (n-1);

    for (int level=1; level<=n; level++) {
        if (level >= 2)
            aut.transitions[{level, 0b11}][2*level - 3].insert({2*level - 1, 2*level - 1});
        aut.transitions[{level, 0b01}][2*level - 2].insert({2*level - 1, 2*level});
        aut.transitions[{level, 0b10}][2*level - 2].insert({2*level, 2*level - 1});
    }
    for (int level=1; level<=n; level++) {
        aut.transitions[{n + level, 1}][2*n + 2*level-3].insert({2*n + 2*level-1, 2*n + 2*level-1});
        aut.transitions[{n + level, 1}][2*n + 2*level-2].insert({2*n + 2*level, 2*n + 2*level-1});
    }
    aut.transitions[{n + (n+1), 1}][2*n + 2*(n+1)-3].insert({2*n + 2*(n+1)-1, 2*n + 2*(n+1)-1});
    aut.transitions[{n + (n+1), 1}][2*n + 2*(n+1)-2].insert({2*n + 2*(n+1)-1, 2*n + 2*(n+1)});
    if (n >= 3) {
        for (int level=n+2; level<=2*n; level++) {
            aut.transitions[{n + level, 1}][2*n + 2*level-3].insert({2*n + 2*level-1, 2*n + 2*level-1});
            aut.transitions[{n + level, 1}][2*n + 2*level-2].insert({2*n + 2*level, 2*n + 2*level-1});
        }
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::One()), 1)][6*n].insert({{}});
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::Zero()), 1)][6*n - 1].insert({{}});
        aut.stateNum = 6*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::One()), 1)][4*n + 2].insert({{}});
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::Zero()), 1)][4*n + 1].insert({{}});
        aut.stateNum = 4*n + 3;
    }
	aut.finalStates.push_back(0);
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::zero_zero_one_zero(int n) {
    TreeAutomata aut;
    assert(n >= 2);
    aut.name = "Zero_Zero_One_Zero";
    aut.qubitNum = n + (n+1) + (n>=3) * (n-1);

    aut.transitions[{1, 1}][0].insert({2,1});
    for (int level=2; level<=n; level++) {
        aut.transitions[{level, 1}][level*2-3].insert({level*2-1, level*2-1});
        aut.transitions[{level, 1}][level*2-2].insert({level*2, level*2-1});
    }
    for (int level=1; level<=n; level++) {
        aut.transitions[{n + level, 1}][2*n + 2*level-3].insert({2*n + 2*level-1, 2*n + 2*level-1});
        aut.transitions[{n + level, 1}][2*n + 2*level-2].insert({2*n + 2*level, 2*n + 2*level-1});
    }
    aut.transitions[{n + (n+1), 1}][2*n + 2*(n+1)-3].insert({2*n + 2*(n+1)-1, 2*n + 2*(n+1)-1});
    aut.transitions[{n + (n+1), 1}][2*n + 2*(n+1)-2].insert({2*n + 2*(n+1)-1, 2*n + 2*(n+1)});
    if (n >= 3) {
        for (int level=n+2; level<=2*n; level++) {
            aut.transitions[{n + level, 1}][2*n + 2*level-3].insert({2*n + 2*level-1, 2*n + 2*level-1});
            aut.transitions[{n + level, 1}][2*n + 2*level-2].insert({2*n + 2*level, 2*n + 2*level-1});
        }
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::One()), 1)][6*n].insert({{}});
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::Zero()), 1)][6*n - 1].insert({{}});
        aut.stateNum = 6*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::One()), 1)][4*n + 2].insert({{}});
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::Zero()), 1)][4*n + 1].insert({{}});
        aut.stateNum = 4*n + 3;
    }
	aut.finalStates.push_back(0);
    // aut.isTopdownDeterministic = true;
    return aut;
}

template <>
AUTOQ::TreeAutomata AUTOQ::TreeAutomata::zero_one_zero(int n) {
    TreeAutomata aut;
    assert(n >= 2);
    aut.name = "Zero_One_Zero";
    aut.qubitNum = (n+1) + (n>=3) * (n-1);

    aut.transitions[{1, 1}][0].insert({2,1});
    for (int level=2; level<=n; level++) {
        aut.transitions[{level, 1}][level*2-3].insert({level*2-1, level*2-1});
        aut.transitions[{level, 1}][level*2-2].insert({level*2, level*2-1});
    }
    aut.transitions[{n+1, 1}][2*n-1].insert({2*(n+1)-1, 2*(n+1)-1});
    aut.transitions[{n+1, 1}][2*n].insert({2*(n+1)-1, 2*(n+1)});
    if (n >= 3) {
        for (int level=n+2; level<=2*n; level++) {
            aut.transitions[{level, 1}][2*(level-1)-1].insert({2*level-1, 2*level-1});
            aut.transitions[{level, 1}][2*(level-1)].insert({2*level, 2*level-1});
        }
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::One()), 1)][4*n].insert({{}});
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::Zero()), 1)][4*n - 1].insert({{}});
        aut.stateNum = 4*n + 1;
    } else {
        assert(n == 2);
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::One()), 1)][2*n + 2].insert({{}});
        aut.transitions[SymbolTag(AUTOQ::Symbol::Concrete(Complex::Complex::Zero()), 1)][2*n + 1].insert({{}});
        aut.stateNum = 2*n + 3;
    }
	aut.finalStates.push_back(0);
    // aut.isTopdownDeterministic = true;
    return aut;
}

template struct AUTOQ::Automata<AUTOQ::Symbol::Concrete>;
template struct AUTOQ::Automata<AUTOQ::Symbol::Symbolic>;