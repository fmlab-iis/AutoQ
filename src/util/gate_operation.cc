#include <vata/util/aut_description.hh>

void VATA::Util::TreeAutomata::X(int t) {
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    TreeAutomata aut2 = *this;
    aut1.value_restriction(t, false);
    aut1.branch_restriction(t, true);
    aut2.value_restriction(t, true);
    aut2.branch_restriction(t, false);
    *this = aut1 + aut2;
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::Y(int t) {
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    TreeAutomata aut2 = *this;
    aut1.value_restriction(t, false);
    aut1.branch_restriction(t, true);
    aut2.value_restriction(t, true);
    aut2.branch_restriction(t, false);
    *this = aut1 - aut2;
    omega_multiplication();
    omega_multiplication();
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::Z(int t) {
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    TreeAutomata aut2 = *this;
    aut1.branch_restriction(t, false);
    aut2.branch_restriction(t, true);
    *this = aut1 - aut2;
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::H(int t) {
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    aut1.value_restriction(t, false);
    TreeAutomata aut2 = *this;
    aut2.value_restriction(t, true);
    TreeAutomata aut3 = aut2;
    aut2.branch_restriction(t, false);
    aut3.branch_restriction(t, true);
    *this = aut1 + aut2 - aut3;
    divide_by_the_square_root_of_two();
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::S(int t) {
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    TreeAutomata aut2 = *this;
    aut1.branch_restriction(t, false);
    aut2.branch_restriction(t, true);
    aut2.omega_multiplication();
    aut2.omega_multiplication();
    *this = aut1 + aut2;
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::T(int t) {
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    TreeAutomata aut2 = *this;
    aut1.branch_restriction(t, false);
    aut2.branch_restriction(t, true);
    aut2.omega_multiplication();
    *this = aut1 + aut2;
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::Rx(int t) {
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    TreeAutomata aut2 = *this;
    aut2.value_restriction(t, false);
    aut2.branch_restriction(t, true);
    TreeAutomata aut3 = *this;
    aut3.value_restriction(t, true);
    aut3.branch_restriction(t, false);
    aut2 = aut2 + aut3;
    aut2.omega_multiplication();
    aut2.omega_multiplication();
    *this = aut1 - aut2;
    divide_by_the_square_root_of_two();
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::Ry(int t) {
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    aut1.value_restriction(t, false);
    TreeAutomata aut2 = *this;
    aut2.value_restriction(t, true);
    TreeAutomata aut3 = aut2;
    aut2.branch_restriction(t, true);
    aut3.branch_restriction(t, false);
    *this = aut1 + aut2 - aut3;
    divide_by_the_square_root_of_two();
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::CNOT(int c, int t) {
    assert(c != t);
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    aut1.branch_restriction(c, false);
    TreeAutomata aut2 = *this;
    aut2.value_restriction(c, true);
    TreeAutomata aut3 = aut2;
    aut2.value_restriction(t, false);
    aut2.branch_restriction(t, true);
    aut2.branch_restriction(c, true);
    aut3.value_restriction(t, true);
    aut3.branch_restriction(t, false);
    aut3.branch_restriction(c, true);
    *this = aut1 + aut2 + aut3;
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::CZ(int c, int t) {
    assert(c != t);
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    aut1.branch_restriction(c, false);
    TreeAutomata aut2 = *this;
    aut2.branch_restriction(t, false);
    TreeAutomata aut3 = aut2;
    aut3.branch_restriction(c, false);
    TreeAutomata aut4 = *this;
    aut4.branch_restriction(t, true);
    aut4.branch_restriction(c, true);
    *this = aut1 + aut2 - aut3 - aut4;
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::Toffoli(int c, int c2, int t) {
    assert(c != c2 && c2 != t && t != c);
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    aut1.branch_restriction(c, false);
    TreeAutomata aut2 = *this;
    aut2.branch_restriction(c2, false);
    TreeAutomata aut3 = aut2;
    aut3.branch_restriction(c, false);
    TreeAutomata aut4 = *this;
    aut4.value_restriction(c, true);
    aut4.value_restriction(c2, true);
    TreeAutomata aut5 = aut4;
    aut4.value_restriction(t, false);
    aut4.branch_restriction(t, true);
    aut4.branch_restriction(c2, true);
    aut4.branch_restriction(c, true);
    aut5.value_restriction(t, true);
    aut5.branch_restriction(t, false);
    aut5.branch_restriction(c2, true);
    aut5.branch_restriction(c, true);
    *this = aut1 + aut2 - aut3 + aut4 + aut5;
    this->semi_undeterminize();
}

void VATA::Util::TreeAutomata::Fredkin(int c, int t, int t2) {
    assert(c != t && t != t2 && t2 != c);
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    aut1.branch_restriction(c, false);
    TreeAutomata aut2 = *this;
    aut2.branch_restriction(c, true);
    TreeAutomata aut3 = aut2;
    aut2.branch_restriction(t, true);
    aut2.branch_restriction(t2, true);
    aut3.branch_restriction(t, false);
    aut3.branch_restriction(t2, false);
    TreeAutomata aut4 = *this;
    aut4.value_restriction(c, true);
    TreeAutomata aut5 = aut4;
    aut4.value_restriction(t, false);
    aut4.value_restriction(t2, true);
    aut4.branch_restriction(t2, false);
    aut4.branch_restriction(t, true);
    aut4.branch_restriction(c, true);
    aut5.value_restriction(t, true);
    aut5.value_restriction(t2, false);
    aut5.branch_restriction(t2, true);
    aut5.branch_restriction(t, false);
    aut5.branch_restriction(c, true);
    *this = aut1 + aut2 - aut3 + aut4 + aut5;
    this->semi_undeterminize();
}