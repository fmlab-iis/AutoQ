#include <vata/util/aut_description.hh>

void VATA::Util::TreeAutomata::Z(int t) {
    this->semi_determinize();
    TreeAutomata aut1 = *this;
    TreeAutomata aut2 = *this;
    aut1.branch_restriction(t, false);
    aut2.branch_restriction(t, true);
    *this = aut1 - aut2;
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