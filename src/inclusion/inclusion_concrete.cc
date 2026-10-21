/**
 * Inclusion checking for Concrete (Tree) automata: operator<<=.
 */
#include "autoq/inclusion_common.hh"
#include "autoq/inclusion_build_trans.hh"
#include "autoq/inclusion_bfs.hh"
#include "autoq/util/util.hh"
#include "autoq/aut_description.hh"

namespace {

// Inclusion-search policy for concrete automata: in every combination of B's
// transitions, the amplitudes B assigns must be one common nonzero multiple of
// the amplitudes A assigns (zero exactly where A's is zero).
struct ConcreteLeafPolicy {
    void begin_vertex() {}
    bool leaf_pairs_consistent(const std::set<std::pair<AUTOQ::Symbol::Concrete, AUTOQ::Symbol::Concrete>>& leaf_pairs) const {
        bool startRatio = false;
        // We use a pair to represent the ratio in case it is not representable.
        std::pair<AUTOQ::Complex::Complex, AUTOQ::Complex::Complex> ratio;
        for (const auto &pair : leaf_pairs) {
            if (pair.first.complex.isZero() && pair.second.complex.isZero()) continue;
            if (!pair.first.complex.isZero() && !pair.second.complex.isZero()) {
                if (!startRatio) {
                    startRatio = true;
                    ratio = std::make_pair(pair.first.complex, pair.second.complex);
                } else if (!(ratio.first * pair.second.complex).valueEqual(ratio.second * pair.first.complex)) {
                    return false;
                }
            } else {
                return false;
            }
        }
        return true;
    }
    void record_feasible(const std::set<std::pair<AUTOQ::Symbol::Concrete, AUTOQ::Symbol::Concrete>>&) {}
    bool leaf_vertex_fails(const AUTOQ::ConcreteAutomata&, const AUTOQ::ConcreteAutomata&) const { return false; }
};

}  // namespace

template <>
bool AUTOQ::ConcreteAutomata::operator<<=(AUTOQ::ConcreteAutomata autB) const {
    const auto &autA = *this;
    autB = autB.operator||(AUTOQ::ConcreteAutomata::zero_amplitude(autB.qubitNum));
    auto start_include = std::chrono::steady_clock::now();

    std::vector<std::map<AUTOQ::ConcreteAutomata::SymbolTag, AUTOQ::ConcreteAutomata::StateVector>> transA;
    std::vector<std::map<AUTOQ::ConcreteAutomata::Symbol, std::map<AUTOQ::ConcreteAutomata::Tag, AUTOQ::ConcreteAutomata::StateVector>>> transB;
    AUTOQ::build_inclusion_trans(autA, autB, transA, transB);

    ConcreteLeafPolicy policy;
    bool holds = AUTOQ::inclusion_bfs_holds(autA, autB, transA, transB, policy);
    auto stop_include = std::chrono::steady_clock::now();
    this->stats_->include_status = AUTOQ::Util::Convert::ToString(stop_include - start_include) + (holds ? "" : " X");
    this->stats_->total_include_time += stop_include - start_include;
    return holds;
}
template <>
bool AUTOQ::ConcreteAutomata::operator_scaled_inclusion_with_renaming(AUTOQ::ConcreteAutomata autB) const {
    return operator<<=(autB);
}
