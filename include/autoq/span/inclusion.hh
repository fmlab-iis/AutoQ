#ifndef AUTOQ_SPAN_INCLUSION_HH
#define AUTOQ_SPAN_INCLUSION_HH

#include <algorithm>
#include <cstddef>
#include <functional>
#include <limits>
#include <map>
#include <optional>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>
#include "autoq/aut_description.hh"

namespace AUTOQ::Span {
using Aut = AUTOQ::ConcreteAutomata;
using State = Aut::State;
using Scalar = AUTOQ::Complex::Complex;

enum class Outcome { Included, NotIncluded, ResourceLimit, UnsupportedInput };
struct Limits {
    std::size_t runs = 0;
    std::size_t basis = 0;
    std::size_t tuples = 0;
    std::size_t equations = 0;
    std::size_t search_steps = 1000000;
    std::size_t depth = 512;
};
struct Options { int qubits = -1; Limits limits{}; };
struct Stats {
    std::size_t a_runs = 0, b_runs = 0, basis = 0;
    std::size_t tuples = 0, equations = 0, search_steps = 0;
};
struct Transition {
    Aut::SymbolTag label;
    Aut::StateVector children;
};
struct CompressedRun {
    std::vector<std::map<State, Transition>> gamma;
    State root() const {
        if (gamma.empty() || gamma.front().size() != 1)
            throw std::invalid_argument("Invalid compressed root layer");
        return gamma.front().begin()->first;
    }
};
struct Result {
    Outcome outcome = Outcome::UnsupportedInput;
    Stats stats{};
    std::optional<CompressedRun> witness{};
    std::string message{};
};
inline const char* to_string(Outcome o) {
    switch (o) {
        case Outcome::Included: return "Included";
        case Outcome::NotIncluded: return "NotIncluded";
        case Outcome::ResourceLimit: return "ResourceLimit";
        case Outcome::UnsupportedInput: return "UnsupportedInput";
    }
    return "UnsupportedInput";
}
namespace detail {
struct BudgetExceeded {};
inline void tick(std::size_t& count, std::size_t limit) {
    if (count == std::numeric_limits<std::size_t>::max() ||
        (limit != 0 && count >= limit)) throw BudgetExceeded{};
    ++count;
}
inline bool exact_backend() {
#if defined(COMPLEX_nTuple)
    return AUTOQ::Complex::nTuple::N == 4;
#elif defined(COMPLEX_FiveTuple)
    return true;
#else
    return false;
#endif
}

// Over a faithfully represented subring of C, nonzero multiplication is
// invertible over C. No coefficient division or floating-point test is used.
template<class C> class LinearSystem {
    std::size_t variables_;
    std::map<std::size_t, std::vector<C>> pivots_{};
    bool consistent_ = true;
public:
    explicit LinearSystem(std::size_t variables) : variables_(variables) {}
    bool add(std::vector<C> row) {
        if (row.size() != variables_ + 1)
            throw std::invalid_argument("Wrong augmented row width");
        if (!consistent_) return false;
        for (const auto& [column, pivot] : pivots_) {
            const C factor = row[column];
            if (factor.isZero()) continue;
            const C scale = pivot[column];
            for (std::size_t j = 0; j <= variables_; ++j) {
                C value = scale * row[j] - factor * pivot[j];
                value.fraction_simplification();
                row[j] = std::move(value);
            }
        }
        for (std::size_t j = 0; j < variables_; ++j) {
            if (!row[j].isZero()) {
                pivots_.emplace(j, std::move(row));
                return true;
            }
        }
        consistent_ = row.back().isZero();
        return consistent_;
    }
};
using Index = std::map<State, std::vector<Transition>>;
inline Index index_automaton(const Aut& aut) {
    Index index;
    std::map<State, Aut::Tag> used;
    for (const auto& [label, parents] : aut.transitions) {
        for (const auto& [parent, alternatives] : parents) {
            for (const auto& children : alternatives) {
                if (children.size() != (label.is_internal() ? 2U : 0U))
                    throw std::invalid_argument("Invalid transition arity");
                if (!label.tag()) continue;
                if ((used[parent] & label.tag()) != 0)
                    throw std::invalid_argument("Overlapping choices for one top state");
                used[parent] |= label.tag();
                if (label.is_internal() && label.symbol().qubit() <= 0)
                    throw std::invalid_argument("Explicit positive qubit labels required");
                index[parent].push_back({label, children});
            }
        }
    }
    return index;
}

// Enumerates the ordered perfect depth-n slice. Transitions ending at other
// depths or carrying a different qubit index cannot generate this slice.
template<class Visitor> void enumerate(
    const Aut& aut, const Index& index, int n, const Limits& limits,
    Stats& stats, std::size_t& run_count, Visitor&& visitor) {
    CompressedRun run;
    run.gamma.resize(static_cast<std::size_t>(n) + 1);
    bool stopped = false;
    std::function<void(int, const std::set<State>&)> layer;
    layer = [&](int d, const std::set<State>& states) {
        if (stopped) return;
        tick(stats.search_steps, limits.search_steps);
        std::vector<State> ordered(states.begin(), states.end());
        std::vector<std::vector<const Transition*>> choices;
        for (State q : ordered) {
            std::vector<const Transition*> candidates;
            auto found = index.find(q);
            if (found != index.end()) {
                for (const auto& t : found->second) {
                    if ((d == n && t.label.is_leaf()) ||
                        (d < n && t.label.is_internal() &&
                         t.label.symbol().qubit() == d + 1))
                        candidates.push_back(&t);
                }
            }
            if (candidates.empty()) return;
            choices.push_back(std::move(candidates));
        }
        std::map<State, Transition> selected;
        std::function<void(std::size_t, Aut::Tag)> pick;
        pick = [&](std::size_t i, Aut::Tag common) {
            if (stopped) return;
            tick(stats.search_steps, limits.search_steps);
            if (i == ordered.size()) {
                run.gamma[static_cast<std::size_t>(d)] = selected;
                if (d == n) {
                    tick(run_count, limits.runs);
                    stopped = !visitor(run);
                } else {
                    std::set<State> next;
                    for (const auto& [q, t] : selected) {
                        (void)q;
                        next.insert(t.children.begin(), t.children.end());
                    }
                    layer(d + 1, next);
                }
                return;
            }
            for (const Transition* t : choices[i]) {
                const auto mask = common & t->label.tag();
                if (!mask) continue;
                selected.insert_or_assign(ordered[i], *t);
                pick(i + 1, mask);
                if (stopped) return;
            }
            selected.erase(ordered[i]);
        };
        pick(0, std::numeric_limits<Aut::Tag>::max());
    };
    for (State root : aut.finalStates) {
        layer(0, {root});
        if (stopped) break;
    }
}

inline bool member(const CompressedRun& target,
                   const std::vector<CompressedRun>& basis,
                   const Limits& limits, Stats& stats) {
    const auto layers = target.gamma.size();
    if (!layers) throw std::invalid_argument("Empty compressed run");
    std::vector<const CompressedRun*> runs{&target};
    for (const auto& b : basis) {
        if (b.gamma.size() != layers)
            throw std::invalid_argument("Mismatched compressed depths");
        runs.push_back(&b);
    }
    using Tuple = std::vector<State>;
    Tuple roots;
    for (const auto* r : runs) roots.push_back(r->root());
    std::set<Tuple> frontier{roots};
    LinearSystem<Scalar> solver(basis.size());
    for (std::size_t d = 0; d < layers; ++d) {
        std::set<Tuple> next;
        for (const auto& tuple : frontier) {
            tick(stats.tuples, limits.tuples);
            if (d + 1 == layers) {
                std::vector<Scalar> equation;
                for (std::size_t j = 1; j < runs.size(); ++j) {
                    const auto& t = runs[j]->gamma[d].at(tuple[j]);
                    if (!t.label.is_leaf() || !t.children.empty())
                        throw std::invalid_argument("Invalid compressed leaf");
                    equation.push_back(t.label.symbol().complex);
                }
                const auto& t = target.gamma[d].at(tuple[0]);
                if (!t.label.is_leaf() || !t.children.empty())
                    throw std::invalid_argument("Invalid compressed target leaf");
                equation.push_back(t.label.symbol().complex);
                tick(stats.equations, limits.equations);
                if (!solver.add(std::move(equation))) return false;
            } else {
                for (std::size_t side = 0; side < 2; ++side) {
                    Tuple child;
                    for (std::size_t j = 0; j < runs.size(); ++j) {
                        const auto& t = runs[j]->gamma[d].at(tuple[j]);
                        if (!t.label.is_internal() || t.children.size() != 2)
                            throw std::invalid_argument("Invalid compressed internal node");
                        child.push_back(t.children[side]);
                    }
                    // Limit frontier memory before allocating additional tuples.
                    if (!next.count(child) && limits.tuples && next.size() >= limits.tuples)
                        throw BudgetExceeded{};
                    next.insert(std::move(child));
                }
            }
        }
        frontier = std::move(next);
    }
    return true;
}
} // namespace detail

inline Result check_inclusion(const Aut& a, const Aut& b, Options options) {
    Result result;
    if (!detail::exact_backend()) {
        result.message = "Requires FiveTuple or nTuple with N=4";
        return result;
    }
    if (options.qubits < 0) {
        result.message = "Negative qubit depth";
        return result;
    }
    if (options.limits.depth &&
        static_cast<std::size_t>(options.qubits) > options.limits.depth) {
        result.outcome = Outcome::ResourceLimit;
        result.message = "Depth limit exceeded";
        return result;
    }
    try {
        const auto ai = detail::index_automaton(a);
        const auto bi = detail::index_automaton(b);
        std::vector<CompressedRun> basis;
        result.outcome = Outcome::Included;
        detail::enumerate(b, bi, options.qubits, options.limits, result.stats,
            result.stats.b_runs, [&](const CompressedRun& run) {
                if (!detail::member(run, basis, options.limits, result.stats)) {
                    if (options.limits.basis && basis.size() >= options.limits.basis)
                        throw detail::BudgetExceeded{};
                    basis.push_back(run);
                    result.stats.basis = basis.size();
                }
                return true;
            });
        detail::enumerate(a, ai, options.qubits, options.limits, result.stats,
            result.stats.a_runs, [&](const CompressedRun& run) {
                if (detail::member(run, basis, options.limits, result.stats)) return true;
                result.witness = run;
                result.outcome = Outcome::NotIncluded;
                return false;
            });
    } catch (const detail::BudgetExceeded&) {
        result.outcome = Outcome::ResourceLimit;
        result.witness.reset();
        result.message = "Search resource limit exceeded; no inclusion conclusion";
    } catch (const std::invalid_argument& e) {
        result.outcome = Outcome::UnsupportedInput;
        result.witness.reset();
        result.message = e.what();
    }
    return result;
}
} // namespace AUTOQ::Span
#endif
