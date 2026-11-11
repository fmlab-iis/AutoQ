#ifndef AUTOQ_SPAN_INCLUSION_HH
#define AUTOQ_SPAN_INCLUSION_HH

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <limits>
#include <map>
#include <optional>
#include <set>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

#include "autoq/aut_description.hh"
#include "autoq/complex/complex.hh"

namespace AUTOQ::Span {

enum class Outcome {
    Included,
    NotIncluded,
    ResourceLimit,
    UnsupportedInput,
};

struct ResourceLimits {
    std::size_t max_basis_runs = 0;
    std::size_t max_b_runs = 0;
    std::size_t max_a_runs = 0;
    std::size_t max_tuple_states = 0;
    std::size_t max_equations = 0;
};

struct Options {
    int qubits = -1;
    ResourceLimits limits{};
};

struct Stats {
    std::size_t b_runs_enumerated = 0;
    std::size_t a_runs_enumerated = 0;
    std::size_t basis_runs_retained = 0;
    std::size_t tuple_states_visited = 0;
    std::size_t equations_added = 0;
};

struct TransitionSelection {
    AUTOQ::ConcreteAutomata::SymbolTag symbol_tag;
    std::set<AUTOQ::ConcreteAutomata::StateVector> targets;
};

struct CompressedRun {
    // gamma[d][state] = selected complete transition at layer d
    std::vector<std::map<AUTOQ::ConcreteAutomata::State, TransitionSelection>> gamma;

    AUTOQ::ConcreteAutomata::State root() const {
        return gamma.empty() || gamma.front().empty() ? -1 : gamma.front().begin()->first;
    }
};

struct Result {
    Outcome outcome = Outcome::UnsupportedInput;
    Stats stats{};
    std::optional<CompressedRun> witness;
    std::string message;
};

namespace detail {

using C = AUTOQ::Complex::Complex;

inline bool supported_exact_backend() {
    return std::is_same_v<C, AUTOQ::Complex::FiveTuple> || std::is_same_v<C, AUTOQ::Complex::nTuple>;
}

inline C zero_c() { return C(0); }

inline void simplify(C &v) {
    if constexpr (requires(C x) { x.fraction_simplification(); }) {
        v.fraction_simplification();
    }
}

inline bool value_equal(const C &a, const C &b) {
    if constexpr (requires(C x, C y) { x.valueEqual(y); }) {
        return a.valueEqual(b);
    }
    return a == b;
}

inline bool is_zero(const C &a) { return value_equal(a, zero_c()); }

struct IncrementalSolver {
    struct Row {
        std::vector<C> coeffs;
        C rhs = zero_c();
    };

    explicit IncrementalSolver(std::size_t vars) : vars_(vars) {}

    bool add_equation(std::vector<C> coeffs, C rhs) {
        Row row{std::move(coeffs), rhs};
        for (std::size_t p : pivot_order_) {
            const C coeff = row.coeffs[p];
            if (is_zero(coeff)) {
                continue;
            }
            const Row &pivot_row = pivots_.at(p);
            const C pivot_coeff = pivot_row.coeffs[p];
            for (std::size_t col = p; col < vars_; ++col) {
                C new_val = pivot_coeff * row.coeffs[col] - coeff * pivot_row.coeffs[col];
                simplify(new_val);
                row.coeffs[col] = std::move(new_val);
            }
            C new_rhs = pivot_coeff * row.rhs - coeff * pivot_row.rhs;
            simplify(new_rhs);
            row.rhs = std::move(new_rhs);
        }

        std::optional<std::size_t> first_nonzero;
        for (std::size_t i = 0; i < vars_; ++i) {
            if (!is_zero(row.coeffs[i])) {
                first_nonzero = i;
                break;
            }
        }

        if (!first_nonzero.has_value()) {
            return is_zero(row.rhs);
        }

        pivots_[*first_nonzero] = std::move(row);
        pivot_order_.push_back(*first_nonzero);
        return true;
    }

private:
    std::size_t vars_;
    std::map<std::size_t, Row> pivots_;
    std::vector<std::size_t> pivot_order_;
};

inline std::vector<TransitionSelection> collect_state_choices(
    const AUTOQ::ConcreteAutomata &aut,
    AUTOQ::ConcreteAutomata::State state,
    int depth,
    int qubits,
    bool &unsupported)
{
    std::vector<TransitionSelection> out;
    bool expect_leaf = (depth == qubits);

    for (const auto &tr : aut.transitions) {
        const auto &st = tr.first;
        auto it = tr.second.find(state);
        if (it == tr.second.end()) {
            continue;
        }

        const bool is_internal = st.symbol().is_internal();
        if (expect_leaf) {
            if (is_internal) {
                unsupported = true;
                return {};
            }
            for (const auto &vec : it->second) {
                if (!vec.empty()) {
                    unsupported = true;
                    return {};
                }
            }
            out.push_back({st, it->second});
            continue;
        }

        if (!is_internal) {
            unsupported = true;
            return {};
        }
        const auto q = static_cast<int>(st.symbol().qubit());
        if (q != depth + 1) {
            unsupported = true;
            return {};
        }
        for (const auto &vec : it->second) {
            if (vec.size() != 2) {
                unsupported = true;
                return {};
            }
        }
        out.push_back({st, it->second});
    }
    return out;
}

template <typename Callback>
Outcome enumerate_compressed_runs(
    const AUTOQ::ConcreteAutomata &aut,
    int qubits,
    std::size_t run_limit,
    std::size_t &run_counter,
    Callback &&on_run)
{
    if (qubits < 0) {
        return Outcome::UnsupportedInput;
    }

    CompressedRun run;
    run.gamma.resize(static_cast<std::size_t>(qubits) + 1);

    bool stop = false;
    bool unsupported = false;

    std::function<void(int, const std::set<AUTOQ::ConcreteAutomata::State> &)> dfs_layer;
    dfs_layer = [&](int depth, const std::set<AUTOQ::ConcreteAutomata::State> &reachable) {
        if (stop || unsupported) {
            return;
        }

        std::vector<AUTOQ::ConcreteAutomata::State> states(reachable.begin(), reachable.end());
        std::vector<std::vector<TransitionSelection>> choices(states.size());
        for (std::size_t i = 0; i < states.size(); ++i) {
            choices[i] = collect_state_choices(aut, states[i], depth, qubits, unsupported);
            if (unsupported || choices[i].empty()) {
                return;
            }
        }

        std::map<AUTOQ::ConcreteAutomata::State, TransitionSelection> layer_selection;

        std::function<void(std::size_t, AUTOQ::ConcreteAutomata::Tag)> pick;
        pick = [&](std::size_t idx, AUTOQ::ConcreteAutomata::Tag common_tags) {
            if (stop || unsupported) {
                return;
            }
            if (idx == states.size()) {
                run.gamma[static_cast<std::size_t>(depth)] = layer_selection;
                if (depth == qubits) {
                    ++run_counter;
                    if (run_limit != 0 && run_counter > run_limit) {
                        stop = true;
                        return;
                    }
                    if (!on_run(run)) {
                        stop = true;
                    }
                    return;
                }

                std::set<AUTOQ::ConcreteAutomata::State> next_reachable;
                for (const auto &kv : layer_selection) {
                    for (const auto &vec : kv.second.targets) {
                        next_reachable.insert(vec[0]);
                        next_reachable.insert(vec[1]);
                    }
                }
                if (next_reachable.empty()) {
                    return;
                }
                dfs_layer(depth + 1, next_reachable);
                return;
            }

            for (const auto &selection : choices[idx]) {
                const auto next_tags = static_cast<AUTOQ::ConcreteAutomata::Tag>(common_tags & selection.symbol_tag.tag());
                if (next_tags == 0) {
                    continue;
                }
                layer_selection[states[idx]] = selection;
                pick(idx + 1, next_tags);
                layer_selection.erase(states[idx]);
                if (stop || unsupported) {
                    return;
                }
            }
        };

        pick(0, std::numeric_limits<AUTOQ::ConcreteAutomata::Tag>::max());
    };

    for (auto root : aut.finalStates) {
        if (stop || unsupported) {
            break;
        }
        dfs_layer(0, {root});
    }

    if (unsupported) {
        return Outcome::UnsupportedInput;
    }
    if (stop && run_limit != 0 && run_counter > run_limit) {
        return Outcome::ResourceLimit;
    }
    return Outcome::Included;
}

inline std::vector<AUTOQ::ConcreteAutomata::State> side_states(const TransitionSelection &sel, std::size_t side) {
    std::set<AUTOQ::ConcreteAutomata::State> out;
    for (const auto &vec : sel.targets) {
        if (side < vec.size()) {
            out.insert(vec[side]);
        }
    }
    return {out.begin(), out.end()};
}

inline bool run_in_span(
    const CompressedRun &target,
    const std::vector<CompressedRun> &basis,
    int qubits,
    ResourceLimits limits,
    Stats &stats,
    Outcome &outcome)
{
    const std::size_t vars = basis.size();
    IncrementalSolver solver(vars);

    using Tuple = std::vector<AUTOQ::ConcreteAutomata::State>;
    std::set<Tuple> frontier;
    Tuple root_tuple;
    root_tuple.push_back(target.root());
    for (const auto &b : basis) {
        root_tuple.push_back(b.root());
    }
    frontier.insert(root_tuple);

    for (int depth = 0; depth <= qubits; ++depth) {
        if (depth == qubits) {
            for (const auto &tuple : frontier) {
                std::vector<C> lhs(vars, zero_c());

                const auto target_it = target.gamma[static_cast<std::size_t>(depth)].find(tuple[0]);
                if (target_it == target.gamma[static_cast<std::size_t>(depth)].end()) {
                    outcome = Outcome::UnsupportedInput;
                    return false;
                }
                C rhs = target_it->second.symbol_tag.symbol().complex;

                for (std::size_t i = 0; i < vars; ++i) {
                    const auto basis_it = basis[i].gamma[static_cast<std::size_t>(depth)].find(tuple[i + 1]);
                    if (basis_it == basis[i].gamma[static_cast<std::size_t>(depth)].end()) {
                        outcome = Outcome::UnsupportedInput;
                        return false;
                    }
                    lhs[i] = basis_it->second.symbol_tag.symbol().complex;
                }

                ++stats.equations_added;
                if (limits.max_equations != 0 && stats.equations_added > limits.max_equations) {
                    outcome = Outcome::ResourceLimit;
                    return false;
                }

                if (!solver.add_equation(std::move(lhs), rhs)) {
                    return false;
                }
            }
            return true;
        }

        std::set<Tuple> next;
        for (const auto &tuple : frontier) {
            for (std::size_t side = 0; side < 2; ++side) {
                std::vector<std::vector<AUTOQ::ConcreteAutomata::State>> options;
                options.reserve(tuple.size());

                const auto tgt_it = target.gamma[static_cast<std::size_t>(depth)].find(tuple[0]);
                if (tgt_it == target.gamma[static_cast<std::size_t>(depth)].end()) {
                    outcome = Outcome::UnsupportedInput;
                    return false;
                }
                options.push_back(side_states(tgt_it->second, side));

                for (std::size_t i = 0; i < vars; ++i) {
                    const auto b_it = basis[i].gamma[static_cast<std::size_t>(depth)].find(tuple[i + 1]);
                    if (b_it == basis[i].gamma[static_cast<std::size_t>(depth)].end()) {
                        outcome = Outcome::UnsupportedInput;
                        return false;
                    }
                    options.push_back(side_states(b_it->second, side));
                }

                if (std::any_of(options.begin(), options.end(), [](const auto &v) { return v.empty(); })) {
                    continue;
                }

                Tuple current(tuple.size(), 0);
                std::function<void(std::size_t)> expand;
                expand = [&](std::size_t idx) {
                    if (idx == options.size()) {
                        ++stats.tuple_states_visited;
                        if (limits.max_tuple_states != 0 && stats.tuple_states_visited > limits.max_tuple_states) {
                            outcome = Outcome::ResourceLimit;
                            return;
                        }
                        next.insert(current);
                        return;
                    }
                    for (auto s : options[idx]) {
                        current[idx] = s;
                        expand(idx + 1);
                        if (outcome == Outcome::ResourceLimit) {
                            return;
                        }
                    }
                };
                expand(0);
                if (outcome == Outcome::ResourceLimit) {
                    return false;
                }
            }
        }
        frontier = std::move(next);
    }
    return true;
}

}  // namespace detail

inline Result check_inclusion(
    const AUTOQ::ConcreteAutomata &a,
    const AUTOQ::ConcreteAutomata &b,
    Options options)
{
    Result result;
    if (!detail::supported_exact_backend()) {
        result.outcome = Outcome::UnsupportedInput;
        result.message = "Span inclusion requires an exact backend (FiveTuple or nTuple).";
        return result;
    }
    if (options.qubits < 0) {
        result.outcome = Outcome::UnsupportedInput;
        result.message = "--qubits must be specified and non-negative.";
        return result;
    }

    std::vector<CompressedRun> basis;

    Outcome enum_outcome = detail::enumerate_compressed_runs(
        b,
        options.qubits,
        options.limits.max_b_runs,
        result.stats.b_runs_enumerated,
        [&](const CompressedRun &run) {
            Outcome check_outcome = Outcome::Included;
            const bool in_span = detail::run_in_span(run, basis, options.qubits, options.limits, result.stats, check_outcome);
            if (check_outcome == Outcome::ResourceLimit || check_outcome == Outcome::UnsupportedInput) {
                result.outcome = check_outcome;
                return false;
            }
            if (!in_span) {
                if (options.limits.max_basis_runs != 0 && basis.size() >= options.limits.max_basis_runs) {
                    result.outcome = Outcome::ResourceLimit;
                    return false;
                }
                basis.push_back(run);
                result.stats.basis_runs_retained = basis.size();
            }
            return true;
        });

    if (result.outcome == Outcome::ResourceLimit || result.outcome == Outcome::UnsupportedInput) {
        return result;
    }
    if (enum_outcome == Outcome::UnsupportedInput || enum_outcome == Outcome::ResourceLimit) {
        result.outcome = enum_outcome;
        return result;
    }

    enum_outcome = detail::enumerate_compressed_runs(
        a,
        options.qubits,
        options.limits.max_a_runs,
        result.stats.a_runs_enumerated,
        [&](const CompressedRun &run) {
            Outcome check_outcome = Outcome::Included;
            const bool in_span = detail::run_in_span(run, basis, options.qubits, options.limits, result.stats, check_outcome);
            if (check_outcome == Outcome::ResourceLimit || check_outcome == Outcome::UnsupportedInput) {
                result.outcome = check_outcome;
                return false;
            }
            if (!in_span) {
                result.outcome = Outcome::NotIncluded;
                result.witness = run;
                return false;
            }
            return true;
        });

    if (result.outcome == Outcome::NotIncluded || result.outcome == Outcome::ResourceLimit || result.outcome == Outcome::UnsupportedInput) {
        return result;
    }
    if (enum_outcome == Outcome::UnsupportedInput || enum_outcome == Outcome::ResourceLimit) {
        result.outcome = enum_outcome;
        return result;
    }

    result.outcome = Outcome::Included;
    return result;
}

using AutomatonVariant = std::variant<AUTOQ::ConcreteAutomata, AUTOQ::SymbolicAutomata, AUTOQ::PredicateAutomata>;

inline Result check_inclusion(const AutomatonVariant &a, const AutomatonVariant &b, Options options) {
    if (!std::holds_alternative<AUTOQ::ConcreteAutomata>(a) || !std::holds_alternative<AUTOQ::ConcreteAutomata>(b)) {
        return {Outcome::UnsupportedInput, {}, std::nullopt, "Span inclusion currently supports concrete automata only."};
    }
    return check_inclusion(std::get<AUTOQ::ConcreteAutomata>(a), std::get<AUTOQ::ConcreteAutomata>(b), options);
}

inline const char *to_string(Outcome o) {
    switch (o) {
        case Outcome::Included: return "Included";
        case Outcome::NotIncluded: return "NotIncluded";
        case Outcome::ResourceLimit: return "ResourceLimit";
        case Outcome::UnsupportedInput: return "UnsupportedInput";
    }
    return "UnsupportedInput";
}

}  // namespace AUTOQ::Span

#endif
