#ifndef AUTOQ_UNIT_TEST_SPAN_TEST_UTIL_HH
#define AUTOQ_UNIT_TEST_SPAN_TEST_UTIL_HH

#include <boost/multiprecision/cpp_int.hpp>
#include <boost/rational.hpp>

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <random>
#include <string>
#include <utility>
#include <vector>

#include "autoq/aut_description.hh"
#include "autoq/complex/complex.hh"
#include "autoq/serialization/timbuk_serializer.hh"

namespace span_test {

using Rat = boost::rational<boost::multiprecision::cpp_int>;

inline AUTOQ::Complex::Complex cplx(int x) {
    return AUTOQ::Complex::Complex(x);
}

inline std::vector<int> index_to_bits(std::size_t idx, int n) {
    std::vector<int> bits(static_cast<std::size_t>(n), 0);
    for (int i = 0; i < n; ++i) {
        bits[static_cast<std::size_t>(n - 1 - i)] = static_cast<int>((idx >> i) & 1ULL);
    }
    return bits;
}

inline AUTOQ::ConcreteAutomata automaton_from_vectors(int n, const std::vector<std::vector<int>> &vectors) {
    AUTOQ::ConcreteAutomata aut;
    aut.qubitNum = n;

    AUTOQ::ConcreteAutomata::State next_state = 0;
    for (const auto &vec : vectors) {
        const AUTOQ::ConcreteAutomata::State root = next_state++;
        aut.finalStates.push_back(root);

        if (n == 0) {
            const int amp = vec.empty() ? 0 : vec[0];
            aut.transitions[{AUTOQ::Symbol::Concrete(cplx(amp)), 1}][root].insert({{}});
            continue;
        }

        std::vector<AUTOQ::ConcreteAutomata::State> level_states{root};
        for (int depth = 0; depth < n; ++depth) {
            std::vector<AUTOQ::ConcreteAutomata::State> next_level;
            for (AUTOQ::ConcreteAutomata::State s : level_states) {
                const AUTOQ::ConcreteAutomata::State l = next_state++;
                const AUTOQ::ConcreteAutomata::State r = next_state++;
                aut.transitions[{depth + 1, 1}][s].insert({l, r});
                next_level.push_back(l);
                next_level.push_back(r);
            }
            level_states = std::move(next_level);
        }

        const std::size_t expected = static_cast<std::size_t>(1ULL << n);
        for (std::size_t i = 0; i < expected; ++i) {
            const int amp = i < vec.size() ? vec[i] : 0;
            aut.transitions[{AUTOQ::Symbol::Concrete(cplx(amp)), 1}][level_states[i]].insert({{}});
        }
    }

    aut.stateNum = next_state;
    return aut;
}

inline Rat to_rat(const AUTOQ::Complex::Complex &x) {
    return x.to_rational();
}

inline std::size_t rank_of_matrix(std::vector<std::vector<Rat>> m) {
    if (m.empty()) {
        return 0;
    }
    const std::size_t rows = m.size();
    const std::size_t cols = m.front().size();
    std::size_t rank = 0;
    std::size_t pivot_col = 0;

    while (rank < rows && pivot_col < cols) {
        std::size_t pivot = rank;
        while (pivot < rows && m[pivot][pivot_col] == Rat(0)) {
            ++pivot;
        }
        if (pivot == rows) {
            ++pivot_col;
            continue;
        }
        std::swap(m[rank], m[pivot]);
        const Rat pivot_val = m[rank][pivot_col];
        for (std::size_t r = rank + 1; r < rows; ++r) {
            if (m[r][pivot_col] == Rat(0)) {
                continue;
            }
            const Rat factor = m[r][pivot_col] / pivot_val;
            for (std::size_t c = pivot_col; c < cols; ++c) {
                m[r][c] -= factor * m[rank][c];
            }
        }
        ++rank;
        ++pivot_col;
    }
    return rank;
}

inline bool dense_rank_span_inclusion(const std::vector<std::vector<int>> &a, const std::vector<std::vector<int>> &b) {
    if (b.empty()) {
        for (const auto &v : a) {
            for (int x : v) {
                if (x != 0) {
                    return false;
                }
            }
        }
        return true;
    }

    std::vector<std::vector<Rat>> only_b;
    for (const auto &v : b) {
        std::vector<Rat> row;
        row.reserve(v.size());
        for (int x : v) {
            row.emplace_back(x);
        }
        only_b.push_back(std::move(row));
    }

    std::vector<std::vector<Rat>> b_and_a = only_b;
    for (const auto &v : a) {
        std::vector<Rat> row;
        row.reserve(v.size());
        for (int x : v) {
            row.emplace_back(x);
        }
        b_and_a.push_back(std::move(row));
    }

    return rank_of_matrix(b_and_a) == rank_of_matrix(only_b);
}

inline std::string write_automaton_file(const AUTOQ::ConcreteAutomata &aut, const std::string &path) {
    std::ofstream os(path);
    os << AUTOQ::Serialization::TimbukSerializer::Serialize(aut);
    os.close();
    return path;
}

inline std::vector<std::vector<int>> fixed_seed_vectors(int count, int dim, unsigned seed) {
    std::mt19937 rng(seed);
    std::uniform_int_distribution<int> dist(-2, 2);
    std::vector<std::vector<int>> out;
    out.reserve(static_cast<std::size_t>(count));
    for (int i = 0; i < count; ++i) {
        std::vector<int> v(static_cast<std::size_t>(dim));
        for (int j = 0; j < dim; ++j) {
            v[static_cast<std::size_t>(j)] = dist(rng);
        }
        out.push_back(std::move(v));
    }
    return out;
}

}  // namespace span_test

#endif
