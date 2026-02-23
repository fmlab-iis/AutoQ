/**
 * LTS-based simulation reduction: build LTS from automata, run simulation, collapse by quotient.
 * - compute_down_sim: build LTS, compute simulation relation, return as DiscontBinaryRelation.
 * - sim_reduce: use compute_down_sim and reindex_aut_states to collapse equivalent states.
 */
#include "autoq/aut_description.hh"
#include "autoq/symbol/concrete.hh"
#include "autoq/symbol/symbolic.hh"
#include "autoq/symbol/predicate.hh"
#include "autoq/symbol/constrained.hh"
#include "autoq/simulation/explicit_lts.hh"
#include "autoq/simulation/automata_to_lts.hh"
#include "autoq/simulation/binary_relation.hh"
#include "autoq/reduce_common.hh"

using namespace AUTOQ;
using namespace AUTOQ::Util;

namespace {

template <typename Symbol>
typename Util::DiscontBinaryRelation<typename Automata<Symbol>::State> compute_down_sim(const AUTOQ::Automata<Symbol>& aut)
{
  using State = typename Automata<Symbol>::State;
  using StateToIndexMap = typename std::unordered_map<State, size_t>;
  using StateToIndexTranslWeak = typename Util::TranslatorWeak<StateToIndexMap>;
  using DiscontBinaryRelOnStates = typename Util::DiscontBinaryRelation<State>;

  StateToIndexMap translMap;
  size_t stateCnt = 0;
  StateToIndexTranslWeak transl(translMap,
      [&stateCnt](const State&) {return stateCnt++;});

  size_t num_states = simulation::count_aut_states(aut);
  AUTOQ::ExplicitLTS lts = simulation::translate_to_lts_downward(aut, num_states, transl);
  BinaryRelation ltsSim = lts.computeSimulation(num_states);
  return DiscontBinaryRelOnStates(ltsSim, translMap);
}

}  // namespace

template <typename Symbol>
void AUTOQ::Automata<Symbol>::sim_reduce()
{
  using State = typename Automata<Symbol>::State;
  using DiscontBinaryRelOnStates = typename Util::DiscontBinaryRelation<State>;
  using StateToStateMap = typename std::unordered_map<State, State>;

  DiscontBinaryRelOnStates sim = compute_down_sim(*this);
  sim.RestrictToSymmetric();
  StateToStateMap collapseMap;
  sim.GetQuotientProjection(collapseMap);
  reduce_detail::reindex_aut_states(*this, collapseMap);
}

template void AUTOQ::Automata<AUTOQ::Symbol::Concrete>::sim_reduce();
template void AUTOQ::Automata<AUTOQ::Symbol::Symbolic>::sim_reduce();
template void AUTOQ::Automata<AUTOQ::Symbol::Predicate>::sim_reduce();
template void AUTOQ::Automata<AUTOQ::Symbol::Index>::sim_reduce();
template void AUTOQ::Automata<AUTOQ::Symbol::Constrained>::sim_reduce();
