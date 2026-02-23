/**
 * LTS construction: add transitions and grow the LTS structure.
 * Simulation algorithm (computeSimulation, Block, SimulationEngine) is in explicit_lts_sim.cc.
 */
#include "autoq/simulation/explicit_lts.hh"

void AUTOQ::ExplicitLTS::addTransition(
	size_t   q,
	size_t   a,
	size_t   r)
{
	if (a >= this->data_.size())
	{
		this->data_.resize(a + 1);
	}

	if (q >= this->data_[a].first.size())
	{
		if (q >= this->states_)
		{
			this->states_ = q + 1;
		}

		this->data_[a].first.resize(q + 1);
	}

	if (r >= this->data_[a].second.size())
	{
		if (r >= this->states_)
		{
			this->states_ = r + 1;
		}

		this->data_[a].second.resize(r + 1);
	}

	this->data_[a].first[q].push_back(r);
	this->data_[a].second[r].push_back(q);

	++this->transitions_;
}
