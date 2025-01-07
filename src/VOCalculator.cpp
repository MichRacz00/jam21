/*
 * GenMC -- Generic Model Checking.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, you can access it online at
 * http://www.gnu.org/licenses/gpl-3.0.html.
 *
 * Author: Michalis Kokologiannakis <michalis@mpi-sws.org>
 */

#include "VOCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"

void VOCalculator::calcRaRelation() {
	auto &g = getGraph();
	auto &raRelation = g.getGlobalRelation(ExecutionGraph::RelationId::ra);

	for (const auto *lab : labels(g)) {
		auto thirdEventLabel = lab;
		auto secondEventLabel = g.getPreviousNonEmptyLabel(thirdEventLabel);
		auto firstEventLabel = g.getPreviousNonEmptyLabel(secondEventLabel);

		// If any two relations have the same stamp,
		// that means no more previous events in this thread,
		// thus relation cannot exist
		if (thirdEventLabel == secondEventLabel) continue;
		if (secondEventLabel == firstEventLabel) continue;

		// The event in the middle must be rel/acq or stronger
		if (!(secondEventLabel->isAtLeastAcquire() || secondEventLabel->isAtLeastRelease())) continue;

		raRelation.addEdge(firstEventLabel->getIndex(), thirdEventLabel->getIndex());
	}
}

/*
*	Initializes ra relation as relation possibly containing all events.
*/
void VOCalculator::initRaRelation() {
	auto &g = getGraph();
	std::vector<Event> allEvents;

	for (const auto *lab : labels(g)) {
		allEvents.push_back(lab->getPos());
	}

	auto &raRelation = g.getGlobalRelation(ExecutionGraph::RelationId::ra);
	raRelation = Calculator::GlobalRelation(allEvents);
}

void VOCalculator::initCalc()
{	
	initRaRelation();

	return;
}

Calculator::CalculationResult VOCalculator::doCalc()
{
	llvm::outs() << "--------------- Called doCalc() ---------------\n";

	auto &g = getGraph();
	//auto &hbRelation = g.getGlobalRelation(ExecutionGraph::RelationId::hb);
	//auto &pscRelation = g.getGlobalRelation(ExecutionGraph::RelationId::psc);
	//auto &coRelation = g.getPerLocRelation(ExecutionGraph::RelationId::co);
	auto &raRelation = g.getGlobalRelation(ExecutionGraph::RelationId::ra);

	calcRaRelation();
	llvm::outs() << raRelation << "\n";

	return Calculator::CalculationResult(false, false);
}

void VOCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific for PSC */
	return;
}
