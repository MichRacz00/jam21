#include "VOCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"

void VOCalculator::initCalc()
{	
	initRaRelation();
	return;
}

Calculator::CalculationResult VOCalculator::doCalc()
{
	llvm::outs() << "--------------- Called doCalc() ---------------\n";

	auto &g = getGraph();
	auto &raRelation = g.getGlobalRelation(ExecutionGraph::RelationId::ra);

	calcRaRelation();
	llvm::outs() << raRelation << "\n";

	return Calculator::CalculationResult(false, false);
}

void VOCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
}

/**
 * Retrieves n previous events starting from and including the given event,
 * and returns them in a vector. The events are ordered from the most recent 
 * (largest timestamp) to the oldest (smallest timestamp), with the given 
 * event at the start of the vector. If fewer than n previous events are available, 
 * an empty vector is returned.
 */

std::vector<std::unique_ptr<EventLabel>> VOCalculator::getPrevMany(const EventLabel *lab, int n) {
	auto &g = getGraph();
	std::vector<std::unique_ptr<EventLabel>> labels;
	auto currentLab = lab;

    while (n > 0) {
        labels.push_back(currentLab->clone());
        auto prevLab = g.getPreviousNonEmptyLabel(currentLab);
		/*
		* If the previous label is the same as the current label, and there are
        * more labels left to retrieve, return an empty vector indicating
        * insufficient previous labels.
		*/ 
		if (prevLab == currentLab && n > 1) return {};
		currentLab = prevLab;
        --n;
    }

    return labels;
}

void VOCalculator::calcRaRelation() {
	auto &g = getGraph();
	auto &raRelation = g.getGlobalRelation(ExecutionGraph::RelationId::ra);

	for (const auto *lab : labels(g)) {
		auto events = getPrevMany(lab, 3);
		if (events.empty()) continue;

		auto thirdEventLabel = events[0].get();
		auto secondEventLabel = events[1].get();
		auto firstEventLabel = events[2].get();

		// The event in the middle must be rel/acq or stronger
		if (!(secondEventLabel->isAtLeastAcquire() || secondEventLabel->isAtLeastRelease())) continue;
		
		raRelation.addEdge(firstEventLabel->getPos(), thirdEventLabel->getPos());
	}
}

/**
 * Initializes ra relation as relation possibly containing all events.
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