#include "HBCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"
#include <deque>

void HBCalculator::initCalc()
{
	// Relations are calculated from scratch everytime doCalc()
	// is called, nothing to do on init
	return;
}

Calculator::CalculationResult HBCalculator::doCalc()
{
	auto &g = getGraph();
	auto& firstThread = *(std::next(g.getThreadList().begin(), 1));

	addIntraThreadHB(firstThread);
	return Calculator::CalculationResult(false, true);
}

void HBCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
}

void HBCalculator::addIntraThreadHB(ExecutionGraph::Thread &eventLabels) {
	std::deque<EventLabel*> lastLabels;

    for (auto &lab : eventLabels) {
		lastLabels.push_back(lab.get());
		if (lastLabels.size() > 5) lastLabels.pop_front();

		if (lastLabels.size() >= 2) {
			auto last = lastLabels.back();
            auto oneButLast = *(std::next(lastLabels.rbegin()));

			if (last->isSC() && oneButLast->isSC()) {
				// Volint
				llvm::outs() << "volint";
			}

			if (lastLabels.size() >= 3) {
				auto twoButLast = *(std::next(lastLabels.rbegin(), 2));
				
				if (lastLabels.size() >= 5) {
					
				}
			}
		}
    }
}