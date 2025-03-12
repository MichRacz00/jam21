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

	std::vector<Event> allEvents;
	for (auto const lab : labels(g)) allEvents.push_back(lab->getPos());
	Calculator::GlobalRelation hb(allEvents);

	for (auto &t : g.getThreadList()) {
		addIntraThreadHB(t, hb);
	}

	llvm::outs() << hb;

	return Calculator::CalculationResult(false, true);
}

void HBCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
}

void HBCalculator::addIntraThreadHB(ExecutionGraph::Thread &eventLabels, Calculator::GlobalRelation &hb) {
	std::deque<EventLabel*> lastLabels;

    for (auto &lab : eventLabels) {
		lastLabels.push_back(lab.get());
		if (lastLabels.size() > 5) lastLabels.pop_front();

		if (lastLabels.size() >= 2) {
			auto last = lastLabels.back();
            auto oneButLast = *(std::next(lastLabels.rbegin()));

			if (last->isSC() && oneButLast->isSC()) {
				// volint
				hb.addEdge(oneButLast->getPos(), last->getPos());
			}

			if (lastLabels.size() >= 3) {
				auto twoButLast = *(std::next(lastLabels.rbegin(), 2));

				if (oneButLast->isSC() && isFence(oneButLast)) {
					// spush
					hb.addEdge(twoButLast->getPos(), last->getPos());
				}

				if (oneButLast->isSC() || oneButLast->isAtLeastAcquire() || oneButLast->isAtLeastRelease()) {
					// ra
					hb.addEdge(twoButLast->getPos(), last->getPos());
				}
				
				if (lastLabels.size() >= 5) {
					auto threeButLast = *(std::next(lastLabels.rbegin(), 3));
					auto fourButLast = *(std::next(lastLabels.rbegin(), 4));

					auto writeCast = dynamic_cast<WriteLabel*>(threeButLast);
					auto readCast = dynamic_cast<ReadLabel*>(threeButLast);

					if (writeCast || readCast) {
						if (isFence(fourButLast) && fourButLast->isAtLeastRelease() && isFence(twoButLast) && twoButLast->isAtLeastAcquire()) {
							// svo
							auto first = *(std::next(lastLabels.rbegin(), 5));
							hb.addEdge(first->getPos(), last->getPos());
						}
					}
				}
			}
		}
    }
}

bool HBCalculator::isFence(EventLabel *lab) {
	switch (lab->getKind())
	{
		case EventLabel::EL_Fence:
		case EventLabel::EL_DskFsync:
		case EventLabel::EL_DskSync:
		case EventLabel::EL_DskPbarrier:
			return true;
		default:
			return false;
	}
}