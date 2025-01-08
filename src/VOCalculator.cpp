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

	calcRaRelation();
	calcSvoRelation();

	auto &g = getGraph();
	auto &svoRelation = g.getGlobalRelation(ExecutionGraph::RelationId::svo);

	//llvm::outs() << raRelation << "\n";
	llvm::outs() << svoRelation << "\n";

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

void VOCalculator::calcSvoRelation() {
	auto &g = getGraph();
	auto &svoRelation = g.getGlobalRelation(ExecutionGraph::RelationId::svo);

	for (const auto *lab : labels(g)) {
		auto events = getPrevMany(lab, 5);
		if (events.empty()) continue;

		auto lastEvent = events[0].get();
		auto fourthEvent = events[1].get();
		auto thirdEvent = events[2].get();
		auto secondEvent = events[3].get();
		auto firstEvent = events[4].get();

		// The second event must be an acquire fence
		if (!(secondEvent->getOrdering() == llvm::AtomicOrdering::Acquire && isFence(secondEvent))) continue;

		// The third event must be either a read or a write
		if (!(isRead(thirdEvent) || isWrite(thirdEvent))) continue;

		// The fourth event must be a release fence
		if (!(fourthEvent->getOrdering() == llvm::AtomicOrdering::Release && isFence(fourthEvent))) continue;

		svoRelation.addEdge(firstEvent->getPos(), lastEvent->getPos());
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
	auto &svoRelation = g.getGlobalRelation(ExecutionGraph::RelationId::svo);
	auto &spushRelation = g.getGlobalRelation(ExecutionGraph::RelationId::spush);

	raRelation = Calculator::GlobalRelation(allEvents);
	svoRelation = Calculator::GlobalRelation(allEvents);
	spushRelation = Calculator::GlobalRelation(allEvents);
}

bool VOCalculator::isFence(EventLabel *lab) {
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

bool VOCalculator::isRead(EventLabel *lab) {
	switch (lab->getKind()) {
		case EventLabel::EL_Read:
		case EventLabel::EL_BWaitRead:
		case EventLabel::EL_SpeculativeRead:
		case EventLabel::EL_ConfirmingRead:
		case EventLabel::EL_DskRead:
		case EventLabel::EL_CasRead:
		case EventLabel::EL_LockCasRead:
		case EventLabel::EL_TrylockCasRead:
		case EventLabel::EL_HelpedCasRead:
		case EventLabel::EL_ConfirmingCasRead:
		case EventLabel::EL_FaiRead:
		case EventLabel::EL_BIncFaiRead:
			return true;
		default:
			return false;
	}
}

bool VOCalculator::isWrite(EventLabel *lab) {
	switch (lab->getKind()) {
		case EventLabel::EL_Write:
		case EventLabel::EL_BInitWrite:
		case EventLabel::EL_BDestroyWrite:
		case EventLabel::EL_UnlockWrite:
		case EventLabel::EL_CasWrite:
		case EventLabel::EL_LockCasWrite:
		case EventLabel::EL_TrylockCasWrite:
		case EventLabel::EL_HelpedCasWrite:
		case EventLabel::EL_ConfirmingCasWrite:
		case EventLabel::EL_FaiWrite:
		case EventLabel::EL_BIncFaiWrite:
		case EventLabel::EL_DskWrite:
		case EventLabel::EL_DskMdWrite:
		case EventLabel::EL_DskDirWrite:
		case EventLabel::EL_DskJnlWrite:
			return true;
		default:
			return false;
	}
}