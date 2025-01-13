#include "VOCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"

/**
 * Adds all events as the set of possible events,
 * from where relations can start.
*/
void VOCalculator::initCalc()
{	
	auto &g = getGraph();
	std::vector<Event> allEvents;

	for (const auto *lab : labels(g)) {
		allEvents.push_back(lab->getPos());
	}

	auto &raRelation = g.getGlobalRelation(ExecutionGraph::RelationId::ra);
	auto &svoRelation = g.getGlobalRelation(ExecutionGraph::RelationId::svo);
	auto &spushRelation = g.getGlobalRelation(ExecutionGraph::RelationId::spush);
	auto &volintRelation = g.getGlobalRelation(ExecutionGraph::RelationId::volint);
	auto &vvoRelation = g.getGlobalRelation(ExecutionGraph::RelationId::vvo);
	auto &voRelation = g.getGlobalRelation(ExecutionGraph::RelationId::vo);
	auto &cojomRelation = g.getGlobalRelation(ExecutionGraph::RelationId::cojom);

	raRelation = Calculator::GlobalRelation(allEvents);
	svoRelation = Calculator::GlobalRelation(allEvents);
	spushRelation = Calculator::GlobalRelation(allEvents);
	volintRelation = Calculator::GlobalRelation(allEvents);
	vvoRelation = Calculator::GlobalRelation(allEvents);
	voRelation = Calculator::GlobalRelation(allEvents);
	cojomRelation = Calculator::GlobalRelation(allEvents);

	return;
}

Calculator::CalculationResult VOCalculator::doCalc()
{
	llvm::outs() << "--------------- Called doCalc() ---------------\n";

	calcRaRelation();
	calcSvoRelation();
	calcSpushRelation();
	calcVolintRelation();
	calcVvoRelation();
	calcVoRelation();
	calcCojomRelation();

	auto &g = getGraph();
	auto &cojomRelation = g.getGlobalRelation(ExecutionGraph::RelationId::cojom);
	auto &voRelation = g.getGlobalRelation(ExecutionGraph::RelationId::vo);
	//llvm::outs() << vvoRelation << "\n";
	llvm::outs() << voRelation << "\n";
	llvm::outs() << cojomRelation << "\n";

	return Calculator::CalculationResult(false, true);
}

void VOCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
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

		// The second event must be a release fence
		if (!(secondEvent->getOrdering() == llvm::AtomicOrdering::Release && isFence(secondEvent))) continue;

		// The third event must be either a read or a write
		if (!(isRead(thirdEvent) || isWrite(thirdEvent))) continue;

		// The fourth event must be an acquire fence
		if (!(fourthEvent->getOrdering() == llvm::AtomicOrdering::Acquire && isFence(fourthEvent))) continue;

		svoRelation.addEdge(firstEvent->getPos(), lastEvent->getPos());
	}
}

void VOCalculator::calcSpushRelation() {
	auto &g = getGraph();
	auto &spushRelation = g.getGlobalRelation(ExecutionGraph::RelationId::spush);

	for (const auto *lab : labels(g)) {
		auto events = getPrevMany(lab, 3);
		if (events.empty()) continue;

		auto thirdEventLabel = events[0].get();
		auto secondEventLabel = events[1].get();
		auto firstEventLabel = events[2].get();

		// The event in the middle must be a SC fence
		if (!(isFence(secondEventLabel) && secondEventLabel->isSC())) continue;

		spushRelation.addEdge(firstEventLabel->getPos(), thirdEventLabel->getPos());
	}
}

void VOCalculator::calcVolintRelation() {
	auto &g = getGraph();
	auto &volintRelation = g.getGlobalRelation(ExecutionGraph::RelationId::volint);

	for (const auto *lab : labels(g)) {
		auto events = getPrevMany(lab, 2);
		if (events.empty()) continue;

		auto secondEventLabel = events[0].get();
		auto firstEventLabel = events[1].get();

		// Both events must be SC
		if (!(firstEventLabel->isSC() && secondEventLabel->isSC())) continue;

		volintRelation.addEdge(firstEventLabel->getPos(), secondEventLabel->getPos());
	}
}

void VOCalculator::calcVvoRelation() {
	auto &g = getGraph();
	auto &raRelation = g.getGlobalRelation(ExecutionGraph::RelationId::ra);
	auto &svoRelation = g.getGlobalRelation(ExecutionGraph::RelationId::svo);
	auto &spushRelation = g.getGlobalRelation(ExecutionGraph::RelationId::spush);
	auto &volintRelation = g.getGlobalRelation(ExecutionGraph::RelationId::volint);
	auto &vvoRelation = g.getGlobalRelation(ExecutionGraph::RelationId::vvo);

	for (const auto *lab : labels(g)) {
		
		// Calculations for rf; (spush U volint)
		if (auto readLabel = dynamic_cast<const ReadLabel *>(lab)) {
			auto writeLabel = readLabel->getRf();
			
			for (auto finalEvent : getAdj(readLabel->getPos(), ExecutionGraph::RelationId::spush)) {
				vvoRelation.addEdge(writeLabel, *finalEvent);
				//llvm::outs() << "rf; spush " << readLabel->getPos() << " -> " << *finalEvent << "\n";
			}

			for (auto finalEvent : getAdj(readLabel->getPos(), ExecutionGraph::RelationId::volint)) {
				vvoRelation.addEdge(writeLabel, *finalEvent);
				//llvm::outs() << "rf; volint " << readLabel->getPos() << " -> " << *finalEvent << "\n";
			}
    	}

		// Calculations for svo; (spush U volint)
		for (auto middleLabel : getAdj(lab->getPos(), ExecutionGraph::RelationId::svo)) {
			for (auto finalLabel : getAdj(*middleLabel, ExecutionGraph::RelationId::spush)) {
				vvoRelation.addEdge(lab->getPos(), *finalLabel);
				//llvm::outs() << "svo; spush " << lab->getPos() << " -> " << *finalLabel << "\n";
			}

			for (auto finalLabel : getAdj(*middleLabel, ExecutionGraph::RelationId::volint)) {
				vvoRelation.addEdge(lab->getPos(), *finalLabel);
				//llvm::outs() << "svo; volint " << lab->getPos() << " -> " << *finalLabel << "\n";
			}
		}

		// Calculations for ra; (spush U volint)
		for (auto middleLabel : getAdj(lab->getPos(), ExecutionGraph::RelationId::ra)) {
			for (auto finalLabel : getAdj(*middleLabel, ExecutionGraph::RelationId::spush)) {
				vvoRelation.addEdge(lab->getPos(), *finalLabel);
				//llvm::outs() << "ra; spush " << lab->getPos() << " -> " << *finalLabel << "\n";
			}

			for (auto finalLabel : getAdj(*middleLabel, ExecutionGraph::RelationId::volint)) {
				vvoRelation.addEdge(lab->getPos(), *finalLabel);
				//llvm::outs() << "ra; volint " << lab->getPos() << " -> " << *finalLabel << "\n";
			}
		}

		// Calculations for spush ; (spush U volint)
		for (auto middleLabel : getAdj(lab->getPos(), ExecutionGraph::RelationId::spush)) {
			for (auto finalLabel : getAdj(*middleLabel, ExecutionGraph::RelationId::spush)) {
				vvoRelation.addEdge(lab->getPos(), *finalLabel);
				//llvm::outs() << "spush; spush " << lab->getPos() << " -> " << *finalLabel << "\n";
			}

			for (auto finalLabel : getAdj(*middleLabel, ExecutionGraph::RelationId::volint)) {
				vvoRelation.addEdge(lab->getPos(), *finalLabel);
				//llvm::outs() << "spush; volint " << lab->getPos() << " -> " << *finalLabel << "\n";
			}
		}

		// Calculations for volint ; (spush U volint)
		for (auto middleLabel : getAdj(lab->getPos(), ExecutionGraph::RelationId::volint)) {
			for (auto finalLabel : getAdj(*middleLabel, ExecutionGraph::RelationId::spush)) {
				vvoRelation.addEdge(lab->getPos(), *finalLabel);
				//llvm::outs() << "volint; spush " << lab->getPos() << " -> " << *finalLabel << "\n";
			}

			for (auto finalLabel : getAdj(*middleLabel, ExecutionGraph::RelationId::volint)) {
				vvoRelation.addEdge(lab->getPos(), *finalLabel);
				//llvm::outs() << "volint; volint " << lab->getPos() << " -> " << *finalLabel << "\n";
			}
		}

		// TODO add pushto
	}
}

void VOCalculator::calcVoRelation() {
	auto &g = getGraph();
	auto &vvoRelation = g.getGlobalRelation(ExecutionGraph::RelationId::vvo);
	auto &voRelation = g.getGlobalRelation(ExecutionGraph::RelationId::vo);

	// Add all edges from vvo to vo
	for (auto &event : vvoRelation.getElems()) {
		for (auto &adj : getAdj(event, ExecutionGraph::RelationId::vvo)) {
			// TODO add po-loc
			voRelation.addEdge(event, *adj);
		}
	}

	voRelation.transClosure();
}

void VOCalculator::calcCojomRelation() {
	auto &g = getGraph();
	auto &voRelation = g.getGlobalRelation(ExecutionGraph::RelationId::vo);
	auto &cojomRelation = g.getGlobalRelation(ExecutionGraph::RelationId::cojom);

	// add coww, cowr and corw edges
	for (auto *lab : labels(g)) {

		// First label must allways be a write
		auto initialLabel = dynamic_cast<WriteLabel *>(lab);
		if (!initialLabel) continue;

		// Iteratoe over all final VO events
		for(auto finalVoEvent : getAdj(initialLabel->getPos(), ExecutionGraph::RelationId::vo)) {

			auto finalVoWriteLabel = dynamic_cast<WriteLabel *>(g.getEventLabel(*finalVoEvent));
			if (finalVoWriteLabel) {
				// If both labels are writes to the same address,
				// and are not the same, then this event is in coww
				if(initialLabel->getAddr() == finalVoWriteLabel->getAddr() && initialLabel != finalVoWriteLabel) {
					cojomRelation.addEdge(lab->getPos(), *finalVoEvent);
				}
			}
			
			/*
			 * If the event in VO is a read, with RF^-1 pointg
			 * to a write to the same location add this relation to cojom
			 */
			auto finalVoReadLabel = dynamic_cast<ReadLabel *>(g.getEventLabel(*finalVoEvent));
			if (finalVoReadLabel) {
				auto finalRfWriteLabel = dynamic_cast<WriteLabel *>(g.getEventLabel(finalVoReadLabel->getRf()));
				
				if (initialLabel->getAddr() == finalRfWriteLabel->getAddr() && initialLabel != finalRfWriteLabel) {
					cojomRelation.addEdge(lab->getPos(), finalVoReadLabel->getRf());
				}
			}
		}
	}
}

std::vector<Event*> VOCalculator::getAdj(Event lab, ExecutionGraph::RelationId relationId) {
	auto &g = getGraph();
	auto relation = g.getGlobalRelation(relationId);
	auto adjLabels = relation.getElems();
	std::vector<Event*> adjEvents;

	for (auto adj = relation.adj_begin(lab); adj != relation.adj_end(lab); ++adj) {
		adjEvents.push_back(&adjLabels[*adj]);
    }

	return adjEvents;
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