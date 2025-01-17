#include "VOCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"

// Helper relations used to calculate vo
Calculator::GlobalRelation spush;
Calculator::GlobalRelation volint;

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
	auto &polocRelation = g.getGlobalRelation(ExecutionGraph::RelationId::poloc);

	raRelation = Calculator::GlobalRelation(allEvents);
	svoRelation = Calculator::GlobalRelation(allEvents);
	spushRelation = Calculator::GlobalRelation(allEvents);
	volintRelation = Calculator::GlobalRelation(allEvents);
	vvoRelation = Calculator::GlobalRelation(allEvents);
	voRelation = Calculator::GlobalRelation(allEvents);
	cojomRelation = Calculator::GlobalRelation(allEvents);
	polocRelation = Calculator::GlobalRelation(allEvents);

	return;
}

Calculator::CalculationResult VOCalculator::doCalc()
{
	calcRaRelation();
	calcSvoRelation();
	calcSpushRelation();
	calcVolintRelation();
	calcVvoRelation();
	calcPolocRelation();
	calcPushtoRelation();
	calcVoRelation();
	calcCojomRelation();

	auto &g = getGraph();

	auto &cojomRelation = g.getGlobalRelation(ExecutionGraph::RelationId::cojom);
	//llvm::outs() << cojomRelation << "\n";

	auto &spushRel = g.getGlobalRelation(ExecutionGraph::RelationId::spush);
	//llvm::outs() << spushRel << "\n";

	auto &volintRel = g.getGlobalRelation(ExecutionGraph::RelationId::volint);
	//llvm::outs() << volintRel << "\n";

	// Calculate acyclicity by transitive closure and irreflexivity.
	calcTransC(ExecutionGraph::RelationId::cojom);
	bool isAcyclic = cojomRelation.isIrreflexive();

	return Calculator::CalculationResult(false, isAcyclic);
}

void VOCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
}

void VOCalculator::calcRaRelation() {
	auto &g = getGraph();
	auto &raRelation = g.getGlobalRelation(ExecutionGraph::RelationId::ra);

	for (EventLabel* lab : labels(g)) {
		auto events = getPrevMany(*lab, 3);
		if (events.empty()) continue;

		// The event in the middle must be rel/acq or stronger
		if (!(events[1].isAtLeastAcquire() || events[1].isAtLeastRelease())) continue;
		raRelation.addEdge(events[0].getPos(), events[3].getPos());
	}
}

void VOCalculator::calcSvoRelation() {
	auto &g = getGraph();
	auto &svoRelation = g.getGlobalRelation(ExecutionGraph::RelationId::svo);

	for (EventLabel* lab : labels(g)) {
		auto events = getPrevMany(*lab, 5);
		if (events.empty()) continue;

		// The second event must be a release fence
		if (!(events[1].getOrdering() == llvm::AtomicOrdering::Release && isFence(&events[1]))) continue;

		// The third event must be either a read or a write
		auto thirdRead = dynamic_cast<ReadLabel*>(&events[2]);
		auto thirdWrite = dynamic_cast<WriteLabel*>(&events[2]);
		if (!thirdRead && !thirdWrite) continue;

		// The fourth event must be an acquire fence
		if (!(events[3].getOrdering() == llvm::AtomicOrdering::Acquire && isFence(&events[3]))) continue;

		svoRelation.addEdge(events[0].getPos(), events[4].getPos());
	}
}

Calculator::GlobalRelation VOCalculator::calcSpushRelation() {
	auto &g = getGraph();
	Calculator::GlobalRelation spush;

	for (const auto *lab : labels(g)) {
		auto events = getPrevMany(lab, 3);
		if (events.empty()) continue;

		auto thirdEventLabel = events[0].get();
		auto secondEventLabel = events[1].get();
		auto firstEventLabel = events[2].get();

		// The event in the middle must be a SC fence
		if (!(isFence(secondEventLabel) && secondEventLabel->isSC())) continue;

		tryAddEdge(firstEventLabel->getPos(), thirdEventLabel->getPos(), &spush);
	}

	return spush;
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

/**
 * Returns a union of all given relations.
 */
Calculator::GlobalRelation VOCalculator::merge(std::vector<Calculator::GlobalRelation> relations) {
	Calculator::GlobalRelation merged;
	for (const auto relation : relations) {
		for (const auto elem : relation) {
			for (auto adjIdx = relation.adj_begin(elem); adjIdx != relation.adj_end(elem); ++adjIdx) {
        		const auto& adjElem = relation.getElems()[*adjIdx];
        		tryAddEdge(elem, adjElem, &merged);
    		}
		}
	}
	return merged;
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

void VOCalculator::calcPolocRelation() {
	auto &g = getGraph();
	auto &polocRelation = g.getGlobalRelation(ExecutionGraph::RelationId::poloc);

	for (auto eventLabel : labels(g)) {
		auto initialMemoryLabel = dynamic_cast<MemAccessLabel *>(eventLabel);
		if (!initialMemoryLabel) continue;

		bool finalLabelFound = false;
		auto nextLabel = eventLabel;
		while (!finalLabelFound) {
			nextLabel = g.getNextLabel(nextLabel);
			// Reached the end of the thread, terminate
			if (!nextLabel) break;

			auto nextMemoryLabel = dynamic_cast<MemAccessLabel *>(nextLabel);
			// is not a memory access label, continue
			if (!nextMemoryLabel) continue;
			
			// Initial and next labels access the same address, return
			if (initialMemoryLabel->getAddr() == nextMemoryLabel->getAddr()) finalLabelFound = true;
		}

		if (finalLabelFound) {
			polocRelation.addEdge(initialMemoryLabel->getPos(), nextLabel->getPos());
		}
	}
}

void VOCalculator::calcVoRelation() {
	auto &g = getGraph();
	auto &vvoRelation = g.getGlobalRelation(ExecutionGraph::RelationId::vvo);
	auto &polocRelation = g.getGlobalRelation(ExecutionGraph::RelationId::poloc);
	auto &voRelation = g.getGlobalRelation(ExecutionGraph::RelationId::vo);

	calcTransC(ExecutionGraph::RelationId::vvo);

	// Add all edges from vvo to vo
	for (auto &event : vvoRelation.getElems()) {
		for (auto &adj : getAdj(event, ExecutionGraph::RelationId::vvo)) {
			voRelation.addEdge(event, *adj);
		}
	}

	// Add all edges from po-loc to vo
	for (auto &event : polocRelation.getElems()) {
		for (auto &adj : getAdj(event, ExecutionGraph::RelationId::poloc)) {
			voRelation.addEdge(event, *adj);
		}
	}
}

/**
 * Calculates push relation which is union of spush
 * and volint, where initial and final events 
 * are writes to the same memory location.
 */
Calculator::GlobalRelation VOCalculator::calcPushRelation() {
	auto &g = getGraph();
	auto spushRelation = g.getGlobalRelation(ExecutionGraph::RelationId::spush);
	auto volintRelation = g.getGlobalRelation(ExecutionGraph::RelationId::volint);

	std::vector<Calculator::GlobalRelation> relations;
	relations.push_back(spushRelation);
	relations.push_back(volintRelation);
	auto spushUvolint = merge(relations);

	Calculator::GlobalRelation push;

	for (const auto elem : spushUvolint.getElems()) {
		// Initial label must be a write
		auto initialWriteLab = g.getWriteLabel(elem);
		if (!initialWriteLab) continue;

		const auto adjElems = getAdj(elem, spushUvolint);
		if (0 < adjElems.size()) {
			for (const auto adjElem : adjElems) {
				// Final label must be a write
				auto finalWriteLab = g.getWriteLabel(adjElem);
				if (!finalWriteLab) continue;

				// If both accesses are to the same location and
				// are not an identity, add an edge in push
				if (initialWriteLab->getAddr() == finalWriteLab->getAddr()
					&& initialWriteLab != finalWriteLab) {
					tryAddEdge(elem, adjElem, &push);
				}
			}
		}
	}

	return push;
}

/**
 * Calculates pushto relation which is a trace order (total order)
 * in the push relation (volint U spush). Total order must not
 * violate po U rf. Total order is calculated using topological
 * sort. All sorts are checked for violations of po U rf relation.
 */
Calculator::GlobalRelation VOCalculator::calcPushtoRelation() {
	auto const push = calcPushRelation();
	std::vector<Event> topologicalSort;

	push.allTopoSort([this, &topologicalSort](auto& sort) {
		auto &g = getGraph();

		for (int i = 1; i < sort.size(); ++i) {
			auto event = sort[i - 1];
			auto nextEvent = sort[i];

			auto lab = g.getEventLabel(event);
			auto nextLab = g.getEventLabel(nextEvent);

			// Topological order (linearisation) violates po U rf view
			// Namely, if porf vector clocks are out of order
			if (!(lab->getPorfView() <= nextLab->getPorfView())) {
				// Reject this topological order
				return false;
			}
		}

		topologicalSort = sort;
        return true;
    });

	/**
	 * Create relation object, add total order edges
	 * reflecting event order from the list
	 * topologicalSort [A, B, C]
	 * relation: (A) -> (B), (B) -> (C)
	 */
	Calculator::GlobalRelation pushto(topologicalSort);
	for (int i = 1; i < pushto.size(); i ++) {
		const auto elemA = pushto.getElems()[i - 1];
		const auto elemB = pushto.getElems()[i];
		tryAddEdge(elemA, elemB, &pushto);
	}

	return pushto;
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

			auto finalVoWriteLabel = g.getWriteLabel(*finalVoEvent);
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
			auto finalVoReadLabel = g.getReadLabel(*finalVoEvent);
			if (finalVoReadLabel) {
				auto finalRfWriteLabel = g.getWriteLabel(finalVoReadLabel->getRf());
				if (!finalRfWriteLabel) continue;

				if (initialLabel->getAddr() == finalRfWriteLabel->getAddr() && initialLabel != finalRfWriteLabel) {
					cojomRelation.addEdge(lab->getPos(), finalVoReadLabel->getRf());
				}
			}

			/*
			 * Add corw edges. Carru out the same check as for coww,
			 * except for the next event in PO.
			 */
			auto finalLabel = g.getEventLabel(*finalVoEvent);
			if (!finalLabel) continue;
			auto finalPoLabel = g.getNextLabel(finalLabel);
			if (!finalPoLabel) continue;

			auto finalPoWriteLabel = dynamic_cast<WriteLabel *>(finalPoLabel);
			if (finalPoWriteLabel) {
				if (initialLabel->getAddr() == finalPoWriteLabel->getAddr() && initialLabel != finalPoWriteLabel) {
					cojomRelation.addEdge(lab->getPos(), finalPoWriteLabel->getPos());
				}
			}
		}

		/*
		 * Add corr edges. Find four events W -rf-> R -po-> R <-rf- W,
		 * flip the last rf relation. Writes must be opaque or stronger
		 * and to the same address.
		 */
		auto initialWriteLabel = dynamic_cast<WriteLabel *>(lab);
		if (initialWriteLabel) {
			if (initialWriteLabel->isNotAtomic()) continue;

			for (auto initialReadEvent : initialWriteLabel->getReadersList()) {

				auto finalReadLabel = dynamic_cast<ReadLabel *>(g.getNextLabel(initialReadEvent));
				if (!finalReadLabel) continue;

				auto finalWriteLabel = dynamic_cast<WriteLabel *>(g.getEventLabel(finalReadLabel->getRf()));
				if (!finalWriteLabel) continue;
				if (finalWriteLabel->isNotAtomic()) continue;
				
				if (initialWriteLabel->getAddr() == finalWriteLabel->getAddr() && initialWriteLabel != finalWriteLabel) {
					cojomRelation.addEdge(initialWriteLabel->getPos(), finalWriteLabel->getPos());
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
 * Retrieves all events in the relation that are directly reachable
 * from the specified event (i.e., all events where an edge from 
 * the given event terminates).
 */
std::vector<Event> VOCalculator::getAdj(Event event, Calculator::GlobalRelation relation) {
	std::vector<Event> adjEvents;
	for (auto adjIdx = relation.adj_begin(event); adjIdx != relation.adj_end(event); ++adjIdx) {
        const auto& adjElem = relation.getElems()[*adjIdx];
    	adjEvents.push_back(adjElem);
    }
	return adjEvents;
}

/**
 * Retrieves n previous event labels starting from and including the given event,
 * and returns them in a vector. The initial event is in the front of the vector,
 * followed by n-1 previous events. If there are less than n prev events,
 * an empty vector is returned.
 */
std::vector<EventLabel> VOCalculator::getPrevMany(EventLabel &lab, int n) {
	auto &g = getGraph();
	std::vector<EventLabel> labels;
	EventLabel* currentLab = &lab;

    while (n > 0) {
        labels.push_back(*currentLab);
        auto prevLab = g.getPreviousLabel(currentLab);

		// Prevoius label is a null pointer, there are no previous events
		// Return a null pointer as there are less than n events left
		if (prevLab) return {};

		currentLab = prevLab;
        --n;
    }

	std::reverse(labels.begin(), labels.end());
    return labels;
}

void VOCalculator::calcTransC(ExecutionGraph::RelationId relationId) {
	auto &g = getGraph();
	auto &relation = g.getGlobalRelation(relationId);

	for (auto event : relation.getElems()) {
		auto lab = g.getEventLabel(event);
		auto labels = calcTransC(lab, relationId);

		for (auto &finalLabel : labels) {
			relation.addEdge(lab->getPos(), finalLabel->getPos());
		}
	}
}

std::vector<std::unique_ptr<EventLabel>> VOCalculator::calcTransC(const EventLabel *lab, ExecutionGraph::RelationId relationId) {
	auto &g = getGraph();
	std::vector<std::unique_ptr<EventLabel>> labels;
	
	auto adj = getAdj(lab->getPos(), relationId);

	// This label in the graph does not have any outgoing edges
	if (adj.size() == 0) {
		return labels;
	}

	// Perform depth first serch, accumulate visited nodes in a vector
	for (auto adjEvent : getAdj(lab->getPos(), relationId)) {
		auto adjLab = g.getEventLabel(*adjEvent);
		labels.push_back(adjLab->clone());

		if (adjLab == lab) return labels;

		auto labTrans = calcTransC(adjLab, relationId);
		std::move(labTrans.begin(), labTrans.end(), std::back_inserter(labels));
	}

	return labels;
}

void VOCalculator::tryAddEdge(Event a, Event b, Calculator::GlobalRelation *relation) {
	bool resA = tryAddNode(a, relation);
	bool resB = tryAddNode(b, relation);
	relation->addEdge(a, b);
}

/**
 * Adds node to a relation only if the node is not already in that relation.
 * 
 * Returns true if node was added, false if that node already exists in the relation.
 * Node is added by creating a new relation, will all edges and nodes from the old
 * relation and including the new node. This is to work around the broken addEdge()
 * funciont in AdjList().
 */
bool VOCalculator::tryAddNode(Event event, Calculator::GlobalRelation *relation) {
	for (const auto elem : relation->getElems()) {
		// Node already exists
		if (event == elem) return false;
	}

	// Create new relation with the same nodes plus the new one
	auto newElems = relation->getElems();
	newElems.push_back(event);
	Calculator::GlobalRelation newRelation(newElems);

	// Add all edges from old relation to new
	for (const auto& elem : relation->getElems()) {
    	for (auto adjIdx = relation->adj_begin(elem); adjIdx != relation->adj_end(elem); ++adjIdx) {
        	const auto& adjElem = relation->getElems()[*adjIdx];
        	newRelation.addEdge(elem, adjElem);
    	}
	}

	*relation = newRelation;
	return true;
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