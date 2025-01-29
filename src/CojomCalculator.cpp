#include "CojomCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"

void CojomCalculator::initCalc()
{
	// Relations are calculated from scratch everytime doCalc()
	// is called, nothing to do on init
	return;
}

Calculator::CalculationResult CojomCalculator::doCalc()
{
	bool isAcyclic = isCojomAcyclic();
	return Calculator::CalculationResult(false, isAcyclic);
}

void CojomCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
}

bool CojomCalculator::isCojomAcyclic() {
	auto rf = calcRfRelation();
	auto ra = calcRaRelation();
	auto svo = calcSvoRelation();

	auto spush = calcSpushRelation();
	auto volint = calcVolintRelation();
	auto push = merge({spush, volint});

	// Intra-thread order
	auto intra = merge({rf, ra, svo, push});

	// Calculate acyclicity for each linearisation of push
	auto pushtos = calcAllLinearisations(push);
	for (auto pushto : pushtos) {
		// Calculate VVO relation
		auto pushtoCompPush = calcComp(pushto, push);
		auto vvo = merge({intra, pushtoCompPush});

		// Calculate VO and cojom relations
		calcTransC(&vvo);
		auto vo = merge({vvo, calcPolocRelation()});
		auto cojom = calcCojom(vo);

		// Calculate acyclicity of cojom by taking transitive closure
		// and checking for irreflexivity
		calcTransC(&cojom);
		if (!cojom.isIrreflexive()) {
			// A cycle has been found
			return false;
		}
	}

	// No cycles in all possible linearisations
	return true;
}

/**
 * Calculates RA relation for the entire graph
 */
Calculator::GlobalRelation CojomCalculator::calcRaRelation() {
	auto &g = getGraph();
	Calculator::GlobalRelation ra;

	for (EventLabel* lab : labels(g)) {
		auto events = getPrevMany(*lab, 3);
		if (events.empty()) {
			// There do not exist 2 previous events to this label
			continue;
		}

		// The event in the middle must be rel/acq or stronger
		if (!(events[1]->isAtLeastAcquire() || events[1]->isAtLeastRelease())) continue;
		tryAddEdge(events[0]->getPos(), events[2]->getPos(), &ra);
	}

	return ra;
}

/**
 * Calculates SVO relation for the entire graph
 */
Calculator::GlobalRelation CojomCalculator::calcSvoRelation() {
	auto &g = getGraph();
	Calculator::GlobalRelation svo;

	for (EventLabel* lab : labels(g)) {
		auto events = getPrevMany(*lab, 5);
		if (events.empty()) continue;

		// The second event must be a release fence
		if (!(events[1]->getOrdering() == llvm::AtomicOrdering::Release && isFence(events[1].get()))) continue;

		// The third event must be either a read or a write
		auto thirdRead = dynamic_cast<ReadLabel*>(events[2].get());
		auto thirdWrite = dynamic_cast<WriteLabel*>(events[2].get());
		if (!thirdRead && !thirdWrite) continue;

		// The fourth event must be an acquire fence
		if (!(events[3]->getOrdering() == llvm::AtomicOrdering::Acquire && isFence(events[3].get()))) continue;

		tryAddEdge(events[0]->getPos(), events[4]->getPos(), &svo);
	}

	return svo;
}

/**
 * Calculates SPUSH relation for the entire graph
 */
Calculator::GlobalRelation CojomCalculator::calcSpushRelation() {
	auto &g = getGraph();
	Calculator::GlobalRelation spush;

	for (EventLabel* lab : labels(g)) {
		auto events = getPrevMany(*lab, 3);
		if (events.empty()) continue;

		// The event in the middle must be a SC fence
		if (!(isFence(events[1].get()) && events[1]->isSC())) continue;

		tryAddEdge(events[0]->getPos(), events[2]->getPos(), &spush);
	}

	

	return spush;
}

/**
 * Calculates volint relation for the entire graph
 */
Calculator::GlobalRelation CojomCalculator::calcVolintRelation() {
	auto &g = getGraph();
	Calculator::GlobalRelation volint;

	for (EventLabel* lab : labels(g)) {
		auto events = getPrevMany(*lab, 2);
		if (events.empty()) continue;

		// Initial and final events must both be SC
		if (!(events[0]->isSC() && events[1]->isSC())) continue;

		tryAddEdge(events[0]->getPos(), events[1]->getPos(), &volint);
	}

	return volint;
}

/**
 * Calculates POLOC relation for the entire graph.
 * POLOC is PO between events accessing the same location.
 */
Calculator::GlobalRelation CojomCalculator::calcPolocRelation() {
	auto &g = getGraph();
	Calculator::GlobalRelation poloc;

	for (auto eventLabel : labels(g)) {
		// Initial label must be a memory access label
		// i.e. it must be accessing some addres
		auto initialMemoryLabel = dynamic_cast<MemAccessLabel *>(eventLabel);
		if (!initialMemoryLabel) continue;

		// Iterate over next labels untill a label
		// accessing the same address is found
		bool finalLabelFound = false;
		auto nextLabel = eventLabel;
		while (!finalLabelFound) {
			nextLabel = g.getNextLabel(nextLabel);

			// Reached the end of the thread, terminate
			if (!nextLabel) break;

			// Final label must be a memory access label
			auto nextMemoryLabel = dynamic_cast<MemAccessLabel *>(nextLabel);
			if (!nextMemoryLabel) continue;
			
			// Initial and next labels access the same address, final label found
			if (initialMemoryLabel->getAddr() == nextMemoryLabel->getAddr()) {
				finalLabelFound = true;
				break;
			}
		}

		// Add edge only if appropriate final label was found
		if (finalLabelFound) {
			tryAddEdge(initialMemoryLabel->getPos(), nextLabel->getPos(), &poloc);
		}
	}

	return poloc;
}

/**
 * Returns a relation with no edges that only contains events
 * from the domain of the given relation.
 */
Calculator::GlobalRelation CojomCalculator::domain(Calculator::GlobalRelation rel) {
	Calculator::GlobalRelation domain;

	for (auto elem : rel) {
		if (getAdj(elem, rel).size() > 0) {
			tryAddNode(elem, &domain);
		}
	}

	return domain;
}

/**
 * Calculates all possible linearisations (trace orders)
 * in the domain of a given relation.
 * 
 * Total order must not violate po U rf.
 */
std::vector<Calculator::GlobalRelation> CojomCalculator::calcAllLinearisations(GlobalRelation rel) {
	std::vector<GlobalRelation> pushtos;
	const auto dom = domain(rel);

	dom.allTopoSort([this, &pushtos](auto& sort) {
		auto &g = getGraph();

		// Iterate over all events in an ordering to check
		// if they adhere to porf view
		for (int i = 0; i < sort.size(); i++) {
			auto lab = g.getEventLabel(sort[i]);

			for (int j = i + 1; j < sort.size(); j ++) {
				auto nextLab = g.getEventLabel(sort[j]);

				// If two events are concurrent, the ordering in the linearisation
				// between those two events can be arbitrary
				bool concurent = !(lab->getPorfView() <= nextLab->getPorfView())
							&& !(nextLab->getPorfView() <= lab->getPorfView());
				if (concurent) continue;

				// If the next event has vector clock lower than the current event,
				// those events have not been ordered consecutively in the po U rf view.
				// This linearisation must be rejected
				if (nextLab->getPorfView() <= lab->getPorfView()) {
					return false;
				}
			}
		}

		/**
	 	* Create relation object, add total order edges
	 	* reflecting event order from the topo sort vecotr, ex:
	 	* 
	 	* topologicalSort [A, B, C]
	 	* relation: (A) -> (B), (B) -> (C)
	 	*/
		Calculator::GlobalRelation pushto(sort);
		for (int i = 1; i < sort.size(); i ++) {
			const auto elemA = pushto.getElems()[i - 1];
			const auto elemB = pushto.getElems()[i];
			tryAddEdge(elemA, elemB, &pushto);
		}

		pushtos.push_back(pushto);

		// Allways return false to keep finding all possible topological sorts
		return false;
    });

	return pushtos;
}

/**
 * Returns the union of all rf edges in the graph
 */
Calculator::GlobalRelation CojomCalculator::calcRfRelation() {
	auto &g = getGraph();
	Calculator::GlobalRelation rf;

	for (auto *lab : labels(g)) {
		if (auto readLabel = dynamic_cast<ReadLabel*>(lab)) {
			auto writeLabel = readLabel->getRf();
			tryAddEdge(writeLabel, readLabel->getPos(), &rf);
		}
	}

	return rf;
}

/**
 * Given VO calculates cojom relation
 */
Calculator::GlobalRelation CojomCalculator::calcCojom(Calculator::GlobalRelation vo) {
	Calculator::GlobalRelation cojom = merge({calcCoww(vo), calcCowr(vo), calcCorw(vo), calcCorr()});
	return cojom;
}

/**
 * Calculation of WWco(vo)
 */
Calculator::GlobalRelation CojomCalculator::calcCoww(GlobalRelation vo) {
	auto &g = getGraph();
	Calculator::GlobalRelation coww;

	for (auto elem : vo.getElems()) {
		// First label must be a write
		auto intialLab = g.getWriteLabel(elem);
		if (!intialLab) continue;

		for (auto finalElem : getAdj(elem, vo)) {
			// Final label must be a write
			auto finalLab = g.getWriteLabel(finalElem);
			if (!finalLab) continue;

			// If writes to the same location and are not an identity
			if (intialLab->getAddr() == finalLab->getAddr()
				&& intialLab != finalLab) {
					tryAddEdge(elem, finalElem, &coww);
				}
		}
	}

	return coww;
}

/**
 * Calculation fo WWco(vo; rf^-1)
 */
Calculator::GlobalRelation CojomCalculator::calcCowr(GlobalRelation vo) {
	auto &g = getGraph();
	Calculator::GlobalRelation cowr;

	for (auto elem : vo.getElems()) {
		// First label must be a write
		auto initialLab = g.getWriteLabel(elem);
		if (!initialLab) continue;

		for (auto finalElem : getAdj(elem, vo)) {
			// Final label of VO must be a read to create RF^-1
			auto middleReadLab = g.getReadLabel(finalElem);
			if (!middleReadLab) continue;

			// Get write associated by RF
			auto finalWriteElem = middleReadLab->getRf();
			auto finalWriteLab = g.getWriteLabel(finalWriteElem);
			if (!finalWriteLab) {
				// Should never be triggered becaouse read must
				// allways have a corresponding write
				// Better than segfault
				continue;
			}

			// If writes to the same location and are not an identity
			if (initialLab->getAddr() == finalWriteLab->getAddr()
				&& elem != finalWriteElem) {
					tryAddEdge(elem, finalWriteElem, &cowr);
				}
		}
	}

	return cowr;
}

/**
 * Calculation of WWco(vo; po)
 */
Calculator::GlobalRelation CojomCalculator::calcCorw(GlobalRelation vo) {
	auto &g = getGraph();
	Calculator::GlobalRelation corw;

	for (auto elem : vo.getElems()) {
		// First label must be a write
		auto initialLab = g.getWriteLabel(elem);
		if (!initialLab) continue;

		for (auto finalElem : getAdj(elem, vo)) {
			// Get next label in PO
			auto middleLab = g.getEventLabel(finalElem);
			if (!middleLab) continue;
			auto finalLab = g.getNextLabel(middleLab);
			if (!finalLab) continue;

			// Must be a write label
			auto finalWriteLab = dynamic_cast<WriteLabel*>(finalLab);
			if (!finalWriteLab) continue;

			// If writes to the same location and are not an identity
			if (initialLab->getAddr() == finalWriteLab->getAddr()
				&& initialLab != finalWriteLab) {
					tryAddEdge(elem, finalLab->getPos(), &corw);
			}
		}
	}

	return corw;
}

/**
 * Calculation of WWco(rf; po; rf^-1)
 */
Calculator::GlobalRelation CojomCalculator::calcCorr() {
	auto &g = getGraph();
	Calculator::GlobalRelation corr;

	for (auto lab : labels(g)) {
		// First labels must be a write that is opaque, rel/acq or volotile
		auto initWriteLab = dynamic_cast<WriteLabel*>(lab);
		if (!initWriteLab) continue;
		if (initWriteLab->isNotAtomic()) continue;

		// Iterate over all reads that read from the inital write
		for (auto initReadElem : initWriteLab->getReadersList()) {
			// Fina all next read labels in PO
			auto initReadLab = dynamic_cast<ReadLabel*>(g.getNextLabel(initReadElem));
			if (!initReadLab) continue;

			// Get next event in PO that is a read to create RF^-1 edge
			auto finalReadElem = g.getNextLabel(initReadElem);
			if (!finalReadElem) continue;
			auto finalReadLab = dynamic_cast<ReadLabel*>(finalReadElem);
			if (!finalReadLab) continue;

			// Get write where RF points from
			auto finalWriteEvent = finalReadLab->getRf();
			auto finalWriteLab = g.getWriteLabel(finalWriteEvent);
			if (!finalWriteLab) {
				// Should never trigger
				continue;
			}

			// Final write must be opaque, rel/acq or volotile
			if (finalWriteLab->isNotAtomic()) continue;

			// Only add to relation if both writes access the same location
			// and are not the same write
			if (initWriteLab->getAddr() == finalWriteLab->getAddr()
				&& initWriteLab != finalWriteLab) {
					tryAddEdge(lab->getPos(), finalWriteEvent, &corr);
				}
		}
	}

	return corr;
}

/**
 * Returns a union of all given relations.
 */
Calculator::GlobalRelation CojomCalculator::merge(std::vector<Calculator::GlobalRelation> relations) {
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

/**
 * Given two relations, computes their composition relA; relB
 */
Calculator::GlobalRelation CojomCalculator::calcComp(Calculator::GlobalRelation relA, Calculator::GlobalRelation relB) {
	Calculator::GlobalRelation compo;
	const auto elemsB = relB.getElems();

	for (auto eventInit : relA) {
		for (auto eventTrans : getAdj(eventInit, relA)) {

			// Check if intermediate event (final in A, initial in B)
			// exists in B. If not, skip this event
			bool transExist = false;
			for (const auto elemB : elemsB) {
				if (eventTrans == elemB) {
					transExist = true;
					break;
				}
			}

			if (!transExist) continue;

			for (auto eventFinal : getAdj(eventTrans, relB)) {
				tryAddEdge(eventInit, eventFinal, &compo);
			}
		}
	}
	return compo;
}

/**
 * Retrieves all events in the relation that are directly reachable
 * from the specified event (i.e., all events where an edge from 
 * the given event terminates).
 */
std::vector<Event> CojomCalculator::getAdj(Event event, Calculator::GlobalRelation relation) {
	std::vector<Event> adjEvents;
	for (auto adjIdx = relation.adj_begin(event); adjIdx != relation.adj_end(event); ++adjIdx) {
        const auto& adjElem = relation.getElems()[*adjIdx];
    	adjEvents.push_back(adjElem);
    }
	return adjEvents;
}

/**
 * Retrieves n previous event labels starting from and including the given event
 * and returns them in a vector. The initial event is in the front of the vector,
 * followed by n-1 previous events. If there are less than n prev events,
 * an empty vector is returned.
 */
std::vector<std::unique_ptr<EventLabel>> CojomCalculator::getPrevMany(EventLabel &lab, int n) {
	auto &g = getGraph();
	std::vector<std::unique_ptr<EventLabel>> labels;
	EventLabel* currentLab = &lab;
 
    while (n > 0) {
        labels.push_back(currentLab->clone());
        auto prevLab = g.getPreviousLabel(currentLab);

		// Prevoius label is a null pointer, there are no previous events
		// Return a null pointer as there are less than n events left
		if (!prevLab) return {};

		currentLab = prevLab;
        --n;
    }

	std::reverse(labels.begin(), labels.end());
    return labels;
}

/**
 * Modifies the relation by inlcuding exhaustive transitive closure
 * for all nodes in the graph.
 */
void CojomCalculator::calcTransC(Calculator::GlobalRelation *relation) {
	auto &g = getGraph();

	for (auto event : relation->getElems()) {
		auto lab = g.getEventLabel(event);
		auto labels = calcTransC(lab, relation, relation->size());

		for (auto &finalLabel : labels) {
			tryAddEdge(lab->getPos(), finalLabel->getPos(), relation);
		}
	}
}

std::vector<std::unique_ptr<EventLabel>> CojomCalculator::calcTransC(const EventLabel *lab, Calculator::GlobalRelation *relation, int size) {
	auto &g = getGraph();
	std::vector<std::unique_ptr<EventLabel>> labels;
	
	auto adj = getAdj(lab->getPos(), *relation);

	// This label in the graph does not have any outgoing edges
	// or we have reached the max recursion depth
	if (adj.size() == 0 || size < 0) {
		return labels;
	}

	// Perform depth first serch, accumulate visited nodes in a vector
	for (auto adjEvent : getAdj(lab->getPos(), *relation)) {
		auto adjLab = g.getEventLabel(adjEvent);
		labels.push_back(adjLab->clone());

		if (adjLab == lab) return labels;

		auto labTrans = calcTransC(adjLab, relation, size - 1);
		std::move(labTrans.begin(), labTrans.end(), std::back_inserter(labels));
	}

	return labels;
}

/**
 * Adds an edge from a to b. If either a or b does not exist,
 * adds them to the relation first.
 */
void CojomCalculator::tryAddEdge(Event a, Event b, Calculator::GlobalRelation *relation) {
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
bool CojomCalculator::tryAddNode(Event event, Calculator::GlobalRelation *relation) {
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

bool CojomCalculator::isFence(EventLabel *lab) {
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