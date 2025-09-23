#include "JAM21GraphCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"
#include <map>
#include <deque>

void JAM21GraphCalculator::initCalc()
{
	// Relations are calculated from scratch everytime doCalc()
	// is called, nothing to do on init
	return;
}

void JAM21GraphCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
}

Calculator::CalculationResult JAM21GraphCalculator::doCalc() {

	auto &g = getGraph();

	std::vector<Event> allLabels;
	for (auto lab : labels(getGraph())) {
		allLabels.push_back(lab->getPos());
	}
	Calculator::GlobalRelation newVo(allLabels);
	vo = newVo;

	calcClocks();
	auto lins = calculateLinearisations();

	for (auto lin : lins) {
		auto copyVo = vo;

		if (lin.size() > 1) {
			for (int i = 0; i < lin.size() - 1; i ++) {
				copyVo.addEdge(lin[i]->getPos(), pushtoSynchpoints[lin[i + 1]]->getPos());
			}
		}
		
		copyVo.transClosure();
		auto voPerLoc = getVoPerLoc(copyVo);

		bool consistent = true;

		for (auto pair : voPerLoc) {
			pair.second.transClosure();
			if (!isConsistent(pair.second)) {
				consistent = false;
				break;
			}
		}

		if (consistent) {
			return CalculationResult(false, true);
		}
	}

	return Calculator::CalculationResult(false, false);
}

void JAM21GraphCalculator::calcClocks(ExecutionGraph::Thread &thread, EventLabel* halt) {
	auto &g = getGraph();

	std::unordered_map<SAddr, EventLabel*> lastAccessPerLoc;
	EventLabel* lastSc = g.getEventLabel(Event::getInitializer());

	for (auto &lab : thread) {
		auto threadStartLab = dynamic_cast<ThreadStartLabel*>(lab.get());
		if (threadStartLab) {
			vo.addEdge(threadStartLab->getParentCreate(), threadStartLab->getPos());
		}

		if (dynamic_cast<ThreadStartLabel*>(lab.get())) {
			vo.addEdge(lab.get()->getPos(), g.getNextLabel(lab.get())->getPos());
		}

		if (lab.get()->getIndex() == 0) continue;

		EventLabel* prevLab = g.getPreviousLabel(lab.get());

		if (lab.get()->isAtLeastAcquire() || lab.get()->isAtLeastRelease()) {
			vo.addEdge(prevLab->getPos(), lab.get()->getPos());

			for (auto pair : lastAccessPerLoc) {
				vo.addEdge(pair.second->getPos(), lab.get()->getPos());
			}
			lastAccessPerLoc.clear();

			if (lab.get()->getOrdering() == llvm::AtomicOrdering::SequentiallyConsistent) {
				if (isFence(lab.get())) {
					pushtoSynchpoints[lab.get()] = lab.get();
					domainSpushVolint.push_back(lab.get());
				} else {
					pushtoSynchpoints[lastSc] = lab.get();
					domainSpushVolint.push_back(lastSc);
				}
				lastSc = lab.get();
			}
		}
		
		auto memLab = dynamic_cast<MemAccessLabel*>(lab.get());
		if (memLab && memLab->getOrdering() == llvm::AtomicOrdering::Monotonic) {
			SAddr addr = memLab->getAddr();
			if (lastAccessPerLoc.find(addr) != lastAccessPerLoc.end()) {
				vo.addEdge(lastAccessPerLoc[addr]->getPos(), memLab->getPos());
			} else {
				vo.addEdge(lastSc->getPos(), memLab->getPos());
			}
			lastAccessPerLoc[addr] = memLab;
		}

		auto readLab = dynamic_cast<ReadLabel*>(lab.get());
		if (readLab) {
			auto rf = readLab->getRf();
			if (!rf.isInitializer()) {
				vo.addEdge(rf, lab.get()->getPos());
			}
		}
	}
}

std::vector<std::vector<EventLabel*>> JAM21GraphCalculator::calculateLinearisations() {
	std::vector<std::vector<EventLabel*>> res;

	std::vector<Event> domain;
	for (auto pair : pushtoSynchpoints) {
		domain.push_back(pair.first->getPos());
	}
	Calculator::GlobalRelation dom(domain);

	dom.allTopoSort([this, &res](auto& sort) {
		auto &g = getGraph();

		for (int i = 0; i < sort.size(); i++) {
			auto lab = g.getEventLabel(sort[i]);

			for (int j = i + 1; j < sort.size(); j ++) {
				auto nextLab = g.getEventLabel(sort[j]);

				bool concurent = !(lab->getPorfView() <= nextLab->getPorfView())
							&& !(nextLab->getPorfView() <= lab->getPorfView());
				if (concurent) continue;

				if (nextLab->getPorfView() <= lab->getPorfView()) {
					return false;
				}
			}
		}

		std::vector<EventLabel*> newSort;
		for (auto e : sort) {
			newSort.push_back(g.getEventLabel(e));
		}
		res.push_back(newSort);

		return false; // Allways return false to keep finding all possible topological orderings
    });

	return res;
}

std::unordered_map<EventLabel*, View> JAM21GraphCalculator::applyLinearisation(std::vector<EventLabel*> lin) {
	auto linVoClocks = voClocks;
	
	for (auto it = lin.begin() + 1; it != lin.end(); ++it) {
		EventLabel* prevLab = *(it - 1);
		EventLabel* linLab = *it;

		auto synchClock = linVoClocks[prevLab];
		synchClock[prevLab->getThread()] ++;
		auto synchPoint = pushtoSynchpoints[linLab];

		// Update all clocks in VO with synchPoint
		for (auto labAndClock : linVoClocks) {
			if (isViewGreater(labAndClock.second, linVoClocks[synchPoint])) {
				linVoClocks[labAndClock.first] = labAndClock.second.update(synchClock);
			}
		}

		// Update the synch point clock
		linVoClocks[synchPoint].update(synchClock);
	}

	return linVoClocks;
}

std::unordered_map<SAddr, Calculator::GlobalRelation> JAM21GraphCalculator::getVoPerLoc(GlobalRelation vo) {
	std::unordered_map<SAddr, GlobalRelation> voPerLoc;
	auto &g = getGraph();

	std::vector<Event> allLabels;
	for (auto lab : labels(getGraph())) {
		allLabels.push_back(lab->getPos());
	}
	Calculator::GlobalRelation newVo(allLabels);

	for (auto a : vo.getElems()) {
		for (auto b : vo.getElems()) {
			if (vo(a, b)) {
				auto memA = dynamic_cast<MemAccessLabel*>(g.getEventLabel(a));
				auto memB = dynamic_cast<MemAccessLabel*>(g.getEventLabel(b));
				if (memA && memB && memA->getAddr() == memB->getAddr()) {
					if (voPerLoc.find(memA->getAddr()) == voPerLoc.end()) {
						Calculator::GlobalRelation newRel(allLabels);
						voPerLoc[memA->getAddr()] = newRel;
					}
					voPerLoc[memA->getAddr()].addEdge(a, b);
				}
			}
		}
	}

	return voPerLoc;
}

bool JAM21GraphCalculator::isConsistent(GlobalRelation vo) {
	auto &g = getGraph();

	for (auto a : vo.getElems()) {
		for (auto b : vo.getElems()) {
			if (!vo(a, b)) continue;
			if (a.isInitializer() || b.isInitializer()) continue;

			auto readLab = g.getReadLabel(b);
			if (readLab && readLab->getRf() != a) {
				vo.addEdge(a, readLab->getRf());
			}
		}
	}

	vo.transClosure();
	return vo.isIrreflexive();
}

bool JAM21GraphCalculator::isFence(EventLabel *lab) {
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

/**
 * a > b
 * 
 * If no component of a is smaller than corresponding
 * component of b, and at least one component of a is larger
 * than the corresponding component of b, true is returned.
 */
bool JAM21GraphCalculator::isViewGreater(View a, View b) {
	int size = std::max(a.size(), b.size());
	bool greaterFound = false;

	for (int i = 0; i < size; i ++) {
        if (a[i] < b[i]) {
			return false; // a is smaller at this index
		} else if (a[i] > b[i]) {
			greaterFound = true;
		}
    }

    return greaterFound;
}

/**
 * a < b
 * 
 * If no component of a is greater than corresponding
 * component of b, and at least one component of a is smaller
 * than the corresponding component of b, true is returned.
 */
bool JAM21GraphCalculator::isViewSmaller(View a, View b) {
	int size = std::max(a.size(), b.size());
	bool smallerFound = false;

	for (int i = 0; i < size; i ++) {
        if (a[i] > b[i]) {
			return false; // a is greater at this index
		} else if (a[i] < b[i]) {
			smallerFound = true;
		}
    }

    return smallerFound;
}