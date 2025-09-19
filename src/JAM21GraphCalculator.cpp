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

	return Calculator::CalculationResult(false, false);
}

void JAM21GraphCalculator::calcClocks(ExecutionGraph::Thread &thread, EventLabel* halt) {
	auto &g = getGraph();

	std::unordered_map<SAddr, EventLabel*> lastAccessPerLoc;
	EventLabel* lastSc = g.getEventLabel(Event::getInitializer());

	for (auto &lab : thread) {
		if (lab.get()->getIndex() == 0) continue;
		if (lab == thread.back()) break;

		EventLabel* prevLab = g.getPreviousLabel(lab.get());

		if (lab.get()->isAtLeastAcquire() || lab.get()->isAtLeastRelease()) {
			vo.addEdge(prevLab->getPos(), lab.get()->getPos());
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
	}

	llvm::outs() << vo;
}

void JAM21GraphCalculator::addToLinearisations(EventLabel* lab, EventLabel* synchLab) {
	pushtoSynchpoints[lab] = synchLab;

	// If there are no linearisations, trivially create the single one
	if (linearisations.empty()) {
		std::vector<EventLabel*> lin;
		linearisations.push_back(lin);
	}

	std::vector<std::vector<EventLabel*>> newLinearisations;
	while (!linearisations.empty()) {
		std::vector<EventLabel*> lin = std::move(linearisations.back());
		linearisations.pop_back();
	
		EventLabel* prevLab = nullptr;
		for (size_t i = 0; i <= lin.size(); ++i) {
    		std::vector<EventLabel*> newLin;

    		// Add all events before the insertion point
			bool valid = true;
    		for (size_t j = 0; j < i; ++j) {
				if (isViewGreater(lin[j]->getPorfView(), lab->getPorfView())) {
					valid = false;
					break;
				}
        		newLin.push_back(lin[j]);
    		}

			if (!valid) continue;

    		// Insert the new event at position i
    		newLin.push_back(lab);

    		// Add all remaining events from position i onwards
    		for (size_t j = i; j < lin.size(); ++j) {
				if (isViewSmaller(lin[j]->getPorfView(), lab->getPorfView())) {
					valid = false;
					break;
				}
        		newLin.push_back(lin[j]);
    		}

			if (!valid) continue;

    		newLinearisations.push_back(newLin);
		}
	}
	linearisations = newLinearisations;
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

std::unordered_map<SAddr, std::vector<EventLabel*>> JAM21GraphCalculator::getAccessesPerLoc(std::unordered_map<EventLabel*, View> linVoClocks) {
	std::unordered_map<SAddr, std::vector<EventLabel*>> accessesPerLoc;

	for (auto labAndView : linVoClocks) {
		auto memLab = dynamic_cast<MemAccessLabel*>(labAndView.first);
		if (memLab) {
            accessesPerLoc[memLab->getAddr()].push_back(memLab);
		}
	}

	return accessesPerLoc;
}

bool JAM21GraphCalculator::isConsistent(
	std::vector<EventLabel*> memAccesses,
	std::unordered_map<EventLabel*, View> linVoClocks)
{
	auto &g = getGraph();

	for (size_t i = 0; i < memAccesses.size(); ++i) {
        EventLabel* labA = memAccesses[i];
		auto writeLabA = dynamic_cast<WriteLabel*>(labA);
		if (!writeLabA) continue;
        const View& viewA = linVoClocks[labA];

        for (size_t j = 0; j < memAccesses.size(); ++j) {
            if (i == j) continue;

            EventLabel* labB = memAccesses[j];
            const View& viewB = linVoClocks[labB];

            if (isViewSmaller(viewA, viewB)) {

				auto readLabB = dynamic_cast<ReadLabel*> (labB);
				if (readLabB) {
					auto rfWrite = readLabB->getRf();
					auto rfLab = g.getEventLabel(rfWrite);

					if (isViewSmaller(linVoClocks[rfLab], linVoClocks[labA])) {
						return false;
					}
				}
            }
        }
    }

	return true;
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