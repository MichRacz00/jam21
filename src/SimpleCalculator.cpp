#include "SimpleCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"
#include <map>
#include <deque>

void SimpleCalculator::initCalc()
{
	// Relations are calculated from scratch everytime doCalc()
	// is called, nothing to do on init
	return;
}

void SimpleCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
}

Calculator::CalculationResult SimpleCalculator::doCalc() {

	calcClocks();

	if (linearisations.size() > 0) {
		for (auto l : linearisations) {
			// TODO: remove
			llvm::outs() << "linearisation: ";
			for (auto lab : l) {
				llvm::outs() << lab->getPos();
			}
			llvm::outs() << "\n";


			auto linVoClocks = applyLinearisation(l);
			auto accessesPerLoc = getAccessesPerLoc(linVoClocks);

			auto consistent = true;
			for (auto addrAndAccesses : accessesPerLoc) {
				// TODO: remove
				//llvm::outs() << addrAndAccesses.first << "\n";
				consistent = isConsistent(addrAndAccesses.second, linVoClocks);
				if (!consistent) break;
			}

			if (consistent) return Calculator::CalculationResult(false, true);

			// TODO: remove
			for (auto labAndClock : linVoClocks) {
				llvm::outs() << labAndClock.first->getPos() << " " << labAndClock.second << "\n";
			}
		}
	} else {
		auto accessesPerLoc = getAccessesPerLoc(voClocks);
		for (auto addrAndAccesses : accessesPerLoc) {
			// TODO: remove
			//llvm::outs() << addrAndAccesses.first << "\n";
			auto consistent = isConsistent(addrAndAccesses.second, voClocks);
			if (consistent) return Calculator::CalculationResult(false, true);
		}
	}

	

	voClocks.clear();
	pushtoSynchpoints.clear();
	linearisations.clear();

	return Calculator::CalculationResult(false, false);
}

void SimpleCalculator::calcClocks(ExecutionGraph::Thread &thread, EventLabel* halt) {
	auto &g = getGraph();

	// Setting up initial vector clock
	auto const firstEvent = thread.front().get();
	auto const tid = firstEvent->getThread();
	auto firstLab = dynamic_cast<ThreadStartLabel*>(firstEvent);
	auto threadCreateEvent = g.getEventLabel(firstLab->getParentCreate());
	auto threadCreateClock = voClocks[threadCreateEvent];

	// Setting up last views
	auto currentVoView = View(threadCreateClock);
	View lastCommonView = currentVoView;
	std::unordered_map<SAddr, View> lastPerLocView;
	
	bool advanceNext = false;
	EventLabel* prevVolint = nullptr;

	for (auto &lab : thread) {
		// VC already calculated for this event, skip
		if (!voClocks[lab.get()].empty()) {
			if (lab.get()->getOrdering() == llvm::AtomicOrdering::SequentiallyConsistent
				&& !isFence(lab.get())) {
				// maintain knowledge of previous SC access even without calculating VCs
				prevVolint = lab.get();
			}
			continue;
		}

		// If previous iteration requested VC advancment of the next VC
		bool advanceNow = false;
		if (advanceNext == true) {
			advanceNext = false;
			advanceNow = true;
		}

		// isRelaxed is true if lab is a relaxed memory access
		auto memLab = dynamic_cast<MemAccessLabel*>(lab.get());
		bool isRelaxed =
			memLab && (
				lab.get()->getOrdering() == llvm::AtomicOrdering::Monotonic ||
				lab.get()->getOrdering() == llvm::AtomicOrdering::NotAtomic
			);
		
		if (isRelaxed) {
			auto addr = memLab->getAddr();
			auto it = lastPerLocView.find(addr);

			if (it == lastPerLocView.end()) {
				// memory location was not yet accessed since last synchronization
				currentVoView = lastCommonView;
			} else {
				// there was already an access to this memory location
				currentVoView = lastPerLocView[addr];
			}

			advanceNow = true;
		}

		// Merge VC of the incoming RF edge
		auto readLab = dynamic_cast<ReadLabel*>(lab.get());
		if (readLab) {
			auto writeLab = g.getEventLabel(readLab->getRf());
			// The VC for RF write not yet calculated, calculate it now
			if (voClocks[writeLab].empty()) {
				calcClocks(g.getThreadList()[writeLab->getThread()], writeLab);
			}
			currentVoView.update(voClocks[writeLab]);
			currentVoView[writeLab->getThread()] ++;
		}

		// ra and svo
		if (lab.get()->getOrdering() == llvm::AtomicOrdering::Release
			|| lab.get()->getOrdering() == llvm::AtomicOrdering::Acquire
			|| lab.get()->getOrdering() == llvm::AtomicOrdering::AcquireRelease)
		{
			advanceNow = true;
			advanceNext = true;
		}

		// Collect synchpoints for pushto relation, add event to linearisations
		if (lab.get()->getOrdering() == llvm::AtomicOrdering::SequentiallyConsistent) {
			if (prevVolint != nullptr) {
				addToLinearisations(prevVolint, lab.get());
			}

			prevVolint = lab.get();

			if(isFence(lab.get())) {
				addToLinearisations(lab.get(), lab.get());
				prevVolint = nullptr;
			}

			advanceNow = true;
			advanceNext = true;
		}
		
		if (advanceNow == true) currentVoView[tid] ++;
		voClocks[lab.get()] = currentVoView;

		if (isRelaxed) {
			// Relaxed memory access, store vo view per location
			lastPerLocView[memLab->getAddr()] = currentVoView;
		} else {
			// Synchronization, merge all relaxed per loc vo views
			for (auto pair : lastPerLocView) {
				currentVoView.update(pair.second);
			}
			lastCommonView = currentVoView;
			lastPerLocView.clear();
		}

		if (lab.get() == halt) return;
	}
}

void SimpleCalculator::addToLinearisations(EventLabel* lab, EventLabel* synchLab) {
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

std::unordered_map<EventLabel*, View> SimpleCalculator::applyLinearisation(std::vector<EventLabel*> lin) {
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

std::unordered_map<SAddr, std::vector<EventLabel*>> SimpleCalculator::getAccessesPerLoc(std::unordered_map<EventLabel*, View> linVoClocks) {
	std::unordered_map<SAddr, std::vector<EventLabel*>> accessesPerLoc;

	for (auto labAndView : linVoClocks) {
		auto memLab = dynamic_cast<MemAccessLabel*>(labAndView.first);
		if (memLab) {
            accessesPerLoc[memLab->getAddr()].push_back(memLab);
		}
	}

	return accessesPerLoc;
}

bool SimpleCalculator::isConsistent(
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

            if (isViewGreater(viewB, viewA)) {
				// TODO remove
                //llvm::outs() << labA->getPos() << " -vo-> " << labB->getPos() << "\n";

				auto readLabB = dynamic_cast<ReadLabel*> (labB);

				if (readLabB) {
					auto rfWrite = readLabB->getRf();
					//if (rfWrite.isInitializer()) continue;
					auto rfLab = g.getEventLabel(rfWrite);
					if (isViewSmaller(linVoClocks[rfLab], linVoClocks[labA])) {
						// TODO remove;
						llvm::outs() << "Inconsistent cojom edge: " << rfWrite << " -> " << labB->getPos() << "\n";
						return false;
					}

					llvm::outs() << labA->getPos() << " -> " << rfWrite << "\n";
				}
            }
        }
    }

	return true;
}

bool SimpleCalculator::isFence(EventLabel *lab) {
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
bool SimpleCalculator::isViewGreater(View a, View b) {
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
bool SimpleCalculator::isViewSmaller(View a, View b) {
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