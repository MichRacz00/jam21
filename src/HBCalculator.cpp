#include "HBCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"
#include <map>
#include <deque>

void HBCalculator::initCalc()
{
	// Relations are calculated from scratch everytime doCalc()
	// is called, nothing to do on init
	return;
}

Calculator::CalculationResult HBCalculator::doCalc() {
	resetViews();

	std::vector<Event> allLabels;
	for (auto lab : labels(getGraph())) {
		allLabels.push_back(lab->getPos());
	}

	Calculator::GlobalRelation a(allLabels);
	cojom = a;

	calcHB();
	llvm::outs() << getGraph();
	//bool correctFR = calcFR();
	//if (!correctFR) return Calculator::CalculationResult(false, false);
	calcMO();
	calcCORR();

	/*

	for (auto pair : mo) {
		WriteLabel* previous = nullptr;
		for (auto lab : pair.second) {
			if (previous != nullptr) {
				llvm::outs() << "Adding mo edge " << previous->getPos() << " -mo-> " << lab->getPos() << "\n";
				cojom.addEdge(previous->getPos(), lab->getPos());
			}
			previous = lab;
		}
	}

	for (auto pair : corr) {
		EventLabel* previous = nullptr;
		for (auto lab : pair.second) {
			if (previous != nullptr) {
				llvm::outs() << "Adding corr edge " << previous->getPos() << " -mo-> " << lab->getPos() << "\n";
				cojom.addEdge(previous->getPos(), lab->getPos());
			}
			previous = lab;
		}
	}
		*/

	llvm::outs() << cojom;

	cojom.transClosure();

	/*

	for (auto pair : mo) {
		WriteLabel* previous = nullptr;
		for (auto lab : pair.second) {
			if (previous != nullptr) {
				auto consistent = checkMoCoherence(previous, lab);
				llvm::outs() << "Checking mo consistence " << previous->getPos() << " -mo?-> " << lab->getPos() << "\n";
				if (!consistent) {
					llvm::outs() << getGraph();
					llvm::outs() << "Incosnistent! on " << previous->getPos() << lab->getPos() << "\n";
					return Calculator::CalculationResult(false, false);
				}
			}
			previous = lab;
		}
	}*/

	llvm::outs() << getGraph();

	if (!cojom.isIrreflexive()) llvm::outs() << "Inconsistent!\n";

	return Calculator::CalculationResult(false, cojom.isIrreflexive());
}

void HBCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
}

void HBCalculator::calcHB() {
	auto &g = getGraph();

	for (auto &t : g.getThreadList()) {
		calcHB(t, t.back().get());
	}
}

void HBCalculator::calcHB(ExecutionGraph::Thread &thread, EventLabel* halt) {
	auto &g = getGraph();
	std::deque<EventLabel*> previousLabels;
	std::unordered_map<SAddr, View> previousAccess;

	auto firstThreadEvent = thread.front().get();
	auto const tid = firstThreadEvent->getThread();
	auto firstThreadEventLab = dynamic_cast<ThreadStartLabel*>(firstThreadEvent);
	auto threadCreateEvent = g.getEventLabel(firstThreadEventLab->getParentCreate());

	// Copy HB vector clock from event that created this thread
	// Advance HB by one in this thread to indicate the thread
	// has started
	auto prevThreadClock = hbClocks[threadCreateEvent];
	prevThreadClock[tid] += 1;
	auto baseView = View(prevThreadClock);

	llvm::outs() << " --- " << tid << " --- \n";

    for (auto &lab : thread) {
		// Keep track of 4 previous labels
		// add current label for future reference
		previousLabels.push_front(lab.get());
		if (previousLabels.size() > 5) previousLabels.pop_back();

		if (!hbClocks[previousLabels[0]].empty()) {
			// VC is already calculated for this event, skip
			continue;
		}

		if (previousLabels.size() >= 2) {
			// Copy previous VC to this event
			hbClocks[previousLabels[0]] = mergeViews(hbClocks[previousLabels[0]], baseView);
		}

		auto labRead = dynamic_cast<ReadLabel*>(lab.get());
		if (labRead) {
			// Read event, get VC from write
			auto labRf = g.getEventLabel(labRead->getRf());
			auto rfTid = labRf->getThread();

			if (hbClocks[labRf].empty()) {
				// Write VC not yet calculated, calculate it and return
				
				llvm::outs() << " --- to thread " << rfTid << " --- \n";
				calcHB(g.getThreadList()[rfTid], g.getEventLabel(labRead->getRf()));
				llvm::outs() << " --- return --- \n";
			}

			// Merge read and write VCs related by RF
			hbClocks[previousLabels[0]] = mergeViews(hbClocks[previousLabels[0]], hbClocks[labRf]);
			hbClocks[previousLabels[0]][rfTid] += 1;
		}

		// Memory access, advance VC by at least one from last access to this location
		// in this thread (po-loc)
		auto const memAccessLab = dynamic_cast<MemAccessLabel*>(lab.get());
		if (memAccessLab) {
			if (previousAccess.find(memAccessLab->getAddr()) != previousAccess.end()) {
				hbClocks[previousLabels[0]] = mergeViews(hbClocks[previousLabels[0]], previousAccess[memAccessLab->getAddr()]);
				if (hbClocks[previousLabels[0]] <= previousAccess[memAccessLab->getAddr()]) {
					hbClocks[previousLabels[0]][tid] += 1;
				}
			}
			previousAccess[memAccessLab->getAddr()] = hbClocks[previousLabels[0]];
		}

		calcIntraThreadHB(lab.get(), previousLabels);

		llvm::outs() << previousLabels[0]->getPos() << " " << hbClocks[previousLabels[0]] << "\n";
		if (previousLabels[0] == halt) {
			// Reached the last event specified, end calculations
			llvm::outs() << " --- halt --- \n";
			return;
		}
    }
}

void HBCalculator::calcIntraThreadHB(EventLabel* lab, std::deque<EventLabel*> previousLabels) {
	auto tid = lab->getThread();

	if (previousLabels.size() >= 2 && previousLabels[1]->isSC() && previousLabels[0]->isSC()) {
		auto const prevHbClock = hbClocks[previousLabels[1]];
		auto currentHbClock = mergeViews(hbClocks[previousLabels[0]], prevHbClock);
		currentHbClock[tid] += 1;
		hbClocks[previousLabels[0]] = currentHbClock;
	}

	if (previousLabels.size() >= 3 && previousLabels[1]->isSC() && isFence(previousLabels[1])) {
		// Advance by 2 to account for a possibly HB ordered intermediate event
		auto const prevHbClock = hbClocks[previousLabels[2]];
		auto currentHbClock = View(prevHbClock);
		currentHbClock[tid] += 2;
		hbClocks[previousLabels[0]] = currentHbClock;
	}

	if (previousLabels.size() >= 3 && (previousLabels[1]->isAtLeastAcquire() || previousLabels[1]->isAtLeastRelease())) {
		// Advance by 2 to account for a possibly HB ordered intermediate event
		auto const prevHbClock = hbClocks[previousLabels[2]];
		auto currentHbClock = mergeViews(hbClocks[previousLabels[0]], prevHbClock);
		currentHbClock[tid] += 2;
		hbClocks[previousLabels[0]] = currentHbClock;
	}

	if (previousLabels.size() >= 4 &&
		previousLabels[1]->getOrdering() == llvm::AtomicOrdering::Release && isFence(previousLabels[1]) &&
		previousLabels[3]->getOrdering() == llvm::AtomicOrdering::Acquire && isFence(previousLabels[3]) &&
		(dynamic_cast<WriteLabel*>(previousLabels[2]) || dynamic_cast<ReadLabel*>(previousLabels[2]))) {

			auto const prevHbClock = hbClocks[previousLabels[4]];
			auto currentHbClock = mergeViews(hbClocks[previousLabels[0]], prevHbClock);
			currentHbClock[tid] += 4;
			hbClocks[previousLabels[0]] = currentHbClock;
	}
}

View HBCalculator::mergeViews(const View a, const View b) {
	auto max_size = std::max(a.size(), b.size());
    View mergedView;
	
    for (unsigned int i = 0; i < max_size; ++i) {
        mergedView[i] = std::max(a[i], b[i]);
    }

	return mergedView;
}

bool HBCalculator::calcFR() {
	auto &g = getGraph();

	std::unordered_map<SAddr, std::set<WriteLabel*>> previousWrites;
	std::vector<std::pair<EventLabel*, View>> sortedHbClocks(hbClocks.begin(), hbClocks.end());
	auto updatedHbClocks = hbClocks;

	std::sort(sortedHbClocks.begin(), sortedHbClocks.end(),
    [](const auto& lhs, const auto& rhs) {
        const View& a = lhs.second;
        const View& b = rhs.second;

        size_t size = std::max(a.size(), b.size());

        for (size_t i = 0; i < size; ++i) {
            auto aVal = (i < a.size()) ? a[i] : 0;
            auto bVal = (i < b.size()) ? b[i] : 0;

            if (aVal != bVal)
				return aVal < bVal; // ascending sort
        }

        return false; // equal views
    });

	auto initReadersList = getInitReadersList();

	for (auto pair : sortedHbClocks) {
    	auto const writeAccess = dynamic_cast<WriteLabel*>(pair.first);

		if (writeAccess) {
			auto const addr = writeAccess->getAddr();

			if (previousWrites.find(addr) == previousWrites.end()) {
				for (auto r : initReadersList[addr]) {

					int writeTid = writeAccess->getThread();
					if (r->getThread() == writeTid) continue;

					llvm::outs() << r->getPos() << " -fr-> " << writeAccess->getPos() << "\n";

					if (updatedHbClocks[r][writeTid] > updatedHbClocks[writeAccess][writeTid]) {
						llvm::outs() << updatedHbClocks[r] << updatedHbClocks[writeAccess] << "\n";
						llvm::outs() << "Incorrect fr edge\n";
						return false;
					} else {
						updateHBClockChain(updatedHbClocks, writeAccess, hbClocks[r]);
					}
				}
	
			} else {
				for (auto it = previousWrites[addr].begin(); it != previousWrites[addr].end(); ) {
					auto previousWrite = *it;
					if (previousWrite == writeAccess) { ++it; continue; }

					if (isViewStrictlyGreater(hbClocks[writeAccess], hbClocks[previousWrite])) {
						for (auto r : previousWrite->getReadersList()) {
							llvm::outs() << r << " -fr-> " << writeAccess->getPos() << "\n";
							updateHBClockChain(updatedHbClocks, writeAccess, hbClocks[g.getEventLabel(r)]);
						}
						// Erase events with View that is in HB of the current write access
						it = previousWrites[addr].erase(it);
					} else {
						++it;
					}
				}
			}

			previousWrites[addr].insert(writeAccess);
		}
	}

	hbClocks = updatedHbClocks;
	return true;
}

std::unordered_map<SAddr, std::set<EventLabel*>> HBCalculator::getInitReadersList() {
	auto &g = getGraph();
	std::unordered_map<SAddr, std::set<EventLabel*>> initReadersList;

	for (auto lab : labels(g)) {
		auto readLabel = dynamic_cast<ReadLabel*>(lab);
		if (!readLabel || !readLabel->getRf().isInitializer()) continue;

		auto const addr = readLabel->getAddr();
		initReadersList[addr].insert(readLabel);
	}

	return initReadersList;
}

void HBCalculator::calcMO() {
	std::unordered_map<SAddr, std::set<WriteLabel*>> previousWrites;
	std::vector<std::pair<EventLabel*, View>> sortedHbClocks(hbClocks.begin(), hbClocks.end());

	std::sort(sortedHbClocks.begin(), sortedHbClocks.end(),
    [](const auto& lhs, const auto& rhs) {
        const View& a = lhs.second;
        const View& b = rhs.second;

        size_t size = std::max(a.size(), b.size());

        for (size_t i = 0; i < size; ++i) {
            auto aVal = (i < a.size()) ? a[i] : 0;
            auto bVal = (i < b.size()) ? b[i] : 0;

            if (aVal != bVal)
                return aVal < bVal; // ascending sort
        }

        return false; // equal views
    });

	for (auto pair : sortedHbClocks) {
    	auto const writeAccess = dynamic_cast<WriteLabel*>(pair.first);

		if (writeAccess) {
			auto const addr = writeAccess->getAddr();

			for (auto it = previousWrites[addr].begin(); it != previousWrites[addr].end(); ) {
				auto previousWrite = *it;
				if (previousWrite == writeAccess) { ++it; continue; }
				
				//llvm::outs() << "Calculating mo for: " << previousWrite->getPos() << " " << writeAccess->getPos() << "\n";

				if (isViewStrictlyGreater(hbClocks[writeAccess], hbClocks[previousWrite])) {

					if (previousWrites.find(addr) == previousWrites.end()) {
						previousWrites[addr] = std::set<WriteLabel*> {writeAccess};
						mo[addr] = std::vector<WriteLabel*> {writeAccess};
					}

					llvm::outs() << previousWrite->getPos() << " -mo-> " << writeAccess->getPos() << "\n";
					// Erase events with View that is in HB of the current write access
					mo[addr].push_back(writeAccess);
					cojom.addEdge(previousWrite->getPos(), writeAccess->getPos());

					//it = previousWrites[addr].erase(it);
					++it;
				} else {
					++it;
				}
			}
			
			previousWrites[addr].insert(writeAccess);
		}
	}
}

void HBCalculator::calcCORR() {
	std::unordered_map<SAddr, std::set<ReadLabel*>> previousReads;
	std::vector<std::pair<EventLabel*, View>> sortedHbClocks(hbClocks.begin(), hbClocks.end());
	auto &g = getGraph();

	std::sort(sortedHbClocks.begin(), sortedHbClocks.end(),
    [](const auto& lhs, const auto& rhs) {
        const View& a = lhs.second;
        const View& b = rhs.second;

        size_t size = std::max(a.size(), b.size());

        for (size_t i = 0; i < size; ++i) {
            auto aVal = (i < a.size()) ? a[i] : 0;
            auto bVal = (i < b.size()) ? b[i] : 0;

            if (aVal != bVal)
                return aVal < bVal; // ascending sort
        }

        return false; // equal views
    });

	for (auto pair : sortedHbClocks) {
    	auto const readAccess = dynamic_cast<ReadLabel*>(pair.first);

		if (readAccess) {
			auto const addr = readAccess->getAddr();

			for (auto it = previousReads[addr].begin(); it != previousReads[addr].end(); ) {
				auto previousRead = *it;
				if (previousRead->getRf() == readAccess->getRf()) { ++it; continue; }

				if (isViewStrictlyGreater(hbClocks[readAccess], hbClocks[previousRead])) {
					if (corr.find(addr) == corr.end()) {
						// Entry in corr for this addres does not exist yet
						corr[addr] = std::vector<EventLabel*> {g.getEventLabel(previousRead->getRf())};
					}

					llvm::outs() << previousRead->getRf() << " -corr-> " << readAccess->getRf() << "\n";
					llvm::outs() << hbClocks[g.getEventLabel(previousRead->getRf())] << hbClocks[g.getEventLabel(readAccess->getRf())] << "\n";

					int startTid = previousRead->getRf().thread;
					llvm::outs() << hbClocks[g.getEventLabel(previousRead->getRf())][startTid] << " <= " << hbClocks[g.getEventLabel(readAccess->getRf())][startTid] << "\n";

					if (hbClocks[g.getEventLabel(previousRead->getRf())][startTid] <= hbClocks[g.getEventLabel(readAccess->getRf())][startTid]) {
						cojom.addEdge(previousRead->getRf(), readAccess->getRf());
						corr[addr].push_back(g.getEventLabel(readAccess->getRf()));
					} else {
						llvm::outs() << "Invalid corr edge\n";
					}
				}

				++it;
			}

			previousReads[addr].insert(readAccess);
		}
	}
}

bool HBCalculator::checkMoCoherence(WriteLabel* start, WriteLabel* end) {
	auto co = getGraph().getCoherenceCalculator();
	auto const addr = start->getAddr();

	bool foundStart = false;
	for (auto locIter = co->store_begin(addr); locIter != co->store_end(addr); ++locIter) {
		Event writeAccess = *locIter;
		if (writeAccess == start->getPos()) foundStart = true;
		if (foundStart && writeAccess == end->getPos()) {
			return true;
		}
	}

	return false;	
}

bool HBCalculator::isViewStrictlyGreater(View a, View b) {
	int size = std::max(a.size(), b.size());
	bool strictlyGreaterFound = false;

	for (int i = 0; i < size; i ++) {
        if (a[i] < b[i]) {
			return false; // a is not greater at this index
		} else if (a[i] > b[i]) {
			strictlyGreaterFound = true;
		}
    }

    return strictlyGreaterFound;
}

void HBCalculator::updateHBClockChain(std::unordered_map<EventLabel*, View> &newHbClock, EventLabel* start, View newView) {
	auto &g = getGraph();
	std::vector<std::pair<EventLabel*, View>> sortedHbClocks(newHbClock.begin(), newHbClock.end());

	std::sort(sortedHbClocks.begin(), sortedHbClocks.end(),
    [](const auto& lhs, const auto& rhs) {
        const View& a = lhs.second;
        const View& b = rhs.second;

        size_t size = std::max(a.size(), b.size());

        for (size_t i = 0; i < size; ++i) {
            auto aVal = (i < a.size()) ? a[i] : 0;
            auto bVal = (i < b.size()) ? b[i] : 0;

            if (aVal != bVal)
				return aVal < bVal; // ascending sort
        }

        return false; // equal views
    });

	for (auto pair : sortedHbClocks) {
		if (!isViewStrictlyGreater(hbClocks[pair.first], hbClocks[start]) && start != pair.first) continue;
		newHbClock[pair.first] = mergeViews(newView, newHbClock[pair.first]);
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

void HBCalculator::resetViews() {
	hbClocks.clear();
	moClocks.clear();
	mo.clear();
	corr.clear();
}