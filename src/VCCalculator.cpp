 #include "VCCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"
#include <map>
#include <deque>

void VCCalculator::initCalc()
{
	// Relations are calculated from scratch everytime doCalc()
	// is called, nothing to do on init
	return;
}

Calculator::CalculationResult VCCalculator::doCalc() {
	resetViews();

	std::vector<Event> allLabels;
	for (auto lab : labels(getGraph())) {
		allLabels.push_back(lab->getPos());
	}

	//llvm::outs() << "\n\n ====================== Model checking " << " linearisations: ======================\n";

	calcHB();

	auto pushtoRel = createPushto(domainPushto);
	auto pushtos = calcAllLinearisations(pushtoRel);

	//llvm::outs() << getGraph();

	auto &g = getGraph();

	for (auto p : pushtos) {
		Calculator::GlobalRelation c(allLabels);
		cojom = c;
		std::unordered_map<EventLabel*, View> copyHbClocks (hbClocks);
		std::unordered_map<EventLabel*, View> updatedHbClocks (hbClocks);

		//llvm::outs() << "Linearisation:\n";
		//llvm::outs() << p;

		for (auto init : p.getElems()) {
			for (auto final : p.getElems()) {
				if (!p(init, final)) {
					continue;
				}

				auto pushtoView = View(hbClocks[g.getEventLabel(init)]);
				pushtoView[init.thread] += 1;

				updateHBClockChain(updatedHbClocks, g.getEventLabel(final), pushtoView);
			}
		}

		hbClocks = updatedHbClocks;

		calcMO();
		calcMObyFR();
		//calcCORR();

		//llvm::outs() << cojom;

		cojom.transClosure();
		if (cojom.isIrreflexive()) {
			return Calculator::CalculationResult(false, true);
		}
		hbClocks = copyHbClocks;
	}

	//llvm::outs() << "Inconsistent!\n";
	return Calculator::CalculationResult(false, false);
}

void VCCalculator::addToLinearisation(EventLabel* e) {
	llvm::outs() << "inserting: " << e->getPos() << "\n";

	if (linearisations.empty()) {
		std::vector<EventLabel*> l;
		l.push_back(e);
		linearisations.push_back(l);
		return;
	}

	for (auto linearisation : linearisations) {
		std::vector<EventLabel*> newLinearisation;

		for (auto it = linearisation.rbegin(); it != linearisation.rend(); ++it) {
			EventLabel* linearisedEvent = *it;
			newLinearisation.push_back(linearisedEvent);

			//llvm::outs() << linearisedEvent->getPos() << linearisedEvent->getPorfView() << " ? " << e->getPos() << e->getPorfView() << "\n";
			if (isViewStrictlyGreater(e->getPorfView(), linearisedEvent->getPorfView())) {
				//llvm::outs() << e->getPos() << " < " << linearisedEvent->getPos() << "\n";
				newLinearisation.push_back(e);
			}
		}

		for (auto e : newLinearisation) {
			llvm::outs() << e->getPos();
		}
		llvm::outs() << "\n";
	}
}

void VCCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
}

void VCCalculator::calcHB() {
	auto &g = getGraph();

	for (auto &t : g.getThreadList()) {
		calcHB(t, t.back().get());
	}
}

void VCCalculator::calcHB(ExecutionGraph::Thread &thread, EventLabel* halt) {
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

	std::unordered_map<SAddr, View> baseViews;

	//llvm::outs() << " --- " << tid << " --- \n";

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
				
				//llvm::outs() << " --- to thread " << rfTid << " --- \n";
				calcHB(g.getThreadList()[rfTid], g.getEventLabel(labRead->getRf()));
				//llvm::outs() << " --- return --- \n";
			}

			// Merge read and write VCs related by RF
			hbClocks[previousLabels[0]] = mergeViews(hbClocks[previousLabels[0]], hbClocks[labRf]);
			hbClocks[previousLabels[0]][rfTid] += 1;
		}

		// Memory access, advance VC by at least one from last access to this location
		// in this thread (po-loc)
		
		auto const memAccessLab = dynamic_cast<MemAccessLabel*>(lab.get());
		calcIntraThreadHB(lab.get(), previousLabels);

		if (memAccessLab) {
			auto previousAccessView = baseViews[memAccessLab->getAddr()];
			hbClocks[previousLabels[0]] = mergeViews(previousAccessView, hbClocks[previousLabels[0]]);
			baseViews[memAccessLab->getAddr()] = hbClocks[previousLabels[0]];
		}

		//llvm::outs() << previousLabels[0]->getPos() << " " << hbClocks[previousLabels[0]] << "\n";
		if (previousLabels[0] == halt) {
			// Reached the last event specified, end calculations
			//llvm::outs() << " --- halt --- \n";
			return;
		}
    }
}

void VCCalculator::calcIntraThreadHB(EventLabel* lab, std::deque<EventLabel*> previousLabels) {
	auto tid = lab->getThread();

	if (previousLabels.size() >= 2 && previousLabels[1]->isSC() && previousLabels[0]->isSC()) {
		auto const prevHbClock = hbClocks[previousLabels[1]];
		auto currentHbClock = mergeViews(hbClocks[previousLabels[0]], prevHbClock);
		currentHbClock[tid] += 1;
		hbClocks[previousLabels[0]] = currentHbClock;
		domainPushto.push_back(previousLabels[1]);
		addToLinearisation(previousLabels[1]);
	}

	if (previousLabels.size() >= 3 && previousLabels[1]->isSC() && isFence(previousLabels[1])) {
		// Advance by 2 to account for a possibly HB ordered intermediate event
		auto const prevHbClock = hbClocks[previousLabels[2]];
		auto currentHbClock = View(prevHbClock);
		currentHbClock[tid] += 2;
		hbClocks[previousLabels[0]] = currentHbClock;
		domainPushto.push_back(previousLabels[2]);
		addToLinearisation(previousLabels[2]);
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

View VCCalculator::mergeViews(const View a, const View b) {
	auto max_size = std::max(a.size(), b.size());
    View mergedView;
	
    for (unsigned int i = 0; i < max_size; ++i) {
        mergedView[i] = std::max(a[i], b[i]);
    }

	return mergedView;
}

Calculator::GlobalRelation VCCalculator::createPushto(std::vector<EventLabel*> domain) {
	auto &g = getGraph();
	std::vector<std::pair<EventLabel*, View>> domainClocks;
	for (auto d : domain) {
		domainClocks.push_back({d, hbClocks[d]});
	}

	std::sort(domainClocks.begin(), domainClocks.end(),
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

	std::vector<Event> domainEventType;
	for (auto d : domain) { domainEventType.push_back(d->getPos()); }
	Calculator::GlobalRelation pushto (domainEventType);

	if (domainClocks.size() < 1) return pushto;

	std::pair<EventLabel*, View> previous = domainClocks.front();
	for (auto d : domainClocks) {
		if (isViewStrictlyGreater(d.second, previous.second)) {
			pushto.addEdge(previous.first->getPos(), d.first->getPos());
		}
		previous = d;
	}

	return pushto;
}

std::vector<Calculator::GlobalRelation> VCCalculator::calcAllLinearisations(GlobalRelation rel) {
	std::vector<GlobalRelation> pushtos;

	rel.allTopoSort([this, &pushtos](auto& sort) {
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

		Calculator::GlobalRelation pushto(sort);
		for (int i = 1; i < sort.size(); i ++) {
			auto elemA = pushto.getElems()[i - 1];
			auto elemB = pushto.getElems()[i];
			if (!isViewStrictlyGreater(hbClocks[g.getEventLabel(elemB)], hbClocks[g.getEventLabel(elemA)])) {
				pushto.addEdge(elemA, elemB);
			}
		}

		pushtos.push_back(pushto);

		// Allways return false to keep finding all possible topological sorts
		return false;
    });

	return pushtos;
}

bool VCCalculator::calcFR() {
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

					//llvm::outs() << r->getPos() << " -fr-> " << writeAccess->getPos() << "\n";

					if (updatedHbClocks[r][writeTid] > updatedHbClocks[writeAccess][writeTid]) {
						//llvm::outs() << updatedHbClocks[r] << updatedHbClocks[writeAccess] << "\n";
						//llvm::outs() << "Incorrect fr edge\n";
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
							//llvm::outs() << r << " -fr-> " << writeAccess->getPos() << "\n";
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

std::unordered_map<SAddr, std::set<EventLabel*>> VCCalculator::getInitReadersList() {
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

void VCCalculator::calcMObyFR() {
	auto &g = getGraph();
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
		auto writeAccess = dynamic_cast<WriteLabel*>(pair.first);
		if (!writeAccess) continue;

		//llvm::outs() << pair.first->getPos() << hbClocks[pair.first] << "\n";

		for (auto nextPair : sortedHbClocks) {
			if (!isViewStrictlyGreater(hbClocks[nextPair.first], hbClocks[pair.first])) continue;
			if (!(hbClocks[pair.first][pair.first->getThread()] < hbClocks[nextPair.first][pair.first->getThread()])) continue;
			if (nextPair.first->getPos().isInitializer()) continue;

			//llvm::outs() << "	" << nextPair.first->getPos() << hbClocks[nextPair.first] << "\n";

			auto readAccess = dynamic_cast<ReadLabel*>(nextPair.first);
			if (readAccess && readAccess->getAddr() == writeAccess->getAddr()) {
				auto writeRf = readAccess->getRf();
				auto writeRfLabel = g.getWriteLabel(writeRf);

				if (writeRf == writeAccess->getPos()) continue;

				if (writeRf.isInitializer()) {
					cojom.addEdge(writeAccess->getPos(), writeRf);
					//llvm::outs() << writeAccess->getPos() << " -mo-(rf)-> " << writeRf << "\n\n";
					break;
				} else if (writeRfLabel && writeRfLabel->getAddr() == writeAccess->getAddr()) {
					cojom.addEdge(writeAccess->getPos(), writeRf);
					//llvm::outs() << writeAccess->getPos() << " -mo-(rf)-> " << writeRf << "\n\n";
					return;
				}
			}
		}
	}
}

void VCCalculator::calcMO() {
	auto &g = getGraph();
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
		auto const readAccess = dynamic_cast<ReadLabel*>(pair.first);

		if (writeAccess) {
			auto const addr = writeAccess->getAddr();

			for (auto it = previousWrites[addr].begin(); it != previousWrites[addr].end(); ) {
				auto previousWrite = *it;
				if (previousWrite == writeAccess) { ++it; continue; }

				if (isViewStrictlyGreater(hbClocks[writeAccess], hbClocks[previousWrite])) {

					if (previousWrites.find(addr) == previousWrites.end()) {
						previousWrites[addr] = std::set<WriteLabel*> {writeAccess};
						mo[addr] = std::vector<WriteLabel*> {writeAccess};
					}

					//llvm::outs() << previousWrite->getPos() << " -mo-> " << writeAccess->getPos() << "\n";
					mo[addr].push_back(writeAccess);
					cojom.addEdge(previousWrite->getPos(), writeAccess->getPos());
				}

				++it;
			}
			
			if (previousWrites[addr].empty()) {
				cojom.addEdge(writeAccess->getPos().getInitializer(), writeAccess->getPos());
				//llvm::outs() << "(0, 0) -mo-> " << writeAccess->getPos() << "\n";
			}

			previousWrites[addr].insert(writeAccess);
		}

		/*
		if (readAccess) {
			auto const addr = readAccess->getAddr();
			auto const writeRf = readAccess->getRf();

			llvm::outs() << "Checkning mo for " << readAccess->getPos() << " <-rf- " << writeRf << "\n";

			auto prevHBWrite = getMinimalWrite(readAccess, readAccess->getAddr());

			if (prevHBWrite->getPos() != writeRf) {
				cojom.addEdge(prevHBWrite->getPos(), writeRf);
				llvm::outs() << prevHBWrite->getPos() << " -mo (rf)-> " << writeRf << "\n";
			} else {
				llvm::outs() << "Previous access in HB is rf-write\n";
				llvm::outs() << "Not added: " << prevHBWrite->getPos() << " -mo-> " << writeRf << "\n";
			}

			if (writeRf.isInitializer()) {
				
			}

			llvm::outs() << "\n";
		}
			*/
	}
}

EventLabel* VCCalculator::getMinimalWrite(EventLabel* m, SAddr addr) {
	auto &g = getGraph();
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
                return aVal > bVal; // descending sort
        }

        return false; // equal views
    });

	bool foundStart = false;
	EventLabel* minimalLabel = m;

	EventLabel* previousWrite = g.getEventLabel(m->getPos().getInitializer());

	llvm::outs() << "Finding minimal write starting at " << m->getPos() << " for addr " << addr << "\n";

	for (auto pair : sortedHbClocks) {
		auto threadStart = dynamic_cast<ThreadStartLabel*>(pair.first);
		auto threadEnd = dynamic_cast<ThreadFinishLabel*>(pair.first);
		auto threadCreateLabel = dynamic_cast<ThreadCreateLabel*>(pair.first);
		if (threadStart || threadEnd || threadCreateLabel) continue;

		if (!foundStart && pair.first == m) {
			foundStart = true;
			continue;
		} else if (!foundStart) {
			continue;
		}

		//llvm::outs() << "Current minimal label " << minimalLabel->getPos() << "\n";

		if (!isViewStrictlySmaller(pair.second, hbClocks[minimalLabel])) {
			continue;
		}

		//llvm::outs() << pair.first->getPos() << minimalLabel->getPos() << "\n";
		//llvm::outs() << pair.second << " < " << hbClocks[minimalLabel] << "\n";
		minimalLabel = pair.first;

		auto writeAccess = dynamic_cast<WriteLabel*> (pair.first);
		if (writeAccess) {
			if (writeAccess->getAddr() == addr && isViewStrictlyGreater(hbClocks[writeAccess], hbClocks[previousWrite])) {
				//llvm::outs() << "found write access previously in HB " << writeAccess->getPos() << "\n";
				return writeAccess;
			}
		}

		auto readAccess = dynamic_cast<ReadLabel*> (pair.first);
		if (readAccess) {
			auto rf = g.getEventLabel(readAccess->getRf());
			auto writeRf = dynamic_cast<WriteLabel*>(rf);
			
			if (readAccess->getAddr() == addr) {
				//llvm::outs() << "returning write access by rf\n";
				return rf;
			}

			minimalLabel = rf;
		}
	}

	//llvm::outs() << "iterated over all accesses\n";

	return g.getEventLabel(m->getPos().getInitializer()); // todo change to previousWrite
}

void VCCalculator::calcCORR() {
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

				//llvm::outs() << readAccess->getPos() << pair.second << "\n";

				if (isViewStrictlyGreater(hbClocks[readAccess], hbClocks[previousRead])) {
					if (corr.find(addr) == corr.end()) {
						// Entry in corr for this addres does not exist yet
						corr[addr] = std::vector<EventLabel*> {g.getEventLabel(previousRead->getRf())};
					}

					//llvm::outs() << previousRead->getRf() << " -corr-> " << readAccess->getRf() << "\n";
					//llvm::outs() << hbClocks[g.getEventLabel(previousRead->getRf())] << hbClocks[g.getEventLabel(readAccess->getRf())] << "\n";

					int startTid = previousRead->getRf().thread;
					//llvm::outs() << hbClocks[g.getEventLabel(previousRead->getRf())][startTid] << " <= " << hbClocks[g.getEventLabel(readAccess->getRf())][startTid] << "\n";

					cojom.addEdge(previousRead->getRf(), readAccess->getRf());
					corr[addr].push_back(g.getEventLabel(readAccess->getRf()));

					/*
					if (hbClocks[g.getEventLabel(previousRead->getRf())][startTid] <= hbClocks[g.getEventLabel(readAccess->getRf())][startTid]) {
						cojom.addEdge(previousRead->getRf(), readAccess->getRf());
						corr[addr].push_back(g.getEventLabel(readAccess->getRf()));
					} else {
						llvm::outs() << "Invalid corr edge\n";
					}
					*/
				}

				++it;
			}

			previousReads[addr].insert(readAccess);
		}
	}
}

bool VCCalculator::checkMoCoherence(WriteLabel* start, WriteLabel* end) {
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

bool VCCalculator::isViewStrictlyGreater(View a, View b) {
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

bool VCCalculator::isViewStrictlySmaller(View a, View b) {
	int size = std::max(a.size(), b.size());
	bool strictlySmallerFound = false;

	for (int i = 0; i < size; i ++) {
        if (a[i] > b[i]) {
			return false;
		} else if (a[i] < b[i]) {
			strictlySmallerFound = true;
		}
    }

    return strictlySmallerFound;
}

void VCCalculator::updateHBClockChain(std::unordered_map<EventLabel*, View> &newHbClock, EventLabel* start, View newView) {
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

	//llvm::outs() << "\n";

	for (auto pair : sortedHbClocks) {
		if ((!isViewStrictlyGreater(hbClocks[pair.first], hbClocks[start]) && start != pair.first)) continue;
		newHbClock[pair.first] = mergeViews(newView, newHbClock[pair.first]);
	}
}

bool VCCalculator::isFence(EventLabel *lab) {
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

void VCCalculator::resetViews() {
	hbClocks.clear();
	moClocks.clear();
	mo.clear();
	corr.clear();
	domainPushto.clear();
	linearisations.clear();
}