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

	calcHB();
	calcFR();
	calcMO();

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
	}

	return Calculator::CalculationResult(false, true);
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

void HBCalculator::calcFR() {
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
					
					if (isViewStrictlyGreater(updatedHbClocks[r], updatedHbClocks[writeAccess])) {
						llvm::outs() << updatedHbClocks[r] << updatedHbClocks[writeAccess] << "\n";
						llvm::outs() << "Incorrect fr edge\n";
					} else {
						updateHBClockChain(updatedHbClocks, writeAccess, hbClocks[r]);
					}
					llvm::outs() << r->getPos() << " -fr-> " << writeAccess->getPos() << "\n";
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

			llvm::outs() << "mo for " << addr << ": ";
			for (auto m : mo[addr]) {
				llvm::outs() << m->getPos();
			}
			llvm::outs() << "\n";

			for (auto it = previousWrites[addr].begin(); it != previousWrites[addr].end(); ) {
				auto previousWrite = *it;
				if (previousWrite == writeAccess) { ++it; continue; }
				
				llvm::outs() << "Calculating mo for: " << previousWrite->getPos() << " " << writeAccess->getPos() << "\n";

				if (isViewStrictlyGreater(hbClocks[writeAccess], hbClocks[previousWrite])) {

					if (previousWrites.find(addr) == previousWrites.end()) {
						previousWrites[addr] = std::set<WriteLabel*> {writeAccess};
						mo[addr] = std::vector<WriteLabel*> {writeAccess};
					}

					llvm::outs() << previousWrite->getPos() << " -mo-> " << writeAccess->getPos() << "\n";
					// Erase events with View that is in HB of the current write access
					mo[addr].push_back(writeAccess);
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
	llvm::outs() << "\n";
}

void HBCalculator::addHBfromMO(Calculator::GlobalRelation &hb, Calculator::GlobalRelation &mo) {
	auto &g = getGraph();

	for (auto const e : mo.getElems()) {
		for (auto const adj : mo.getElems()) {
			if (!mo(e, adj)) continue;
			if (e == adj) continue;
			
			auto const lab = g.getEventLabel(e);

			auto const labWrite = dynamic_cast<WriteLabel *>(lab);
			auto const adjWrite = g.getWriteLabel(adj);

			// WW coh
			hb.addEdge(e, adj);

			if (labWrite && adjWrite) {
				// RR coh
				for (auto labR : labWrite->getReadersList()) {
					for (auto adjR : adjWrite->getReadersList()) {
						if (labR != adjR) hb.addEdge(labR, adjR);
					}
				}
			}

			if (labWrite) {
				// WR coh
				for (auto r : labWrite->getReadersList()) {
					hb.addEdge(r, adj);
				}
			}

			if (adjWrite) {
				// RW coh
				for (auto r : adjWrite->getReadersList()) {
					hb.addEdge(e, r);
				}
			}
		}
	}
}

void HBCalculator::addHBfromInit(Calculator::GlobalRelation &hb) {
	for (auto const e : hb.getElems()) {
		if (e.isInitializer()) continue;
		hb.addEdge(e.getInitializer(), e);
	}
}

Calculator::GlobalRelation HBCalculator::mergeHBandMO(Calculator::GlobalRelation &hb, Calculator::GlobalRelation &mo) {
	auto &g = getGraph();

	Calculator::GlobalRelation merged(hb.getElems());

	for (auto const e : hb.getElems()) {
		for (auto const adj : hb.getElems()) {
			if (hb(e, adj) || mo(e, adj)) merged.addEdge(e, adj);
		}
	}

	return merged;
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
}

void HBCalculator::calcLabelViews(EventLabel *lab) {
	const auto &g = getGraph();
 
	advanceCurrentView(lab);

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
		 	calcReadViews(llvm::dyn_cast<ReadLabel>(lab));
		 	break;
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
		 	calcWriteViews(llvm::dyn_cast<WriteLabel>(lab));
		 	break;
	 	case EventLabel::EL_Fence:
	 	case EventLabel::EL_DskFsync:
	 	case EventLabel::EL_DskSync:
	 	case EventLabel::EL_DskPbarrier:
		 	calcFenceViews(llvm::dyn_cast<FenceLabel>(lab));
		 	break;
	 	case EventLabel::EL_ThreadStart:
		 	//calcStartViews(llvm::dyn_cast<ThreadStartLabel>(lab));
		 	break;
	 	case EventLabel::EL_ThreadJoin:
		 	//calcJoinViews(llvm::dyn_cast<ThreadJoinLabel>(lab));
		 	break;
	 	case EventLabel::EL_ThreadCreate:
	 	case EventLabel::EL_ThreadFinish:
	 	case EventLabel::EL_Optional:
	 	case EventLabel::EL_LoopBegin:
	 	case EventLabel::EL_SpinStart:
	 	case EventLabel::EL_FaiZNESpinEnd:
	 	case EventLabel::EL_LockZNESpinEnd:
		case EventLabel::EL_Malloc:
	 	case EventLabel::EL_Free:
	 	case EventLabel::EL_HpRetire:
	 	case EventLabel::EL_LockLAPOR:
	 	case EventLabel::EL_UnlockLAPOR:
		case EventLabel::EL_DskOpen:
		case EventLabel::EL_HelpingCas:
		case EventLabel::EL_HpProtect:
			//calcBasicViews(lab);
			break;
		case EventLabel::EL_SmpFenceLKMM:
			ERROR("LKMM fences can only be used with -lkmm!\n");
			break;
	 	case EventLabel::EL_RCULockLKMM:
	 	case EventLabel::EL_RCUUnlockLKMM:
	 	case EventLabel::EL_RCUSyncLKMM:
			ERROR("RCU primitives can only be used with -lkmm!\n");
			break;
		default:
			BUG();
	}
}

void HBCalculator::advanceCurrentView(EventLabel *lab) {
	auto const &g = getGraph();
	auto const prevLab = g.getPreviousNonEmptyLabel(lab);
	currentView[makeKey(lab)] = currentView[makeKey(prevLab)];
	currentView[makeKey(lab)][lab->getThread()] += 1;

	raAccessView[makeKey(lab)] = raAccessView[makeKey(prevLab)];
	releaseView[makeKey(lab)] = releaseView[makeKey(prevLab)];
	acquireView[makeKey(lab)] = acquireView[makeKey(prevLab)];

	llvm::outs() << lab->getPos();
	printView(currentView[makeKey(lab)]);
}

void HBCalculator::calcWriteViews(WriteLabel *lab) {
	auto const &g = getGraph();
	auto const prevLab = g.getPreviousLabel(lab);

	if (lab->getOrdering() == llvm::AtomicOrdering::Release) {
		auto const address = lab->getAddr().get();

		// set ra access view to current timestamp
		raAccessView[makeKey(lab)][address] = currentView[makeKey(lab)][lab->getThread()];
		
		llvm::outs() << "RF    ";
		printView(raAccessView[makeKey(lab)]);

	} else if (lab->getOrdering() == llvm::AtomicOrdering::Monotonic) {
		// monotonic is equivalent to relaxed

		auto const address = lab->getAddr().get();

		raAccessView[makeKey(lab)][address] = releaseView[makeKey(lab)][lab->getThread()];

		llvm::outs() << "RF    ";
		printView(raAccessView[makeKey(lab)]);
	}
}

void HBCalculator::calcReadViews(ReadLabel *lab) {
	auto const &g = getGraph();
	auto const prevLab = g.getPreviousLabel(lab);

	if (lab->getOrdering() == llvm::AtomicOrdering::Acquire) {
		auto const rf = g.getWriteLabel(lab->getRf());

		if (rf) {
			if (rf->getOrdering() == llvm::AtomicOrdering::Release) {
				// rf event is a realease write access
				auto const address = lab->getAddr().get();

				// set index of current view of rf event to maximum of ra access view and current view
				currentView[makeKey(lab)][rf->getThread()] =
					std::max(raAccessView[makeKey(rf)][address], currentView[makeKey(lab)][rf->getThread()]);

				llvm::outs() << "      ";
				printView(currentView[makeKey(lab)]);

			}
			
		} else if (lab->getRf().isInitializer()) {
			// rf event is the [init] event
			auto const address = lab->getAddr().get();

			currentView[makeKey(lab)][0] = 0;

			llvm::outs() << "      ";
			printView(currentView[makeKey(lab)]);
		}

	} else if (lab->getOrdering() == llvm::AtomicOrdering::Monotonic) {
		auto const rf = g.getWriteLabel(lab->getRf());

		if (rf) {
			if (rf->getOrdering() == llvm::AtomicOrdering::Monotonic) {
				auto const address = lab->getAddr().get();
				auto const acquireViewEntry = acquireView[makeKey(lab)][lab->getThread()];

				acquireView[makeKey(lab)] = currentView[makeKey(lab)];
				acquireView[makeKey(lab)][lab->getThread()] =
					std::max(acquireViewEntry, raAccessView[makeKey(rf)][address]);

				llvm::outs() << "A     ";
				printView(acquireView[makeKey(lab)]);
			}
		} else if (lab->getRf().isInitializer()) {
			auto const address = lab->getAddr().get();
			auto const acquireViewEntry = acquireView[makeKey(lab)][lab->getThread()];

			acquireView[makeKey(lab)] = currentView[makeKey(lab)];
			acquireView[makeKey(lab)][lab->getThread()] = acquireViewEntry;

			llvm::outs() << "A     ";
			printView(acquireView[makeKey(lab)]);
		}
	}
}

void HBCalculator::calcFenceViews(FenceLabel *lab) {
	if (lab->getOrdering() == llvm::AtomicOrdering::Release) {
		releaseView[makeKey(lab)][lab->getThread()] = currentView[makeKey(lab)][lab->getThread()];

		llvm::outs() << "R     ";
		printView(releaseView[makeKey(lab)]);

	} else if (lab->getOrdering() == llvm::AtomicOrdering::Acquire) {
		currentView[makeKey(lab)][lab->getThread()] =
			std::max(currentView[makeKey(lab)][lab->getThread()], acquireView[makeKey(lab)][lab->getThread()]);
		
		llvm::outs() << "      ";
		printView(currentView[makeKey(lab)]);
	}
}

std::string HBCalculator::makeKey(const EventLabel *lab) {
	std::ostringstream oss;
    oss << lab->getThread() << "-" << lab->getIndex();
    return oss.str();
}

template <typename K, typename V>
void HBCalculator::printView(const std::unordered_map<K, V> &v) {
	llvm::outs() << "[";
	for (const auto& [key, value] : v) {
        llvm::outs() << "(" << key << ": " << value << ") ";
    }
	llvm::outs() << "]\n";
}