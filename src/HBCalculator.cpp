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

Calculator::CalculationResult HBCalculator::doCalc()
{
	auto &g = getGraph();

	std::vector<Event> allEvents;
	for (auto const lab : labels(g)) allEvents.push_back(lab->getPos());
	Calculator::GlobalRelation hb(allEvents);
	Calculator::GlobalRelation mo(allEvents);

	calcHB();
	calcMO();

	hb.transClosure();
	
	addHBfromInit(hb);
	//addImplicitHB(hb);

	addHBfromMO(hb, mo);

	//llvm::outs() << getGraph();
	//llvm::outs() << hb << "\n";
	//llvm::outs() << mo << "\n";
	//llvm::outs() << " ============================================================= \n";

	//for (auto const l : labels(g)) {
	//	calcLabelViews(l);
	//}
	
	resetViews();
	//return Calculator::CalculationResult(false, hbUmo.isIrreflexive());
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
	hbClocks[firstThreadEvent] = View(prevThreadClock);

	llvm::outs() << " --- " << tid << " --- \n";

    for (auto &lab : thread) {
		// Keep track of 4 previous labels
		// add current label for future reference
		previousLabels.push_front(lab.get());
		if (previousLabels.size() > 5) previousLabels.pop_back();

		// Remember last HB view to this location
		View previousAccessView;
		auto const memAccessLab = dynamic_cast<MemAccessLabel*>(lab.get());
		if (memAccessLab) {
			previousAccessView = previousAccess[memAccessLab->getAddr()];
			previousAccess[memAccessLab->getAddr()] = hbClocks[memAccessLab];
		}

		if (!hbClocks[previousLabels[0]].empty()) {
			// VC is already calculated for this event, skip
			continue;
		}

		if (previousLabels.size() >= 2) {
			// Copy previous VC to this event
			hbClocks[previousLabels[0]] = mergeViews(hbClocks[previousLabels[0]], hbClocks[previousLabels[1]]);
		}

		auto labRead = dynamic_cast<ReadLabel*>(lab.get());
		if (labRead) {
			// Read event, get VC from write
			auto labRf = g.getEventLabel(labRead->getRf());

			if (hbClocks[labRf].empty()) {
				// Write VC not yet calculated, calculate it and return
				auto rfTid = labRf->getThread();
				llvm::outs() << " --- to thread " << rfTid << " --- \n";
				calcHB(g.getThreadList()[rfTid], g.getEventLabel(labRead->getRf()));
				llvm::outs() << " --- return --- \n";
			}

			// Merge read and write VCs related by RF
			hbClocks[previousLabels[0]] = mergeViews(hbClocks[previousLabels[0]], hbClocks[labRf]);
		}

		calcIntraThreadHB(lab.get(), previousLabels);

		// Memory access, advance VC by at least one from last access to this location
		// in this thread (po-loc)
		if (memAccessLab) {
			hbClocks[previousLabels[0]] = mergeViews(hbClocks[previousLabels[0]], previousAccessView);
			hbClocks[previousLabels[0]][tid] += 1;
		}

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

void HBCalculator::calcMO() {
	auto &g = getGraph();

	std::unordered_map<SAddr, std::set<WriteLabel*>> previousWrites;
	std::vector<std::pair<EventLabel*, View>> sortedHbClocks(hbClocks.begin(), hbClocks.end());

	std::sort(sortedHbClocks.begin(), sortedHbClocks.end(),
    [](const auto& a, const auto& b) { 
        return !(b.second <= a.second);
    });

	for (auto pair : sortedHbClocks) {
    	auto const writeAccess = dynamic_cast<WriteLabel*>(pair.first);
		auto const readAccess = dynamic_cast<ReadLabel*>(pair.first);

		if (writeAccess) {
			auto const addr = writeAccess->getAddr();

			if (previousWrites.find(addr) == previousWrites.end()) {
				previousWrites[addr] = std::set<WriteLabel*> {writeAccess};
	
			} else {
				for (auto it = previousWrites[addr].begin(); it != previousWrites[addr].end(); ) {
					auto previousWrite = *it;
					if (previousWrite == writeAccess) { ++it; continue; }

					if (isViewStrictlyGreater(hbClocks[previousWrite], hbClocks[writeAccess])) {
						llvm::outs() << previousWrite->getPos() << " -mo-> " << writeAccess->getPos() << "\n";
						for (auto r : previousWrite->getReadersList()) {
							llvm::outs() << r << " -fr-> " << writeAccess->getPos() << "\n";
						}
						// Erase events with View that is in HB of the current write access
						it = previousWrites[addr].erase(it);
					} else {
						++it;
					}
				}

				previousWrites[addr].insert(writeAccess);

				for (auto w : previousWrites[addr]) {
					llvm::outs() << w->getPos();
				}
				llvm::outs() << "\n";
			}

		}
	}
}

bool HBCalculator::isViewStrictlyGreater(View a, View b) {
	int size = std::max(a.size(), b.size());

	for (int i = 0; i < size; i ++) {
        if (b[i] < a[i]) {
			return false;
		}
    }

    return true;
}

void HBCalculator::updateSet(std::set<EventLabel*> &events, EventLabel* hbEvent) {
	if (&events == nullptr) {
        std::set<EventLabel*> newSet;
        events = newSet;
    }

	for (auto it = events.begin(); it != events.end();) {
        if (!(hbClocks[hbEvent] <= hbClocks[*it])) {
            //it = events.erase(it);
			++it;
        } else {
            ++it;
        }
    }

	events.insert(hbEvent);
}

EventLabel* HBCalculator::getMaximalHBEvent(std::set<EventLabel*> &events, EventLabel* hbEvent) {
	EventLabel* maximalEvent = nullptr;

    for (auto* event : events) {
        if (hbClocks[event] <= hbClocks[hbEvent]) {
            if (!maximalEvent || hbClocks[maximalEvent] <= hbClocks[event]) {
                maximalEvent = event;
            }
        }
    }

    return maximalEvent;
}

void HBCalculator::addFRtoHB(WriteLabel* labOut, WriteLabel* labIn) {

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