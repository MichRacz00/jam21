#include "HBCalculator.hpp"
#include "Error.hpp"
#include "ExecutionGraph.hpp"
#include "GraphIterators.hpp"
#include <deque>
#include <map>

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

	for (auto &t : g.getThreadList()) {
		addIntraThreadHB(t, hb);
	}
	hb.transClosure();
	
	addHBfromInit(hb);
	//addImplicitHB(hb);

	calcMO(hb, mo);

	addHBfromMO(hb, mo);

	//llvm::outs() << getGraph();
	//llvm::outs() << hb << "\n";
	//llvm::outs() << mo << "\n";
	//llvm::outs() << " ============================================================= \n";
	
	auto hbUmo = mergeHBandMO(hb, mo);
	hbUmo.transClosure();

	for (auto const l : labels(g)) {
		calcLabelViews(l);
	}
	
	return Calculator::CalculationResult(false, hbUmo.isIrreflexive());
}

void HBCalculator::removeAfter(const VectorClock &preds)
{
	/* We do not track anything specific */
	return;
}

void HBCalculator::addIntraThreadHB(ExecutionGraph::Thread &eventLabels, Calculator::GlobalRelation &hb) {
	std::deque<EventLabel*> lastLabels;
	std::map<SAddr, Event> previousAccess;
	auto &g = getGraph();

    for (auto &lab : eventLabels) {
		lastLabels.push_back(lab.get());
		if (lastLabels.size() > 5) lastLabels.pop_front();

		auto labMemAccess = dynamic_cast<MemAccessLabel*>(lab.get());
		if (labMemAccess) {
			if (previousAccess.find(labMemAccess->getAddr()) == previousAccess.end()) {
				auto firstThreadEvent = eventLabels.front().get();
				hb.addEdge(firstThreadEvent->getPos(), labMemAccess->getPos());
				previousAccess[labMemAccess->getAddr()] = labMemAccess->getPos();
			} else {
				auto prevAccessLab = previousAccess[labMemAccess->getAddr()];
				hb.addEdge(prevAccessLab, labMemAccess->getPos());
				previousAccess[labMemAccess->getAddr()] = labMemAccess->getPos();
			}
		}	

		auto labThreadStart = dynamic_cast<ThreadStartLabel*>(lab.get());
		if (labThreadStart) {
			auto labCreate = labThreadStart->getParentCreate();
			if (labCreate != labThreadStart->getPos()) {
				hb.addEdge(labCreate, labThreadStart->getPos());
			}
		}

		auto labRead = dynamic_cast<ReadLabel*>(lab.get());
		if (labRead) {
			auto labRf = labRead->getRf();
			hb.addEdge(labRf, labRead->getPos());
		}

		if (lastLabels.size() >= 2) {
			auto last = lastLabels.back();
            auto oneButLast = *(std::next(lastLabels.rbegin()));

			if (last->isSC() && oneButLast->isSC()) {
				// volint
				hb.addEdge(oneButLast->getPos(), last->getPos());
			}

			if (lastLabels.size() >= 3) {
				auto twoButLast = *(std::next(lastLabels.rbegin(), 2));

				if (oneButLast->isSC() && isFence(oneButLast)) {
					// spush
					hb.addEdge(twoButLast->getPos(), last->getPos());
				}

				if (oneButLast->isSC() || oneButLast->isAtLeastAcquire() || oneButLast->isAtLeastRelease()) {
					// ra
					hb.addEdge(twoButLast->getPos(), last->getPos());
				}
				
				if (lastLabels.size() >= 5) {
					auto threeButLast = *(std::next(lastLabels.rbegin(), 3));
					auto fourButLast = *(std::next(lastLabels.rbegin(), 4));

					auto writeCast = dynamic_cast<WriteLabel*>(threeButLast);
					auto readCast = dynamic_cast<ReadLabel*>(threeButLast);

					if (writeCast || readCast) {
						if (isFence(fourButLast) && fourButLast->isAtLeastRelease() && isFence(twoButLast) && twoButLast->isAtLeastAcquire()) {
							// svo
							auto first = *(std::next(lastLabels.rbegin(), 5));
							hb.addEdge(first->getPos(), last->getPos());
						}
					}
				}
			}
		}
    }
}

void HBCalculator::calcMO(Calculator::GlobalRelation &hb, Calculator::GlobalRelation &mo) {
	auto &g = getGraph();

	for (auto const e : hb.getElems()) {
		for (auto const adj : hb.getElems()) {
			if (!hb(e, adj)) continue;
			if (e == adj) continue;

			auto const lab = g.getEventLabel(e);

			auto const labWrite = dynamic_cast<WriteLabel *>(lab);
			auto const labRead = dynamic_cast<ReadLabel *>(lab);

			auto const adjWrite = g.getWriteLabel(adj);
			auto const adjRead = g.getReadLabel(adj);

			if (labWrite && adjWrite) {
				if (labWrite->getAddr() == adjWrite->getAddr()) {
					mo.addEdge(e, adj);
				}

			} else if (labWrite && adjRead) {
				auto rf = adjRead->getRf();
				if (e != rf && labWrite->getAddr() == adjRead->getAddr()) {
					mo.addEdge(e, rf);
				} else if (e != rf && rf.isInitializer()) {
					mo.addEdge(e, rf);
				}

			} else if (labRead && adjWrite) {
				auto rf = labRead->getRf();
				if (rf.isInitializer()) {
					mo.addEdge(rf, adj);
				} else if (g.getWriteLabel(rf)->getAddr() == adjWrite->getAddr()) {
					mo.addEdge(rf, adj);
				}

			} else if (labRead && adjRead) {
				auto rfLab = labRead->getRf();
				auto rfAdj = adjRead->getRf();

				if (rfLab != rfAdj) {
					if (rfLab.isInitializer() || rfAdj.isInitializer()) {
						mo.addEdge(rfLab, rfAdj);	
					} else if (g.getWriteLabel(rfLab)->getAddr() == g.getWriteLabel(rfAdj)->getAddr()) {
						mo.addEdge(rfLab, rfAdj);
					}
				}
			} else if (adjWrite) {
				if (e.isInitializer()) {
					mo.addEdge(e, adj);
				}
			}
		}
	}
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

void HBCalculator::calcLabelViews(EventLabel *lab) {
	const auto &g = getGraph();
 
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
		 	//calcReadViews(llvm::dyn_cast<ReadLabel>(lab));
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
		 	//calcFenceViews(llvm::dyn_cast<FenceLabel>(lab));
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

void HBCalculator::calcWriteViews(WriteLabel *lab) {
	if (lab->getOrdering() == llvm::AtomicOrdering::Release) {
		auto const address = lab->getAddr().get();
		llvm::outs() << address << "\n";
		raWriteView[address] = 1;
	}
}