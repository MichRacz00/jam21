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

	addImplicitHB(hb);

	calcMO(hb, mo);

	auto hbUmo = mergeHBandMO(hb, mo);
	
	hbUmo.transClosure();

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
			hb.addEdge(labCreate, labThreadStart->getPos());
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

			auto const lab = g.getEventLabel(e);

			auto const labWrite = dynamic_cast<WriteLabel *>(lab);
			auto const labRead = dynamic_cast<ReadLabel *>(lab);

			auto const adjWrite = g.getWriteLabel(adj);
			auto const adjRead = g.getReadLabel(adj);

			if (labWrite && adjWrite) {
				if (labWrite->getAddr() == adjWrite->getAddr()) {
					mo.addEdge(e, adj);
					//hb.addEdge(e, adj);
				}

			} else if (labWrite && adjRead) {
				auto rf = adjRead->getRf();
				if (e != rf && labWrite->getAddr() == adjRead->getAddr()) {
					mo.addEdge(e, rf);
					//hb.addEdge(e, rf);
				}

			} else if (labRead && adjWrite) {
				auto rf = labRead->getRf();
				if (g.getWriteLabel(rf)->getAddr() == adjWrite->getAddr()) {
					mo.addEdge(rf, adj);
					//hb.addEdge(rf, adj);
				}

			} else if (labRead && adjRead) {
				auto rfLab = labRead->getRf();
				auto rfAdj = adjRead->getRf();
				if (g.getWriteLabel(rfLab)->getAddr() == g.getWriteLabel(rfAdj)->getAddr()) {
					mo.addEdge(rfLab, rfAdj);
					//hb.addEdge(rfLab, rfAdj);
				}
			}
		}
	}
}

void HBCalculator::addImplicitHB(Calculator::GlobalRelation &hb) {
	auto &g = getGraph();

	for (auto lab : labels(g)) {
		auto labRead = dynamic_cast<ReadLabel *> (lab);
		if (!labRead) continue;

		auto read_addr = labRead->getAddr();

		auto rf = labRead->getRf();

		for (auto const adj : hb.getElems()) {
			//llvm::outs() << rf << adj << "\n";
			if (!hb(rf, adj)) continue;
			auto const labWrite = g.getWriteLabel(adj);
			if (!labWrite) continue;
			if (labRead->getAddr() != labWrite->getAddr()) continue;
			hb.addEdge(labRead->getPos(), adj);
		}
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