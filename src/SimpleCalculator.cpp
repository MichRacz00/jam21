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

	voClocks.clear();
	polocClocks.clear();

	return Calculator::CalculationResult(false, true);
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

	llvm::outs() << "\n";

	for (auto &lab : thread) {
		// VC already calculated for this event, skip
		if (!voClocks[lab.get()].empty()) continue;

		// If previous iteration requested VC advancment of the next VC
		bool advanceNow = false;
		if (advanceNext == true) {
			advanceNext = false;
			advanceNow = true;
		}

		// isRelaxed is true if lab is a relaxed memory access
		auto memLab = dynamic_cast<MemAccessLabel*>(lab.get());
		bool isRelaxed = memLab && lab.get()->getOrdering() == llvm::AtomicOrdering::Monotonic;
		
		if (isRelaxed) {
			auto addr = memLab->getAddr();
			auto it = lastPerLocView.find(addr);

			if (it == lastPerLocView.end()) {
				// this location was not accessed since last synchronization yet
				currentVoView = lastCommonView;
			} else {
				// advance last 
				currentVoView = lastPerLocView[addr];
			}

			advanceNow = true;
		}

		// ra and svo
		if (lab.get()->getOrdering() == llvm::AtomicOrdering::Release
			|| lab.get()->getOrdering() == llvm::AtomicOrdering::Acquire
			|| lab.get()->getOrdering() == llvm::AtomicOrdering::AcquireRelease)
		{
			advanceNow = true;
			advanceNext = true;
		}

		// sc fence and memory access
		if (lab.get()->getOrdering() == llvm::AtomicOrdering::SequentiallyConsistent) {
			advanceNow = true;
			advanceNext = true;
		}
		
		if (advanceNow == true) currentVoView[tid] ++;

		voClocks[lab.get()] = currentVoView;

		if (isRelaxed) {
			// Relaxed memory access, store vo view per location
			lastPerLocView[memLab->getAddr()] = currentVoView;
		} else {
			// Synchronization, merge all relaxed vo views
			for (auto pair : lastPerLocView) {
				currentVoView.update(pair.second);
			}
			lastCommonView = currentVoView;
			lastPerLocView.clear();
		}

		llvm::outs() << lab.get()->getPos() << voClocks[lab.get()] << "\n";
	}
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