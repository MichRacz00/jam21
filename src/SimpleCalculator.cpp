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

	auto const firstEvent = thread.front().get();
	auto const tid = firstEvent->getThread();
	auto firstLab = dynamic_cast<ThreadStartLabel*>(firstEvent);
	auto threadCreateEvent = g.getEventLabel(firstLab->getParentCreate());

	auto threadCreateClock = voClocks[threadCreateEvent];
	auto currentVoView = View(threadCreateClock);

	bool advanceNext = false;

	std::unordered_map<SAddr, View> lastPerLocView;
	View lastCommonView = View(threadCreateClock);

	llvm::outs() << "\n";

	for (auto &lab : thread) {
		if (!voClocks[lab.get()].empty()) {
			currentVoView = voClocks[lab.get()];
			continue;
		}

		// relaxed memory access
		auto memLab = dynamic_cast<MemAccessLabel*>(lab.get());
		if (memLab && lab.get()->getOrdering() == llvm::AtomicOrdering::Monotonic) {
			auto it = lastPerLocView.find(memLab);

			llvm::outs() << lab.get()->getPos() << " relaxed\n";

			// this location was not accessed since last synchronization yet
			if (it == lastPerLocView.end()) {

			}
		}

		bool advanceNow = false;
		if (advanceNext = true) {
			advanceNext = false;
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
		
		if (advanceNow == true) {
			currentVoView[tid] ++;
		}
	}
	llvm::outs() << "\n";
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