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

	calcHBClocks();

	hbClocks.clear();
	polocClocks.clear();

	return Calculator::CalculationResult(false, true);
}

void SimpleCalculator::calcHBClocks(ExecutionGraph::Thread &thread, EventLabel* halt) {
	auto &g = getGraph();

	auto const firstThreadEvent = thread.front().get();
	auto const tid = firstThreadEvent->getThread();

	auto firstThreadLab = dynamic_cast<ThreadStartLabel*>(firstThreadEvent);
	auto threadCreateEvent = g.getEventLabel(firstThreadLab->getParentCreate());

	auto threadCreateClock = hbClocks[threadCreateEvent];
	auto baseView = View(threadCreateClock);
	auto commonRfView = View();

	std::unordered_map<SAddr, View> previousAccessViews;

	llvm::outs() << "\n";

	for (auto &lab : thread) {
		if (!hbClocks[lab.get()].empty()) {
			baseView = hbClocks[lab.get()];
			continue;
		}

		auto currentView = baseView;

		// Merge View from incoming RF edge
		auto readLab = dynamic_cast<ReadLabel*>(lab.get());
		if (readLab && !readLab->getRf().isInitializer()) {
			auto rfLab = g.getEventLabel(readLab->getRf());
			auto rfTid = rfLab->getThread();

			// RF View not yet calculated, calculate it
			if (hbClocks[rfLab].empty()) {
				auto &rfThread = g.getThreadList()[rfTid];
				calcHBClocks(rfThread, rfLab);
				llvm::outs() << "\n";
			}

			// Merge RF View, increase by 1 to reflect synch effect of RF
			currentView.update(hbClocks[rfLab]);
			currentView[rfTid]++;
		}

		bool syncCurrent = false
		|| dynamic_cast<ThreadFinishLabel*>(lab.get())
		|| ((lab.get()->isAtLeastAcquire() || lab.get()->isAtLeastRelease())
				&& (dynamic_cast<ReadLabel*>(lab.get()) || dynamic_cast<WriteLabel*>(lab.get())));

		bool syncBoth = (lab.get()->getOrdering() == llvm::AtomicOrdering::SequentiallyConsistent && isFence(lab.get()));

		bool syncNext = dynamic_cast<ThreadStartLabel*>(lab.get());

		if (syncCurrent || syncBoth) {
			if (currentView[tid] <= baseView[tid]) {
				currentView[tid]++;
			}
		}

		llvm::outs() << lab.get()->getPos() << " " << currentView << "\n";
		hbClocks[lab.get()] = currentView;

		baseView = currentView;

		if (syncNext || syncBoth) {
			baseView[tid]++;
		}

		if (halt == lab.get()) return;
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