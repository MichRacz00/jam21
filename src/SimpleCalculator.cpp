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

		// If previous access to the same location has the same value, increment by 1
		auto memAccess = dynamic_cast<MemAccessLabel*>(lab.get());
		if (memAccess) {
			auto addr = memAccess->getAddr();
			if (currentView[tid] <= previousAccessViews[addr][tid]) {
				currentView[tid] = previousAccessViews[addr][tid];
				currentView[tid]++;
			}
			previousAccessViews[addr] = currentView;
		}

		bool syncCurrent =
			// Thread finish label should allways be at the end of the thread
			dynamic_cast<ThreadFinishLabel*>(lab.get())
			// Rel, Acq and SC accesses (ra relation)
			|| ((lab.get()->isAtLeastAcquire() || lab.get()->isAtLeastRelease())
				&& (dynamic_cast<ReadLabel*>(lab.get()) || dynamic_cast<WriteLabel*>(lab.get())));

		bool syncBoth =
			// SC fence (spush), all events before in po must be before,
			// all events after must be after thus synch of current and next event
			(lab.get()->getOrdering() == llvm::AtomicOrdering::SequentiallyConsistent && isFence(lab.get()))
			// Adds synchronization for svo relation
			|| (lab.get()->getOrdering() == llvm::AtomicOrdering::Release && isFence(lab.get()))
			|| (lab.get()->getOrdering() == llvm::AtomicOrdering::Acquire && isFence(lab.get()));

		// Thread start label must allways be before all events
		bool syncNext = dynamic_cast<ThreadStartLabel*>(lab.get());

		if (syncCurrent || syncBoth) {
			if (currentView[tid] <= baseView[tid]) {
				currentView[tid] = baseView[tid];
				currentView[tid] ++;
			}
		}

		hbClocks[lab.get()] = currentView;

		if (syncNext || syncBoth) {
			currentView[tid] ++;
		}

		baseView = currentView;

		llvm::outs() << lab.get()->getPos() << " " << hbClocks[lab.get()] << baseView << " ";
		llvm::outs() <<"\n";

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