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
				// memory location was not yet accessed since last synchronization
				currentVoView = lastCommonView;
			} else {
				// ther was already an access to this memory location
				currentVoView = lastPerLocView[addr];
			}

			advanceNow = true;
		}

		auto readLab = dynamic_cast<ReadLabel*>(lab.get());
		if (readLab) {
			auto writeLab = g.getEventLabel(readLab->getRf());
			if (voClocks[writeLab].empty()) {
				calcClocks(g.getThreadList()[writeLab->getThread()], writeLab);
			}
			currentVoView.update(voClocks[writeLab]);
			currentVoView[writeLab->getThread()] ++;
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
			// Synchronization, merge all relaxed per loc vo views
			for (auto pair : lastPerLocView) {
				currentVoView.update(pair.second);
			}
			lastCommonView = currentVoView;
			lastPerLocView.clear();
		}

		llvm::outs() << lab.get()->getPos() << voClocks[lab.get()] << "\n";

		if (lab.get() == halt) return;
	}
}

void SimpleCalculator::addToLinearisations(EventLabel* lab) {
	// If there are no linearisations, trivially create the single one
	if (linearisations.empty()) {
		std::vector<EventLabel*> initLin;
		initLin.push_back(lab);
		linearisations.push_back(initLin);
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