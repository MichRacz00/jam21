#ifndef __VO_CALCULATOR_HPP__
#define __VO_CALCULATOR_HPP__

#include "Calculator.hpp"
#include "ExecutionGraph.hpp"
#include "SAddr.hpp"
#include <unordered_map>
#include <deque>
#include <set>

class EventLabel;

// Declaration of a hashing function for EventLabel
// which allos EventLabel to be a key in a hash map
namespace std {
    template <>
    struct hash<EventLabel*> {
        size_t operator()(const EventLabel* label) const {
            return reinterpret_cast<size_t>(label);
        }
    };
}

class HBCalculator : public Calculator {

public:
	HBCalculator(ExecutionGraph &g) : Calculator(g) {}

	/* Overrided Calculator methods */

	/* Initialize necessary matrices */
	void initCalc() override;

	/* Performs a step of the LB calculation */
	Calculator::CalculationResult doCalc() override;

	/* The calculator is informed about the removal of some events */
	void removeAfter(const VectorClock &preds) override;

	std::unique_ptr<Calculator> clone(ExecutionGraph &g) const override {
		return std::make_unique<HBCalculator>(g);
	}

private:
	std::unordered_map<EventLabel*, View> hbClocks;

	void calcHB();
	void calcHB(ExecutionGraph::Thread &thread, EventLabel* halt);
	void calcIntraThreadHB(EventLabel* lab, std::deque<EventLabel*> previousLabels);
	void calcMO();

	void addFRtoHB(WriteLabel* labOut, WriteLabel* labIn);
	void updateHBClockChain(std::unordered_map<EventLabel*, View> &newHbClocks, EventLabel* start, View newView);

	View mergeViews(const View a, const View b);
	bool isViewStrictlyGreater(const View a, const View b);

	std::unordered_map<std::string, std::unordered_map<SAddr::Width, int>> raAccessView;

	std::unordered_map<std::string, std::unordered_map<int, int>> currentView;
	std::unordered_map<std::string, std::unordered_map<int, int>> releaseView;
	std::unordered_map<std::string, std::unordered_map<int, int>> acquireView;

	
	void addPoloc(ExecutionGraph::Thread &eventLabels, Calculator::GlobalRelation &hb);
	Calculator::GlobalRelation mergeHBandMO(Calculator::GlobalRelation &hb, Calculator::GlobalRelation &mo);
	void addHBfromInit(Calculator::GlobalRelation &hb);
	void addHBfromMO(Calculator::GlobalRelation &hb, Calculator::GlobalRelation &mo);

	bool isFence(EventLabel *lab);

	void resetViews();

	void calcLabelViews(EventLabel *lab);
	void advanceCurrentView(EventLabel *lab);
	void calcWriteViews(WriteLabel *lab);
	void calcReadViews(ReadLabel *lab);
	void calcFenceViews(FenceLabel *lab);

	std::string makeKey(const EventLabel *lab);

	template <typename K, typename V>
	void printView(const std::unordered_map<K, V> &v);
};

#endif /* __VO_CALCULATOR_HPP__ */
