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
	std::unordered_map<EventLabel*, View> moClocks;
	std::unordered_map<SAddr, std::vector<WriteLabel*>> mo;
	std::unordered_map<SAddr, std::vector<EventLabel*>> corr;
	std::vector<EventLabel*> domainPushto;

	void calcHB();
	void calcHB(ExecutionGraph::Thread &thread, EventLabel* halt);
	void calcIntraThreadHB(EventLabel* lab, std::deque<EventLabel*> previousLabels);
	bool calcFR();
	void calcMO();
	void calcCORR();
	bool checkMoCoherence(WriteLabel* start, WriteLabel* end);

	EventLabel* getMinimalWrite(EventLabel* m, SAddr addr);

	Calculator::GlobalRelation createPushto(std::vector<EventLabel*> domain);
	std::vector<Calculator::GlobalRelation> calcAllLinearisations(GlobalRelation rel);

	void addFRtoHB(WriteLabel* labOut, WriteLabel* labIn);
	void updateHBClockChain(std::unordered_map<EventLabel*, View> &newHbClocks, EventLabel* start, View newView);
	std::unordered_map<SAddr, std::set<EventLabel*>> getInitReadersList();

	View mergeViews(const View a, const View b);
	bool isViewStrictlyGreater(const View a, const View b);
	bool isViewStrictlySmaller(const View a, const View b);
	bool isFence(EventLabel *lab);

	void resetViews();

	Calculator::GlobalRelation cojom;
};

#endif /* __VO_CALCULATOR_HPP__ */
