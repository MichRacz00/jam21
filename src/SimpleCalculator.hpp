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

class SimpleCalculator : public Calculator {

public:
	SimpleCalculator(ExecutionGraph &g) : Calculator(g) {}

	/* Overrided Calculator methods */

	/* Initialize necessary matrices */
	void initCalc() override;

	/* Performs a step of the LB calculation */
	Calculator::CalculationResult doCalc() override;

	/* The calculator is informed about the removal of some events */
	void removeAfter(const VectorClock &preds) override;

	std::unique_ptr<Calculator> clone(ExecutionGraph &g) const override {
		return std::make_unique<SimpleCalculator>(g);
	}

private:
	std::unordered_map<EventLabel*, View> voClocks;
	std::vector<std::vector<EventLabel*>> linearisations;

	void calcClocks() {
		auto &g = getGraph();
		for (auto &t : g.getThreadList()) {
			calcClocks(t);
		}
	}

	void calcClocks(ExecutionGraph::Thread &t) {
		auto &lastLab = t.back();
		calcClocks(t, lastLab.get());
	}

	void calcClocks(ExecutionGraph::Thread &thread, EventLabel* halt);

	void addToLinearisations(EventLabel* lab);

	bool isFence(EventLabel *lab);
};

#endif /* __SIMPLE_CALCULATOR_HPP__ */
