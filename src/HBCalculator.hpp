#ifndef __VO_CALCULATOR_HPP__
#define __VO_CALCULATOR_HPP__

#include "Calculator.hpp"
#include "ExecutionGraph.hpp"

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

	void addIntraThreadHB(ExecutionGraph::Thread &labels, Calculator::GlobalRelation &hb);
	void calcMO(Calculator::GlobalRelation &hb, Calculator::GlobalRelation &mo);

	bool isFence(EventLabel *lab);

};

#endif /* __VO_CALCULATOR_HPP__ */
