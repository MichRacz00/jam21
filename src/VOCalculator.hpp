#ifndef __PSC_CALCULATOR_HPP__
#define __PSC_CALCULATOR_HPP__

#include "Calculator.hpp"

class VOCalculator : public Calculator {

public:
	VOCalculator(ExecutionGraph &g) : Calculator(g) {}

	/* Overrided Calculator methods */

	/* Initialize necessary matrices */
	void initCalc() override;

	/* Performs a step of the LB calculation */
	Calculator::CalculationResult doCalc() override;

	/* The calculator is informed about the removal of some events */
	void removeAfter(const VectorClock &preds) override;

	std::unique_ptr<Calculator> clone(ExecutionGraph &g) const override {
		return std::make_unique<VOCalculator>(g);
	}

private:
    void initRaRelation();
    std::vector<std::unique_ptr<EventLabel>> getPrevMany(const EventLabel *lab, int n);
    void calcRaRelation();
    void calcSvoRelation();
    void calcSpushRelation();
    void calcVolintRelation();
	void calcVvoRelation();
	void calcVoRelation();

    bool isFence(EventLabel *lab);
	bool isRead(EventLabel *lab);
	bool isWrite(EventLabel *lab);
};

#endif /* __PSC_CALCULATOR_HPP__ */
