#ifndef __VO_CALCULATOR_HPP__
#define __VO_CALCULATOR_HPP__

#include "Calculator.hpp"
#include "ExecutionGraph.hpp"

class CojomCalculator : public Calculator {

public:
	CojomCalculator(ExecutionGraph &g) : Calculator(g) {}

	/* Overrided Calculator methods */

	/* Initialize necessary matrices */
	void initCalc() override;

	/* Performs a step of the LB calculation */
	Calculator::CalculationResult doCalc() override;

	/* The calculator is informed about the removal of some events */
	void removeAfter(const VectorClock &preds) override;

	std::unique_ptr<Calculator> clone(ExecutionGraph &g) const override {
		return std::make_unique<CojomCalculator>(g);
	}

private:
    // ------ Functions to calculate relations ------
    // Relations that capture rel/acq memory events
    Calculator::GlobalRelation calcRaRelation();
    Calculator::GlobalRelation calcSvoRelation();

    // Relations that capture synchronization effects of volotile
    // memory accesses
    Calculator::GlobalRelation calcSpushRelation();
    Calculator::GlobalRelation calcVolintRelation();

    // Other helper relations
    Calculator::GlobalRelation calcPolocRelation();
    Calculator::GlobalRelation calcPushRelation();
    Calculator::GlobalRelation calcPushtoRelation();
    Calculator::GlobalRelation calcRfRelation();

    // Calculations of visibility orders
    Calculator::GlobalRelation calcVvoRelation();
    Calculator::GlobalRelation calcVoRelation();

    // Helper relations for co-jom
    Calculator::GlobalRelation calcCoww(GlobalRelation vo);
    Calculator::GlobalRelation calcCowr(GlobalRelation vo);
    Calculator::GlobalRelation calcCorw(GlobalRelation vo);
    Calculator::GlobalRelation calcCorr();
    Calculator::GlobalRelation calcCojom();

    // ------ Helper functions on relations ------
    std::vector<std::unique_ptr<EventLabel>> getPrevMany(EventLabel &lab, int n);
    std::vector<Event> getAdj(Event event, Calculator::GlobalRelation relation);

    Calculator::GlobalRelation merge(std::vector<Calculator::GlobalRelation> relations);
    Calculator::GlobalRelation calcComp(Calculator::GlobalRelation relA, Calculator::GlobalRelation relB);

    void calcTransC(Calculator::GlobalRelation *relation);
    std::vector<std::unique_ptr<EventLabel>> calcTransC(const EventLabel *lab, Calculator::GlobalRelation *relation);

    void tryAddEdge(Event a, Event b, Calculator::GlobalRelation *relation);
    bool tryAddNode(Event event, Calculator::GlobalRelation *relation);

    bool isFence(EventLabel *lab);
};

#endif /* __VO_CALCULATOR_HPP__ */
