#ifndef __VO_CALCULATOR_HPP__
#define __VO_CALCULATOR_HPP__

#include "Calculator.hpp"
#include "ExecutionGraph.hpp"

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

    // Calculations of visibility orders
    Calculator::GlobalRelation calcVvoRelation();
    Calculator::GlobalRelation calcVoRelation();

    // Helper relations for co-jom
    Calculator::GlobalRelation calcCoww();
    Calculator::GlobalRelation calcCowr();
    Calculator::GlobalRelation calcCorw();
    Calculator::GlobalRelation calcCorr();
    Calculator::GlobalRelation calcCojom();

    std::vector<std::unique_ptr<EventLabel>> getPrevMany(EventLabel &lab, int n);
    void calcTransC(ExecutionGraph::RelationId relationId);

    std::vector<std::unique_ptr<EventLabel>> calcTransC(const EventLabel *lab, ExecutionGraph::RelationId relationId);

    void tryAddEdge(Event a, Event b, Calculator::GlobalRelation *relation);

    Calculator::GlobalRelation merge(std::vector<Calculator::GlobalRelation> relations);

    void calcCojomRelation();

    std::vector<Event*> getAdj(Event lab, ExecutionGraph::RelationId relationId);

    std::vector<Event> getAdj(Event event, Calculator::GlobalRelation relation);

    bool tryAddNode(Event event, Calculator::GlobalRelation *relation);

    bool isFence(EventLabel *lab);
    bool isRead(EventLabel *lab);
	bool isWrite(EventLabel *lab);
};

#endif /* __VO_CALCULATOR_HPP__ */
