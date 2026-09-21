import ErdosProblems.Erdos269.PaperExactDenominatorR13
import ErdosProblems.Erdos269.PaperFixedStartResidueR14

/-!
# Axiom audit for the exact-denominator and fixed-start paper statements

This target keeps the new statement checks together with the pre-existing
running-LCM identity used by both papers.
-/

#print axioms ErdosProblems.Erdos269.smoothPrefixLcm_eq_threePrimeHeight
#print axioms ErdosProblems.Erdos269.PaperR13.exact_denominators_and_minimal_clearing
#print axioms ErdosProblems.Erdos269.PaperR13.scaled_state_is_integer_iff_firstClearingIndex_le
#print axioms ErdosProblems.Erdos269.PaperR13.clearingCondition_iff_max
#print axioms ErdosProblems.Erdos269.PaperR13.firstClearingIndex_spec
#print axioms ErdosProblems.Erdos269.PaperR13.firstClearingIndex_minimal
#print axioms ErdosProblems.Erdos269.PaperR13.firstClearingIndex_le_sufficient
#print axioms ErdosProblems.Erdos269.PaperR14.eventually_fixedStartResidue_formula
#print axioms ErdosProblems.Erdos269.PaperR14.fixedStartResidue_ratio_tendsto
#print axioms ErdosProblems.Erdos269.PaperR14.eventually_fixedStartResidue_eq_tail_of_integral
