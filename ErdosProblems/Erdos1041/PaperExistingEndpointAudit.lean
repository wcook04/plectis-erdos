import ErdosProblems.Erdos1041.CriticalTwoRootProximity
import ErdosProblems.Erdos1041.NewtonFlowTrajectory
import ErdosProblems.Erdos1041.CubicQuotientFiberCase
import ErdosProblems.Erdos1041.PrimitiveQuinticInteriorTail
import ErdosProblems.Erdos1041.SharpCollinearChebyshev

/-!
# Exact existing endpoints for eight displayed paper results

This is an audit driver, not a new proof and not a Comparator wrapper.
The six distinct declarations below cover eight rows: the two value-equation
and two collision-locus rows are repeated between the papers. The local
compiler was unavailable during preparation of this return. Run this file
under the pinned toolchain to obtain fresh axiom output.

Do not add near-matching selectors or geometric consumers to this list as
though they formalised the whole remaining paper theorem.
-/

#check ErdosProblems.Erdos1041.exists_two_roots_dist_sum_le_two_mul_geomMean
#print axioms ErdosProblems.Erdos1041.exists_two_roots_dist_sum_le_two_mul_geomMean

#check ErdosProblems.Erdos1041.newtonFlow_real_value_hasDerivAt
#print axioms ErdosProblems.Erdos1041.newtonFlow_real_value_hasDerivAt

#check ErdosProblems.Erdos1041.translated_samePositiveRay_parameterization
#print axioms ErdosProblems.Erdos1041.translated_samePositiveRay_parameterization

#check ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound
#print axioms ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound

#check ErdosProblems.Erdos1041.primitiveInterior_exists_two_tailEnergy_lt_one
#print axioms ErdosProblems.Erdos1041.primitiveInterior_exists_two_tailEnergy_lt_one

#check ErdosProblems.Erdos1041.cubic_has_safe_root_spoke
#print axioms ErdosProblems.Erdos1041.cubic_has_safe_root_spoke
