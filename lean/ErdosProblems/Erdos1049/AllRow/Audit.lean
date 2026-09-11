import ErdosProblems.Erdos1049.AllRow.Smoke

/-!
# Explicit transitive axiom audit for the complete all-row authoring chain

Every command below was executed by the focused all-row audit on 2026-09-09.
The usual Lean/Mathlib logical foundations appear; no additional project axiom
or placeholder axiom is used. Private lemmas are audited transitively.
-/

#print axioms ErdosProblems.Erdos1049.AllRow.S
#print axioms ErdosProblems.Erdos1049.AllRow.constantCoeff_q_pow
#print axioms ErdosProblems.Erdos1049.AllRow.Agree
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.refl
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.of_eq
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.symm
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.trans
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.mono
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.add
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.sub
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.mul
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.pow
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.sum
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.shift
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.backward
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.X_pow_zero
#print axioms ErdosProblems.Erdos1049.AllRow.Agree.inv
#print axioms ErdosProblems.Erdos1049.AllRow.geom
#print axioms ErdosProblems.Erdos1049.AllRow.geom_zero
#print axioms ErdosProblems.Erdos1049.AllRow.geom_succ
#print axioms ErdosProblems.Erdos1049.AllRow.geom_at_zero
#print axioms ErdosProblems.Erdos1049.AllRow.map_geom
#print axioms ErdosProblems.Erdos1049.AllRow.one_sub_mul_geom
#print axioms ErdosProblems.Erdos1049.AllRow.geom_agree_inverse
#print axioms ErdosProblems.Erdos1049.AllRow.associated_above
#print axioms ErdosProblems.Erdos1049.AllRow.associated_congr
#print axioms ErdosProblems.Erdos1049.AllRow.rowExponent
#print axioms ErdosProblems.Erdos1049.AllRow.two_mul_triangle
#print axioms ErdosProblems.Erdos1049.AllRow.rowExponent_zero
#print axioms ErdosProblems.Erdos1049.AllRow.rowExponent_column
#print axioms ErdosProblems.Erdos1049.AllRow.rowExponent_succ
#print axioms ErdosProblems.Erdos1049.AllRow.rowExponent_ge_depth
#print axioms ErdosProblems.Erdos1049.AllRow.backward_sum
#print axioms ErdosProblems.Erdos1049.AllRow.finiteRatio
#print axioms ErdosProblems.Erdos1049.AllRow.finiteUnit
#print axioms ErdosProblems.Erdos1049.AllRow.finiteTail
#print axioms ErdosProblems.Erdos1049.AllRow.transition
#print axioms ErdosProblems.Erdos1049.AllRow.state
#print axioms ErdosProblems.Erdos1049.AllRow.constantCoeff_finiteRatio
#print axioms ErdosProblems.Erdos1049.AllRow.constantCoeff_finiteUnit
#print axioms ErdosProblems.Erdos1049.AllRow.finiteTail_succ
#print axioms ErdosProblems.Erdos1049.AllRow.finiteTail_state_succ
#print axioms ErdosProblems.Erdos1049.AllRow.finiteTail_difference
#print axioms ErdosProblems.Erdos1049.AllRow.state_difference
#print axioms ErdosProblems.Erdos1049.AllRow.finite_row_factorisation
#print axioms ErdosProblems.Erdos1049.AllRow.constantCoeff_state
#print axioms ErdosProblems.Erdos1049.AllRow.finite_row_initial
#print axioms ErdosProblems.Erdos1049.AllRow.ratioPolynomial
#print axioms ErdosProblems.Erdos1049.AllRow.gradePolynomial
#print axioms ErdosProblems.Erdos1049.AllRow.gradePolynomial_C
#print axioms ErdosProblems.Erdos1049.AllRow.gradePolynomial_X
#print axioms ErdosProblems.Erdos1049.AllRow.coeff_gradePolynomial
#print axioms ErdosProblems.Erdos1049.AllRow.ratioPolynomial_coeff_zero
#print axioms ErdosProblems.Erdos1049.AllRow.finiteRatio_eq_eval
#print axioms ErdosProblems.Erdos1049.AllRow.eval_ratioPolynomial
#print axioms ErdosProblems.Erdos1049.AllRow.eval_ratioPolynomial_agree
#print axioms ErdosProblems.Erdos1049.AllRow.finiteUnit_agree_source
#print axioms ErdosProblems.Erdos1049.AllRow.finiteTail_agree_source
#print axioms ErdosProblems.Erdos1049.AllRow.zero_ratio_fraction
#print axioms ErdosProblems.Erdos1049.AllRow.sourceGrade
#print axioms ErdosProblems.Erdos1049.AllRow.grade_ratioPolynomial_zero
#print axioms ErdosProblems.Erdos1049.AllRow.grade_ratioPolynomial_pos
#print axioms ErdosProblems.Erdos1049.AllRow.grade_ratioPolynomial_agree
#print axioms ErdosProblems.Erdos1049.AllRow.source_tail_initial
#print axioms ErdosProblems.Erdos1049.AllRow.sourceTailCoefficient
#print axioms ErdosProblems.Erdos1049.AllRow.sourceTailCoefficient_zero
#print axioms ErdosProblems.Erdos1049.AllRow.sourceTailCoefficient_pos
#print axioms ErdosProblems.Erdos1049.AllRow.sourceTailCoefficient_above
#print axioms ErdosProblems.Erdos1049.AllRow.sum_sourceTailCoefficient
#print axioms ErdosProblems.Erdos1049.AllRow.moment_agree_finite_tails
#print axioms ErdosProblems.Erdos1049.AllRow.coeff_transformed_eq_tail_sum
#print axioms ErdosProblems.Erdos1049.AllRow.coeff_transformed_below
#print axioms ErdosProblems.Erdos1049.AllRow.coeff_transformed_first
#print axioms ErdosProblems.Erdos1049.zudilinRowInitialMonomial_all
#print axioms ErdosProblems.Erdos1049.order_zudilinTransformedNormalizedMoment_all
#print axioms ErdosProblems.Erdos1049.zudilinSharpHankelOrderAndCoeff_all
#print axioms ErdosProblems.Erdos1049.order_zudilinNormalizedHankelDet_all
#print axioms ErdosProblems.Erdos1049.leadingCoeff_zudilinNormalizedHankelDet_all
#print axioms ErdosProblems.Erdos1049.coeff_zudilinNormalizedHankelDet_all_rat
#print axioms ErdosProblems.Erdos1049.zudilinNormalizedHankelDet_ne_zero_all
