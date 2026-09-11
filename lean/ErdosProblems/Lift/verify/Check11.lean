import ErdosProblems.Lift.InduceLaw

open ErdosProblems.Lift.InduceLaw

#print axioms genWindowDiscrepancy_congr_diag
#print axioms genCertifiedKill_congr_diag
#print axioms diagWindow_disjoint
#print axioms diagWindow_disjoint_of_three_le
#print axioms diagWindow_inter_two
#print axioms diagWindow_inter_two_pow
#print axioms genWindowDiscrepancy_eq_blockSum_sub
#print axioms blockSum_two_mul_congr_diag
#print axioms double_rung_residual
#print axioms not_genCertifiedKill_of_eq_zero
#print axioms no_window_local_lift
#print axioms certified_cell_blind_at_rung
#print axioms genWindowDiscrepancy_point_mass
#print axioms rung_value_unconstrained
#print axioms double_rung_value_unconstrained

-- Statement audit: print the fully-elaborated types of the two headline theorems.
#check @no_window_local_lift
#check @rung_value_unconstrained
#check @certified_cell_blind_at_rung

-- Does the file prove ANY new fact about Nat.totient itself?
-- Sanity probe: the "counterexample" f in no_window_local_lift is not a totient.
-- Confirm the negative is only about arbitrary ℤ-sequences by checking that
-- diagWindow at p=2 is NOT disjoint (so the p>=3 hypothesis is load-bearing).
example : ¬ Disjoint (diagWindow 4 4) (diagWindow (2 * 4) 4) := by decide
