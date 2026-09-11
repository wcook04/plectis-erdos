import ErdosProblems.Lift.AngleA3

open ErdosProblems.Lift.AngleA3 Erdos249257.TotientTailPeriodKiller

#print axioms windowDiscrepancy_zero_shift
#print axioms windowDiscrepancy_add_shift
#print axioms windowDiscrepancy_mul_shift
#print axioms windowDiscrepancy_ladder_diagonal
#print axioms windowDiscrepancy_ladder_offDiagonal
#print axioms windowDiscrepancy_double_offDiagonal
#print axioms windowDiscrepancy_double_diagonal
#print axioms certifiedKill_of_two_pow_dvd
#print axioms certifiedKill_lift_of_common_dvd
#print axioms certifiedKill_ladder_lift
#print axioms certifiedKill_double_lift
#print axioms certifiedKill_two_two_five
#print axioms windowDiscrepancy_two_four_five
#print axioms windowDiscrepancy_two_two_five
#print axioms windowDiscrepancy_four_two_five_emod
#print axioms not_certifiedKill_four_two_five
#print axioms annihilation_is_the_decomposition
#print axioms periodLcm_three
#print axioms periodLcm_four
#print axioms not_certifiedKill_six_six_six
#print axioms certifiedKill_twelve_six_six
#print axioms certifiedKill_periodLcm_offDiagonal_at_four
#print axioms windowDiscrepancy_six_values
#print axioms two_dvd_correction_six
#print axioms not_four_dvd_correction_six
#print axioms not_certifiedKill_diagonal_at_eight_depth14
#print axioms certifiedKill_offDiagonal_at_eight_depth14
#print axioms windowDiscrepancy_emod_pow
#print axioms certifiedKill_of_endpoint
#print axioms certifiedKill_of_endpoint'

-- Adversarial probe 1: is `certifiedKill_ladder_lift` satisfiable at all when δ is
-- forced to be the true symmetric size of the correction?  Show the hypotheses are
-- contradictory once δ ≥ 2^(L-1).
example {k H L : ℕ} {e : ℤ} (hL : 1 ≤ L)
    (hlow : ((H : ℤ) + ((k + 1) * H : ℕ) + L + 2) + 2 ^ (L - 1)
        < windowDiscrepancy H H L % 2 ^ L)
    (hhigh : windowDiscrepancy H H L % 2 ^ L
        < 2 ^ L - (((H : ℤ) + ((k + 1) * H : ℕ) + L + 2) + 2 ^ (L - 1))) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  have hsplit : (2 : ℤ) ^ (m + 1) = 2 ^ m + 2 ^ m := by
    rw [pow_succ]; ring
  simp only [Nat.add_sub_cancel] at hlow hhigh
  have hM : (0 : ℤ) ≤ (H : ℤ) + ((k + 1) * H : ℕ) + (m + 1 : ℕ) + 2 := by positivity
  linarith

-- Adversarial probe 2: the lift law is a *consequence of* nothing more than the exact
-- decomposition; the hypothesis pins the new residue completely.  Confirm that the
-- hypothesis set implies the conclusion's residue is determined, i.e. the "lift" carries
-- no arithmetic that the direct evaluation at the new scale does not.
example (k H L : ℕ) :
    windowDiscrepancy ((k + 1) * H) H L % 2 ^ L
      = (windowDiscrepancy H H L
          + ∑ i ∈ Finset.range k, windowDiscrepancy H ((2 + i) * H) L) % 2 ^ L := by
  rw [windowDiscrepancy_ladder_offDiagonal]
