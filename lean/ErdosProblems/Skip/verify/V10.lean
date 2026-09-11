import ErdosProblems.Skip.LadderT67

open ErdosProblems ErdosProblems.Skip.LadderT67
open Erdos249257 Erdos249257.TotientTailPeriodKiller

-- Band theorems
#print axioms ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_72
#print axioms ErdosProblems.Skip.LadderT67.diagonalKill_band_le_72_explicit
#print axioms ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_78
#print axioms ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_80
#print axioms ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82
#print axioms ErdosProblems.Skip.LadderT67.diagonalKill_band_monotone
#print axioms ErdosProblems.Skip.LadderT67.band_maximal_at_82

-- periodLcm values
#print axioms ErdosProblems.Skip.LadderT67.periodLcm_73_value
#print axioms ErdosProblems.Skip.LadderT67.periodLcm_79_value
#print axioms ErdosProblems.Skip.LadderT67.periodLcm_81_value
#print axioms ErdosProblems.Skip.LadderT67.periodLcm_83_value
#print axioms ErdosProblems.Skip.LadderT67.periodLcm_81_eq_three_mul
#print axioms ErdosProblems.Skip.LadderT67.periodLcm_81_ne_80
#print axioms ErdosProblems.Skip.LadderT67.periodLcm_83_eq_mul
#print axioms ErdosProblems.Skip.LadderT67.periodLcm_83_ne_82

-- Depth floors
#print axioms ErdosProblems.Skip.LadderT67.t73_depth_floor
#print axioms ErdosProblems.Skip.LadderT67.t79_depth_floor
#print axioms ErdosProblems.Skip.LadderT67.t81_depth_floor
#print axioms ErdosProblems.Skip.LadderT67.t83_depth_floor

-- Certificates
#print axioms ErdosProblems.Skip.LadderT67.certifiedKill_diagonal_t73
#print axioms ErdosProblems.Skip.LadderT67.certifiedKill_diagonal_t79
#print axioms ErdosProblems.Skip.LadderT67.certifiedKill_diagonal_t81

-- Negatives
#print axioms ErdosProblems.Skip.LadderT67.not_certifiedKill_diagonal_t73_111
#print axioms ErdosProblems.Skip.LadderT67.not_certifiedKill_diagonal_t73_112
#print axioms ErdosProblems.Skip.LadderT67.not_certifiedKill_diagonal_t79_117
#print axioms ErdosProblems.Skip.LadderT67.not_certifiedKill_diagonal_t79_118
#print axioms ErdosProblems.Skip.LadderT67.not_certifiedKill_diagonal_t79_119
#print axioms ErdosProblems.Skip.LadderT67.not_certifiedKill_diagonal_t81_119
#print axioms ErdosProblems.Skip.LadderT67.t73_not_certifiedKill_at_t71_depth
#print axioms ErdosProblems.Skip.LadderT67.t79_not_certifiedKill_below_117

-- Minimal depths and the two headline negatives
#print axioms ErdosProblems.Skip.LadderT67.t73_minimal_depth
#print axioms ErdosProblems.Skip.LadderT67.t79_minimal_depth
#print axioms ErdosProblems.Skip.LadderT67.t81_minimal_depth
#print axioms ErdosProblems.Skip.LadderT67.ladder_excess_not_monotone
#print axioms ErdosProblems.Skip.LadderT67.rung_depth_not_strictly_increasing
#print axioms ErdosProblems.Skip.LadderT67.ladder_minimal_depths

-- Plateau steps
#print axioms ErdosProblems.Skip.LadderT67.periodLcm_flat_73_78
#print axioms ErdosProblems.Skip.LadderT67.pl80
#print axioms ErdosProblems.Skip.LadderT67.pl82

/-
ADVERSARIAL PROBE.  The reduction to Erdos #249 consumes a COFINAL supply:
  irrational_totient_series_of_lcm_diagonal_certificate_supply
    (hsupply : forall t0, exists t, t0 <= t /\ exists L, certifiedKill (periodLcm t) (periodLcm t) L)
The file proves a bounded band (t <= 82).  If a bounded band sufficed, the
following would typecheck.  It does not, and this is the whole point: the
`sorry`-free corpus cannot close the gap from `t <= 82` to cofinality.
-/
example : (∀ t : ℕ, t ≤ 82 → ∃ L, certifiedKill (periodLcm t) (periodLcm t) L) :=
  ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82

-- The band gives the cofinal supply ONLY for thresholds already below 83.
example (t₀ : ℕ) (h : t₀ ≤ 82) :
    ∃ t, t₀ ≤ t ∧ ∃ L, certifiedKill (periodLcm t) (periodLcm t) L :=
  ⟨t₀, le_refl _, ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82 t₀ h⟩

-- and at t₀ = 83 the file supplies nothing: the statement below is exactly
-- what is missing, and it is NOT proved anywhere in this file.
#check @ErdosProblems.Skip.LadderT67.t83_depth_floor
