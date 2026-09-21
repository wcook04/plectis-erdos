import Erdos249257.HalfCylinderFullShellSeamBridge
import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.DyadicPrefixCompression

/-!
Paper-form restatement of the whole asserted environment

* `record:257bm-c19` (`paper/reasoning-parts/erdos257/a257_front.tex:4373`),
  "An eventual nonnegative margin suffices".

Fix a positive depth `k` and put `D = G ∩ {2,…,k}`
(`paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc`).  The environment
asserts, in order:

1. the displayed equivalence `r_k(1/2) < 2^(-(k+1)) ↔ F_k(J) ≥ 0` for some
   `J ≥ 0` (`paper_eventual_nonnegative_margin_equivalence`);
2. the normalised value
   `2^(-J) F_k(J) = ∑_{i=1}^{J} c_D(k+1+i) 2^(-i) - C_D(k)`
   (`paper_frozen_margin_normalised_value`);
3. that this normalised expression is nondecreasing in `J`
   (`paper_frozen_margin_normalised_monotone`);
4. that its limit is `1 - 2^(k+1) r_k(1/2)`
   (`paper_frozen_margin_normalised_tendsto`);
5. that the limit is positive exactly under the strict dyadic inequality
   (`paper_frozen_margin_limit_pos_iff`);
6. that at positive `k` oddness of the reduced excess numerator excludes
   equality at zero (`paper_greedyHalfRemainder_ne_dyadicCap`);
7. the tail bound `∑_{r≥1} c_D(m+r) 2^(-r) ≤ m + 2`
   (`paper_coeffTail_le_index_add_two`);
8. the effective sufficient test: with `η = 1 - 2^(k+1) r_k(1/2) > 0`,
   `(k+J+3) 2^(-J) < η` forces `F_k(J) > 0`
   (`paper_effective_horizon_test`);
9. that `η` is rational for the finite support `D`
   (`paper_eta_hasRationalValue`).

Paper notation: `F_k(J) = greedyHalfFrozenMargin k J`,
`r_k(1/2) = greedyMersenneRemainder (1/2 : ℝ) k`,
`2^(-(k+1)) = halfDyadicCap (k+1)`, `c_D(n) = supportCoeff ↑D n`,
`C_D(N) = mobiusCenteredHalfCarry ↑D N`, `D = halfGreedyPrefixSupport k`, and
`∑_{r≥1} c_D(m+r) 2^(-r) = binaryCoeffTail (supportCoeff ↑D) m`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Filter
open Erdos249257 Erdos249257.HalfCarryReachability
open Erdos249257.HalfCylinderFiniteShadow
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## The finite support `D = G ∩ {2,…,k}` -/

/-- The paper's finite support `D = G ∩ {2,…,k}` is the tree's
`halfGreedyPrefixSupport k`.  Rank `0` is never greedily selected and rank `1`
is skipped for the half target, so cutting `G` at `k` already lands inside
`{2,…,k}`. -/
theorem paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc (k : ℕ) :
    (↑(halfGreedyPrefixSupport k) : Set ℕ) =
      greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Icc 2 k := by
  have hpre : (↑(halfGreedyPrefixSupport k) : Set ℕ) =
      greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Iic k := by
    have h := primitivePrefix_greedyMersenneSupport_eq_prefixRat (1 / 2 : ℚ) k
    have h' : primitivePrefix (greedyMersenneSupport (1 / 2 : ℝ)) k =
        (↑(halfGreedyPrefixSupport k) : Set ℕ) := by
      simpa [halfGreedyPrefixSupport] using h
    rw [← h']
    rfl
  have h2 : ∀ a ∈ greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Iic k, 2 ≤ a := by
    rintro a ⟨ha, hak⟩
    by_contra hlt
    push_neg at hlt
    have hmem : a ∈ (↑(halfGreedyPrefixSupport k) : Set ℕ) := by
      rw [hpre]; exact ⟨ha, hak⟩
    interval_cases a
    · exact (zero_not_mem_greedyMersenneSupport _) ha
    · exact one_not_mem_halfGreedyPrefixSupport k (by simpa using hmem)
  ext a
  constructor
  · intro ha
    have ha' : a ∈ greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Iic k := by
      rw [hpre] at ha; exact ha
    exact ⟨ha'.1, Set.mem_Icc.mpr ⟨h2 a ha', ha'.2⟩⟩
  · rintro ⟨ha, hIcc⟩
    rw [hpre]
    exact ⟨ha, Set.mem_Iic.mpr (Set.mem_Icc.mp hIcc).2⟩

/-! ## The displayed equivalence -/

/-- At positive depth the greedy half remainder never lands exactly on the
next dyadic cap: the reduced excess numerator is odd, hence nonzero.  This is
the environment's clause "at positive `k`, oddness of the reduced excess
numerator excludes equality at zero". -/
theorem paper_greedyHalfRemainder_ne_dyadicCap {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k ≠ halfDyadicCap (k + 1) := by
  intro heq
  have hL : 0 < halfGreedyPrefixDenominator k := Rat.den_pos (halfGreedyPrefixRat k)
  have hcapR : (((1 / (2 : ℚ) ^ (k + 1)) : ℚ) : ℝ) = halfDyadicCap (k + 1) := by
    unfold halfDyadicCap
    push_cast
    rw [div_pow]
    norm_num
  have hhalf : (((1 / 2 : ℚ)) : ℝ) = (1 / 2 : ℝ) := by norm_num
  have hratEq : greedyMersenneRemainderRat (1 / 2 : ℚ) k = 1 / (2 : ℚ) ^ (k + 1) := by
    have hcast : ((greedyMersenneRemainderRat (1 / 2 : ℚ) k : ℚ) : ℝ)
        = (((1 / (2 : ℚ) ^ (k + 1)) : ℚ) : ℝ) := by
      rw [cast_greedyMersenneRemainderRat, hcapR, hhalf]
      exact heq
    exact_mod_cast hcast
  have hsub : Rat.divInt (halfGreedyResidualDisplayedNumerator k)
      ((2 * halfGreedyPrefixDenominator k : ℕ) : ℤ) - 1 / (2 : ℚ) ^ (k + 1) = 0 := by
    rw [← greedyHalfRemainderRat_eq_displayed_divInt, hratEq, sub_self]
  rw [divInt_sub_nextDyadic_eq_excess_divInt _ k _ hL, Rat.divInt_eq_div] at hsub
  have hdenPos : 0 < 2 ^ (k + 1) * halfGreedyPrefixDenominator k :=
    Nat.mul_pos (by positivity) hL
  have hden : ((((2 ^ (k + 1) * halfGreedyPrefixDenominator k : ℕ) : ℤ)) : ℚ) ≠ 0 := by
    simp only [ne_eq, Int.cast_natCast, Nat.cast_eq_zero]
    omega
  rcases div_eq_zero_iff.mp hsub with hz | hz
  · have hE : halfGreedyNextDyadicExcessNumerator k = 0 := by
      have hzInt :
          nextDyadicExcessIntNumerator (halfGreedyResidualDisplayedNumerator k) k
            (halfGreedyPrefixDenominator k) = 0 := by exact_mod_cast hz
      simpa [halfGreedyNextDyadicExcessNumerator] using hzInt
    have hodd := halfGreedyNextDyadicExcessNumerator_odd hk
    rw [hE] at hodd
    simp at hodd
  · exact hden hz

/-- Paper display of `record:257bm-c19`: for a positive depth `k`,

`r_k(1/2) < 2^(-(k+1))  ↔  F_k(J) ≥ 0 for some J ≥ 0`. -/
theorem paper_eventual_nonnegative_margin_equivalence {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) ↔
      ∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J := by
  rw [exists_greedyHalfFrozenMargin_nonneg_iff_excess_neg k hk]
  constructor
  · intro hlt
    have hE := (greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos k).1 hlt.le
    obtain ⟨m, hm⟩ := halfGreedyNextDyadicExcessNumerator_odd hk
    omega
  · intro hE
    exact lt_of_le_of_ne
      ((greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos k).2 hE.le)
      (paper_greedyHalfRemainder_ne_dyadicCap hk)

/-! ## The normalised margin: value, monotonicity, limit -/

/-- The tree's finite coefficient window written with the paper's index
range `i = 1,…,J`. -/
private theorem finiteCoeffWindow_eq_sum_Icc (A : Set ℕ) (n J : ℕ) :
    finiteCoeffWindow A n J =
      ∑ i ∈ Finset.Icc 1 J, (supportCoeff A (n + i) : ℝ) / (2 : ℝ) ^ i := by
  induction J with
  | zero => simp [finiteCoeffWindow]
  | succ J ih =>
      have hstep : finiteCoeffWindow A n (J + 1) =
          finiteCoeffWindow A n J +
            (supportCoeff A (n + J + 1) : ℝ) / (2 : ℝ) ^ (J + 1) := by
        simp [finiteCoeffWindow, Finset.sum_range_succ]
      rw [hstep, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ J + 1),
        show n + J + 1 = n + (J + 1) from by omega]

/-- The environment's normalised value:

`2^(-J) F_k(J) = ∑_{i=1}^{J} c_D(k+1+i) 2^(-i) - C_D(k)`. -/
theorem paper_frozen_margin_normalised_value (k J : ℕ) :
    (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J =
      (∑ i ∈ Finset.Icc 1 J,
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + i) : ℝ) /
            (2 : ℝ) ^ i) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
  have hid := greedyHalfFrozenMargin_cast_eq_pow_mul_window_sub_carry k J
  have hwin := finiteCoeffWindow_eq_sum_Icc
    (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J
  have hpow : ((2 : ℝ) ^ J) ≠ 0 := by positivity
  rw [hid, hwin]
  field_simp

/-- The environment's monotonicity clause: the normalised expression, not
necessarily `F_k(J)` itself, is nondecreasing in `J`. -/
theorem paper_frozen_margin_normalised_monotone (k : ℕ) :
    Monotone (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J) := by
  apply monotone_nat_of_le_succ
  intro J
  simp only [paper_frozen_margin_normalised_value]
  have hle : (∑ i ∈ Finset.Icc 1 J,
        (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + i) : ℝ) /
          (2 : ℝ) ^ i) ≤
      ∑ i ∈ Finset.Icc 1 (J + 1),
        (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + i) : ℝ) /
          (2 : ℝ) ^ i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (by omega))
    intro i _ _
    positivity
  linarith

/-- The finite-support Lambert identity in carry coordinates: the quantity
`η = 1 - 2^(k+1) r_k(1/2)` is the complete coefficient tail of `D` after row
`k+1` minus the centred carry `C_D(k)`. -/
theorem paper_eta_eq_coeffTail_sub_carry (k : ℕ) :
    1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k =
      binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
  have hrem := greedyHalfRemainder_eq_integerCarry_sub_coeffTail_div_pow k
  have hcarry : halfGreedyPrefixIntegerCarry k =
      mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k + 1 := by
    dsimp [halfGreedyPrefixIntegerCarry, mobiusCenteredHalfCarry, integerHalfCarry]
    ring
  have htail : halfGreedyPrefixCoeffTail k =
      binaryCoeffTail
        (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1) := rfl
  have hpow : ((2 : ℝ) ^ (k + 1)) ≠ 0 := by positivity
  rw [hrem, hcarry, htail]
  push_cast
  field_simp
  ring

/-- The environment's limit clause: the normalised expression converges to
`1 - 2^(k+1) r_k(1/2)`. -/
theorem paper_frozen_margin_normalised_tendsto (k : ℕ) :
    Tendsto (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J)
      atTop
      (nhds (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)) := by
  have hfun : (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J) =
      fun J : ℕ ↦
        finiteCoeffWindow (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J -
          (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
    funext J
    rw [greedyHalfFrozenMargin_cast_eq_pow_mul_window_sub_carry k J]
    have hpow : ((2 : ℝ) ^ J) ≠ 0 := by positivity
    field_simp
  rw [hfun, paper_eta_eq_coeffTail_sub_carry k]
  exact (tendsto_finiteCoeffWindow_atTop
    (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1)).sub tendsto_const_nhds

/-- The environment's positivity clause: the limit is positive exactly under
the strict dyadic inequality `r_k(1/2) < 2^(-(k+1))`. -/
theorem paper_frozen_margin_limit_pos_iff (k : ℕ) :
    0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k ↔
      greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hcap : halfDyadicCap (k + 1) = 1 / (2 : ℝ) ^ (k + 1) := by
    unfold halfDyadicCap
    rw [div_pow]
    norm_num
  rw [hcap, lt_div_iff₀ hpow]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ## The quantitative effective test -/

/-- The environment's tail bound `∑_{r≥1} c_D(m+r) 2^(-r) ≤ m + 2`.  It holds
for every support, in particular for the finite support `D`: the divisor count
`c_A(n)` never exceeds `n`, and a coefficient sequence of at most linear growth
has this uniform dyadic tail bound. -/
theorem paper_coeffTail_le_index_add_two (A : Set ℕ) (m : ℕ) :
    binaryCoeffTail (supportCoeff A) m ≤ (m : ℝ) + 2 :=
  binaryCoeffTail_le (supportCoeff A) (supportCoeff_le_self A) m

/-- The environment's effective sufficient test.  Write
`η = 1 - 2^(k+1) r_k(1/2) > 0`.  Since the omitted tail after row `k+1+J`
is at most `k+J+3`, the inequality `(k+J+3) 2^(-J) < η` forces
`F_k(J) > 0`. -/
theorem paper_effective_horizon_test (k J : ℕ)
    (heta : 0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)
    (htest : ((k + J + 3 : ℕ) : ℝ) / (2 : ℝ) ^ J <
      1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) :
    0 < greedyHalfFrozenMargin k J := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
  have hsplit := binaryCoeffTail_eq_finiteCoeffWindow_add_shiftedTail
    (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J
  have hU : binaryCoeffTail
      (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1 + J) ≤
      ((k + J + 3 : ℕ) : ℝ) := by
    have h := paper_coeffTail_le_index_add_two
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + J)
    have hc : ((k + 1 + J : ℕ) : ℝ) + 2 = ((k + J + 3 : ℕ) : ℝ) := by
      push_cast; ring
    linarith [h, hc.le, hc.ge]
  have htestMul : ((k + J + 3 : ℕ) : ℝ) <
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) *
        (2 : ℝ) ^ J := (div_lt_iff₀ hpow).mp htest
  have hwc : finiteCoeffWindow (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J -
      (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) =
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) -
        binaryCoeffTail
            (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1 + J) /
          (2 : ℝ) ^ J := by
    rw [paper_eta_eq_coeffTail_sub_carry k]
    linarith [hsplit]
  have hexp : (2 : ℝ) ^ J *
      ((1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) -
        binaryCoeffTail
            (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1 + J) /
          (2 : ℝ) ^ J) =
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) *
          (2 : ℝ) ^ J -
        binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1 + J) := by
    field_simp
  have hfinal : (0 : ℝ) < (greedyHalfFrozenMargin k J : ℝ) := by
    rw [greedyHalfFrozenMargin_cast_eq_pow_mul_window_sub_carry k J, hwc, hexp]
    linarith
  exact_mod_cast hfinal

/-- The environment's closing clause: for the finite support `D`, the value
`η = 1 - 2^(k+1) r_k(1/2)` is rational, so the test above is effective.  It is
the negated reduced dyadic excess ratio `-E_k / D_k`. -/
theorem paper_eta_hasRationalValue (k : ℕ) :
    HasRationalValue
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) := by
  have hred := halfGreedyPrefix_reducedTailGapCoordinates k
  refine ⟨-halfGreedyNextDyadicExcessNumerator k,
    halfGreedyPrefixDenominator k, hred.1, ?_⟩
  have hgap := hred.2
  rw [show k + 1 - 1 = k from by omega] at hgap
  rw [paper_eta_eq_coeffTail_sub_carry k]
  push_cast
  rw [neg_div]
  linarith

#print axioms paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc
#print axioms paper_greedyHalfRemainder_ne_dyadicCap
#print axioms paper_eventual_nonnegative_margin_equivalence
#print axioms paper_frozen_margin_normalised_value
#print axioms paper_frozen_margin_normalised_monotone
#print axioms paper_eta_eq_coeffTail_sub_carry
#print axioms paper_frozen_margin_normalised_tendsto
#print axioms paper_frozen_margin_limit_pos_iff
#print axioms paper_coeffTail_le_index_add_two
#print axioms paper_effective_horizon_test
#print axioms paper_eta_hasRationalValue

end ErdosProblems.Erdos257.PaperCompleteR21
