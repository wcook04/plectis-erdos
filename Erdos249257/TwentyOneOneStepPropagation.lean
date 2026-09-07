import Erdos249257.TwentyOneQuotientGreedy

/-!
# One-step propagation at `1 / 21`

This module records exact finite identities for extending a retained lower
support by one quotient row.  It does not assert that suitable rows occur
cofinally.
-/

namespace Erdos249257

open Filter Set

/-- The next binary digit of the scaled target `2^M / 21`. -/
def twentyOneTargetBit (M : ℕ) : ℕ :=
  2 * (2 ^ M % 21) / 21

theorem twentyOneTargetBit_le_one (M : ℕ) :
    twentyOneTargetBit M ≤ 1 := by
  unfold twentyOneTargetBit
  have hmod : 2 ^ M % 21 < 21 := Nat.mod_lt _ (by omega)
  have hlt : 2 * (2 ^ M % 21) / 21 < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by omega)).2
    omega
  omega

/-- Exact one-bit cocycle for the denominator-`21` quotient target. -/
theorem twentyOneQuotientTarget_succ (M : ℕ) :
    twentyOneQuotientTarget (M + 1) =
      2 * twentyOneQuotientTarget M + twentyOneTargetBit M := by
  have hpow : 2 ^ (M + 1) = 2 * 2 ^ M := by rw [pow_succ']
  have hdecomp := Nat.mod_add_div (2 ^ M) 21
  have hscaled :
      2 * 2 ^ M =
        2 * (2 ^ M % 21) + 21 * (2 * (2 ^ M / 21)) := by
    omega
  unfold twentyOneQuotientTarget twentyOneTargetBit
  rw [hpow, hscaled,
    Nat.add_mul_div_left (2 * (2 ^ M % 21)) (2 * (2 ^ M / 21))
      (by omega)]
  omega

/-- A quotient row with terminal defect `s` is exact when its quotient and
the defect partition the scaled target. -/
def TwentyOneQRowExact (D : Finset ℕ) (M s : ℕ) : Prop :=
  localPrefixQuotient D M + s = twentyOneQuotientTarget M

/-- The part of a finite support retained below a cutoff. -/
def twentyOneRetainedLowerPrefix (D : Finset ℕ) (R : ℕ) : Finset ℕ :=
  D.filter fun d ↦ d ≤ R

/-- The doubled terminal defect available before the next quotient bit is
processed. -/
def twentyOneSuffixReservoir (s : ℕ) : ℕ :=
  2 * s

/-- The divisor contribution made by a retained prefix at the next row. -/
def twentyOneBorrowContribution (D : Finset ℕ) (M : ℕ) : ℕ :=
  endpointDivisorContribution D (M + 1)

/-- Exact one-step cocycle.  The left side is the next prefix quotient plus
the reservoir and target bit; the right side is the next target plus the
divisor contribution. -/
theorem twentyOne_qRow_cocycle
    {D : Finset ℕ} {M s : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : TwentyOneQRowExact D M s) :
    localPrefixQuotient D (M + 1) +
        (twentyOneSuffixReservoir s + twentyOneTargetBit M) =
      twentyOneQuotientTarget (M + 1) +
        twentyOneBorrowContribution D M := by
  unfold TwentyOneQRowExact at hrow
  unfold twentyOneSuffixReservoir twentyOneBorrowContribution
  rw [localPrefixQuotient_succ hD, twentyOneQuotientTarget_succ]
  omega

/-- If the real Mersenne prefix is still below `1/21`, the one-step divisor
contribution cannot exhaust the reservoir and the new target bit. -/
theorem twentyOne_borrowContribution_le_reservoir_add_bit_of_prefix_le
    {D : Finset ℕ} {M s : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : TwentyOneQRowExact D M s)
    (hsafe : localMersennePrefixValue D ≤ (1 / 21 : ℚ)) :
    twentyOneBorrowContribution D M ≤
      twentyOneSuffixReservoir s + twentyOneTargetBit M := by
  have hnext := localPrefixQuotient_le_twentyOneTarget_of_prefix_le
    (D := D) (M := M + 1) hD hsafe
  have hcocycle := twentyOne_qRow_cocycle hD hrow
  omega

/-- A successful borrow leaves an exact next-row terminal defect. -/
theorem twentyOne_qRowExact_succ_of_borrow_le
    {D : Finset ℕ} {M s : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d)
    (hrow : TwentyOneQRowExact D M s)
    (hborrow : twentyOneBorrowContribution D M ≤
      twentyOneSuffixReservoir s + twentyOneTargetBit M) :
    TwentyOneQRowExact D (M + 1)
      (twentyOneSuffixReservoir s + twentyOneTargetBit M -
        twentyOneBorrowContribution D M) := by
  unfold TwentyOneQRowExact
  have hcocycle := twentyOne_qRow_cocycle hD hrow
  omega

/-- Failure of the one-step borrow forces a genuine finite overshoot, but
the overshoot is at most linear in the row depth after binary scaling. -/
theorem twentyOne_failedBorrow_prefix_interval
    {D : Finset ℕ} {M s : ℕ}
    (hM : 2 ≤ M)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < M)
    (hrow : TwentyOneQRowExact D M s)
    (hfail : twentyOneSuffixReservoir s + twentyOneTargetBit M <
      twentyOneBorrowContribution D M) :
    (1 / 21 : ℚ) < localMersennePrefixValue D ∧
      localMersennePrefixValue D ≤
        (1 / 21 : ℚ) + (M - 2 : ℚ) / (2 : ℚ) ^ M := by
  have hDtwo : ∀ d ∈ D, 2 ≤ d := fun d hd ↦ (hD d hd).1
  have hcocycle := twentyOne_qRow_cocycle hDtwo hrow
  have hoverNat :
      twentyOneQuotientTarget (M + 1) <
        localPrefixQuotient D (M + 1) := by
    omega
  have hgapNat :
      localPrefixQuotient D (M + 1) -
          twentyOneQuotientTarget (M + 1) ≤ D.card := by
    have hc : twentyOneBorrowContribution D M ≤ D.card := by
      unfold twentyOneBorrowContribution endpointDivisorContribution
      exact Finset.card_filter_le _ _
    omega
  have hcard : D.card + 2 ≤ M := by
    have hsubset : D ⊆ Finset.Icc 2 (M - 1) := by
      intro d hd
      simp only [Finset.mem_Icc]
      have hdlt := (hD d hd).2
      exact ⟨(hD d hd).1, by omega⟩
    have hcardLe : D.card ≤ M - 2 := by
      calc
        D.card ≤ (Finset.Icc 2 (M - 1)).card := Finset.card_le_card hsubset
        _ = M - 2 := by simp; omega
    omega
  have hscale := scaled_localMersennePrefixValue
    (D := D) (M := M + 1) hDtwo
  have htarget := scaled_one_div_twenty_one_eq_target_add_fraction (M + 1)
  have hF0 := localFractionMass_nonneg (D := D) (M := M + 1) hDtwo
  have hFcard := localFractionMass_le_card (D := D) (M := M + 1) hDtwo
  have hrho0 := twentyOneTargetFraction_nonneg (M + 1)
  have hrho1 := twentyOneTargetFraction_lt_one (M + 1)
  have hpowPos : (0 : ℚ) < (2 : ℚ) ^ (M + 1) := by positivity
  have hscaledEq :
      (2 : ℚ) ^ (M + 1) *
          (localMersennePrefixValue D - (1 / 21 : ℚ)) =
        ((localPrefixQuotient D (M + 1) : ℚ) -
            twentyOneQuotientTarget (M + 1)) +
          (localFractionMass D (M + 1) -
            twentyOneTargetFraction (M + 1)) := by
    rw [mul_sub, hscale, htarget]
    ring
  have hgapQ :
      (1 : ℚ) ≤ (localPrefixQuotient D (M + 1) : ℚ) -
        twentyOneQuotientTarget (M + 1) := by
    have hsucc : twentyOneQuotientTarget (M + 1) + 1 ≤
        localPrefixQuotient D (M + 1) := hoverNat
    have hcastSucc :
        ((twentyOneQuotientTarget (M + 1) + 1 : ℕ) : ℚ) ≤
          (localPrefixQuotient D (M + 1) : ℚ) := by exact_mod_cast hsucc
    push_cast at hcastSucc
    linarith
  have hgapUpperQ :
      (localPrefixQuotient D (M + 1) : ℚ) -
          twentyOneQuotientTarget (M + 1) ≤ D.card := by
    rw [← Nat.cast_sub hoverNat.le]
    exact_mod_cast hgapNat
  have hscaledPos :
      0 < (2 : ℚ) ^ (M + 1) *
        (localMersennePrefixValue D - (1 / 21 : ℚ)) := by
    rw [hscaledEq]
    linarith
  have hlower : (1 / 21 : ℚ) < localMersennePrefixValue D := by
    have hdiff : 0 < localMersennePrefixValue D - (1 / 21 : ℚ) := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    linarith
  have hscaledUpper :
      (2 : ℚ) ^ (M + 1) *
          (localMersennePrefixValue D - (1 / 21 : ℚ)) ≤
        2 * (M - 2 : ℚ) := by
    rw [hscaledEq]
    have hcardQ : (D.card : ℚ) + 2 ≤ M := by exact_mod_cast hcard
    linarith
  refine ⟨hlower, ?_⟩
  have hpowM : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
  have hpowSucc : (2 : ℚ) ^ (M + 1) = 2 * (2 : ℚ) ^ M := by
    rw [pow_succ']
  rw [hpowSucc] at hscaledUpper
  have hdiffUpper :
      localMersennePrefixValue D - (1 / 21 : ℚ) ≤
        (M - 2 : ℚ) / (2 : ℚ) ^ M := by
    apply (le_div_iff₀ hpowM).2
    nlinarith
  linarith

/-- There are failed exact one-step borrows at arbitrarily large row depths.
The finite supports may be unrelated from one depth to the next. -/
def TwentyOneCofinalFailedBorrows : Prop :=
  ∀ R : ℕ, ∃ M : ℕ, ∃ D : Finset ℕ, ∃ s : ℕ,
    max R 2 ≤ M ∧
    (∀ d ∈ D, 2 ≤ d ∧ d < M) ∧
    TwentyOneQRowExact D M s ∧
    twentyOneSuffixReservoir s + twentyOneTargetBit M <
      twentyOneBorrowContribution D M

/-- Cofinal failure of the exact one-step borrow already puts `1/21` in the
closed Mersenne achievement set.  No compatibility between the finite
supports is needed. -/
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalFailedBorrows
    (hcofinal : TwentyOneCofinalFailedBorrows) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  classical
  choose M D s hM hD hrow hfail using hcofinal
  let y : ℕ → ℝ := fun R => ((localMersennePrefixValue (D R) : ℚ) : ℝ)
  have hMtwo : ∀ R : ℕ, 2 ≤ M R := by
    intro R
    exact (le_max_right R 2).trans (hM R)
  have hMtop : Tendsto M atTop atTop := by
    exact tendsto_atTop_mono
      (fun R => (le_max_left R 2).trans (hM R)) tendsto_id
  have hbound : ∀ R : ℕ,
      |y R - (1 : ℝ) / 21| ≤
        ((M R + 1 : ℕ) : ℝ) / (2 : ℝ) ^ M R := by
    intro R
    have hinter := twentyOne_failedBorrow_prefix_interval
      (hMtwo R) (hD R) (hrow R) (hfail R)
    have hnonneg : 0 ≤ y R - (1 : ℝ) / 21 := by
      dsimp [y]
      rw [sub_nonneg]
      have hlow : (((1 / 21 : ℚ)) : ℝ) ≤
          ((localMersennePrefixValue (D R) : ℚ) : ℝ) := by
        exact_mod_cast (le_of_lt hinter.1)
      push_cast at hlow
      linarith
    rw [abs_of_nonneg hnonneg]
    have hupper :
        y R - (1 : ℝ) / 21 ≤
          ((M R : ℝ) - 2) / (2 : ℝ) ^ M R := by
      have hinterR :
          ((localMersennePrefixValue (D R) : ℚ) : ℝ) ≤
            (1 : ℝ) / 21 +
              ((M R : ℝ) - 2) / (2 : ℝ) ^ M R := by
        have hQ : ((localMersennePrefixValue (D R) : ℚ) : ℝ) ≤
            (((1 / 21 : ℚ) + ((M R : ℚ) - 2) / (2 : ℚ) ^ M R : ℚ) : ℝ) := by
          exact_mod_cast hinter.2
        push_cast at hQ
        linarith
      dsimp [y]
      linarith
    calc
      y R - (1 : ℝ) / 21 ≤
          ((M R : ℝ) - 2) / (2 : ℝ) ^ M R := hupper
      _ ≤ ((M R + 1 : ℕ) : ℝ) / (2 : ℝ) ^ M R := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        push_cast
        linarith
  have hy : Tendsto y atTop (nhds ((1 : ℝ) / 21)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have habs : Tendsto (fun R : ℕ => |y R - (1 : ℝ) / 21|)
        atTop (nhds 0) := by
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun R => abs_nonneg _
      · exact Filter.Eventually.of_forall hbound
      · exact tendsto_nat_succ_div_two_pow_zero.comp hMtop
    simpa [Real.norm_eq_abs] using habs
  have hyMem : ∀ R : ℕ, y R ∈ mersenneAchievementSet := by
    intro R
    let A : Set ℕ := ↑(D R)
    have hA0 : 0 ∉ A := by
      intro hzero
      have := (hD R 0 (by simpa [A] using hzero)).1
      omega
    refine ⟨A, hA0, ?_⟩
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [y, localMersennePrefixValue_eq_finiteErdosSum]
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall hyMem)

/-- If `1/21` is absent from the Mersenne achievement set, failed exact
one-step borrows cannot occur at unbounded row depths. -/
theorem not_cofinalFailedBorrows_of_one_div_twenty_one_not_mem
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    ¬ TwentyOneCofinalFailedBorrows := by
  intro hcofinal
  exact hnot
    (one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalFailedBorrows
      hcofinal)

/-- Under nonmembership, every sufficiently deep exact retained-prefix row
has enough reservoir and target bit to pay its next divisor contribution. -/
theorem eventually_borrowContribution_le_of_one_div_twenty_one_not_mem
    (hnot : (1 / 21 : ℝ) ∉ mersenneAchievementSet) :
    ∃ R : ℕ, ∀ M : ℕ, ∀ D : Finset ℕ, ∀ s : ℕ,
      max R 2 ≤ M →
      (∀ d ∈ D, 2 ≤ d ∧ d < M) →
      TwentyOneQRowExact D M s →
      twentyOneBorrowContribution D M ≤
        twentyOneSuffixReservoir s + twentyOneTargetBit M := by
  have hncofinal :=
    not_cofinalFailedBorrows_of_one_div_twenty_one_not_mem hnot
  by_contra hrepair
  apply hncofinal
  intro R
  push_neg at hrepair
  obtain ⟨M, D, s, hM, hD, hrow, hfail⟩ := hrepair R
  exact ⟨M, D, s, hM, hD, hrow, by omega⟩

#print axioms twentyOne_qRow_cocycle
#print axioms twentyOne_borrowContribution_le_reservoir_add_bit_of_prefix_le
#print axioms twentyOne_failedBorrow_prefix_interval
#print axioms
  one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalFailedBorrows
#print axioms
  eventually_borrowContribution_le_of_one_div_twenty_one_not_mem

end Erdos249257
