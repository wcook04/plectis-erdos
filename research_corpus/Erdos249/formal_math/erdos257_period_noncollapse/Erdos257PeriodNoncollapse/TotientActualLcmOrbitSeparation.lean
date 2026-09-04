import Erdos257PeriodNoncollapse.DiagonalFlexibleOddWindowAffine
import Erdos257PeriodNoncollapse.PivotAntiReconstruction

/-!
# Actual LCM-orbit separation for Erdős #249

The actual centered odd-window state is a finite dyadic approximation to the
LCM-diagonal tail orbit

`R_(2H) - R_H`, where `H = lcm(1, ..., 2^a)`.

This file records the exact approximation identity, its elementary error
bound, and the resulting bridge from a cofinal `1/32` separation of the
actual tail orbit to the landed signed-margin producer.  The separation
supply is deliberately explicit: divisibility of the LCM multipliers, or
irrationality alone, does not force such quantitative anti-concentration.
-/

namespace Erdos257PeriodNoncollapse
namespace DiagonalFreshLossBridge
namespace PowerTwoOddWindowAffine

open TotientTailPeriodKiller

/-- The LCM height used by the power-two endpoint at exponent `a`. -/
def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)

/-- The actual LCM-diagonal tail orbit at exponent `a`. -/
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)

/-- The normalized unreduced raw block at odd rank `q`. -/
noncomputable def actualLcmRawApprox (a q : ℕ) : ℝ :=
  (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) : ℝ) /
    (2 : ℝ) ^ (2 * q + 1)

/-- The elementary error radius for the odd-rank raw approximation. -/
noncomputable def actualLcmRawErrorRadius (a q : ℕ) : ℝ :=
  ((2 * actualLcmHeight a + 2 * q + 3 : ℕ) : ℝ) /
    (2 : ℝ) ^ (2 * q + 1)

/-- The adjacent raw block is the diagonal window numerator plus its terminal
letter. -/
theorem diagonalAdjacentSuffixRawBlock_eq_windowDiscrepancy_add_terminal
    (t m : ℕ) :
    diagonalAdjacentSuffixRawBlock t 0 m =
      windowDiscrepancy (periodLcm t) (periodLcm t) m +
        diagonalWindowIncrement t (m + 1) := by
  unfold diagonalAdjacentSuffixRawBlock
  simp only [zero_add]
  congr 1
  unfold windowDiscrepancy
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun z : ℤ => z * 2 ^ (m - 1 - r))
  unfold diagonalWindowIncrement
  have htop :
      2 * periodLcm t + (1 + r) =
        periodLcm t + periodLcm t + 1 + r := by
    omega
  have hbot : periodLcm t + (1 + r) = periodLcm t + 1 + r := by
    omega
  rw [htop, hbot]

/-- The actual LCM tail orbit is the usual integer translate of the scaled
#249 series orbit. -/
theorem actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix (a : ℕ) :
    actualLcmTailOrbit a =
      (2 : ℝ) ^ actualLcmHeight a *
          ((2 : ℝ) ^ actualLcmHeight a - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) -
        ((totientPrefix (2 * actualLcmHeight a) : ℝ) -
          (totientPrefix (actualLcmHeight a) : ℝ)) := by
  simpa only [actualLcmTailOrbit, two_mul] using
    (tail_diff_eq_scaled_totient_series_sub_prefix
      (actualLcmHeight a) (actualLcmHeight a))

/-- Exact remainder after replacing the actual LCM tail orbit by the odd-rank
raw block.  The terminal raw letter occurs twice in the adjacent block, which
is why it is subtracted from the once-shifted tail difference. -/
theorem actualLcmTailOrbit_sub_rawApprox_eq (a q : ℕ) :
    actualLcmTailOrbit a - actualLcmRawApprox a q =
      (totientTail
            (2 * actualLcmHeight a + (2 * q + 1) + 1) -
          totientTail (actualLcmHeight a + (2 * q + 1) + 1) -
          (diagonalWindowIncrement (2 ^ a) ((2 * q + 1) + 1) : ℝ)) /
        (2 : ℝ) ^ ((2 * q + 1) + 1) := by
  let H := actualLcmHeight a
  let m := 2 * q + 1
  let D := totientTail (H + m + H) - totientTail (H + m)
  let d : ℝ := diagonalWindowIncrement (2 ^ a) (m + 1)
  have hblock :=
    diagonalAdjacentSuffixRawBlock_eq_windowDiscrepancy_add_terminal
      (2 ^ a) m
  have hblockR :
      (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 m : ℝ) =
        (windowDiscrepancy H H m : ℝ) + d := by
    dsimp [H, d]
    exact_mod_cast hblock
  have hwindow0 := tail_diff_eq_windowDiscrepancy_div_add_shifted H H m
  have hwindow :
      totientTail (2 * H) - totientTail H =
        (windowDiscrepancy H H m : ℝ) / 2 ^ m + D / 2 ^ m := by
    dsimp [D]
    simpa only [two_mul] using hwindow0
  have hdelta :
      (deltaTotient H (H + m + 1) : ℝ) = d := by
    dsimp [d]
    unfold deltaTotient diagonalWindowIncrement
    have htop :
        H + m + 1 + H = 2 * periodLcm (2 ^ a) + (m + 1) := by
      dsimp [H, actualLcmHeight]
      omega
    have hbot : H + m + 1 = periodLcm (2 ^ a) + (m + 1) := by
      dsimp [H, actualLcmHeight]
      omega
    rw [htop, hbot]
  have hstep := tail_diff_succ H (H + m)
  rw [hdelta] at hstep
  have hp : (2 : ℝ) ^ m ≠ 0 := by positivity
  have hstep' :
      totientTail (2 * H + m + 1) - totientTail (H + m + 1) =
        2 * D - d := by
    dsimp [D]
    rw [show 2 * H + m + 1 = H + m + 1 + H by omega]
    exact hstep
  have hmain :
      (totientTail (2 * H) - totientTail H) -
          (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 m : ℝ) / 2 ^ m =
        (totientTail (2 * H + m + 1) - totientTail (H + m + 1) - d) /
          2 ^ (m + 1) := by
    rw [hwindow, hblockR, hstep', pow_succ]
    field_simp [hp]
    ring
  simpa [actualLcmTailOrbit, actualLcmRawApprox, H, m, d,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmain

/-- The normalized odd-rank raw block approximates the actual LCM tail orbit
with an explicit elementary error. -/
theorem abs_actualLcmTailOrbit_sub_rawApprox_lt (a q : ℕ) :
    |actualLcmTailOrbit a - actualLcmRawApprox a q| <
      actualLcmRawErrorRadius a q := by
  let H := actualLcmHeight a
  let m := 2 * q + 1
  let D :=
    totientTail (2 * H + m + 1) - totientTail (H + m + 1)
  let d : ℝ := diagonalWindowIncrement (2 ^ a) (m + 1)
  have hD : |D| < ((2 * H + m + 3 : ℕ) : ℝ) := by
    dsimp [D]
    have h := abs_tail_diff_lt H (H + m + 1)
    convert h using 1 <;> push_cast <;> ring
  have hdZ := abs_diagonalWindowIncrement_le (2 ^ a) (m + 1)
  have hd : |d| ≤ ((2 * H + m + 1 : ℕ) : ℝ) := by
    dsimp [d, H]
    exact_mod_cast hdZ
  have hnum : |D - d| < ((4 * H + 2 * m + 4 : ℕ) : ℝ) := by
    calc
      |D - d| ≤ |D| + |d| := abs_sub D d
      _ < ((2 * H + m + 3 : ℕ) : ℝ) +
          ((2 * H + m + 1 : ℕ) : ℝ) := add_lt_add_of_lt_of_le hD hd
      _ = ((4 * H + 2 * m + 4 : ℕ) : ℝ) := by push_cast; ring
  rw [actualLcmTailOrbit_sub_rawApprox_eq]
  change |(D - d) / (2 : ℝ) ^ (m + 1)| < actualLcmRawErrorRadius a q
  rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 ^ (m + 1) by positivity)]
  calc
    |D - d| / (2 : ℝ) ^ (m + 1) <
        ((4 * H + 2 * m + 4 : ℕ) : ℝ) /
          (2 : ℝ) ^ (m + 1) := by
            exact div_lt_div_of_pos_right hnum (by positivity)
    _ = actualLcmRawErrorRadius a q := by
      dsimp [actualLcmRawErrorRadius, H, m]
      push_cast
      rw [show 2 * q + 1 + 1 = (2 * q + 1) + 1 by omega, pow_succ]
      ring

/-- At a power-two endpoint, the normalized raw block is the integral raw
half divided by `4^q`. -/
theorem actualLcmRawApprox_eq_half_div_fourPow
    {a q : ℕ} (ha : 2 ≤ a) :
    actualLcmRawApprox a q =
      ((diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2 : ℤ) : ℝ) /
        (4 : ℝ) ^ q := by
  have heven :=
    diagonalAdjacentSuffixRawBlock_powerTwo_oddDepth_even
      (a := a) (q := q) ha
  have hhalf :
      2 * (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2) =
        diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) :=
    Int.two_mul_ediv_two_of_even heven
  have hhalfR :
      (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) : ℝ) =
        2 *
          ((diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2 : ℤ) : ℝ) := by
    exact_mod_cast hhalf.symm
  have hpow :
      (2 : ℝ) ^ (2 * q + 1) = 2 * (4 : ℝ) ^ q := by
    calc
      (2 : ℝ) ^ (2 * q + 1) = (2 : ℝ) ^ (2 * q) * 2 := by rw [pow_succ]
      _ = ((2 : ℝ) ^ 2) ^ q * 2 := by rw [pow_mul]
      _ = 2 * (4 : ℝ) ^ q := by norm_num; ring
  unfold actualLcmRawApprox
  rw [hhalfR, hpow]
  field_simp [show (4 : ℝ) ^ q ≠ 0 by positivity]

/-- Integer separation of the normalized raw block is exactly what is needed
to force the landed half-word band. -/
theorem halfWordBandAt_of_rawApprox_integerSeparation
    {a q : ℕ} (ha : 2 ≤ a) (hq : 3 ≤ q)
    (hsep : ∀ z : ℤ,
      (1 : ℝ) / 32 ≤ |actualLcmRawApprox a q - (z : ℝ)|) :
    PowerTwoOddHalfWordBandAt a q := by
  apply (halfWordBandAt_iff_state_abs ha hq).2
  by_contra hnot
  have hsmall : |state a q| < edge q := lt_of_not_ge hnot
  let A : ℤ :=
    diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2
  let M : ℤ := (4 : ℤ) ^ q
  let u : ℤ := actualCenteredLift A M
  have hM : 0 < M := by dsimp [M]; positivity
  have hstate : state a q = u := by
    rfl
  rw [hstate] at hsmall
  have hscale : M = 32 * edge q := by
    dsimp [M]
    exact fourPow_eq_thirtyTwo_mul_edge hq
  have hu32 : 32 * |u| < M := by omega
  have hmod : Int.ModEq M u A := by
    exact actualCenteredLift_modEq A M
  obtain ⟨z, hz⟩ := hmod.dvd
  have hzR : (A : ℝ) - (u : ℝ) = (M : ℝ) * (z : ℝ) := by
    exact_mod_cast hz
  have hquotient :
      (A : ℝ) / (M : ℝ) - (z : ℝ) = (u : ℝ) / (M : ℝ) := by
    field_simp [show (M : ℝ) ≠ 0 by positivity]
    nlinarith
  have hratio : |(u : ℝ) / (M : ℝ)| < (1 : ℝ) / 32 := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < (M : ℝ) by exact_mod_cast hM)]
    rw [div_lt_iff₀ (show (0 : ℝ) < (M : ℝ) by exact_mod_cast hM)]
    have hu32R : (32 : ℝ) * |(u : ℝ)| < (M : ℝ) := by
      exact_mod_cast hu32
    nlinarith
  have hraw :
      actualLcmRawApprox a q = (A : ℝ) / (M : ℝ) := by
    simpa [A, M] using actualLcmRawApprox_eq_half_div_fourPow ha
  have hnear :
      |actualLcmRawApprox a q - (z : ℝ)| < (1 : ℝ) / 32 := by
    rw [hraw, hquotient]
    exact hratio
  exact (not_lt_of_ge (hsep z)) hnear

/-- Cofinal quantitative anti-concentration of the actual LCM tail orbit at
the canonical odd ranks. -/
def PowerTwoActualLcmOrbitSeparationSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 2 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ∀ z : ℤ,
      (1 : ℝ) / 32 + actualLcmRawErrorRadius a q ≤
        |actualLcmTailOrbit a - (z : ℝ)|

/-- Actual LCM-orbit separation supplies the exact landed signed-margin
producer. -/
theorem powerTwoActualPenultimateSignedMarginSupply_of_actualLcmOrbitSeparation
    (hsupply : PowerTwoActualLcmOrbitSeparationSupply) :
    PowerTwoActualPenultimateSignedMarginSupply := by
  apply powerTwoActualPenultimateSignedMarginSupply_iff_halfWordBandSupply.mpr
  intro a₀
  obtain ⟨a, q, ha, hdepth, hsep⟩ := hsupply a₀
  have ha2 : 2 ≤ a := (le_max_left 2 a₀).trans ha
  have hcanon : 10 ≤ canonicalAdjacentSuffixDepth (2 ^ a) :=
    canonicalAdjacentSuffixDepth_ten_le _
  have hle := canonicalAdjacentSuffixDepth_le_oddGuarded (2 ^ a)
  have hq : 3 ≤ q := by
    rw [hdepth] at hle
    omega
  have hrawSep : ∀ z : ℤ,
      (1 : ℝ) / 32 ≤ |actualLcmRawApprox a q - (z : ℝ)| := by
    intro z
    by_contra hnot
    have hraw :
        |actualLcmRawApprox a q - (z : ℝ)| < (1 : ℝ) / 32 :=
      lt_of_not_ge hnot
    have herr := abs_actualLcmTailOrbit_sub_rawApprox_lt a q
    have htriangle :
        |actualLcmTailOrbit a - (z : ℝ)| ≤
          |actualLcmTailOrbit a - actualLcmRawApprox a q| +
            |actualLcmRawApprox a q - (z : ℝ)| := by
      calc
        |actualLcmTailOrbit a - (z : ℝ)| =
            |(actualLcmTailOrbit a - actualLcmRawApprox a q) +
              (actualLcmRawApprox a q - (z : ℝ))| := by ring_nf
        _ ≤ |actualLcmTailOrbit a - actualLcmRawApprox a q| +
            |actualLcmRawApprox a q - (z : ℝ)| := abs_add_le _ _
    have hlt :
        |actualLcmTailOrbit a - (z : ℝ)| <
          (1 : ℝ) / 32 + actualLcmRawErrorRadius a q := by
      linarith
    exact (not_lt_of_ge (hsep z)) hlt
  have hband :=
    halfWordBandAt_of_rawApprox_integerSeparation ha2 hq hrawSep
  exact ⟨a, q, ha, hdepth, hband⟩

/-- The orbit-separation supply therefore closes the existing Erdős #249
endpoint. -/
theorem irrational_totientSeries_of_actualLcmOrbitSeparationSupply
    (hsupply : PowerTwoActualLcmOrbitSeparationSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  exact irrational_totientSeries_of_actualPenultimateSignedMarginSupply
    (powerTwoActualPenultimateSignedMarginSupply_of_actualLcmOrbitSeparation
      hsupply)

#print axioms abs_actualLcmTailOrbit_sub_rawApprox_lt
#print axioms powerTwoActualPenultimateSignedMarginSupply_of_actualLcmOrbitSeparation
#print axioms irrational_totientSeries_of_actualLcmOrbitSeparationSupply

end PowerTwoOddWindowAffine
end DiagonalFreshLossBridge
end Erdos257PeriodNoncollapse
