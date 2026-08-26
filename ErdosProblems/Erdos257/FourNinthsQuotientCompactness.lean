import ErdosProblems.Erdos257.FourNinthsQuotientDefect
import Erdos249257.TwentyOneQuotientCompactness

/-!
# A compactness consumer for the executable 4/9 quotient defect

The quotient-defect bridge turns a dyadic bound on the executable remainder into a finite
Mersenne support whose scaled error from `4/9` is `O(2^d+d)` at endpoint `2d`.  Division by
`4^d` makes that error vanish.  Closedness of the Mersenne achievement set then supplies
the exact target.

This file deliberately states the remaining producer: the all-depth nonnegative dyadic
window is not proved here.
-/

namespace ErdosProblems.Erdos257

namespace FourNinthsQuotientCompactness

open Erdos257PeriodNoncollapse
open FourNinthsQuotientDefect
open Filter Set

/-- Fractional part of the scaled `4/9` target at diagonal depth `d`. -/
def fourNinthsTargetFraction (d : ℕ) : ℚ :=
  ((4 ^ (d + 1) % 9 : ℕ) : ℚ) / 9

/-- Exact quotient/fraction decomposition of `4^d * (4/9)`. -/
theorem scaled_four_ninths_eq_target_add_fraction (d : ℕ) :
    (2 : ℚ) ^ (2 * d) * (4 / 9 : ℚ) =
      (fourNinthsQuotientTarget d : ℚ) + fourNinthsTargetFraction d := by
  have hdecomp := Nat.mod_add_div (4 ^ (d + 1)) 9
  have hdecompQ :
      ((4 ^ (d + 1) % 9 : ℕ) : ℚ) +
          9 * ((4 ^ (d + 1) / 9 : ℕ) : ℚ) =
        (4 : ℚ) ^ (d + 1) := by
    exact_mod_cast hdecomp
  have hscale : (2 : ℚ) ^ (2 * d) * 4 = (4 : ℚ) ^ (d + 1) := by
    rw [pow_mul, pow_succ]
    norm_num
    ring
  unfold fourNinthsQuotientTarget fourNinthsTargetFraction
  rw [div_eq_mul_inv, ← mul_assoc, hscale]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  linarith

theorem fourNinthsTargetFraction_nonneg (d : ℕ) :
    0 ≤ fourNinthsTargetFraction d := by
  unfold fourNinthsTargetFraction
  positivity

theorem fourNinthsTargetFraction_lt_one (d : ℕ) :
    fourNinthsTargetFraction d < 1 := by
  unfold fourNinthsTargetFraction
  have hmod : 4 ^ (d + 1) % 9 < 9 := Nat.mod_lt _ (by omega)
  exact (div_lt_one (by norm_num : (0 : ℚ) < 9)).2 (by exact_mod_cast hmod)

/-- Natural form of the quotient defect, used only after quotient admissibility is known. -/
def fourNinthsDiagonalNaturalDefect (d : ℕ) : ℕ :=
  fourNinthsQuotientTarget d - fourNinthsDiagonalPrefixQuotient d

/-- The natural defect is the nonnegative executable remainder. -/
theorem fourNinthsDiagonalNaturalDefect_eq_toNat_rho
    (d : ℕ) (hnonneg : 0 ≤ (fourNinthsDiagonalState d).rho) :
    fourNinthsDiagonalNaturalDefect d =
      (fourNinthsDiagonalState d).rho.toNat := by
  have hadm :=
    (fourNinthsDiagonalState_rho_nonnegative_iff_prefixQuotient_le d).mp hnonneg
  have hbridge := fourNinthsDiagonalState_rho_eq_target_sub_prefixQuotient d
  have hcast :
      ((fourNinthsDiagonalNaturalDefect d : ℕ) : ℤ) =
        (fourNinthsDiagonalState d).rho := by
    unfold fourNinthsDiagonalNaturalDefect
    rw [Nat.cast_sub hadm]
    omega
  have htoNat : (((fourNinthsDiagonalState d).rho.toNat : ℕ) : ℤ) =
      (fourNinthsDiagonalState d).rho := Int.toNat_of_nonneg hnonneg
  exact_mod_cast hcast.trans htoNat.symm

/-- Exact scaled error identity for any admissible 4/9 quotient row. -/
theorem scaled_localMersennePrefixValue_sub_four_ninths
    {D : Finset ℕ} {d : ℕ}
    (hD : ∀ a ∈ D, 2 ≤ a)
    (hadm : localPrefixQuotient D (2 * d) ≤ fourNinthsQuotientTarget d) :
    (2 : ℚ) ^ (2 * d) *
        (localMersennePrefixValue D - (4 / 9 : ℚ)) =
      localFractionMass D (2 * d) -
        ((fourNinthsQuotientTarget d - localPrefixQuotient D (2 * d) : ℕ) : ℚ) -
          fourNinthsTargetFraction d := by
  have hscale := scaled_localMersennePrefixValue
    (D := D) (M := 2 * d) hD
  have htarget := scaled_four_ninths_eq_target_add_fraction d
  have hdefect :
      (((fourNinthsQuotientTarget d - localPrefixQuotient D (2 * d) : ℕ) : ℚ)) =
        (fourNinthsQuotientTarget d : ℚ) -
          (localPrefixQuotient D (2 * d) : ℚ) := by
    rw [Nat.cast_sub hadm]
  rw [mul_sub, hscale, htarget, hdefect]
  ring

/-- Explicit approximation bound for an admissible finite 4/9 quotient row. -/
theorem abs_localMersennePrefixValue_sub_four_ninths_le
    {D : Finset ℕ} {d : ℕ}
    (hD : ∀ a ∈ D, 2 ≤ a)
    (hadm : localPrefixQuotient D (2 * d) ≤ fourNinthsQuotientTarget d) :
    |((localMersennePrefixValue D : ℚ) : ℝ) - (4 : ℝ) / 9| ≤
      (((fourNinthsQuotientTarget d - localPrefixQuotient D (2 * d) : ℕ) +
          D.card + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * d) := by
  have hid := scaled_localMersennePrefixValue_sub_four_ninths hD hadm
  have hF0 := localFractionMass_nonneg (D := D) (M := 2 * d) hD
  have hFcard := localFractionMass_le_card (D := D) (M := 2 * d) hD
  have htarget0 := fourNinthsTargetFraction_nonneg d
  have htarget1 := fourNinthsTargetFraction_lt_one d
  have hpowQ : (0 : ℚ) < (2 : ℚ) ^ (2 * d) := by positivity
  have herror :
      localMersennePrefixValue D - (4 / 9 : ℚ) =
        (localFractionMass D (2 * d) -
            ((fourNinthsQuotientTarget d - localPrefixQuotient D (2 * d) : ℕ) : ℚ) -
              fourNinthsTargetFraction d) / (2 : ℚ) ^ (2 * d) := by
    rw [eq_div_iff hpowQ.ne']
    simpa [mul_comm] using hid
  have habsQ :
      |localMersennePrefixValue D - (4 / 9 : ℚ)| ≤
        (((fourNinthsQuotientTarget d - localPrefixQuotient D (2 * d) : ℕ) +
            D.card + 1 : ℕ) : ℚ) / (2 : ℚ) ^ (2 * d) := by
    rw [herror, abs_div, abs_of_pos hpowQ]
    apply div_le_div_of_nonneg_right _ hpowQ.le
    rw [abs_le]
    constructor <;> push_cast <;> linarith
  have habsR :
      (((|localMersennePrefixValue D - (4 / 9 : ℚ)| : ℚ) : ℝ)) ≤
        (((((fourNinthsQuotientTarget d -
              localPrefixQuotient D (2 * d) : ℕ) + D.card + 1 : ℕ) : ℚ) /
            (2 : ℚ) ^ (2 * d) : ℚ) : ℝ) := by
    exact_mod_cast habsQ
  simpa using habsR

/-- **Executable compactness consumer.**  If the actual 4/9 diagonal stays in its
nonnegative dyadic quotient window, its finite selected supports converge to `4/9`. -/
theorem four_ninths_mem_mersenneAchievementSet_of_diagonal_window
    (hwindow : ∀ d : ℕ,
      0 ≤ (fourNinthsDiagonalState d).rho ∧
        (fourNinthsDiagonalState d).rho ≤ (2 : ℤ) ^ d) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet := by
  classical
  let y : ℕ → ℝ := fun d ↦
    ((localMersennePrefixValue (fourNinthsDiagonalSupport (d + 1)) : ℚ) : ℝ)
  have hdist :
      Tendsto (fun d : ℕ ↦ dist (y d) (4 / 9 : ℝ)) atTop (nhds 0) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun _ ↦ dist_nonneg)
      (Filter.Eventually.of_forall fun d ↦ ?_)
      (tendsto_twentyOne_evenQuotientWindow_error.comp
        (by simpa [Nat.add_comm] using tendsto_add_atTop_nat 1))
    rw [Real.dist_eq]
    let D := fourNinthsDiagonalSupport (d + 1)
    have hD : ∀ a ∈ D, 2 ≤ a := fun a ha ↦
      (fourNinthsDiagonalSupport_rank_bounds ha).1
    have hnonneg := (hwindow (d + 1)).1
    have hadm : localPrefixQuotient D (2 * (d + 1)) ≤
        fourNinthsQuotientTarget (d + 1) := by
      rw [localPrefixQuotient_fourNinthsDiagonalSupport]
      exact (fourNinthsDiagonalState_rho_nonnegative_iff_prefixQuotient_le
        (d + 1)).mp hnonneg
    calc
      |y d - (4 / 9 : ℝ)| ≤
          (((fourNinthsQuotientTarget (d + 1) -
                localPrefixQuotient D (2 * (d + 1)) : ℕ) +
              D.card + 1 : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * (d + 1)) := by
        exact abs_localMersennePrefixValue_sub_four_ninths_le hD hadm
      _ ≤
          (((2 ^ (d + 1) + (2 * (d + 1) + 1) : ℕ) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * (d + 1)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hdefect :
            fourNinthsQuotientTarget (d + 1) -
                localPrefixQuotient D (2 * (d + 1)) ≤ 2 ^ (d + 1) := by
          rw [localPrefixQuotient_fourNinthsDiagonalSupport]
          change fourNinthsDiagonalNaturalDefect (d + 1) ≤ 2 ^ (d + 1)
          rw [fourNinthsDiagonalNaturalDefect_eq_toNat_rho _ hnonneg]
          rw [← Int.ofNat_le]
          simpa [Int.toNat_of_nonneg hnonneg] using (hwindow (d + 1)).2
        have hcard : D.card ≤ d + 2 := by
          have hsubset : D ⊆ Finset.range (d + 2) := by
            intro a ha
            exact (Finset.mem_filter.mp ha).1
          simpa [D] using Finset.card_le_card hsubset
        exact_mod_cast (by omega :
          (fourNinthsQuotientTarget (d + 1) -
                localPrefixQuotient D (2 * (d + 1))) + D.card + 1 ≤
            2 ^ (d + 1) + (2 * (d + 1) + 1))
  have hy : Tendsto y atTop (nhds (4 / 9 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.2 hdist
  have hyMem : ∀ d : ℕ, y d ∈ mersenneAchievementSet := by
    intro d
    let D := fourNinthsDiagonalSupport (d + 1)
    let A : Set ℕ := ↑D
    have hA0 : 0 ∉ A := by
      intro hzero
      have hbounds := fourNinthsDiagonalSupport_rank_bounds (d := d + 1)
        (a := 0) (by simpa [A, D] using hzero)
      omega
    refine ⟨A, hA0, ?_⟩
    rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [y, D, A, localMersennePrefixValue_eq_finiteErdosSum]
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall hyMem)

/-- The existing selected-landing rank producer supplies the lower side of the window.
Thus only the dyadic upper side is additionally needed by this compactness endpoint. -/
theorem four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_upperWindow
    (hrank : FourNinthsSelectedLandingRankProducer)
    (hupper : ∀ d : ℕ,
      (fourNinthsDiagonalState d).rho ≤ (2 : ℤ) ^ d) :
    (4 / 9 : ℝ) ∈ mersenneAchievementSet := by
  apply four_ninths_mem_mersenneAchievementSet_of_diagonal_window
  intro d
  exact ⟨fourNinthsDiagonal_nonnegative_of_selectedLandingRankProducer hrank d,
    hupper d⟩

#print axioms scaled_localMersennePrefixValue_sub_four_ninths
#print axioms abs_localMersennePrefixValue_sub_four_ninths_le
#print axioms four_ninths_mem_mersenneAchievementSet_of_diagonal_window
#print axioms
  four_ninths_mem_mersenneAchievementSet_of_rankProducer_of_upperWindow

end FourNinthsQuotientCompactness

end ErdosProblems.Erdos257
