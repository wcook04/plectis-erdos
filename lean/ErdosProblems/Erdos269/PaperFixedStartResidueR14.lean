import ErdosProblems.Erdos269.PaperR7WindowResults
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The fixed-start residue limit from the long paper

For a fixed multiplier `B` and starting scale `lo`, the paper studies the
least positive residue of the actual window forcing modulo the actual window
product.  This file proves its eventual exact formula and limiting proportion.
The proof includes the delicate integral case: the finite quotients approach
`B X_lo` strictly from below, so their floors stabilise at `ceil (B X_lo) - 1`.
-/

namespace ErdosProblems.Erdos269.PaperR14

open Filter
open scoped Topology
open PaperR7

/-- Euclidean division written in the least-positive-residue convention. -/
theorem leastPositiveResidue_neg_eq_floor (C : ℕ) (hC : 0 < C) (x : ℤ) :
    (leastPositiveResidue C (-x) : ℤ) =
      (C : ℤ) * (⌊(x : ℝ) / (C : ℝ)⌋ + 1) - x := by
  let q : ℤ := ⌊(x : ℝ) / (C : ℝ)⌋
  let c : ℤ := (C : ℤ) * (q + 1) - x
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have hfloor := Int.floor_le ((x : ℝ) / (C : ℝ))
  have hlt := Int.lt_floor_add_one ((x : ℝ) / (C : ℝ))
  have hxlt : (x : ℝ) < (q : ℝ) * (C : ℝ) + C := by
    have := (div_lt_iff₀ hCR).mp hlt
    dsimp [q] at this ⊢
    push_cast at this ⊢
    nlinarith
  have hqle : (q : ℝ) * (C : ℝ) ≤ x := by
    exact (le_div_iff₀ hCR).mp hfloor
  have hcposR : (0 : ℝ) < (c : ℝ) := by
    dsimp [c]
    push_cast
    linarith
  have hcleR : (c : ℝ) ≤ C := by
    dsimp [c]
    push_cast
    linarith
  have hcpos : 0 < c := by exact_mod_cast hcposR
  have hcle : Int.natAbs c ≤ C := by
    have hcleZ : c ≤ (C : ℤ) := by exact_mod_cast hcleR
    exact_mod_cast (show (Int.natAbs c : ℤ) ≤ (C : ℤ) by
      simpa [Int.natAbs_of_nonneg hcpos.le] using hcleZ)
  have hmod : Int.ModEq C c (-x) := by
    dsimp [c]
    convert Int.modEq_add_fac_self (a := -x) (t := q + 1) (n := (C : ℤ)) using 1 <;> ring
  have hres := leastPositiveResidue_eq_natAbs_of_pos_le_modEq hC hcpos hcle hmod
  have hcast : ((Int.natAbs c : ℕ) : ℤ) = c := by
    simp [Int.natAbs_of_nonneg hcpos.le]
  calc
    (leastPositiveResidue C (-x) : ℤ) = (Int.natAbs c : ℕ) := by exact_mod_cast hres
    _ = c := hcast
    _ = (C : ℤ) * (⌊(x : ℝ) / (C : ℝ)⌋ + 1) - x := by rfl

/-- The scaled terminal tail divided by the fixed-start window product tends
to zero.  This is the analytic input in the paper's residue-limit proof. -/
theorem scaled_tail_div_window_tendsto_zero (B lo : ℕ) :
    Tendsto
      (fun h : ℕ =>
        (B : ℝ) * trueNormalizedState (lo + h) /
          (actualWindowProduct lo h : ℝ))
      atTop (nhds 0) := by
  let majorant : ℕ → ℝ := fun h =>
    1350 * B * ((lo + h + 1 : ℕ) : ℝ) ^ 2 / (8 : ℝ) ^ h
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (8 : ℝ) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num)
  have hshift := hbase.comp (tendsto_add_atTop_nat (lo + 1))
  have hmaj : Tendsto majorant atTop (nhds 0) := by
    have hmul := hshift.const_mul
      (1350 * (B : ℝ) * (8 : ℝ) ^ (lo + 1))
    convert hmul using 1
    · funext h
      dsimp [majorant]
      rw [pow_add]
      push_cast
      field_simp
      ring
    · simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Eventually.of_forall fun h => ?_) (Eventually.of_forall fun h => ?_)
  · exact div_nonneg
      (mul_nonneg (by positivity) (trueNormalizedState_pos _).le)
      (by positivity)
  · have hW := (actualWindowProduct_geometric_bounds lo h).1
    have hWpos : (0 : ℝ) < actualWindowProduct lo h := by
      exact_mod_cast actualWindowProduct_pos lo h
    have hX := trueNormalizedState_le_quadratic (lo + h)
    have hBnonneg : (0 : ℝ) ≤ B := by positivity
    have hXnonneg : (0 : ℝ) ≤ trueNormalizedState (lo + h) :=
      (trueNormalizedState_pos _).le
    dsimp [majorant]
    have hrecip : (actualWindowProduct lo h : ℝ)⁻¹ <
        15 / (8 : ℝ) ^ h := by
      rw [inv_eq_one_div]
      have hp : (0 : ℝ) < (8 : ℝ) ^ h := by positivity
      calc
        1 / (actualWindowProduct lo h : ℝ) <
            1 / ((8 : ℝ) ^ h / 15) :=
          one_div_lt_one_div_of_lt (div_pos hp (by norm_num)) hW
        _ = 15 / (8 : ℝ) ^ h := by field_simp
    calc
      (B : ℝ) * trueNormalizedState (lo + h) /
          (actualWindowProduct lo h : ℝ)
          = (B : ℝ) * trueNormalizedState (lo + h) *
              (actualWindowProduct lo h : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (B : ℝ) * (90 * ((lo + h + 1 : ℕ) : ℝ) ^ 2) *
              (actualWindowProduct lo h : ℝ)⁻¹ := by
            gcongr
      _ ≤ (B : ℝ) * (90 * ((lo + h + 1 : ℕ) : ℝ) ^ 2) *
              (15 / (8 : ℝ) ^ h) := by
            gcongr
      _ = 1350 * B * ((lo + h + 1 : ℕ) : ℝ) ^ 2 / (8 : ℝ) ^ h := by ring

/-- The quotient appearing in Euclidean division approaches the fixed state
strictly from below. -/
theorem forcing_quotient_eq (B lo h : ℕ) :
    (((B : ℤ) * actualWindowForcing lo h : ℤ) : ℝ) /
        (actualWindowProduct lo h : ℝ) =
      (B : ℝ) * trueNormalizedState lo -
        (B : ℝ) * trueNormalizedState (lo + h) /
          (actualWindowProduct lo h : ℝ) := by
  have hwindow := trueNormalizedState_window lo h
  change trueNormalizedState (lo + h) =
    (actualWindowBase lo h : ℝ) * trueNormalizedState lo -
      (actualWindowForcing lo h : ℝ) at hwindow
  rw [actualWindowBase_eq_product] at hwindow
  have hW : (actualWindowProduct lo h : ℝ) ≠ 0 := by
    exact_mod_cast (actualWindowProduct_pos lo h).ne'
  push_cast at hwindow ⊢
  field_simp [hW]
  nlinarith

/-- The floor is eventually the predecessor of the ceiling, including when
the limiting fixed state is itself integral. -/
theorem eventually_floor_forcing_quotient (B lo : ℕ) (hB : 0 < B) :
    ∀ᶠ h in atTop,
      ⌊(((B : ℤ) * actualWindowForcing lo h : ℤ) : ℝ) /
          (actualWindowProduct lo h : ℝ)⌋ =
        ⌈(B : ℝ) * trueNormalizedState lo⌉ - 1 := by
  let y : ℝ := (B : ℝ) * trueNormalizedState lo
  let gap : ℝ := y - ((⌈y⌉ - 1 : ℤ) : ℝ)
  have hgap : 0 < gap := by
    dsimp [gap]
    have := Int.ceil_lt_add_one y
    push_cast at this ⊢
    linarith
  have heps := (scaled_tail_div_window_tendsto_zero B lo).eventually
    (eventually_lt_nhds hgap)
  filter_upwards [heps] with h hepslt
  rw [forcing_quotient_eq]
  apply Int.floor_eq_iff.mpr
  constructor
  · dsimp [gap, y] at hepslt ⊢
    linarith
  · have htailpos : 0 <
        (B : ℝ) * trueNormalizedState (lo + h) /
          (actualWindowProduct lo h : ℝ) := by
      exact div_pos (mul_pos (by exact_mod_cast hB) (trueNormalizedState_pos _))
        (by exact_mod_cast actualWindowProduct_pos lo h)
    have hyceil : y ≤ (⌈y⌉ : ℤ) := Int.le_ceil y
    dsimp [y] at hyceil ⊢
    push_cast at hyceil ⊢
    linarith

/-- The eventual exact formula in the paper's fixed-start proposition. -/
theorem eventually_fixedStartResidue_formula (B lo : ℕ) (hB : 0 < B) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        ((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) *
            (actualWindowProduct lo h : ℝ) -
          (B : ℝ) * trueNormalizedState lo *
            (actualWindowProduct lo h : ℝ) +
          (B : ℝ) * trueNormalizedState (lo + h) := by
  filter_upwards [eventually_floor_forcing_quotient B lo hB] with h hfloor
  have hC := actualWindowProduct_pos lo h
  have hlpr := leastPositiveResidue_neg_eq_floor
    (actualWindowProduct lo h) hC ((B : ℤ) * actualWindowForcing lo h)
  rw [hfloor] at hlpr
  have hwindow := trueNormalizedState_window lo h
  change trueNormalizedState (lo + h) =
    (actualWindowBase lo h : ℝ) * trueNormalizedState lo -
      (actualWindowForcing lo h : ℝ) at hwindow
  rw [actualWindowBase_eq_product] at hwindow
  have hlprR :
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        (((actualWindowProduct lo h : ℕ) : ℤ) *
          (⌈(B : ℝ) * trueNormalizedState lo⌉ - 1 + 1) -
          (B : ℤ) * actualWindowForcing lo h : ℤ) := by
    exact_mod_cast hlpr
  rw [hlprR]
  push_cast at hwindow ⊢
  rw [hwindow]
  ring

/-- The least-positive residue occupies asymptotically the gap from `B X_lo`
to the next integer, exactly as stated in the long paper. -/
theorem fixedStartResidue_ratio_tendsto (B lo : ℕ) (hB : 0 < B) :
    Tendsto
      (fun h : ℕ =>
        (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) /
            (actualWindowProduct lo h : ℝ))
      atTop
      (nhds (((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) -
        (B : ℝ) * trueNormalizedState lo)) := by
  have heps := scaled_tail_div_window_tendsto_zero B lo
  let c : ℝ := ((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) -
    (B : ℝ) * trueNormalizedState lo
  have hmain : Tendsto
      (fun h : ℕ => c +
        (B : ℝ) * trueNormalizedState (lo + h) /
          (actualWindowProduct lo h : ℝ)) atTop (nhds c) := by
    simpa using (tendsto_const_nhds.add heps)
  apply hmain.congr'
  filter_upwards [eventually_fixedStartResidue_formula B lo hB] with h hformula
  have hW : (actualWindowProduct lo h : ℝ) ≠ 0 := by
    exact_mod_cast (actualWindowProduct_pos lo h).ne'
  rw [hformula]
  dsimp [c]
  field_simp [hW]

/-- Integral fixed states are the zero-gap special case of the exact formula. -/
theorem eventually_fixedStartResidue_eq_tail_of_integral
    (B lo : ℕ) (hB : 0 < B) (hInt : ∃ z : ℤ, (B : ℝ) * trueNormalizedState lo = z) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        (B : ℝ) * trueNormalizedState (lo + h) := by
  obtain ⟨z, hz⟩ := hInt
  filter_upwards [eventually_fixedStartResidue_formula B lo hB] with h hformula
  rw [hz, Int.ceil_intCast] at hformula
  push_cast at hformula ⊢
  linarith

end ErdosProblems.Erdos269.PaperR14
