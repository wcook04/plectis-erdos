import ErdosProblems.Erdos68.CompanionOrbitRationality
import ErdosProblems.Erdos68.SecondLayerDigit

/-!
# Erdős #68: the unconditional companion-constant carry law

Let `C = ∑_{n≥2} 1/(n!(n!−1))` be the fixed companion constant and let
`F_m = m!·C_m` be the finite fractional carrier of the carry congruence normal
form.  This module removes the last conditional hypothesis between the finite
carrier and the fixed constant.

**Tail identity.**  `F_m = m!·C − δ_m` with the scaled omitted tail
`δ_m = m! ∑_{n>m} 1/(n!(n!−1))`, and

`0 < δ_m < 1/((m+1)!−1)`.

**Wrap indicator.**  Put `σ_m = [fract(m!·C) < δ_m]`.  Then
`⌊F_m⌋ = ⌊m!·C⌋ − σ_m` exactly.

**Carry law.**  For every `m ≥ 3`, with `d_m(C)` the canonical factorial
digit of `C`,

`b_m = (m − 1 − d_m(C)) + σ_m − m·σ_{m−1}`.

Hence a unit carry forces `d_m(C) ∈ {m−2, m−1}`, a zero carry forces
`d_m(C) ∈ {m−1, 0}`, and the floor-stability hypothesis of
`SecondLayerDigit` is exactly `σ_m = 0`.  The constant-only miss certificate
of `ConstantOnlyMissCertificates` is therefore unconditional: if `⌊m!·C⌋`
avoids the two residues `−2` and `−1` modulo `m`, the carry at `m` is
non-unit.

None of this produces a cofinal miss; it makes the carry sequence an exact
function of one fixed real constant plus an explicit sub-factorial
exceptional indicator.
-/

namespace ErdosProblems.Erdos68

open scoped BigOperators

/-- The scaled omitted companion tail `δ_m = m! ∑_{n>m} 1/(n!(n!−1))`. -/
noncomputable def companionScaledTail (m : ℕ) : ℝ :=
  (m.factorial : ℝ) * ∑' k : ℕ, compConstTerm (m + 1 + k)

theorem summable_compConstTerm_tail (m : ℕ) :
    Summable (fun k : ℕ => compConstTerm (m + 1 + k)) := by
  have hs := (summable_nat_add_iff (m + 1)).2 summable_compConstTerm
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

theorem companionScaledTail_pos (m : ℕ) (hm : 1 ≤ m) : 0 < companionScaledTail m := by
  unfold companionScaledTail
  refine mul_pos (by positivity) ?_
  have h0 : 0 < compConstTerm (m + 1 + 0) := compConstTerm_pos (by omega)
  exact (summable_compConstTerm_tail m).tsum_pos
    (fun k => by
      by_cases hk : 2 ≤ m + 1 + k
      · exact (compConstTerm_pos hk).le
      · simp [compConstTerm, hk])
    0 h0

/-- Termwise domination of the companion tail by the exponential tail. -/
private theorem compConstTerm_tail_le (m k : ℕ) (hm : 1 ≤ m) :
    compConstTerm (m + 1 + k) ≤
      (1 / ((((m + 1).factorial : ℕ) : ℝ) - 1)) *
        (1 / (((m + 1 + k).factorial : ℕ) : ℝ)) := by
  have h2 : 2 ≤ m + 1 + k := by omega
  rw [compConstTerm, if_pos h2]
  push_cast
  have hfacLe : (((m + 1).factorial : ℕ) : ℝ) ≤
      (((m + 1 + k).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hone : (1 : ℝ) < (((m + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_lt_factorial.mpr (by omega)
  have hA : (0 : ℝ) < (((m + 1).factorial : ℕ) : ℝ) - 1 := by linarith
  have hB : (0 : ℝ) < (((m + 1 + k).factorial : ℕ) : ℝ) - 1 := by linarith
  have hF : (0 : ℝ) < (((m + 1 + k).factorial : ℕ) : ℝ) := by positivity
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le
  · positivity
  · have hAB : (((m + 1).factorial : ℕ) : ℝ) - 1 ≤
        (((m + 1 + k).factorial : ℕ) : ℝ) - 1 := by linarith
    calc
      ((((m + 1).factorial : ℕ) : ℝ) - 1) * (((m + 1 + k).factorial : ℕ) : ℝ)
          ≤ ((((m + 1 + k).factorial : ℕ) : ℝ) - 1) *
              (((m + 1 + k).factorial : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hAB hF.le
      _ = (((m + 1 + k).factorial : ℕ) : ℝ) *
            ((((m + 1 + k).factorial : ℕ) : ℝ) - 1) := by ring

/-- `δ_m < 1/((m+1)!−1)`: the omitted tail is far below one factorial cell. -/
theorem companionScaledTail_lt (m : ℕ) (hm : 2 ≤ m) :
    companionScaledTail m < 1 / ((((m + 1).factorial : ℕ) : ℝ) - 1) := by
  have hone : (1 : ℝ) < (((m + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_lt_factorial.mpr (by omega)
  have hA : (0 : ℝ) < (((m + 1).factorial : ℕ) : ℝ) - 1 := by linarith
  have hsumLe :
      (∑' k : ℕ, compConstTerm (m + 1 + k)) ≤
        (1 / ((((m + 1).factorial : ℕ) : ℝ) - 1)) * unitFactTail m := by
    unfold unitFactTail
    rw [← tsum_mul_left]
    exact (summable_compConstTerm_tail m).tsum_le_tsum
      (fun k => compConstTerm_tail_le m k (by omega))
      ((summable_unitFactTail m).mul_left _)
  have hscaled := unitFactScaledTail_pos_lt_one (m := m) hm
  unfold companionScaledTail
  calc
    (m.factorial : ℝ) * ∑' k : ℕ, compConstTerm (m + 1 + k)
        ≤ (m.factorial : ℝ) *
            ((1 / ((((m + 1).factorial : ℕ) : ℝ) - 1)) * unitFactTail m) :=
      mul_le_mul_of_nonneg_left hsumLe (by positivity)
    _ = (1 / ((((m + 1).factorial : ℕ) : ℝ) - 1)) * unitFactScaledTail m := by
      unfold unitFactScaledTail
      ring
    _ < (1 / ((((m + 1).factorial : ℕ) : ℝ) - 1)) * 1 :=
      mul_lt_mul_of_pos_left hscaled.2 (by positivity)
    _ = 1 / ((((m + 1).factorial : ℕ) : ℝ) - 1) := by ring

theorem companionScaledTail_lt_one (m : ℕ) (hm : 2 ≤ m) :
    companionScaledTail m < 1 := by
  have h := companionScaledTail_lt m hm
  have hfac : (2 : ℝ) ≤ (((m + 1).factorial : ℕ) : ℝ) := by
    have hnat : (2 : ℕ) ≤ (m + 1).factorial := by
      calc
        2 = (2 : ℕ).factorial := by norm_num
        _ ≤ (m + 1).factorial := Nat.factorial_le (by omega)
    exact_mod_cast hnat
  have hA : (1 : ℝ) ≤ (((m + 1).factorial : ℕ) : ℝ) - 1 := by linarith
  calc
    companionScaledTail m < 1 / ((((m + 1).factorial : ℕ) : ℝ) - 1) := h
    _ ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hA

/-- The finite companion partial sum, cast to the reals, is the range-sum of
the anchored companion terms. -/
theorem compConstPartial_cast_eq_sum_range (m : ℕ) :
    ((compConstPartial m : ℚ) : ℝ) =
      ∑ n ∈ Finset.range (m + 1), compConstTerm n := by
  have hset : Finset.Icc 2 m =
      (Finset.range (m + 1)).filter (fun n => 2 ≤ n) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    omega
  unfold compConstPartial
  push_cast
  rw [hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h2 : 2 ≤ n
  · rw [if_pos h2, compConstTerm, if_pos h2]
    push_cast
    ring
  · rw [if_neg h2, compConstTerm, if_neg h2]

/-- `C = C_m + (tail after m)`. -/
theorem companionConstant_eq_partial_add_tail (m : ℕ) :
    companionConstant =
      ((compConstPartial m : ℚ) : ℝ) + ∑' k : ℕ, compConstTerm (m + 1 + k) := by
  unfold companionConstant
  have hsplit := summable_compConstTerm.sum_add_tsum_nat_add (m + 1)
  rw [← hsplit, compConstPartial_cast_eq_sum_range]
  congr 1
  apply tsum_congr
  intro k
  congr 1
  omega

/-- **Tail identity.**  The finite fractional carrier is the fixed constant's
factorial orbit minus the scaled omitted tail. -/
theorem scaledPrefixFrac_cast_eq_companion_sub_tail (m : ℕ) (hm : 2 ≤ m) :
    ((scaledPrefixFrac m : ℚ) : ℝ) =
      (m.factorial : ℝ) * companionConstant - companionScaledTail m := by
  rw [scaledPrefixFrac_eq_compConstPartial_mul m hm,
    companionConstant_eq_partial_add_tail m]
  unfold companionScaledTail
  push_cast
  ring

/-- Subtracting `0 < δ < 1` lowers a floor exactly when the fractional part
is below `δ`. -/
theorem floor_sub_small_eq_floor_sub_indicator (J δ : ℝ)
    (hδpos : 0 < δ) (hδlt : δ < 1) :
    ⌊J - δ⌋ = ⌊J⌋ - (if Int.fract J < δ then 1 else 0) := by
  have hJ : J - δ = (⌊J⌋ : ℝ) + (Int.fract J - δ) := by
    have := Int.floor_add_fract J
    linarith
  rw [hJ, Int.floor_intCast_add]
  have hf0 := Int.fract_nonneg J
  have hf1 := Int.fract_lt_one J
  split_ifs with h
  · have : ⌊Int.fract J - δ⌋ = -1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    omega
  · push Not at h
    have : ⌊Int.fract J - δ⌋ = 0 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    omega

/-- The near-integer wrap indicator `σ_m = [fract(m!·C) < δ_m]`. -/
noncomputable def companionWrap (m : ℕ) : ℤ :=
  if Int.fract ((m.factorial : ℝ) * companionConstant) < companionScaledTail m
  then 1 else 0

theorem companionWrap_eq_zero_or_one (m : ℕ) :
    companionWrap m = 0 ∨ companionWrap m = 1 := by
  unfold companionWrap
  split_ifs <;> simp

/-- **Wrap identity.**  `⌊F_m⌋ = ⌊m!·C⌋ − σ_m`. -/
theorem floor_scaledPrefixFrac_eq_facFloor_sub_wrap (m : ℕ) (hm : 2 ≤ m) :
    ⌊scaledPrefixFrac m⌋ = facFloor companionConstant m - companionWrap m := by
  have hcast : ⌊scaledPrefixFrac m⌋ = ⌊((scaledPrefixFrac m : ℚ) : ℝ)⌋ :=
    (Rat.floor_cast (scaledPrefixFrac m)).symm
  rw [hcast, scaledPrefixFrac_cast_eq_companion_sub_tail m hm,
    floor_sub_small_eq_floor_sub_indicator _ _
      (companionScaledTail_pos m (by omega)) (companionScaledTail_lt_one m hm)]
  unfold facFloor companionWrap
  rfl

/-- The finite second-layer floor of `SecondLayerDigit` is the carrier floor. -/
theorem secondLayerPrefixFloor_eq_floor_scaledPrefixFrac (m : ℕ) (hm : 2 ≤ m) :
    secondLayerPrefixFloor m = ⌊scaledPrefixFrac m⌋ := by
  unfold secondLayerPrefixFloor
  rw [scaledPrefixFrac_eq_compConstPartial_mul m hm]
  rfl

/-- **Unconditional companion carry law.**  For `m ≥ 3`,
`b_m = (m − 1 − d_m(C)) + σ_m − m·σ_{m−1}`. -/
theorem factorialGapStepCarry_eq_companion_digit_law (m : ℕ) (hm : 3 ≤ m) :
    factorialGapStepCarry m =
      ((m : ℤ) - 1 - canonicalDigit companionConstant m) +
        companionWrap m - (m : ℤ) * companionWrap (m - 1) := by
  have hdigit := secondLayerPrefixDigit_eq_carry (m := m) (by omega)
  unfold secondLayerPrefixDigit at hdigit
  rw [secondLayerPrefixFloor_eq_floor_scaledPrefixFrac m (by omega),
    secondLayerPrefixFloor_eq_floor_scaledPrefixFrac (m - 1) (by omega),
    floor_scaledPrefixFrac_eq_facFloor_sub_wrap m (by omega),
    floor_scaledPrefixFrac_eq_facFloor_sub_wrap (m - 1) (by omega)] at hdigit
  unfold canonicalDigit
  linear_combination hdigit

/-- A unit carry forces the companion digit into the two top classes. -/
theorem canonicalDigit_companion_of_unit_carry {m : ℕ} (hm : 3 ≤ m)
    (hunit : factorialGapStepCarry m = 1) :
    canonicalDigit companionConstant m = (m : ℤ) - 2 ∨
      canonicalDigit companionConstant m = (m : ℤ) - 1 := by
  have hlaw := factorialGapStepCarry_eq_companion_digit_law m hm
  have hd0 := canonicalDigit_nonneg companionConstant m (by omega)
  have hdlt := canonicalDigit_lt_radix companionConstant m (by omega)
  have hw := companionWrap_eq_zero_or_one m
  have hw' := companionWrap_eq_zero_or_one (m - 1)
  have hm3 : (3 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  rcases hw with hw | hw <;> rcases hw' with hw' | hw' <;>
    rw [hw, hw'] at hlaw <;> omega

/-- A zero carry forces the companion digit into `{m−1, 0}`. -/
theorem canonicalDigit_companion_of_zero_carry {m : ℕ} (hm : 3 ≤ m)
    (hzero : factorialGapStepCarry m = 0) :
    canonicalDigit companionConstant m = (m : ℤ) - 1 ∨
      canonicalDigit companionConstant m = 0 := by
  have hlaw := factorialGapStepCarry_eq_companion_digit_law m hm
  have hd0 := canonicalDigit_nonneg companionConstant m (by omega)
  have hdlt := canonicalDigit_lt_radix companionConstant m (by omega)
  have hw := companionWrap_eq_zero_or_one m
  have hw' := companionWrap_eq_zero_or_one (m - 1)
  have hm3 : (3 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  rcases hw with hw | hw <;> rcases hw' with hw' | hw' <;>
    rw [hw, hw'] at hlaw <;> omega

/-- **Unconditional constant-only miss certificate.**  If the floor of the
fixed constant's factorial orbit avoids the residues `−2` and `−1` modulo
`m`, the carry at `m` is non-unit.  No tail hypothesis remains. -/
theorem factorialGapStepCarry_ne_one_of_companion_floor_residues
    {m : ℕ} (hm : 3 ≤ m)
    (hfloor : ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0)
    (hpred : ((facFloor companionConstant m + 1 : ℤ) % (m : ℤ)) ≠ 0) :
    factorialGapStepCarry m ≠ 1 := by
  refine factorialGapStepCarry_ne_one_of_constant_floor_residues hm
    ((m.factorial : ℝ) * companionConstant) (companionScaledTail m)
    (scaledPrefixFrac_cast_eq_companion_sub_tail m (by omega))
    (companionScaledTail_pos m (by omega)) (companionScaledTail_lt_one m (by omega))
    ?_ ?_
  · simpa [facFloor] using hfloor
  · simpa [facFloor] using hpred

/-- The floor-stability hypothesis of `SecondLayerDigit` at the companion
constant is exactly the absence of a wrap: `δ_m ≤ fract(m!·C)`. -/
theorem secondLayerFloorStableAt_companion_iff (m : ℕ) (hm : 2 ≤ m) :
    SecondLayerFloorStableAt companionConstant m ↔
      companionScaledTail m ≤
        Int.fract ((m.factorial : ℝ) * companionConstant) := by
  unfold SecondLayerFloorStableAt
  rw [secondLayerPrefixFloor_eq_floor_scaledPrefixFrac m hm,
    floor_scaledPrefixFrac_eq_facFloor_sub_wrap m hm]
  unfold companionWrap
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    rw [if_pos hlt] at h
    omega
  · intro h
    rw [if_neg (not_lt.mpr h)]
    simp

/-- Away from wraps at `m` and `m−1`, the carry is exactly the complement
digit of the companion constant. -/
theorem factorialGapStepCarry_eq_complement_companion_digit_of_no_wrap
    {m : ℕ} (hm : 3 ≤ m)
    (hnow : companionScaledTail m ≤
      Int.fract ((m.factorial : ℝ) * companionConstant))
    (hprev : companionScaledTail (m - 1) ≤
      Int.fract (((m - 1).factorial : ℝ) * companionConstant)) :
    factorialGapStepCarry m = (m : ℤ) - 1 - canonicalDigit companionConstant m := by
  have hlaw := factorialGapStepCarry_eq_companion_digit_law m hm
  have hw : companionWrap m = 0 := by
    unfold companionWrap
    rw [if_neg (not_lt.mpr hnow)]
  have hw' : companionWrap (m - 1) = 0 := by
    unfold companionWrap
    rw [if_neg (not_lt.mpr hprev)]
  rw [hw, hw'] at hlaw
  omega

#print axioms companionScaledTail_lt
#print axioms scaledPrefixFrac_cast_eq_companion_sub_tail
#print axioms floor_scaledPrefixFrac_eq_facFloor_sub_wrap
#print axioms factorialGapStepCarry_eq_companion_digit_law
#print axioms canonicalDigit_companion_of_unit_carry
#print axioms canonicalDigit_companion_of_zero_carry
#print axioms factorialGapStepCarry_ne_one_of_companion_floor_residues
#print axioms secondLayerFloorStableAt_companion_iff
#print axioms factorialGapStepCarry_eq_complement_companion_digit_of_no_wrap

end ErdosProblems.Erdos68
