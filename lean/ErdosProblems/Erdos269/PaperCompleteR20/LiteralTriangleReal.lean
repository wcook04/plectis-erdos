import ErdosProblems.Erdos269.PaperCompleteR20.LiteralTriangle
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring

/-! Exact logarithmic coordinates and the paper's rectangle lower bound. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators

noncomputable def triangleLogPoint (v : ℕ × ℕ) : ℝ :=
  (v.1 : ℝ) * Real.logb 2 3 + (v.2 : ℝ) * Real.logb 2 5

noncomputable def triangleTheta (p : ℕ) : ℝ := 1 / Real.logb 2 p

theorem triangleLogPoint_eq_log (v : ℕ × ℕ) :
    triangleLogPoint v = Real.logb 2 (triangleOddPart v) := by
  simp only [triangleLogPoint, triangleOddPart, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]

theorem triangleLogPoint_nonneg (v : ℕ × ℕ) : 0 ≤ triangleLogPoint v := by
  unfold triangleLogPoint
  have h3 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 3)
  have h5 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 5)
  positivity

theorem mem_literalTriangle_log_iff {a : ℕ} {v : ℕ × ℕ} :
    v ∈ literalTriangle a ↔ triangleLogPoint v < (a : ℝ) + 1 := by
  rw [mem_literalTriangle_iff, triangleLogPoint_eq_log]
  have hm : (0 : ℝ) < triangleOddPart v := by unfold triangleOddPart; positivity
  have h := Real.logb_lt_iff_lt_rpow (y := (a : ℝ) + 1)
    (by norm_num : (1 : ℝ) < 2) hm
  rw [show (a : ℝ) + 1 = ((a + 1 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast] at h
  exact (by exact_mod_cast h.symm)

theorem floor_triangleLogPoint (v : ℕ × ℕ) :
    ⌊triangleLogPoint v⌋₊ = Nat.log 2 (triangleOddPart v) := by
  rw [triangleLogPoint_eq_log]
  simpa only [Nat.cast_ofNat] using Real.natFloor_logb_natCast 2 (triangleOddPart v)

theorem triangle_lift_log {a : ℕ} {v : ℕ × ℕ} (hv : v ∈ literalTriangle a) :
    Real.logb 2 (smooth3Val 2 3 5 (triangleShellLift a v).1 v.1 v.2) =
      (a : ℝ) + Int.fract (triangleLogPoint v) := by
  have hk : Nat.log 2 (triangleOddPart v) ≤ a := by
    have hm : triangleOddPart v ≠ 0 := by simp [triangleOddPart]
    have := Nat.log_lt_of_lt_pow hm (mem_literalTriangle_iff.mp hv)
    omega
  have hf := Int.floor_add_fract (triangleLogPoint v)
  rw [← natCast_floor_eq_intCast_floor (triangleLogPoint_nonneg v),
    floor_triangleLogPoint] at hf
  simp only [smooth3Val, triangleShellLift, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  push_cast [Nat.cast_sub hk]
  unfold triangleLogPoint at hf ⊢
  linarith

theorem logb_eq_binary_mul_theta (p : ℕ) (x : ℝ) :
    Real.logb p x = Real.logb 2 x * triangleTheta p := by
  rw [triangleTheta, one_div, Real.inv_logb, mul_comm]
  exact (Real.mul_logb (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (2 : ℝ) ≠ 1) (by norm_num : (2 : ℝ) ≠ -1)).symm

theorem log_lift_eq_floor_phase (p : ℕ) {a : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ literalTriangle a) :
    Nat.log p (smooth3Val 2 3 5 (triangleShellLift a v).1 v.1 v.2) =
      ⌊((a : ℝ) + Int.fract (triangleLogPoint v)) * triangleTheta p⌋₊ := by
  rw [← Real.natFloor_logb_natCast, logb_eq_binary_mul_theta, triangle_lift_log hv]

theorem log_endpoint_eq_floor_theta (p a : ℕ) :
    Nat.log p (2 ^ (a + 1)) = ⌊((a : ℝ) + 1) * triangleTheta p⌋₊ := by
  rw [← Real.natFloor_logb_natCast, logb_eq_binary_mul_theta]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one, Nat.cast_add, Nat.cast_one]

noncomputable def literalLogWeight (a : ℕ) (v : ℕ × ℕ) : ℕ :=
  3 ^ (⌊((a : ℝ) + 1) * triangleTheta 3⌋₊ -
    ⌊((a : ℝ) + Int.fract (triangleLogPoint v)) * triangleTheta 3⌋₊) *
  5 ^ (⌊((a : ℝ) + 1) * triangleTheta 5⌋₊ -
    ⌊((a : ℝ) + Int.fract (triangleLogPoint v)) * triangleTheta 5⌋₊)

theorem literalTriangleWeight_eq_logWeight {a : ℕ} {v : ℕ × ℕ}
    (hv : v ∈ literalTriangle a) : literalTriangleWeight a v = literalLogWeight a v := by
  unfold literalTriangleWeight oddHeightSuffix235 literalLogWeight
  change 3 ^ (Nat.log 3 (2 ^ (a + 1)) -
      Nat.log 3 (smooth3Val 2 3 5 (triangleShellLift a v).1 v.1 v.2)) *
    5 ^ (Nat.log 5 (2 ^ (a + 1)) -
      Nat.log 5 (smooth3Val 2 3 5 (triangleShellLift a v).1 v.1 v.2)) = _
  rw [log_endpoint_eq_floor_theta, log_endpoint_eq_floor_theta,
    log_lift_eq_floor_phase 3 hv, log_lift_eq_floor_phase 5 hv]

theorem actual_numerator_eq_logarithmic_triangle (a : ℕ) :
    dyadicOrderedBlockDigit235 a = ∑ v ∈ literalTriangle a, literalLogWeight a v := by
  rw [actual_numerator_eq_literal_triangle]
  exact Finset.sum_congr rfl (fun _ hv => literalTriangleWeight_eq_logWeight hv)

noncomputable def triangleRectangleSide (a p : ℕ) : ℕ :=
  ⌊(a : ℝ) / (2 * Real.logb 2 p)⌋₊ + 1

theorem triangle_rectangle_subset (a : ℕ) :
    (Finset.range (triangleRectangleSide a 3)).product
      (Finset.range (triangleRectangleSide a 5)) ⊆ literalTriangle a := by
  intro v hv
  rcases Finset.mem_product.mp hv with ⟨hj, hk⟩
  have h3 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 3)
  have h5 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 5)
  have hjn : v.1 ≤ ⌊(a : ℝ) / (2 * Real.logb 2 3)⌋₊ := by
    have := Finset.mem_range.mp hj
    simp only [triangleRectangleSide, Nat.cast_ofNat] at this
    omega
  have hkn : v.2 ≤ ⌊(a : ℝ) / (2 * Real.logb 2 5)⌋₊ := by
    have := Finset.mem_range.mp hk
    simp only [triangleRectangleSide, Nat.cast_ofNat] at this
    omega
  have hjR := (Nat.le_floor_iff (by positivity : 0 ≤ (a : ℝ) / (2 * Real.logb 2 3))).mp hjn
  have hkR := (Nat.le_floor_iff (by positivity : 0 ≤ (a : ℝ) / (2 * Real.logb 2 5))).mp hkn
  have hjb := (le_div_iff₀ (by positivity : 0 < 2 * Real.logb 2 3)).mp hjR
  have hkb := (le_div_iff₀ (by positivity : 0 < 2 * Real.logb 2 5)).mp hkR
  apply mem_literalTriangle_log_iff.mpr
  unfold triangleLogPoint
  nlinarith

theorem triangle_rectangle_lower_bound (a : ℕ) :
    triangleRectangleSide a 3 * triangleRectangleSide a 5 ≤ dyadicOrderedBlockDigit235 a := by
  have h := (Finset.card_le_card (triangle_rectangle_subset a)).trans
    (triangle_card_le_actual_numerator a)
  have hc : ((Finset.range (triangleRectangleSide a 3)).product
      (Finset.range (triangleRectangleSide a 5))).card =
      triangleRectangleSide a 3 * triangleRectangleSide a 5 := by
    simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range]
  exact hc ▸ h

private theorem rectangleSide_dominates (a p : ℕ) (hp : 1 < p) :
    (a : ℝ) + 1 ≤ (2 * Real.logb 2 p + 1) * (triangleRectangleSide a p : ℝ) := by
  have hlog : 0 < Real.logb 2 (p : ℝ) :=
    Real.logb_pos (by norm_num) (by exact_mod_cast hp)
  have hf := Nat.lt_floor_add_one ((a : ℝ) / (2 * Real.logb 2 p))
  have hs : (triangleRectangleSide a p : ℝ) =
      (⌊(a : ℝ) / (2 * Real.logb 2 p)⌋₊ : ℝ) + 1 := by
    simp only [triangleRectangleSide, Nat.cast_add, Nat.cast_one]
  rw [← hs] at hf
  have hh := (div_lt_iff₀ (by positivity : 0 < 2 * Real.logb 2 p)).mp hf
  have h1 : (1 : ℝ) ≤ triangleRectangleSide a p := by
    rw [hs]
    have := Nat.cast_nonneg (α := ℝ) ⌊(a : ℝ) / (2 * Real.logb 2 p)⌋₊
    linarith
  nlinarith

noncomputable def triangleQuadraticDenominator : ℝ :=
  (2 * Real.logb 2 3 + 1) * (2 * Real.logb 2 5 + 1)

theorem triangleQuadraticDenominator_pos : 0 < triangleQuadraticDenominator := by
  have h3 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 3)
  have h5 := Real.logb_pos (by norm_num : (1 : ℝ) < 2) (by norm_num : (1 : ℝ) < 5)
  unfold triangleQuadraticDenominator
  positivity

theorem actual_numerator_two_sided_quadratic (a : ℕ) :
    (a + 1 : ℝ) ^ 2 / triangleQuadraticDenominator ≤ dyadicOrderedBlockDigit235 a ∧
      (dyadicOrderedBlockDigit235 a : ℝ) ≤ 15 * (a + 1 : ℝ) ^ 2 := by
  constructor
  · apply (div_le_iff₀ triangleQuadraticDenominator_pos).mpr
    have h3 := rectangleSide_dominates a 3 (by decide)
    have h5 := rectangleSide_dominates a 5 (by decide)
    norm_num only [Nat.cast_ofNat] at h3 h5
    have hr : (triangleRectangleSide a 3 : ℝ) * triangleRectangleSide a 5 ≤
        dyadicOrderedBlockDigit235 a := by exact_mod_cast triangle_rectangle_lower_bound a
    have hprod := mul_le_mul h3 h5 (by positivity : (0 : ℝ) ≤ a + 1)
      (le_trans (by positivity : (0 : ℝ) ≤ a + 1) h3)
    calc
      (a + 1 : ℝ) ^ 2 ≤ triangleQuadraticDenominator *
          ((triangleRectangleSide a 3 : ℝ) * triangleRectangleSide a 5) := by
        unfold triangleQuadraticDenominator
        nlinarith only [hprod]
      _ ≤ (dyadicOrderedBlockDigit235 a : ℝ) * triangleQuadraticDenominator := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr triangleQuadraticDenominator_pos.le
  · exact_mod_cast dyadicOrderedBlockDigit235_le_quadratic a

theorem actual_numerator_unbounded (M : ℝ) : ∃ a : ℕ, M < dyadicOrderedBlockDigit235 a := by
  obtain ⟨a, ha⟩ := exists_nat_gt (M * triangleQuadraticDenominator)
  refine ⟨a, ?_⟩
  have hb := (div_le_iff₀ triangleQuadraticDenominator_pos).mp
    (actual_numerator_two_sided_quadratic a).1
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have h : M * triangleQuadraticDenominator <
      (dyadicOrderedBlockDigit235 a : ℝ) * triangleQuadraticDenominator := by nlinarith
  exact (mul_lt_mul_iff_left₀ triangleQuadraticDenominator_pos).mp h

/-- Complete formula, four possible weights, literal rectangle bounds,
quantitative quadratic growth and unboundedness from the paper's lemma. -/
theorem literal_triangle_whole :
    (∀ a, dyadicOrderedBlockDigit235 a = ∑ v ∈ literalTriangle a, literalLogWeight a v) ∧
    (∀ a v, v ∈ literalTriangle a →
      literalLogWeight a v = 1 ∨ literalLogWeight a v = 3 ∨
      literalLogWeight a v = 5 ∨ literalLogWeight a v = 15) ∧
    (∀ a, triangleRectangleSide a 3 * triangleRectangleSide a 5 ≤ dyadicOrderedBlockDigit235 a) ∧
    (∀ a : ℕ, (a + 1 : ℝ) ^ 2 / triangleQuadraticDenominator ≤ dyadicOrderedBlockDigit235 a ∧
      (dyadicOrderedBlockDigit235 a : ℝ) ≤ 15 * (a + 1 : ℝ) ^ 2) ∧
    (∀ M : ℝ, ∃ a : ℕ, M < dyadicOrderedBlockDigit235 a) := by
  refine ⟨actual_numerator_eq_logarithmic_triangle, ?_, triangle_rectangle_lower_bound,
    actual_numerator_two_sided_quadratic, actual_numerator_unbounded⟩
  intro a v hv
  rw [← literalTriangleWeight_eq_logWeight hv]
  exact literalTriangleWeight_four_values hv

#print axioms literal_triangle_whole
#print axioms actual_numerator_eq_logarithmic_triangle
#print axioms triangle_rectangle_lower_bound

end ErdosProblems.Erdos269.PaperCompleteR20
