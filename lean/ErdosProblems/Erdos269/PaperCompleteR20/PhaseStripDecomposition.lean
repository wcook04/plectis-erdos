import ErdosProblems.Erdos269.PaperCompleteR20.StripDecomposition
import ErdosProblems.Erdos269.PaperCompleteR20.LiteralTriangleReal
import ErdosProblems.Erdos269.PaperCompleteR20.WeightedShiftArithmetic

/-! The printed integer-floor weights and their exact crossing factors. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators

noncomputable def phaseFloor (p a : ℕ) (t : ℝ) : ℤ :=
  ⌊((a : ℝ) + t) * triangleTheta p⌋

noncomputable def phaseOmega (a : ℕ) (t : ℝ) : ℝ :=
  (3 : ℝ) ^ (phaseFloor 3 a 1 - phaseFloor 3 a t) *
    (5 : ℝ) ^ (phaseFloor 5 a 1 - phaseFloor 5 a t)

noncomputable def phaseCarry (p a : ℕ) (t : ℝ) (u : ℕ) : ℤ :=
  phaseFloor p (a + u) t - phaseFloor p a t - phaseFloor p u 0

noncomputable def phaseChi (a : ℕ) (t : ℝ) (u : ℕ) : ℝ :=
  (3 : ℝ) ^ (-phaseCarry 3 a t u) * (5 : ℝ) ^ (-phaseCarry 5 a t u)

theorem triangleTheta_pos {p : ℕ} (hp : 1 < p) : 0 < triangleTheta p := by
  unfold triangleTheta
  exact one_div_pos.mpr (Real.logb_pos (by norm_num) (by exact_mod_cast hp))

theorem phaseFloor_zero_eq_log {p : ℕ} (hp : 1 < p) (a : ℕ) :
    phaseFloor p a 0 = (Nat.log p (2 ^ a) : ℤ) := by
  have hlog : Nat.log p (2 ^ a) = ⌊(a : ℝ) * triangleTheta p⌋₊ := by
    rw [← Real.natFloor_logb_natCast, logb_eq_binary_mul_theta]
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
  rw [phaseFloor, add_zero, hlog, Int.natCast_floor_eq_floor
    (mul_nonneg (Nat.cast_nonneg a) (triangleTheta_pos hp).le)]

theorem phaseFloor_one_eq_log {p : ℕ} (hp : 1 < p) (a : ℕ) :
    phaseFloor p a 1 = (Nat.log p (2 ^ (a + 1)) : ℤ) := by
  simpa only [phaseFloor, Nat.cast_add, Nat.cast_one, add_zero] using
    phaseFloor_zero_eq_log hp (a + 1)

theorem phaseCarry_zero_or_one (p a : ℕ) (t : ℝ) (u : ℕ) :
    phaseCarry p a t u = 0 ∨ phaseCarry p a t u = 1 := by
  have he : ((a + u : ℕ) + t : ℝ) * triangleTheta p =
      ((a : ℝ) + t) * triangleTheta p + (u : ℝ) * triangleTheta p := by
    push_cast
    ring
  have hl := Int.le_floor_add (((a : ℝ) + t) * triangleTheta p)
    ((u : ℝ) * triangleTheta p)
  have hu := Int.le_floor_add_floor (((a : ℝ) + t) * triangleTheta p)
    ((u : ℝ) * triangleTheta p)
  unfold phaseCarry phaseFloor
  rw [he]
  simp only [add_zero]
  omega

theorem shiftGamma_eq_floor_powers (a u : ℕ) :
    shiftGamma a u =
      (3 : ℝ) ^ (phaseFloor 3 a 1 + phaseFloor 3 u 0 - phaseFloor 3 (a + u) 1) *
      (5 : ℝ) ^ (phaseFloor 5 a 1 + phaseFloor 5 u 0 - phaseFloor 5 (a + u) 1) := by
  rw [phaseFloor_one_eq_log (by decide : 1 < (3 : ℕ)),
    phaseFloor_zero_eq_log (by decide : 1 < (3 : ℕ)),
    phaseFloor_one_eq_log (by decide : 1 < (3 : ℕ)),
    phaseFloor_one_eq_log (by decide : 1 < (5 : ℕ)),
    phaseFloor_zero_eq_log (by decide : 1 < (5 : ℕ)),
    phaseFloor_one_eq_log (by decide : 1 < (5 : ℕ))]
  simp only [shiftGamma, shiftHeight, threePrimeHeight,
    Nat.log_pow (by decide : 1 < (2 : ℕ))]
  simp only [Nat.cast_mul, Nat.cast_pow,
    zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_sub₀ (by norm_num : (5 : ℝ) ≠ 0),
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_add₀ (by norm_num : (5 : ℝ) ≠ 0),
    zpow_natCast, pow_add, pow_one]
  field_simp
  <;> ring

theorem weighted_phase_transport (a u : ℕ) (t : ℝ) :
    shiftGamma a u * phaseOmega (a + u) t = phaseOmega a t * phaseChi a t u := by
  rw [shiftGamma_eq_floor_powers]
  unfold phaseOmega phaseChi phaseCarry
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have h5 : (5 : ℝ) ≠ 0 := by norm_num
  calc
    _ = ((3 : ℝ) ^ (phaseFloor 3 a 1 + phaseFloor 3 u 0 - phaseFloor 3 (a + u) 1) *
          (3 : ℝ) ^ (phaseFloor 3 (a + u) 1 - phaseFloor 3 (a + u) t)) *
        ((5 : ℝ) ^ (phaseFloor 5 a 1 + phaseFloor 5 u 0 - phaseFloor 5 (a + u) 1) *
          (5 : ℝ) ^ (phaseFloor 5 (a + u) 1 - phaseFloor 5 (a + u) t)) := by ring
    _ = ((3 : ℝ) ^ (phaseFloor 3 a 1 - phaseFloor 3 a t) *
          (3 : ℝ) ^ (-(phaseFloor 3 (a + u) t - phaseFloor 3 a t - phaseFloor 3 u 0))) *
        ((5 : ℝ) ^ (phaseFloor 5 a 1 - phaseFloor 5 a t) *
          (5 : ℝ) ^ (-(phaseFloor 5 (a + u) t - phaseFloor 5 a t - phaseFloor 5 u 0))) := by
      rw [← zpow_add₀ h3, ← zpow_add₀ h5, ← zpow_add₀ h3, ← zpow_add₀ h5]
      congr 2 <;> omega
    _ = _ := by ring

private theorem phase_weight_factor {p : ℕ} (hp : 1 < p) (a : ℕ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (p : ℝ) ^ (⌊((a : ℝ) + 1) * triangleTheta p⌋₊ -
      ⌊((a : ℝ) + t) * triangleTheta p⌋₊) =
      (p : ℝ) ^ (phaseFloor p a 1 - phaseFloor p a t) := by
  have hθ := (triangleTheta_pos hp).le
  have hle : ⌊((a : ℝ) + t) * triangleTheta p⌋₊ ≤
      ⌊((a : ℝ) + 1) * triangleTheta p⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_right (show (a : ℝ) + t ≤ a + 1 by linarith) hθ)
  rw [← zpow_natCast, Int.natCast_sub hle,
    Int.natCast_floor_eq_floor (mul_nonneg (by positivity) hθ),
    Int.natCast_floor_eq_floor (mul_nonneg (by positivity) hθ)]
  rfl

theorem literalLogWeight_eq_phaseOmega (a : ℕ) (v : ℕ × ℕ) :
    (literalLogWeight a v : ℝ) = phaseOmega a (Int.fract (triangleLogPoint v)) := by
  simp only [literalLogWeight, Nat.cast_mul, Nat.cast_pow]
  rw [phase_weight_factor (by decide : 1 < (3 : ℕ)) a _
      (Int.fract_nonneg _) (Int.fract_lt_one _).le,
    phase_weight_factor (by decide : 1 < (5 : ℕ)) a _
      (Int.fract_nonneg _) (Int.fract_lt_one _).le]
  rfl

theorem actual_numerator_eq_phase_triangle (a : ℕ) :
    (dyadicOrderedBlockDigit235 a : ℝ) =
      ∑ v ∈ literalTriangle a, phaseOmega a (Int.fract (triangleLogPoint v)) := by
  rw [actual_numerator_eq_logarithmic_triangle]
  push_cast
  exact Finset.sum_congr rfl (fun v _ => literalLogWeight_eq_phaseOmega a v)

theorem literalTriangle_monotone : Monotone literalTriangle := by
  intro a b hab v hv
  apply mem_literalTriangle_iff.mpr
  exact (mem_literalTriangle_iff.mp hv).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.add_le_add_right hab 1))

/-- The exact first formula of the printed strip proposition. -/
theorem actual_weighted_strip_decomposition (c : ℕ → ℤ) (σ r a : ℕ) :
    shiftedNumerator c σ r a / 15 =
      ∑ s ∈ Finset.range (σ + 1),
        ∑ v ∈ entryStrip (fun n => literalTriangle (a + n * r)) s,
          phaseOmega a (Int.fract (triangleLogPoint v)) *
            ∑ ν ∈ Finset.Icc s σ, (c ν : ℝ) *
              phaseChi a (Int.fract (triangleLogPoint v)) (ν * r) := by
  have hT : Monotone (fun n => literalTriangle (a + n * r)) := by
    intro n m hnm
    exact literalTriangle_monotone (Nat.add_le_add_left (Nat.mul_le_mul_right r hnm) a)
  have hterm : ∀ ν, (c ν : ℝ) * shiftGamma a (ν * r) *
      (dyadicOrderedBlockDigit235 (a + ν * r) : ℝ) =
      ∑ v ∈ literalTriangle (a + ν * r),
        phaseOmega a (Int.fract (triangleLogPoint v)) *
          ((c ν : ℝ) * phaseChi a (Int.fract (triangleLogPoint v)) (ν * r)) := by
    intro ν
    rw [actual_numerator_eq_phase_triangle, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    calc
      _ = (c ν : ℝ) * (shiftGamma a (ν * r) *
          phaseOmega (a + ν * r) (Int.fract (triangleLogPoint v))) := by ring
      _ = _ := by rw [weighted_phase_transport]; ring
  unfold shiftedNumerator
  rw [mul_div_cancel_left₀ _ (by norm_num : (15 : ℝ) ≠ 0)]
  simp_rw [hterm]
  rw [nested_finite_strip_decomposition _ hT]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]

def cubicShiftCoefficient : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => 3
  | _ => -1

/-- Vanishing crossing bits leave exactly the three boundary strips. -/
theorem actual_cubic_no_crossing_strips (a r : ℕ)
    (hcross : ∀ ν : ℕ, ν ≤ 3 → ∀ v ∈ literalTriangle (a + ν * r),
      phaseCarry 3 a (Int.fract (triangleLogPoint v)) (ν * r) = 0 ∧
      phaseCarry 5 a (Int.fract (triangleLogPoint v)) (ν * r) = 0) :
    shiftedNumerator cubicShiftCoefficient 3 r a / 15 =
      -(∑ v ∈ literalTriangle (a + r) \ literalTriangle a,
          phaseOmega a (Int.fract (triangleLogPoint v))) +
        2 * (∑ v ∈ literalTriangle (a + 2 * r) \ literalTriangle (a + r),
          phaseOmega a (Int.fract (triangleLogPoint v))) -
        (∑ v ∈ literalTriangle (a + 3 * r) \ literalTriangle (a + 2 * r),
          phaseOmega a (Int.fract (triangleLogPoint v))) := by
  have hT : Monotone (fun n => literalTriangle (a + n * r)) := by
    intro n m hnm
    exact literalTriangle_monotone (Nat.add_le_add_left (Nat.mul_le_mul_right r hnm) a)
  have hweight : ∀ ν : ℕ, ν ≤ 3 →
      shiftGamma a (ν * r) * (dyadicOrderedBlockDigit235 (a + ν * r) : ℝ) =
        ∑ v ∈ literalTriangle (a + ν * r),
          phaseOmega a (Int.fract (triangleLogPoint v)) := by
    intro ν hν
    rw [actual_numerator_eq_phase_triangle, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [weighted_phase_transport]
    have hc := hcross ν hν v hv
    simp only [phaseChi, hc.1, hc.2, neg_zero, zpow_zero, mul_one, one_mul]
  have hexpand : shiftedNumerator cubicShiftCoefficient 3 r a / 15 =
      (∑ v ∈ literalTriangle a, phaseOmega a (Int.fract (triangleLogPoint v))) -
        3 * (∑ v ∈ literalTriangle (a + r),
          phaseOmega a (Int.fract (triangleLogPoint v))) +
        3 * (∑ v ∈ literalTriangle (a + 2 * r),
          phaseOmega a (Int.fract (triangleLogPoint v))) -
        (∑ v ∈ literalTriangle (a + 3 * r),
          phaseOmega a (Int.fract (triangleLogPoint v))) := by
    unfold shiftedNumerator
    rw [mul_div_cancel_left₀ _ (by norm_num : (15 : ℝ) ≠ 0)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      mul_assoc, hweight 0 (by decide), hweight 1 (by decide),
      hweight 2 (by decide), hweight 3 (by decide)]
    norm_num [cubicShiftCoefficient]
    <;> ring
  rw [hexpand]
  simpa only [zero_mul, one_mul, add_zero] using
    cubic_difference_boundary_strips (fun n => literalTriangle (a + n * r)) hT
      (fun v => phaseOmega a (Int.fract (triangleLogPoint v)))

#print axioms weighted_phase_transport
#print axioms actual_weighted_strip_decomposition
#print axioms actual_cubic_no_crossing_strips

end ErdosProblems.Erdos269.PaperCompleteR20
