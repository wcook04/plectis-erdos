import ErdosProblems.Erdos1041.PaperAnalyticTargets

/-!
# Erdős 1041: two limits of the sufficient conditions

Two propositions of the short paper's section "Three limits of the sufficient
conditions" (`paper/1041/erdos-1041-lemniscate-newton-flow.tex`).

## `res:one-root-gamma-false` (line 838)

`p(z) = z^8 - (3/2)z`, `C` the component of `{|p| ≤ 1}` containing the origin:
`C` contains exactly one zero and a neighbourhood of the closed disc of radius
`5/8`, so `H^1(∂C) > 5π/4`; and `Γ(1/4)^2/(2√π) ≤ (π/2)(1+√2) < 5π/4`.

The component clauses ("exactly one zero", "a neighbourhood of the closed
`5/8` disc") and the final numerical gap are proved here outright.  Two
classical inputs enter `one_root_gamma_false` as explicit, named hypotheses.
Both are now theorems of this tree, and `LobeUnconditional.lean` states the
proposition with no hypotheses:

* `PlanePerimeterBound`: the classical plane encircling bound — the
  one-dimensional Hausdorff measure of the boundary of a bounded planar set
  containing a closed disc of radius `ρ` is at least the circumference `2πρ`.
  (Mathlib has `μH[1]` but no isoperimetric or perimeter-monotonicity
  inequality.)
* `hGammaQuarter`: the standard decimal enclosure `Γ(1/4) ≤ 3.63` of the
  classical constant `Γ(1/4) = 3.625609908…`.  Mathlib has `Real.Gamma` but no
  numerical evaluation of it, and no lemniscate/AGM identity.

## `res:arity-not-capacity` (line 880)

`g(z) = z^3 - (3/400)z - 3/32`: all roots in the open unit disc and
`μ = 187/2000 ≤ 1/2`; the first merger joins two root components, so `k₀ = 2`,
but the component at level `2μ` containing that pair has normalised capacity
`1`.  This module proves the root-disc clause and the least-critical-value
clause, including that `187/2000` is the least critical-value modulus.
`ArityNotCapacity.lean` states and proves the whole proposition as
`Arity.arity_not_capacity`: the merger clause and `k₀ = 2` outright, and the
capacity clause modulo the named hypothesis `LemniscateTransfiniteDiameter`,
the classical value `t^{1/n}` of the transfinite diameter of the filled
lemniscate `{|p| ≤ t}` of a monic polynomial `p` of degree `n`.  The extra
theorem `arity_critical_values_lt_double_mu` records that both critical values
lie strictly below the level `2μ`.
-/

set_option autoImplicit false

noncomputable section

namespace ErdosProblems.Erdos1041.PaperCompleteR21

open Polynomial Set

/-! ## `res:one-root-gamma-false` -/

namespace Lobe

/-- `p(z) = z^8 - (3/2)z`. -/
def lobePolynomial : ℂ[X] := X ^ 8 - C (3 / 2) * X

theorem lobe_eval (z : ℂ) : lobePolynomial.eval z = z ^ 8 - (3 / 2 : ℂ) * z := by
  simp [lobePolynomial]

theorem lobe_eval_factor (z : ℂ) :
    lobePolynomial.eval z = z * (z ^ 7 - (3 / 2 : ℂ)) := by
  rw [lobe_eval]; ring

theorem lobe_root_iff (z : ℂ) :
    lobePolynomial.eval z = 0 ↔ z = 0 ∨ z ^ 7 = (3 / 2 : ℂ) := by
  rw [lobe_eval_factor, mul_eq_zero, sub_eq_zero]

theorem lobe_norm_le {z : ℂ} :
    ‖lobePolynomial.eval z‖ ≤ ‖z‖ ^ 8 + (3 / 2 : ℝ) * ‖z‖ := by
  rw [lobe_eval]
  have H := norm_sub_le (z ^ 8) ((3 / 2 : ℂ) * z)
  simpa [norm_pow, norm_mul, norm_div] using H

/-- The whole open disc of radius `16/25 = 0.64` is inside `{|p| ≤ 1}`. -/
theorem lobe_wide_disk {z : ℂ} (hz : ‖z‖ < 16 / 25) :
    ‖lobePolynomial.eval z‖ ≤ 1 := by
  have h0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hp : ‖z‖ ^ 8 ≤ (16 / 25 : ℝ) ^ 8 := pow_le_pow_left₀ h0 hz.le 8
  have hnum : (16 / 25 : ℝ) ^ 8 + 24 / 25 ≤ 1 := by norm_num
  have := lobe_norm_le (z := z)
  linarith

/-- Every point of the circle `|z| = 4/5` is outside the closed unit sublevel. -/
theorem lobe_outer_circle {z : ℂ} (hz : ‖z‖ = 4 / 5) :
    1 < ‖lobePolynomial.eval z‖ := by
  have hid : (3 / 2 : ℂ) * z = z ^ 8 - lobePolynomial.eval z := by
    rw [lobe_eval]; ring
  have H : (3 / 2 : ℝ) * ‖z‖ ≤ ‖z‖ ^ 8 + ‖lobePolynomial.eval z‖ := by
    calc
      (3 / 2 : ℝ) * ‖z‖ = ‖(3 / 2 : ℂ) * z‖ := by simp [norm_mul, norm_div]
      _ = ‖z ^ 8 - lobePolynomial.eval z‖ := congrArg norm hid
      _ ≤ ‖z ^ 8‖ + ‖lobePolynomial.eval z‖ := norm_sub_le _ _
      _ = ‖z‖ ^ 8 + ‖lobePolynomial.eval z‖ := by rw [norm_pow]
  rw [hz] at H
  norm_num at H
  linarith

/-- Inside the barrier disc the only zero of `p` is the origin. -/
theorem lobe_unique_root_in_barrier {z : ℂ} (hz : ‖z‖ ≤ 4 / 5) :
    lobePolynomial.eval z = 0 ↔ z = 0 := by
  constructor
  · intro hroot
    rcases (lobe_root_iff z).1 hroot with he | he
    · exact he
    · have hnorm : ‖z‖ ^ 7 = (3 / 2 : ℝ) := by
        have H := congrArg norm he
        simpa [norm_pow, norm_div] using H
      have hpow : ‖z‖ ^ 7 ≤ (4 / 5 : ℝ) ^ 7 := pow_le_pow_left₀ (norm_nonneg z) hz 7
      norm_num at hpow
      linarith
  · rintro rfl
    simp [lobePolynomial]

/-- The closed unit sublevel set of `p`. -/
def lobeSublevel : Set ℂ := {z : ℂ | ‖lobePolynomial.eval z‖ ≤ 1}

/-- `C`: the connected component of `{|p| ≤ 1}` containing the origin. -/
def lobeComponent : Set ℂ := connectedComponentIn lobeSublevel 0

theorem zero_mem_lobeSublevel : (0 : ℂ) ∈ lobeSublevel := by
  simp [lobeSublevel, lobePolynomial]

theorem zero_mem_lobeComponent : (0 : ℂ) ∈ lobeComponent :=
  mem_connectedComponentIn zero_mem_lobeSublevel

/-- The wide open disc is contained in `C`. -/
theorem wide_ball_subset : Metric.ball (0 : ℂ) (16 / 25) ⊆ lobeComponent := by
  apply IsPreconnected.subset_connectedComponentIn
  · exact (convex_ball (0 : ℂ) (16 / 25)).isPreconnected
  · simpa using (by norm_num : (0 : ℝ) < 16 / 25)
  · intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact lobe_wide_disk hz

/-- **Clause 2.** `C` contains a neighbourhood of the closed disc of radius
`5/8`. -/
theorem lobe_nhd_of_closed_disc :
    ∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) (5 / 8) ⊆ U ∧ U ⊆ lobeComponent := by
  refine ⟨Metric.ball (0 : ℂ) (16 / 25), Metric.isOpen_ball, ?_, wide_ball_subset⟩
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-- The barrier argument: `C` stays inside the disc of radius `4/5`. -/
theorem lobeComponent_subset_barrier :
    lobeComponent ⊆ Metric.closedBall (0 : ℂ) (4 / 5) := by
  by_contra hcon
  rw [Set.not_subset] at hcon
  obtain ⟨w, hwC, hw⟩ := hcon
  have hpre : IsPreconnected lobeComponent := isPreconnected_connectedComponentIn
  have hsub : lobeComponent ⊆ lobeSublevel := connectedComponentIn_subset _ _
  have hcover : lobeComponent ⊆
      Metric.ball (0 : ℂ) (4 / 5) ∪ (Metric.closedBall (0 : ℂ) (4 / 5))ᶜ := by
    intro z hz
    by_cases h : ‖z‖ < 4 / 5
    · left; rw [Metric.mem_ball, dist_zero_right]; exact h
    · push_neg at h
      rcases eq_or_lt_of_le h with heq | hlt
      · exfalso
        have := lobe_outer_circle (z := z) heq.symm
        have hz' : ‖lobePolynomial.eval z‖ ≤ 1 := hsub hz
        linarith
      · right
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
        exact hlt
  have h1 : (lobeComponent ∩ Metric.ball (0 : ℂ) (4 / 5)).Nonempty :=
    ⟨0, zero_mem_lobeComponent, by simpa using (by norm_num : (0 : ℝ) < 4 / 5)⟩
  have h2 : (lobeComponent ∩ (Metric.closedBall (0 : ℂ) (4 / 5))ᶜ).Nonempty := ⟨w, hwC, hw⟩
  obtain ⟨x, _, hx1, hx2⟩ :=
    hpre _ _ Metric.isOpen_ball Metric.isClosed_closedBall.isOpen_compl hcover h1 h2
  exact hx2 (Metric.ball_subset_closedBall hx1)

/-- **Clause 1.** `C` contains exactly one zero of `p`, namely the origin. -/
theorem lobe_unique_zero :
    {z : ℂ | z ∈ lobeComponent ∧ lobePolynomial.eval z = 0} = {(0 : ℂ)} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hzC, hz0⟩
    have hb := lobeComponent_subset_barrier hzC
    rw [Metric.mem_closedBall, dist_zero_right] at hb
    exact (lobe_unique_root_in_barrier hb).mp hz0
  · rintro rfl
    exact ⟨zero_mem_lobeComponent, by simp [lobePolynomial]⟩

theorem lobeComponent_bounded : Bornology.IsBounded lobeComponent :=
  (Metric.isBounded_closedBall).subset lobeComponent_subset_barrier

/-- **Clause 4.** The numerical gap `(π/2)(1+√2) < 5π/4`. -/
theorem lobe_perimeter_numeric_gap :
    (Real.pi / 2) * (1 + Real.sqrt 2) < 5 * Real.pi / 4 := by
  have hs : Real.sqrt 2 < (3 / 2 : ℝ) := by
    have H := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  nlinarith [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr hs)]

/-- The external classical input for the perimeter clause: for a bounded
planar set containing a closed disc of radius `ρ`, the one-dimensional
Hausdorff measure of the boundary is at least the circumference `2πρ`.
This is absent from Mathlib (which has `μH[1]` but no perimeter-monotonicity
or isoperimetric inequality) and from this tree. -/
def PlanePerimeterBound : Prop :=
  ∀ (A : Set ℂ) (x : ℂ) (ρ : ℝ), 0 ≤ ρ → Bornology.IsBounded A →
    Metric.closedBall x ρ ⊆ A →
    ENNReal.ofReal (2 * Real.pi * ρ)
      ≤ MeasureTheory.Measure.hausdorffMeasure 1 (frontier A)

/-- **Clause 3, modulo the plane encircling bound.** -/
theorem lobe_perimeter_gt (hperim : PlanePerimeterBound) :
    ENNReal.ofReal (5 * Real.pi / 4)
      < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) := by
  have hball : Metric.closedBall (0 : ℂ) (63 / 100) ⊆ lobeComponent := by
    refine subset_trans ?_ wide_ball_subset
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have h := hperim lobeComponent 0 (63 / 100) (by norm_num) lobeComponent_bounded hball
  refine lt_of_lt_of_le ?_ h
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  nlinarith [Real.pi_pos]

/-- **Clause 5, modulo the classical value of `Γ(1/4)`.**
`Γ(1/4)^2/(2√π) ≤ (π/2)(1+√2)`. -/
theorem lobe_gamma_constant_le (hGammaQuarter : Real.Gamma (1 / 4) ≤ 3.63) :
    Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)
      ≤ (Real.pi / 2) * (1 + Real.sqrt 2) := by
  have hπ : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hsπ0 : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hsπ : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hsπlb : (1.772 : ℝ) ≤ Real.sqrt Real.pi := by nlinarith
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2lb : (1.414 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hG0 : 0 ≤ Real.Gamma (1 / 4) := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hGsq : Real.Gamma (1 / 4) ^ 2 ≤ 13.1769 := by nlinarith
  have hden : 0 < 2 * Real.sqrt Real.pi := by nlinarith
  have hAB : (1.772 : ℝ) * 2.414 ≤ Real.sqrt Real.pi * (1 + Real.sqrt 2) :=
    mul_le_mul hsπlb (by linarith) (by norm_num) (by linarith)
  have hT : (3.1415 : ℝ) * (1.772 * 2.414)
      ≤ Real.pi * (Real.sqrt Real.pi * (1 + Real.sqrt 2)) :=
    mul_le_mul hπ.le hAB (by norm_num) (by linarith [Real.pi_pos])
  rw [div_le_iff₀ hden]
  nlinarith [hT, hGsq]

/-- **The whole proposition `res:one-root-gamma-false`**, modulo the two named
external inputs. -/
theorem one_root_gamma_false (hperim : PlanePerimeterBound)
    (hGammaQuarter : Real.Gamma (1 / 4) ≤ 3.63) :
    {z : ℂ | z ∈ lobeComponent ∧ lobePolynomial.eval z = 0} = {(0 : ℂ)} ∧
      (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) (5 / 8) ⊆ U ∧
        U ⊆ lobeComponent) ∧
      ENNReal.ofReal (5 * Real.pi / 4)
        < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) ∧
      Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)
        ≤ (Real.pi / 2) * (1 + Real.sqrt 2) ∧
      (Real.pi / 2) * (1 + Real.sqrt 2) < 5 * Real.pi / 4 :=
  ⟨lobe_unique_zero, lobe_nhd_of_closed_disc, lobe_perimeter_gt hperim,
    lobe_gamma_constant_le hGammaQuarter, lobe_perimeter_numeric_gap⟩

end Lobe

/-! ## `res:arity-not-capacity`: the elementary clauses -/

namespace Arity

/-- `g(z) = z^3 - (3/400)z - 3/32`. -/
def G : ℂ[X] := X ^ 3 + (C (-3 / 400 : ℂ) * X ^ 1 + C (-3 / 32 : ℂ))

@[simp] theorem eval_G (z : ℂ) : G.eval z = z ^ 3 - (3 / 400 : ℂ) * z - 3 / 32 := by
  simp only [G, eval_add, eval_pow, eval_X, eval_mul, eval_C, pow_one]
  ring

theorem G_monic_and_degree : G.Monic ∧ G.natDegree = 3 := by
  let tail : ℂ[X] := C (-3 / 400 : ℂ) * X ^ 1 + C (-3 / 32 : ℂ)
  have h1 : (C (-3 / 400 : ℂ) * X ^ 1).degree ≤ (1 : WithBot ℕ) :=
    degree_C_mul_X_pow_le 1 (-3 / 400 : ℂ)
  have h2 : (C (-3 / 32 : ℂ)).degree ≤ (1 : WithBot ℕ) :=
    le_trans degree_C_le (by norm_num)
  have ht : tail.degree ≤ (1 : WithBot ℕ) :=
    le_trans (degree_add_le _ _) (max_le h1 h2)
  have hlt : tail.degree < (X ^ 3 : ℂ[X]).degree := by
    rw [degree_X_pow]
    exact lt_of_le_of_lt ht (by norm_num)
  have hm : G.Monic := (monic_X_pow 3).add_of_left hlt
  have hd : G.degree = (3 : WithBot ℕ) := by
    change (X ^ 3 + tail).degree = _
    rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
    simp
  exact ⟨hm, natDegree_eq_of_degree_eq_some hd⟩

@[simp] theorem eval_derivative_G (z : ℂ) :
    G.derivative.eval z = 3 * z ^ 2 - 3 / 400 := by
  norm_num [G, Polynomial.derivative_pow]
  ring

/-- **Clause 1.** All roots lie in the open unit disc. -/
theorem arity_roots_in_open_disc {z : ℂ} (hz : G.eval z = 0) : ‖z‖ < 1 := by
  rw [eval_G] at hz
  have he : z ^ 3 = (3 / 400 : ℂ) * z + 3 / 32 := by linear_combination hz
  have hbound : ‖z‖ ^ 3 ≤ (3 / 400 : ℝ) * ‖z‖ + 3 / 32 := by
    calc
      ‖z‖ ^ 3 = ‖z ^ 3‖ := (norm_pow z 3).symm
      _ = ‖(3 / 400 : ℂ) * z + 3 / 32‖ := congrArg norm he
      _ ≤ ‖(3 / 400 : ℂ) * z‖ + ‖(3 / 32 : ℂ)‖ := norm_add_le _ _
      _ = (3 / 400 : ℝ) * ‖z‖ + 3 / 32 := by
        rw [norm_mul]; norm_num
  by_contra hnot
  have hge : 1 ≤ ‖z‖ := le_of_not_gt hnot
  have hprod : 0 ≤ (‖z‖ - 1) * (‖z‖ ^ 2 + ‖z‖) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith [norm_nonneg z]

theorem critical_factor (z : ℂ) :
    G.derivative.eval z = (3 : ℂ) * (z - 1 / 20) * (z + 1 / 20) := by
  rw [eval_derivative_G]; ring

theorem all_critical_points (z : ℂ) :
    G.derivative.eval z = 0 ↔ z = 1 / 20 ∨ z = -(1 / 20) := by
  rw [critical_factor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · norm_num at h3
      · exact Or.inl (by linear_combination h4)
    · exact Or.inr (by linear_combination h2)
  · rintro (rfl | rfl) <;> norm_num

@[simp] theorem value_plus : G.eval (1 / 20 : ℂ) = -47 / 500 := by
  rw [eval_G]; norm_num

@[simp] theorem value_minus : G.eval (-(1 / 20) : ℂ) = -187 / 2000 := by
  rw [eval_G]; norm_num

theorem norm_value_plus : ‖G.eval (1 / 20 : ℂ)‖ = 47 / 500 := by
  rw [value_plus, show (-47 / 500 : ℂ) = ((-47 / 500 : ℝ) : ℂ) by norm_num,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem norm_value_minus : ‖G.eval (-(1 / 20) : ℂ)‖ = 187 / 2000 := by
  rw [value_minus, show (-187 / 2000 : ℂ) = ((-187 / 2000 : ℝ) : ℂ) by norm_num,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- **Clause 2, first half.** `μ = 187/2000` really is the least critical-value
modulus, not a supplied value. -/
theorem arity_criticalMinimum :
    PaperAnalyticTargets.CriticalMinimum G (187 / 2000 : ℝ) := by
  constructor
  · exact ⟨-(1 / 20), (all_critical_points _).mpr (Or.inr rfl), norm_value_minus.symm⟩
  · rintro x ⟨c, hc, rfl⟩
    rcases (all_critical_points c).mp hc with rfl | rfl
    · rw [norm_value_plus]; norm_num
    · rw [norm_value_minus]

/-- **Clause 2, second half.** `μ ≤ 1/2`. -/
theorem arity_mu_le_half : (187 / 2000 : ℝ) ≤ 1 / 2 := by norm_num

/-- Both critical values lie strictly below the level `2μ`, so every critical
point lies in `{|g| < 2μ}`.  That set is connected, and its closure is the whole
filled lemniscate `{|g| ≤ 2μ}`: see `Arity.closure_doubleLevelComponent` in
`ArityNotCapacity.lean`. -/
theorem arity_critical_values_lt_double_mu (c : ℂ) (hc : G.derivative.eval c = 0) :
    ‖G.eval c‖ < 2 * (187 / 2000 : ℝ) := by
  rcases (all_critical_points c).mp hc with rfl | rfl
  · rw [norm_value_plus]; norm_num
  · rw [norm_value_minus]; norm_num

/-- The elementary part of `res:arity-not-capacity`: `g` is a monic cubic whose
roots lie in the open unit disc, whose critical points are `±1/20`, and whose
least critical-value modulus is `μ = 187/2000 ≤ 1/2`.  `Arity.arity_not_capacity`
in `ArityNotCapacity.lean` states the whole proposition, including `k₀ = 2` and
the normalised-capacity clause. -/
theorem arity_elementary_clauses :
    G.Monic ∧ G.natDegree = 3 ∧
      PaperAnalyticTargets.RootsInOpenUnitDisc G ∧
      (∀ z : ℂ, G.derivative.eval z = 0 ↔ z = 1 / 20 ∨ z = -(1 / 20)) ∧
      PaperAnalyticTargets.CriticalMinimum G (187 / 2000 : ℝ) ∧
      (187 / 2000 : ℝ) ≤ 1 / 2 :=
  ⟨G_monic_and_degree.1, G_monic_and_degree.2, fun _ => arity_roots_in_open_disc,
    all_critical_points, arity_criticalMinimum, arity_mu_le_half⟩

end Arity

#print axioms Lobe.lobe_unique_zero
#print axioms Lobe.lobe_nhd_of_closed_disc
#print axioms Lobe.lobe_perimeter_numeric_gap
#print axioms Lobe.lobe_perimeter_gt
#print axioms Lobe.lobe_gamma_constant_le
#print axioms Lobe.one_root_gamma_false
#print axioms Arity.arity_roots_in_open_disc
#print axioms Arity.arity_criticalMinimum
#print axioms Arity.arity_critical_values_lt_double_mu
#print axioms Arity.arity_elementary_clauses

end ErdosProblems.Erdos1041.PaperCompleteR21
