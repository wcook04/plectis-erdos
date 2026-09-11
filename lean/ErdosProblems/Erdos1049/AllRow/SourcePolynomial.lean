import ErdosProblems.Erdos1049.AllRow.FiniteStates

/-!
# Source-exact finite polynomial approximations

The state variable in `Polynomial S` is distinct from the power-series
variable in `S = ℤ[[q]]`. Both inverse factors of the literal normalized source
ratio are replaced by finite geometric polynomials. Agreement is proved in
both filtrations: the q-filtration after evaluation, and the state-variable
filtration after reduction modulo q.

Verified locally by the focused all-row audit on 2026-09-09.
-/

noncomputable section

namespace ErdosProblems.Erdos1049.AllRow

open scoped BigOperators

/-- A genuinely finite polynomial approximating the source ratio `H_t(w)`. -/
def ratioPolynomial (t B : ℕ) : Polynomial S :=
  (1 - Polynomial.X) ^ 3 *
    (1 - Polynomial.C (PowerSeries.X ^ t) * Polynomial.X) ^ 2 *
    geom B (Polynomial.C (PowerSeries.X ^ t) * Polynomial.X ^ 2) *
    geom B (Polynomial.C (PowerSeries.X ^ (t + 1)) * Polynomial.X ^ 2)

/-- Reduce the coefficient variable q to zero and retain the state variable as
a formal power-series variable. This is a ring homomorphism, not evaluation of
an infinite series at a unit. -/
def gradePolynomial : Polynomial S →+* S :=
  (Polynomial.eval₂RingHom PowerSeries.C PowerSeries.X).comp
    (Polynomial.mapRingHom PowerSeries.constantCoeff)

@[simp] theorem gradePolynomial_C (f : S) :
    gradePolynomial (Polynomial.C f) =
      PowerSeries.C (PowerSeries.constantCoeff f) := by
  simp only [gradePolynomial, RingHom.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.coe_eval₂RingHom, Polynomial.map_C, Polynomial.eval₂_C]

@[simp] theorem gradePolynomial_X :
    gradePolynomial (Polynomial.X : Polynomial S) = PowerSeries.X := by
  simp [gradePolynomial]

@[simp] theorem coeff_gradePolynomial (p : Polynomial S) (r : ℕ) :
    PowerSeries.coeff r (gradePolynomial p) =
      PowerSeries.constantCoeff (p.coeff r) := by
  change PowerSeries.coeff r
    ((p.map PowerSeries.constantCoeff).eval₂ PowerSeries.C PowerSeries.X) = _
  rw [Polynomial.eval₂_C_X_eq_coe]
  simp

private theorem polynomial_eval_geom (B : ℕ) (p : Polynomial S) (x : S) :
    (geom B p).eval x = geom B (p.eval x) := by
  simpa only [Polynomial.coe_evalRingHom] using
    (map_geom (Polynomial.evalRingHom x) B p)

@[simp] theorem ratioPolynomial_coeff_zero (t B : ℕ) (hB : 0 < B) :
    (ratioPolynomial t B).coeff 0 = 1 := by
  have heval : (ratioPolynomial t B).eval 0 = 1 := by
    simp [ratioPolynomial, polynomial_eval_geom, geom_at_zero, hB]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  exact heval

/-- Reconstruct a polynomial in any range containing its support. -/
private theorem polynomial_eq_sum_range (p : Polynomial S) (M : ℕ)
    (hM : p.natDegree ≤ M) :
    p = ∑ r ∈ Finset.range (M + 1), Polynomial.monomial r (p.coeff r) := by
  classical
  ext r
  have hs :
      (∑ k ∈ Finset.range (M + 1), Polynomial.monomial k (p.coeff k)).coeff r =
        if r ∈ Finset.range (M + 1) then p.coeff r else 0 := by
    simp [Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, eq_comm]
  rw [hs]
  split_ifs with hr
  · rfl
  · simp only [Finset.mem_range, not_lt] at hr
    have hdeg : p.natDegree < r := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg]

/-- The finite ratio used by the state machine is exactly polynomial
substitution, provided the chosen range contains the polynomial support. -/
theorem finiteRatio_eq_eval (p : Polynomial S) (M n : ℕ)
    (hM : p.natDegree ≤ M) (hp0 : p.coeff 0 = 1) :
    finiteRatio (fun r => p.coeff r) M n =
      p.eval (PowerSeries.X ^ (n + 1)) := by
  have hp := polynomial_eq_sum_range p M hM
  have he := congrArg (Polynomial.eval (PowerSeries.X ^ (n + 1))) hp
  rw [Polynomial.eval_finset_sum, Finset.sum_range_succ'] at he
  simp only [Polynomial.eval_monomial, pow_zero, mul_one, hp0] at he
  rw [finiteRatio, he]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [← pow_mul]

/-- Exact evaluation of the finite source ratio. -/
theorem eval_ratioPolynomial (t B n : ℕ) :
    (ratioPolynomial t B).eval (PowerSeries.X ^ (n + 1)) =
      (1 - PowerSeries.X ^ (n + 1)) ^ 3 *
        (1 - PowerSeries.X ^ (n + t + 1)) ^ 2 *
        geom B (PowerSeries.X ^ (2 * n + t + 2) : S) *
        geom B (PowerSeries.X ^ (2 * n + t + 3) : S) := by
  simp only [ratioPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, polynomial_eval_geom,
    Polynomial.eval_C, Polynomial.eval_X]
  have h₁ : (PowerSeries.X : S) ^ t * PowerSeries.X ^ (n + 1) =
      PowerSeries.X ^ (n + t + 1) := by
    rw [← pow_add]
    congr 1 <;> omega
  have h₂ : (PowerSeries.X : S) ^ t * (PowerSeries.X ^ (n + 1)) ^ 2 =
      PowerSeries.X ^ (2 * n + t + 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1 <;> ring
  have h₃ : (PowerSeries.X : S) ^ (t + 1) * (PowerSeries.X ^ (n + 1)) ^ 2 =
      PowerSeries.X ^ (2 * n + t + 3) := by
    rw [← pow_mul, ← pow_add]
    congr 1 <;> ring
  rw [h₁, h₂, h₃]

/-- Exact source identification modulo the requested q-cut-off. -/
theorem eval_ratioPolynomial_agree (D B t n : ℕ) (hD : D ≤ B) :
    Agree D ((ratioPolynomial t B).eval (PowerSeries.X ^ (n + 1)))
      (zudilinNormalizedTailStepUnit n t) := by
  rw [eval_ratioPolynomial, zudilinNormalizedTailStepUnit]
  apply Agree.mul
  · apply Agree.mul
    · exact Agree.refl _ _
    · apply geom_agree_inverse D B (2 * n + t + 2) (by omega)
      nlinarith
  · apply geom_agree_inverse D B (2 * n + t + 3) (by omega)
    nlinarith

/-- Source-normalized units, not an unrelated moment model. -/
theorem finiteUnit_agree_source (D B t M : ℕ) (hB : 0 < B) (hD : D ≤ B)
    (hM : (ratioPolynomial t B).natDegree ≤ M) :
    ∀ n, Agree D
      (finiteUnit (fun r => (ratioPolynomial t B).coeff r) M
        (zudilinNormalizedTailUnit 0 t) n)
      (zudilinNormalizedTailUnit n t) := by
  intro n
  induction n with
  | zero => exact Agree.refl _ _
  | succ n ih =>
      rw [finiteUnit, zudilinNormalizedTailUnit_succ]
      apply ih.mul
      rw [finiteRatio_eq_eval (ratioPolynomial t B) M n hM
        (ratioPolynomial_coeff_zero t B hB)]
      exact eval_ratioPolynomial_agree D B t n hD

/-- The normalized tails have exactly the same finite q-jets. -/
theorem finiteTail_agree_source (D B t M : ℕ) (hB : 0 < B) (hD : D ≤ B)
    (hM : (ratioPolynomial t B).natDegree ≤ M) (n : ℕ) :
    Agree D
      (finiteTail (fun r => (ratioPolynomial t B).coeff r) M
        (zudilinNormalizedTailUnit 0 t) n t)
      (zudilinNormalizedTail n t) := by
  exact (finiteUnit_agree_source D B t M hB hD hM n).shift ((n + 1) * t)

/-- The zero-state associated ratio written with the same quadratic
 denominator as the source polynomial. -/
theorem zero_ratio_fraction :
    (1 - PowerSeries.X : S) ^ 5 *
        PowerSeries.invOfUnit (1 - PowerSeries.X ^ 2) 1 =
      zudilinZeroTailAssociatedH := by
  have hfact : (1 - PowerSeries.X : S) * (1 + PowerSeries.X) =
      1 - PowerSeries.X ^ 2 := by ring
  have hi := invOfUnit_mul_one
    (1 - PowerSeries.X : S) (1 + PowerSeries.X : S) (by simp) (by simp)
  rw [hfact] at hi
  have hc : (1 - PowerSeries.X : S) *
      PowerSeries.invOfUnit (1 - PowerSeries.X) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp)
  rw [hi, zudilinZeroTailAssociatedH]
  calc
    ((1 : S) - PowerSeries.X) ^ 5 *
        (PowerSeries.invOfUnit ((1 : S) - PowerSeries.X) 1 *
          PowerSeries.invOfUnit ((1 : S) + PowerSeries.X) 1) =
      ((1 : S) - PowerSeries.X) ^ 4 *
        ((((1 : S) - PowerSeries.X) *
          PowerSeries.invOfUnit ((1 : S) - PowerSeries.X) 1) *
          PowerSeries.invOfUnit ((1 : S) + PowerSeries.X) 1) := by ring
    _ = ((1 : S) - PowerSeries.X) ^ 4 *
          PowerSeries.invOfUnit ((1 : S) + PowerSeries.X) 1 := by rw [hc, one_mul]

/-- The associated source ratio depends on whether the original tail parameter
is zero; it is not reselected when a state moves. -/
def sourceGrade (t : ℕ) : S :=
  if t = 0 then zudilinZeroTailAssociatedH else zudilinPositiveTailAssociatedH

theorem grade_ratioPolynomial_zero (B : ℕ) (hB : 0 < B) :
    gradePolynomial (ratioPolynomial 0 B) =
      (1 - PowerSeries.X : S) ^ 5 * geom B (PowerSeries.X ^ 2 : S) := by
  simp only [ratioPolynomial, map_mul, map_pow, map_sub, map_one,
    map_geom, gradePolynomial_C, gradePolynomial_X, pow_zero,
    map_one, pow_one, PowerSeries.constantCoeff_X, map_zero,
    map_one, zero_mul, one_mul, sub_zero]
  simp only [zero_pow (by omega : 0 + 1 ≠ 0), zero_mul]
  rw [geom_at_zero B hB]
  ring

theorem grade_ratioPolynomial_pos (t B : ℕ) (ht : 0 < t) (hB : 0 < B) :
    gradePolynomial (ratioPolynomial t B) = zudilinPositiveTailAssociatedH := by
  simp [ratioPolynomial, map_geom, gradePolynomial_C, gradePolynomial_X,
    constantCoeff_q_pow, Nat.ne_of_gt ht, Nat.succ_ne_zero,
    geom_at_zero, hB, zudilinPositiveTailAssociatedH]

/-- The first `D` state-variable coefficients of the finite ratio are the
literal source's associated ratio. -/
theorem grade_ratioPolynomial_agree (D B t : ℕ) (hB : 0 < B) (hD : D ≤ B) :
    Agree D (gradePolynomial (ratioPolynomial t B)) (sourceGrade t) := by
  by_cases ht : t = 0
  · subst t
    rw [grade_ratioPolynomial_zero B hB, sourceGrade, if_pos rfl,
      ← zero_ratio_fraction]
    apply Agree.mul (Agree.refl _ _)
    exact geom_agree_inverse D B 2 (by omega) (by omega)
  · rw [grade_ratioPolynomial_pos t B (by omega) hB,
      sourceGrade, if_neg ht]

/-- A finite polynomial model gives the full initial monomial of each actual
normalized source tail, uniformly in the depth, column, and tail parameter. -/
theorem source_tail_initial (j l t : ℕ) :
    (∀ d, d < rowExponent j l →
      PowerSeries.coeff d
        (zudilinBackwardShiftApply j (j + l) (fun n => zudilinNormalizedTail n t))
          = 0) ∧
    PowerSeries.coeff (rowExponent j l)
      (zudilinBackwardShiftApply j (j + l) (fun n => zudilinNormalizedTail n t)) =
        hankelAssociatedCoeff (fun r => PowerSeries.coeff r (sourceGrade t)) j t := by
  let D := rowExponent j l + 1
  let B := D + j + 1
  let p := ratioPolynomial t B
  let M := max p.natDegree j
  let a : ℕ → S := fun r => p.coeff r
  let C : S := zudilinNormalizedTailUnit 0 t
  have hB : 0 < B := by dsimp [B]; omega
  have hDB : D ≤ B := by dsimp [B]; omega
  have hjB : j + 1 ≤ B := by dsimp [B]; omega
  have hpM : p.natDegree ≤ M := le_max_left _ _
  have hjM : j ≤ M := le_max_right _ _
  have hC : PowerSeries.constantCoeff C = 1 := by
    dsimp [C]
    exact constantCoeff_zudilinNormalizedTailUnit 0 t
  have hmodel := finite_row_initial a M C hC j l t hjM
  have hsource : Agree D
      (zudilinBackwardShiftApply j (j + l) (fun n => finiteTail a M C n t))
      (zudilinBackwardShiftApply j (j + l) (fun n => zudilinNormalizedTail n t)) := by
    apply Agree.backward
    intro n
    exact finiteTail_agree_source D B t M hB hDB hpM n
  have hgrade : ∀ r, 0 < r → r ≤ j →
      PowerSeries.constantCoeff (a r) = PowerSeries.coeff r (sourceGrade t) := by
    intro r _ hr
    have h := grade_ratioPolynomial_agree (j + 1) B t hB hjB r (by omega)
    simpa only [coeff_gradePolynomial] using h
  have hassoc := associated_congr
    (fun r => PowerSeries.constantCoeff (a r))
    (fun r => PowerSeries.coeff r (sourceGrade t)) j hgrade t
  constructor
  · intro d hd
    rw [← hsource d (by dsimp [D]; omega)]
    exact hmodel.1 d hd
  · rw [← hsource (rowExponent j l) (by dsimp [D]; omega), hmodel.2, hassoc]

end ErdosProblems.Erdos1049.AllRow
