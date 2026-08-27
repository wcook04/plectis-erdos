import ErdosProblems.Erdos1041.TetranomialL2Selector

/-!
# Erdős #1041: product-sensitive tetranomial L2 selector

The crude estimate `sum x_i <= card S` discards the root product.  For numbers
in `[0,1]`, the sharp elementary inequality

`sum x_i <= card S - 1 + product x_i`

retains it.  Applied to `x_i = normSq (w_i^s)`, Vieta turns the product into
`normSq(c)^s`.  This module checks the finite inequality and its exact signed
L2 selector consumer; the companion note performs the Vieta specialization.
-/

open scoped ComplexConjugate

namespace ErdosProblems.Erdos1041

/-- For a nonempty finite family in the unit interval, the sum is at most one
less than the cardinality plus the product. -/
theorem sum_le_card_sub_one_add_prod
    {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ S, 0 ≤ x i) (hx1 : ∀ i ∈ S, x i ≤ 1)
    (hne : S.Nonempty) :
    ∑ i ∈ S, x i ≤ (S.card : ℝ) - 1 + ∏ i ∈ S, x i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hne
  | @insert a S ha ih =>
      by_cases hS : S.Nonempty
      · have ih' := ih
          (fun i hi => hx0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hx1 i (Finset.mem_insert_of_mem hi)) hS
        have hP0 : 0 ≤ ∏ i ∈ S, x i :=
          Finset.prod_nonneg fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
        have hP1 : ∏ i ∈ S, x i ≤ 1 :=
          Finset.prod_le_one
            (fun i hi => hx0 i (Finset.mem_insert_of_mem hi))
            (fun i hi => hx1 i (Finset.mem_insert_of_mem hi))
        have hxa0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self _ _)
        have hxa1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self _ _)
        have hpair : (∏ i ∈ S, x i) + x a ≤
            1 + (∏ i ∈ S, x i) * x a := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hP1) (sub_nonneg.mpr hxa1)]
        simp only [Finset.sum_insert ha, Finset.prod_insert ha,
          Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
        nlinarith
      · have hSEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        subst S
        simp

/-- The product of the squared norms of the `s`th powers is the `s`th
power of the squared norm of the product. -/
theorem prod_normSq_pow_eq_normSq_prod_pow
    {ι : Type*} (S : Finset ι) (w : ι → ℂ) (s : ℕ) :
    ∏ i ∈ S, Complex.normSq (w i ^ s) =
      Complex.normSq (∏ i ∈ S, w i) ^ s := by
  classical
  have hpow (z : ℂ) : Complex.normSq (z ^ s) = Complex.normSq z ^ s := by
    induction s with
    | zero => simp [Complex.normSq_apply]
    | succ s ih =>
        rw [pow_succ, pow_succ, Complex.normSq_mul, ih]
  have hprod : Complex.normSq (∏ i ∈ S, w i) =
      ∏ i ∈ S, Complex.normSq (w i) := by
    induction S using Finset.induction_on with
    | empty => simp [Complex.normSq_apply]
    | @insert a S ha ih =>
        simp [ha, Complex.normSq_mul, ih]
  calc
    ∏ i ∈ S, Complex.normSq (w i ^ s) =
        ∏ i ∈ S, Complex.normSq (w i) ^ s := by
          apply Finset.prod_congr rfl
          intro i hi
          exact hpow (w i)
    _ = (∏ i ∈ S, Complex.normSq (w i)) ^ s := by
          rw [Finset.prod_pow]
    _ = Complex.normSq (∏ i ∈ S, w i) ^ s := by rw [hprod]

/-- Vieta-ready magnitude form of the exact product identity. -/
theorem prod_normSq_pow_eq_normSq_constant_pow
    {ι : Type*} (S : Finset ι) (w : ι → ℂ) (s : ℕ) (c : ℂ)
    (hproduct : Complex.normSq (∏ i ∈ S, w i) = Complex.normSq c) :
    ∏ i ∈ S, Complex.normSq (w i ^ s) = Complex.normSq c ^ s := by
  rw [prod_normSq_pow_eq_normSq_prod_pow S w s, hproduct]

/-- The product-sensitive signed selector.  The caller supplies the exact real
product, which is `normSq(c)^s` for a complete monic root family. -/
theorem exists_two_tails_norm_lt_one_of_product_coeff_budget
    {ι : Type*} (S : Finset ι) (v : ι → ℂ)
    (b c moment : ℂ) (productMoment : ℝ)
    (hcard : 2 ≤ S.card) (hmoment : ∑ i ∈ S, v i = moment)
    (hv : ∀ i ∈ S, Complex.normSq (v i) ≤ 1)
    (hproduct : ∏ i ∈ S, Complex.normSq (v i) = productMoment)
    (hcoeff :
      (S.card : ℝ) * Complex.normSq c +
          Complex.normSq b * ((S.card : ℝ) - 1 + productMoment) +
            2 * (conj c * b * moment).re <
        (S.card : ℝ) - 1) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      ‖c + b * v i‖ < 1 ∧ ‖c + b * v j‖ < 1 := by
  have hv0 : ∀ i ∈ S, 0 ≤ Complex.normSq (v i) :=
    fun i hi => Complex.normSq_nonneg _
  have hne : S.Nonempty := Finset.nonempty_of_ne_empty (by
    intro h
    subst S
    simp at hcard)
  have hsum := sum_le_card_sub_one_add_prod S
    (fun i => Complex.normSq (v i)) hv0 hv hne
  rw [hproduct] at hsum
  have hb0 : 0 ≤ Complex.normSq b := Complex.normSq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsum hb0
  apply exists_two_tails_norm_lt_one_of_exact_L2_budget S v b c hcard
  rw [hmoment]
  nlinarith

end ErdosProblems.Erdos1041
