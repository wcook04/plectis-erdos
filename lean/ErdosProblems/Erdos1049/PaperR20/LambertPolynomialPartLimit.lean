import ErdosProblems.Erdos1049.PaperR20.PolynomialPartUniqueness
import ErdosProblems.Erdos1049.PaperR20.MomentAtInfinity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# The Lambert polynomial part at infinity

This module proves that the finite convolution in `lambertPolynomialPart` is
the actual polynomial part of `P(p) * F(p⁻¹)`.  The analytic input is Tannery's
theorem applied to the shifted divisor-count tail.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Filter Polynomial Topology Finset
open scoped BigOperators

noncomputable section

def realDivisorSeries (q : ℝ) : ℝ :=
  ∑' n : ℕ, (n.divisors.card : ℝ) * q ^ n

lemma realDivisorSeries_summable {q : ℝ} (hq : |q| < 1) :
    Summable (fun n : ℕ => (n.divisors.card : ℝ) * q ^ n) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) * |q| ^ n)
  · simpa using summable_norm_pow_mul_geometric_of_norm_lt_one (r := q) 1 hq
  · intro n
    rw [norm_mul, Real.norm_natCast, norm_pow, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.card_divisors_le_self n) (pow_nonneg (abs_nonneg q) n)

/-- Real form of the pinned Mathlib divisor-antidiagonal identity. -/
lemma realDivisorSeries_eq_lambert (q : ℝ) (hq : |q| < 1) :
    realDivisorSeries q = PaperR16.lambert q := by
  have hsum := realDivisorSeries_summable hq
  have hs := tsum_zero_pnat_eq_tsum_nat hsum
  have hid := tsum_pow_div_one_sub_eq_tsum_sigma (r := q) hq 0
  have hp : (∑' n : ℕ+, q ^ (n : ℕ) / (1 - q ^ (n : ℕ))) =
      ∑' n : ℕ+, ((n : ℕ).divisors.card : ℝ) * q ^ (n : ℕ) := by
    simpa only [pow_zero, one_mul, ArithmeticFunction.sigma_zero_apply] using hid
  calc
    realDivisorSeries q =
        ∑' n : ℕ+, ((n : ℕ).divisors.card : ℝ) * q ^ (n : ℕ) := by
      simpa only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero,
        zero_mul, zero_add, realDivisorSeries] using hs.symm
    _ = ∑' n : ℕ+, q ^ (n : ℕ) / (1 - q ^ (n : ℕ)) := hp.symm
    _ = ∑' n : ℕ, q ^ (n + 1) / (1 - q ^ (n + 1)) :=
      tsum_pnat_eq_tsum_succ (f := fun n : ℕ => q ^ n / (1 - q ^ n))
    _ = PaperR16.lambert q := (PaperR16.lambert_eq_tsum_positive q hq).symm

def divisorTail (i : ℕ) (p : ℝ) : ℝ :=
  ∑' n : ℕ, ((n + i + 1).divisors.card : ℝ) * p⁻¹ ^ (n + 1)

lemma divisorTail_tendsto_zero (i : ℕ) :
    Tendsto (divisorTail i) atTop (𝓝 0) := by
  let bound : ℕ → ℝ := fun n =>
    (i + 1 : ℝ) * (n + 1 : ℝ) * (1 / 2 : ℝ) ^ (n + 1)
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n) := by
    simpa using summable_norm_pow_mul_geometric_of_norm_lt_one
      (R := ℝ) 1 (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
  have hbound : Summable bound := by
    have hs := (summable_nat_add_iff 1).2 hbase
    simpa [bound, mul_assoc] using hs.mul_left (i + 1 : ℝ)
  have ht := tendsto_tsum_of_dominated_convergence
      (f := fun p n => ((n + i + 1).divisors.card : ℝ) * p⁻¹ ^ (n + 1))
      (g := fun _ => (0 : ℝ)) hbound (by
        intro n
        simpa using (tendsto_inv_atTop_zero.pow (n + 1)).const_mul
          (((n + i + 1).divisors.card : ℝ))) (by
        filter_upwards [eventually_ge_atTop (2 : ℝ)] with p hp
        intro n
        have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
        have hinv : |p⁻¹| ≤ (1 / 2 : ℝ) := by
          rw [abs_of_pos (inv_pos.mpr hp0)]
          simpa only [one_div] using (inv_le_inv₀ hp0 (by norm_num)).2 hp
        rw [norm_mul, Real.norm_natCast, norm_pow, Real.norm_eq_abs]
        apply mul_le_mul
        · calc
            ((n + i + 1).divisors.card : ℝ) ≤ (n + i + 1 : ℕ) := by
              exact_mod_cast Nat.card_divisors_le_self (n + i + 1)
            _ ≤ (i + 1 : ℝ) * (n + 1 : ℝ) := by
              push_cast
              have hn : (0 : ℝ) ≤ n := by positivity
              have hi : (0 : ℝ) ≤ i := by positivity
              nlinarith
        · exact pow_le_pow_left₀ (abs_nonneg _) hinv _
        · positivity
        · positivity)
  simpa only [divisorTail, tsum_zero] using ht

def monomialLambertPart (i : ℕ) (p : ℝ) : ℝ :=
  ∑ r ∈ range i, ((i - r).divisors.card : ℝ) * p ^ r

/-- Exact finite-prefix/tail decomposition for one monomial. -/
lemma monomial_lambert_sub_part_eq_tail (i : ℕ) {p : ℝ} (hp : 1 < p) :
    p ^ i * PaperR16.lambert p⁻¹ - monomialLambertPart i p =
      divisorTail i p := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hq : |p⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr (lt_trans zero_lt_one hp))]
    exact inv_lt_one_of_one_lt₀ hp
  have hs := realDivisorSeries_summable hq
  have hsplit := hs.sum_add_tsum_nat_add (i + 1)
  have hprefix : p ^ i *
      (∑ n ∈ range (i + 1), (n.divisors.card : ℝ) * p⁻¹ ^ n) =
      monomialLambertPart i p := by
    rw [Finset.sum_range_succ']
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero, zero_mul,
      mul_zero, zero_add, add_zero]
    rw [Finset.mul_sum, monomialLambertPart]
    rw [← Finset.sum_range_reflect
      (fun r => ((i - r).divisors.card : ℝ) * p ^ r) i]
    apply Finset.sum_congr rfl
    intro r hr
    have hri : r + 1 ≤ i := Nat.succ_le_iff.mpr (Finset.mem_range.mp hr)
    rw [inv_pow]
    calc
      p ^ i * (((r + 1).divisors.card : ℝ) * (p ^ (r + 1))⁻¹) =
          ((r + 1).divisors.card : ℝ) * (p ^ i * (p ^ (r + 1))⁻¹) := by ring
      _ = ((r + 1).divisors.card : ℝ) * p ^ (i - (r + 1)) := by
        rw [← pow_sub₀ p hp0 hri]
      _ = _ := by
        have hindex : i - (i - 1 - r) = r + 1 := by omega
        have hexponent : i - (r + 1) = i - 1 - r := by omega
        rw [hindex]
        rw [hexponent]
  have htail : p ^ i *
      (∑' n : ℕ, ((n + (i + 1)).divisors.card : ℝ) * p⁻¹ ^ (n + (i + 1))) =
      divisorTail i p := by
    unfold divisorTail
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    have he : n + (i + 1) = (n + 1) + i := by omega
    rw [he, pow_add]
    simp only [inv_pow]
    rw [show n + 1 + i = n + i + 1 by omega]
    field_simp [hp0] <;> ring
  rw [← realDivisorSeries_eq_lambert p⁻¹ hq, realDivisorSeries] 
  rw [← hsplit]
  rw [mul_add, hprefix, htail, add_sub_cancel_left]

lemma monomial_lambert_tendsto (i : ℕ) :
    Tendsto (fun p : ℝ =>
      p ^ i * PaperR16.lambert p⁻¹ - monomialLambertPart i p)
      atTop (𝓝 0) := by
  apply (divisorTail_tendsto_zero i).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
  exact (monomial_lambert_sub_part_eq_tail i hp).symm

/-- Evaluation of the literal finite convolution equals the coefficientwise
sum of the monomial polynomial parts. -/
lemma eval_lambertPolynomialPart (P : ℤ[X]) (p : ℝ) :
    realPolynomialEval (lambertPolynomialPart P) p =
      ∑ i ∈ range (P.natDegree + 1), (P.coeff i : ℝ) * monomialLambertPart i p := by
  have eval_intCast (z : ℤ) :
      Polynomial.eval₂ (Int.castRingHom ℝ) p (z : ℤ[X]) = (z : ℝ) := by
    rw [← Polynomial.C_eq_intCast, Polynomial.eval₂_C]
    rfl
  simp [lambertPolynomialPart, realPolynomialEval, monomialLambertPart,
    divisorCount, Finset.mul_sum, Polynomial.eval₂_finset_sum, eval_intCast]

/-- Every integer polynomial has the asserted Lambert polynomial part. -/
theorem hasLambertPolynomialPartLimit (P : ℤ[X]) :
    HasLambertPolynomialPartLimit P := by
  rw [HasLambertPolynomialPartLimit]
  rw [show (fun p : ℝ => realPolynomialEval P p * PaperR16.lambert p⁻¹ -
      realPolynomialEval (lambertPolynomialPart P) p) = fun p : ℝ =>
      ∑ i ∈ range (P.natDegree + 1), (P.coeff i : ℝ) *
        (p ^ i * PaperR16.lambert p⁻¹ - monomialLambertPart i p) by
    funext p
    rw [realPolynomialEval, Polynomial.eval₂_eq_sum_range,
      eval_lambertPolynomialPart]
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    change (P.coeff i : ℝ) * p ^ i * PaperR16.lambert p⁻¹ -
      (P.coeff i : ℝ) * monomialLambertPart i p =
      (P.coeff i : ℝ) * (p ^ i * PaperR16.lambert p⁻¹ - monomialLambertPart i p)
    ring]
  have hsum := tendsto_finset_sum (range (P.natDegree + 1)) (fun i hi =>
    (monomial_lambert_tendsto i).const_mul (P.coeff i : ℝ))
  simpa using hsum

/-- With the two analytic limits discharged, an exact Padé remainder identity
is the sole remaining input needed to identify the paper's `β_m`. -/
theorem coefficientBetaPoly_eq_of_pade_remainder (m : ℕ) (B : ℤ[X])
    (hremainder : ∀ p : ℝ, 1 < p →
      PaperR12.actualMoment p⁻¹ m =
        coefficientAlpha p m * PaperR16.lambert p⁻¹ - realPolynomialEval B p) :
    B = coefficientBetaPoly m :=
  coefficientBetaPoly_unique_of_remainder m B
    (hasLambertPolynomialPartLimit _) (actualMoment_inverse_tendsto_one m) hremainder

#print axioms realDivisorSeries_eq_lambert
#print axioms divisorTail_tendsto_zero
#print axioms hasLambertPolynomialPartLimit
#print axioms coefficientBetaPoly_eq_of_pade_remainder

end
end ErdosProblems.Erdos1049.PaperR20
