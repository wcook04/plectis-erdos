import Mathlib
import ErdosProblems.Erdos257.PaperCompleteR8.DyadicDivisorFrames
import ErdosProblems.Erdos257.PaperCompleteR8.PrimeHarmonicBlocks

/-!
# Divisor-product masses and the separating host's weighted frame budget

The reciprocal divisor sum is computed from the actual prime product. Its
exponential upper bound and the prescribed harmonic scales give a summable
sequence of literal dyadic frame weights. Identifying these literal weights
with the finite-prime weighted term uses the odd-cofactor valuation identity;
the divergent logarithmic moment is a separate remaining step.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset

/-- Sum of divisors of a product of distinct primes. -/
theorem sum_divisors_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ d ∈ (P.prod id).divisors, d) = ∏ p ∈ P, (p + 1) := by
  classical
  revert hP
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | @insert p P hp ih =>
    intro hP
    have hprime := hP p (mem_insert_self p P)
    have hrest : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (P.prod id) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply hprime.coprime_iff_not_dvd.mpr
      intro hd
      have heq := (Nat.prime_dvd_prime_iff_eq hprime (hrest q hq)).mp hd
      exact hp (heq.symm ▸ hq)
    rw [prod_insert hp, prod_insert hp]
    change (∑ d ∈ (p * P.prod id).divisors, d) =
      (p + 1) * ∏ q ∈ P, (q + 1)
    rw [hcop.sum_divisors_mul, hprime.sum_divisors, ih hrest]

/-- Reciprocal divisor sums are the ordinary divisor sum divided by the integer. -/
theorem reciprocal_divisor_sum_eq (M : ℕ) (hM : 0 < M) :
    (∑ d ∈ M.divisors, (1 : ℝ) / d) =
      (∑ d ∈ M.divisors, (d : ℝ)) / (M : ℝ) := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  apply (eq_div_iff hMne).2
  calc
    _ = ∑ d ∈ M.divisors, (M : ℝ) / d := by
      rw [sum_mul]
      apply sum_congr rfl
      intro d hd
      ring
    _ = ∑ d ∈ M.divisors, ((M / d : ℕ) : ℝ) := by
      apply sum_congr rfl
      intro d hd
      exact (Nat.cast_div (Nat.dvd_of_mem_divisors hd)
        (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne')).symm
    _ = _ := Nat.sum_div_divisors M (fun d : ℕ => (d : ℝ))

/-- The exact Euler product of the finite divisor frame. -/
theorem reciprocal_divisor_prime_product (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ d ∈ (P.prod id).divisors, (1 : ℝ) / d) =
      ∏ p ∈ P, (1 + (1 : ℝ) / p) := by
  have hM : 0 < P.prod id := prod_pos (fun p hp => (hP p hp).pos)
  rw [reciprocal_divisor_sum_eq _ hM]
  have hnum : (∑ d ∈ (P.prod id).divisors, (d : ℝ)) = ∏ p ∈ P, ((p : ℝ) + 1) := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (sum_divisors_prime_product P hP)
    simpa only [Nat.cast_sum, Nat.cast_prod, Nat.cast_add, Nat.cast_one] using h
  have hden : ((P.prod id : ℕ) : ℝ) = ∏ p ∈ P, (p : ℝ) := by simp
  rw [hnum, hden, ← prod_div_distrib]
  apply prod_congr rfl
  intro p hp
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).ne_zero
  field_simp

/-- Harmonic mass bounds the actual reciprocal divisor sum. -/
theorem reciprocal_divisor_prime_product_le_exp (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ d ∈ (P.prod id).divisors, (1 : ℝ) / d) ≤
      Real.exp (∑ p ∈ P, (1 : ℝ) / p) := by
  rw [reciprocal_divisor_prime_product P hP, Real.exp_sum]
  apply prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    simpa only [add_comm] using Real.add_one_le_exp ((1 : ℝ) / p)

def divisorFrameBudget (P : Finset ℕ) (k : ℕ) : ℝ :=
  (∑ d ∈ (P.prod id).divisors, (1 : ℝ) / d) /
    ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1)

/-- Exact literal weighted sum on the actual dyadic divisor frame. -/
theorem dyadic_frame_literal_weight_sum (M k : ℕ) :
    (∑ a ∈ dyadicDivisorFrame M k,
      ((2 : ℝ) ^ (k + 2)) / ((a : ℝ) * ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1))) =
    (∑ d ∈ M.divisors, (1 : ℝ) / d) /
      ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1) := by
  classical
  unfold dyadicDivisorFrame
  rw [sum_image]
  · rw [sum_div]
    apply sum_congr rfl
    intro d hd
    have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
    have hpow : (2 : ℝ) ^ (k + 2) ≠ 0 := by positivity
    have hn : (0 : ℕ) < 2 ^ (k + 2) := Nat.pow_pos (by decide)
    have hh : (1 : ℝ) < 2 ^ (2 ^ (k + 2) : ℕ) := one_lt_pow₀ (by norm_num) hn.ne'
    have hden : (2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1 ≠ 0 := by linarith
    push_cast
    field_simp
    <;> ring
  · intro a ha b hb heq
    exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) heq

/-- The concrete row scales yield a geometric majorant, with explicit constants. -/
theorem divisorFrameBudget_le_geometric (P : Finset ℕ) (k : ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hS : (∑ p ∈ P, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) :
    divisorFrameBudget P k ≤ 6 * (3 / 16 : ℝ) ^ k := by
  let n : ℕ := 2 ^ k
  have hn : 0 < n := Nat.pow_pos (by decide)
  have hnum : (∑ d ∈ (P.prod id).divisors, (1 : ℝ) / d) ≤ 3 * (3 : ℝ) ^ n := by
    have he := (reciprocal_divisor_prime_product_le_exp P hP).trans (Real.exp_le_exp.mpr hS)
    have hpow : Real.exp ((2 : ℝ) ^ k) = Real.exp 1 ^ n := by
      simpa [n] using Real.exp_nat_mul 1 (2 ^ k)
    rw [Real.exp_add, hpow] at he
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n
    have hmul := mul_le_mul hp Real.exp_one_lt_three.le (Real.exp_pos 1).le (by positivity : (0 : ℝ) ≤ 3 ^ n)
    exact he.trans (by simpa [mul_comm] using hmul)
  have hpowid : (2 : ℝ) ^ (2 ^ (k + 2) : ℕ) = (16 : ℝ) ^ n := by
    have hi : (2 : ℕ) ^ (k + 2) = 4 * n := by dsimp [n]; rw [pow_add]; ring
    rw [hi, pow_mul]
    norm_num
  have hbig : (2 : ℝ) ≤ (16 : ℝ) ^ n := by
    have hh := le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 16) hn.ne'
    linarith
  have hden : (0 : ℝ) < (16 : ℝ) ^ n - 1 := by linarith
  have hhalf : (16 : ℝ) ^ n / 2 ≤ (16 : ℝ) ^ n - 1 := by linarith
  have hbound : divisorFrameBudget P k ≤ 6 * (3 / 16 : ℝ) ^ n := by
    unfold divisorFrameBudget
    rw [hpowid]
    calc
      _ ≤ (3 * (3 : ℝ) ^ n) / ((16 : ℝ) ^ n - 1) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ ≤ (3 * (3 : ℝ) ^ n) / ((16 : ℝ) ^ n / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hhalf
      _ = _ := by rw [div_pow]; ring
  have hkn : k ≤ n := (show k < 2 ^ k from Nat.lt_two_pow_self).le
  have hlast := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 3 / 16)
    (by norm_num : (3 / 16 : ℝ) ≤ 1) hkn
  exact hbound.trans (mul_le_mul_of_nonneg_left hlast (by norm_num))

/-- Summability of the actual finite-product frame budgets at the prescribed scales. -/
theorem summable_divisorFrameBudget (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p)
    (hS : ∀ k, (∑ p ∈ P k, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) :
    Summable (fun k => divisorFrameBudget (P k) k) := by
  have hgeo : Summable (fun k : ℕ => 6 * (3 / 16 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(3 / 16 : ℝ)‖ < 1)).mul_left 6
  apply Summable.of_nonneg_of_le _ (fun k => divisorFrameBudget_le_geometric (P k) k (hP k) (hS k)) hgeo
  intro k
  unfold divisorFrameBudget
  apply div_nonneg (sum_nonneg (fun d _ => by positivity))
  have hh : (1 : ℝ) ≤ 2 ^ (2 ^ (k + 2) : ℕ) := one_le_pow₀ (by norm_num)
  linarith

/-- Concrete disjoint odd-prime blocks have a summable divisor-frame budget;
the harmonic supply is proved, not an assumed supplier. -/
theorem exists_disjoint_prime_blocks_summable_divisor_budgets :
    ∃ P : ℕ → Finset ℕ, Pairwise (fun k l => Disjoint (P k) (P l)) ∧
      (∀ k, (∀ p ∈ P k, Nat.Prime p ∧ 2 < p) ∧
        (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p ∧
        (∑ p ∈ P k, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) ∧
      Summable (fun k => divisorFrameBudget (P k) k) := by
  obtain ⟨P, hdisjoint, hP⟩ := exists_separating_prime_blocks
  refine ⟨P, hdisjoint, hP, ?_⟩
  exact summable_divisorFrameBudget P
    (fun k p hp => ((hP k).1 p hp).1) (fun k => (hP k).2.2)

end ErdosProblems.Erdos257.PaperCompleteR8
end
