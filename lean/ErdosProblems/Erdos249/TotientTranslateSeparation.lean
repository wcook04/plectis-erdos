import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Extremal separation of normalized totient translates

For distinct nonnegative shifts, the normalized totient translates have
supremum distance one, even after any fixed cutoff. A prime in a reduced
arithmetic progression makes one value close to one; a prescribed product
of other primes makes the second close to zero. Only one translate must be
prime. The product is chosen using divergence of the reciprocal-prime sum.

This is the arithmetic input to a uniform finite-rank approximation barrier.
It does not assert irrationality of the binary totient series.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace ErdosProblems.Erdos249.TotientTranslateSeparation

def normalizedTotient (n : ℕ) : ℝ := (Nat.totient n : ℝ) / n

/-- Both indices in the corresponding paper matrix range over positive integers. -/
def totientHankel (i j : ℕ) : ℝ := normalizedTotient (i + j + 2)

theorem normalizedTotient_nonneg (n : ℕ) : 0 ≤ normalizedTotient n := by
  unfold normalizedTotient
  positivity

theorem normalizedTotient_le_one (n : ℕ) : normalizedTotient n ≤ 1 := by
  by_cases hn : n = 0
  · simp [normalizedTotient, hn]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).2
    exact_mod_cast Nat.totient_le n

theorem totientHankel_abs_le_one (i j : ℕ) : |totientHankel i j| ≤ 1 := by
  rw [totientHankel, abs_of_nonneg (normalizedTotient_nonneg _)]
  exact normalizedTotient_le_one _

private theorem product_times_sum_bound {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) :
    (∏ i ∈ s, (1 - x i)) * (1 + ∑ i ∈ s, x i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hxa := hx a (Finset.mem_insert_self _ _)
      have hxs : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1 :=
        fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have hP : 0 ≤ ∏ i ∈ s, (1 - x i) :=
        Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hxs i hi).2
      have hS : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i hi => (hxs i hi).1
      have hdrop : (1 - x a) * (1 + (x a + ∑ i ∈ s, x i)) ≤
          1 + ∑ i ∈ s, x i := by
        nlinarith [mul_nonneg hxa.1 hS, sq_nonneg (x a)]
      have h := mul_le_mul_of_nonneg_left hdrop hP
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      nlinarith [ih hxs]

/-- Primes above any fixed bound have finite Euler products arbitrarily close to zero. -/
theorem exists_small_prime_product (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ B < p) ∧
      (∏ p ∈ P, (1 - (1 : ℝ) / p)) < ε := by
  classical
  let f : ℕ → ℝ := fun n => if n.Prime ∧ B < n then 1 / n else 0
  have hf0 : ∀ n, 0 ≤ f n := by
    intro n
    simp only [f]
    split_ifs <;> positivity
  have hns : ¬ Summable f := by
    intro hf
    apply not_summable_one_div_on_primes
    apply hf.congr_atTop
    filter_upwards [eventually_gt_atTop B] with n hn
    simp [f, hn, Set.indicator_apply]
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, 1 / ε < ∑ n ∈ s, f n := by
    by_contra h
    push_neg at h
    exact hns (summable_of_sum_le hf0 h)
  let P := s.filter fun p => p.Prime ∧ B < p
  have hP : ∀ p ∈ P, p.Prime ∧ B < p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hsum : 1 / ε < ∑ p ∈ P, (1 : ℝ) / p := by
    simpa only [P, Finset.sum_filter, f] using hs
  have hunit : ∀ p ∈ P, 0 ≤ (1 : ℝ) / p ∧ (1 : ℝ) / p ≤ 1 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).1.one_le
    exact ⟨by positivity, (div_le_one (by linarith)).2 hp1⟩
  have hbound := product_times_sum_bound P (fun p : ℕ => (1 : ℝ) / p) hunit
  have hsum0 : 0 ≤ ∑ p ∈ P, (1 : ℝ) / p := Finset.sum_nonneg fun p _ => by positivity
  refine ⟨P, hP, ?_⟩
  have hmul : 1 < ε * (∑ p ∈ P, (1 : ℝ) / p) := by
    have h := mul_lt_mul_of_pos_left hsum hε
    simpa [hε.ne'] using h
  by_contra hnot
  have he : ε ≤ ∏ p ∈ P, (1 - (1 : ℝ) / p) := le_of_not_gt hnot
  have h := mul_le_mul_of_nonneg_right he (by linarith :
    0 ≤ 1 + ∑ p ∈ P, (1 : ℝ) / p)
  nlinarith

theorem normalizedTotient_product {n : ℕ} (hn : n ≠ 0) :
    normalizedTotient n = ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p) := by
  have heq : (Nat.totient n : ℝ) = (n : ℝ) *
      ∏ p ∈ n.primeFactors, (1 - (1 : ℝ) / p) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at h
    simpa only [one_div] using h
  unfold normalizedTotient
  rw [heq]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp [hnR]

/-- Prescribing prime divisors only decreases the normalized totient. -/
theorem normalizedTotient_le_prime_product (P : Finset ℕ) {n : ℕ} (hn : n ≠ 0)
    (hP : ∀ p ∈ P, p.Prime ∧ p ∣ n) :
    normalizedTotient n ≤ ∏ p ∈ P, (1 - (1 : ℝ) / p) := by
  rw [normalizedTotient_product hn]
  apply Finset.prod_le_prod_of_subset_of_le_one
  · intro p hp
    exact (hP p hp).1.mem_primeFactors (hP p hp).2 hn
  · intro p hp
    have hp1 : (1 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    exact sub_nonneg.mpr ((div_le_one (by linarith)).2 hp1)
  · intro p _ _
    have : 0 ≤ (1 : ℝ) / p := by positivity
    linarith

private theorem separation_of_lt (i k : ℕ) (hik : i < k)
    (N : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ j, N < j ∧ 1 - η < totientHankel i j - totientHankel k j := by
  let Δ := k - i
  have hΔ : 0 < Δ := by dsimp [Δ]; omega
  obtain ⟨P, hP, hsmall⟩ := exists_small_prime_product Δ (η / 2) (by linarith)
  let M := ∏ p ∈ P, p
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hP p hp).1.ne_zero
  have hcop : Δ.Coprime M := by
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    exact ((hP p hp).1.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hΔ (hP p hp).2)).symm
  have hcopZ : IsCoprime (-(Δ : ℤ)) (M : ℤ) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).neg_left
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / (η / 2))
  obtain ⟨p, hplarge, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_zmodEq (K + i + N + 2) hM hcopZ
  have hMdiv : M ∣ p + Δ := by
    have hz : (p : ℤ) + (Δ : ℤ) ≡ 0 [ZMOD (M : ℤ)] := by
      simpa using hpmod.add_right (Δ : ℤ)
    exact_mod_cast Int.modEq_zero_iff_dvd.mp hz
  have hlow : normalizedTotient (p + Δ) < η / 2 := by
    apply lt_of_le_of_lt (normalizedTotient_le_prime_product P (by omega) ?_) hsmall
    intro q hq
    exact ⟨(hP q hq).1, (Finset.dvd_prod_of_mem (fun q : ℕ => q) hq).trans hMdiv⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpinv : (1 : ℝ) / p < η / 2 := by
    apply (div_lt_iff₀ hpR).2
    have hKp : (K : ℝ) < p := by exact_mod_cast (show K < p by omega)
    have h := mul_lt_mul_of_pos_left (hK.trans hKp) (by linarith : 0 < η / 2)
    rwa [mul_one_div_cancel (by linarith : η / 2 ≠ 0)] at h
  have hhigh : 1 - η / 2 < normalizedTotient p := by
    unfold normalizedTotient
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one, sub_div,
      div_self hpR.ne']
    linarith
  let j := p - (i + 2)
  have hj : N < j := by dsimp [j]; omega
  have he1 : i + j + 2 = p := by dsimp [j]; omega
  have he2 : k + j + 2 = p + Δ := by dsimp [j, Δ]; omega
  refine ⟨j, hj, ?_⟩
  simpa only [totientHankel, he1, he2] using (by linarith :
    1 - η < normalizedTotient p - normalizedTotient (p + Δ))

/-- The supremum distance is one, with witnesses beyond every fixed cutoff. -/
theorem totientHankel_row_separation_cofinal (i k : ℕ) (hik : i ≠ k)
    (N : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ j, N < j ∧ 1 - η < |totientHankel i j - totientHankel k j| := by
  rcases lt_or_gt_of_ne hik with hlt | hgt
  · obtain ⟨j, hj, h⟩ := separation_of_lt i k hlt N η hη
    exact ⟨j, hj, h.trans_le (le_abs_self _)⟩
  · obtain ⟨j, hj, h⟩ := separation_of_lt k i hgt N η hη
    refine ⟨j, hj, ?_⟩
    rw [abs_sub_comm]
    exact h.trans_le (le_abs_self _)

theorem totientHankel_row_separation (i k : ℕ) (hik : i ≠ k)
    (η : ℝ) (hη : 0 < η) :
    ∃ j, 1 - η < |totientHankel i j - totientHankel k j| := by
  obtain ⟨j, _, hj⟩ := totientHankel_row_separation_cofinal i k hik 0 η hη
  exact ⟨j, hj⟩

end ErdosProblems.Erdos249.TotientTranslateSeparation
