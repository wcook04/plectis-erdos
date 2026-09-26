import ErdosProblems.Erdos257.PaperCompleteR8.DivisorFrameWeightedBudget
import ErdosProblems.Erdos257.PaperCompleteR8.CountableCoverLogBudget
import ErdosProblems.Erdos257.PaperCompleteR7.AnalyticTargets

/-! # Canonical finite-prime weights on the dyadic divisor host

The valuation identity identifies the literal frame budget with the original
finite-prime weighted criterion. A nonnegative finite-subcover argument then
transports summability to the actual infinite union.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset PaperCompleteR7

 theorem primeSetPart_two_dyadic {d : ℕ} (k : ℕ) (hd : ¬ 2 ∣ d) :
    primeSetPart {2} (2 ^ (k + 2) * d) = 2 ^ (k + 2) := by
  have hd0 : d ≠ 0 := by intro h; apply hd; simp [h]
  have hpow0 : 2 ^ (k + 2) ≠ 0 := pow_ne_zero _ (by decide)
  have hfac : (2 ^ (k + 2) * d).factorization 2 = k + 2 := by
    rw [Nat.factorization_mul hpow0 hd0]
    simp [Nat.factorization_pow_self Nat.prime_two, Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd hd]
  simp [primeSetPart, hfac]

 theorem dyadic_frame_canonical_weight_sum (M k : ℕ) (hodd : ¬ 2 ∣ M) :
    (∑ a ∈ dyadicDivisorFrame M k, primeWeightedTerm 2 {2} a) =
      (∑ d ∈ M.divisors, (1 : ℝ) / d) /
        ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1) := by
  calc
    _ = ∑ a ∈ dyadicDivisorFrame M k,
        ((2 : ℝ) ^ (k + 2)) / ((a : ℝ) * ((2 : ℝ) ^ (2 ^ (k + 2) : ℕ) - 1)) := by
      apply sum_congr rfl
      intro a ha
      obtain ⟨d, hd, rfl⟩ := mem_image.mp ha
      have hdodd : ¬ 2 ∣ d := fun h => hodd (h.trans (Nat.dvd_of_mem_divisors hd))
      simp [primeWeightedTerm, primeSetPart_two_dyadic k hdodd]
    _ = _ := dyadic_frame_literal_weight_sum M k

/-- Summable nonnegative frame masses control the indicator of their union.
Overlaps are allowed; only the upper bound is needed. -/
theorem summable_indicator_frame_union (G : ℕ → Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hs : Summable (fun k => ∑ a ∈ G k, w a)) :
    Summable (Set.indicator {a | ∃ k, a ∈ G k} w) := by
  classical
  let A : Set ℕ := {a | ∃ k, a ∈ G k}
  apply summable_of_sum_le (c := ∑' k, ∑ a ∈ G k, w a)
  · intro a
    exact Set.indicator_nonneg (fun a _ => hw a) a
  intro s
  obtain ⟨J, hJ⟩ := exists_finite_frame_subcover (s.filter (· ∈ A)) G
    (fun a ha => (mem_filter.mp ha).2)
  calc
    (∑ a ∈ s, Set.indicator A w a) ≤
        ∑ a ∈ s, ∑ k ∈ J, if a ∈ G k then w a else 0 := by
      apply sum_le_sum
      intro a ha
      by_cases hA : a ∈ A
      · obtain ⟨k, hk, hak⟩ := mem_biUnion.mp (hJ (mem_filter.mpr ⟨ha, hA⟩))
        rw [Set.indicator_of_mem hA]
        have hnonneg : ∀ j ∈ J, 0 ≤ if a ∈ G j then w a else 0 := by
          intro j hj
          by_cases haj : a ∈ G j
          · simp [haj, hw a]
          · simp [haj]
        simpa [hak] using
          (Finset.single_le_sum (f := fun j => if a ∈ G j then w a else 0)
            hnonneg hk)
      · rw [Set.indicator_of_notMem hA]
        exact sum_nonneg (fun k _ => by
          by_cases hak : a ∈ G k
          · simp [hak, hw a]
          · simp [hak])
    _ = ∑ k ∈ J, ∑ a ∈ s, if a ∈ G k then w a else 0 := sum_comm
    _ ≤ ∑ k ∈ J, ∑ a ∈ G k, w a := by
      apply sum_le_sum
      intro k hk
      rw [← sum_filter]
      exact sum_le_sum_of_subset_of_nonneg
        (fun a ha => (mem_filter.mp ha).2) (fun a _ _ => hw a)
    _ ≤ ∑' k, ∑ a ∈ G k, w a :=
      hs.sum_le_tsum J (fun k _ => sum_nonneg (fun a _ => hw a))

 theorem summable_canonical_dyadic_host (P : ℕ → Finset ℕ)
    (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p)
    (hS : ∀ k, (∑ p ∈ P k, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) :
    Summable (Set.indicator (dyadicDivisorHost (fun k => (P k).prod id))
      (primeWeightedTerm 2 {2})) := by
  have hodd : ∀ k, ¬ 2 ∣ (P k).prod id := by
    intro k h
    obtain ⟨p, hp, hd⟩ := (Nat.prime_two.prime.dvd_finset_prod_iff id).mp h
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hP k p hp).1).mp hd
    have := (hP k p hp).2
    omega
  have hw : ∀ a, 0 ≤ primeWeightedTerm 2 {2} a := by
    intro a
    unfold primeWeightedTerm
    apply div_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    have hpow : (1 : ℝ) ≤ 2 ^ primeSetPart {2} a := one_le_pow₀ (by norm_num)
    exact sub_nonneg.mpr hpow
  apply summable_indicator_frame_union _ _ hw
  have heq : (fun k => ∑ a ∈ dyadicDivisorFrame ((P k).prod id) k,
      primeWeightedTerm 2 {2} a) = (fun k => divisorFrameBudget (P k) k) := by
    funext k
    exact dyadic_frame_canonical_weight_sum _ _ (hodd k)
  rw [heq]
  exact summable_divisorFrameBudget P (fun k p hp => (hP k p hp).1) hS

/-- The prime-block construction supplies an infinite positive host satisfying
 the original binary finite-prime weighted criterion. -/
theorem exists_infinite_dyadic_weighted_host :
    ∃ P : ℕ → Finset ℕ,
      Pairwise (fun k l => Disjoint (P k) (P l)) ∧
      (∀ k, (∀ p ∈ P k, Nat.Prime p ∧ 2 < p) ∧
        (2 : ℝ) ^ k ≤ ∑ p ∈ P k, (1 : ℝ) / p ∧
        (∑ p ∈ P k, (1 : ℝ) / p) ≤ (2 : ℝ) ^ k + 1) ∧
      (dyadicDivisorHost (fun k => (P k).prod id)).Infinite ∧
      0 ∉ dyadicDivisorHost (fun k => (P k).prod id) ∧
      FinitePrimeWeighted 2 (dyadicDivisorHost (fun k => (P k).prod id)) := by
  obtain ⟨P, hdis, hP⟩ := exists_separating_prime_blocks
  refine ⟨P, hdis, hP, dyadicDivisorHost_infinite _ ?_,
    zero_not_mem_dyadicDivisorHost _, ?_⟩
  · intro k
    exact prod_pos (fun p hp => ((hP k).1 p hp).1.pos)
  · refine ⟨{2}, by simp, ?_, summable_canonical_dyadic_host P
      (fun k p hp => (hP k).1 p hp) (fun k => (hP k).2.2)⟩
    intro p hp
    have hp2 : p = 2 := mem_singleton.mp hp
    simpa [hp2] using Nat.prime_two

end ErdosProblems.Erdos257.PaperCompleteR8
end
