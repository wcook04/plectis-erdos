import ErdosProblems.Erdos257.PaperCompleteR8.BoundedMassCoverBudget

/-!
# Separation for the paper's bounded-mass divisor rows

Each row escapes every fixed finite set of integers and has reciprocal mass
at least one. The vanishing-tail criterion therefore rules out summability.
Pairwise disjoint complete prime alphabets make each fixed finite prime set
absent from all sufficiently late rows. On those rows its weighted term is
exactly the reciprocal term divided by b - 1, so the same argument applies.
This is the literal bounded-mass witness, rather than the alternate reverseHost.
The exact Lean check and axiom output decide validation, not this description.
-/

noncomputable section
open scoped Classical
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

def boundedMassHost : Set ℕ :=
  {a | ∃ j, a ∈ divisorCube (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes}

theorem boundedMassPrimeRow_index_lt_q (j : ℕ) : j < (boundedMassPrimeRow j).q := by
  have h : j + 1 < 4 ^ (j + 1) := Nat.lt_pow_self (by norm_num)
  have hq := (boundedMassPrimeRow j).q_large
  omega

theorem boundedMassPrimeRow_le_mem (j a : ℕ)
    (ha : a ∈ divisorCube (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes) :
    (boundedMassPrimeRow j).q ≤ a := by
  obtain ⟨d, hd, rfl⟩ := mem_image.mp ha
  have hdpos := Nat.pos_of_mem_divisors hd
  nlinarith

theorem boundedMassHost_positive : 0 ∉ boundedMassHost := by
  rintro ⟨j, hj⟩
  have h := boundedMassPrimeRow_le_mem j 0 hj
  have hq := (boundedMassPrimeRow j).q_prime.pos
  omega

theorem boundedMassHost_infinite : boundedMassHost.Infinite := by
  intro hf
  obtain ⟨B, hB⟩ := hf.bddAbove
  have hmem : (boundedMassPrimeRow B).q ∈ boundedMassHost := by
    refine ⟨B, ?_⟩
    exact factor_mem_divisorCube _ _ (fun p hp => ((boundedMassPrimeRow B).primes_spec p hp).1)
  have hle := hB hmem
  have hgt := boundedMassPrimeRow_index_lt_q B
  omega

/-- A positive mass on each sufficiently late row contradicts vanishing tails.
Row disjointness is not required: every individual row escapes finite sets. -/
theorem boundedMassHost_not_summable_of_row_lower (f : ℕ → ℝ)
    (c : ℝ) (hc : 0 < c) (J : ℕ)
    (hrow : ∀ j, J ≤ j → c ≤ ∑ a ∈
      divisorCube (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes, f a) :
    ¬ Summable (Set.indicator boundedMassHost f) := by
  intro hs
  obtain ⟨s, hsmall⟩ := summable_iff_vanishing_norm.mp hs c hc
  let j := max J (s.sup id)
  let F := divisorCube (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes
  have hdis : Disjoint F s := by
    apply disjoint_left.mpr
    intro a ha has
    have ha1 := boundedMassPrimeRow_le_mem j a ha
    have ha2 : a ≤ j := (Finset.le_sup (f := id) has).trans (le_max_right _ _)
    exact (not_lt_of_ge ha1) (ha2.trans_lt (boundedMassPrimeRow_index_lt_q j))
  have h := hsmall F hdis
  have heq : (∑ a ∈ F, Set.indicator boundedMassHost f a) = ∑ a ∈ F, f a := by
    apply sum_congr rfl
    intro a ha
    exact Set.indicator_of_mem (show a ∈ boundedMassHost from ⟨j, ha⟩) f
  rw [heq, Real.norm_eq_abs] at h
  have hlo := hrow j (le_max_left _ _)
  have hle := le_abs_self (∑ a ∈ F, f a)
  exact (not_lt_of_ge (hlo.trans hle)) h

theorem boundedMassHost_reciprocal_not_summable :
    ¬ Summable (Set.indicator boundedMassHost (fun a : ℕ => (1 : ℝ) / a)) := by
  apply boundedMassHost_not_summable_of_row_lower _ 1 (by norm_num) 0
  intro j _
  exact (boundedMassPrimeRow_reciprocal_bounds j).1

theorem boundedMassAlphabet_eventually_avoids (p : ℕ) :
    ∃ J : ℕ, ∀ j, J ≤ j → p ∉ boundedMassAlphabet j := by
  by_cases h : ∃ i, p ∈ boundedMassAlphabet i
  · obtain ⟨i, hi⟩ := h
    refine ⟨i + 1, ?_⟩
    intro j hj hp
    have hne : j ≠ i := by omega
    exact disjoint_left.mp (boundedMassAlphabets_disjoint hne) hp hi
  · exact ⟨0, fun j _ hp => h ⟨j, hp⟩⟩

theorem boundedMassAlphabet_eventually_avoids_finset (P : Finset ℕ) :
    ∃ J : ℕ, ∀ j, J ≤ j → ∀ p ∈ P, p ∉ boundedMassAlphabet j := by
  induction P using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert p P hp ih =>
    obtain ⟨J, hJ⟩ := ih
    obtain ⟨K, hK⟩ := boundedMassAlphabet_eventually_avoids p
    refine ⟨max J K, ?_⟩
    intro j hj r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hK j ((le_max_right _ _).trans hj)
    · exact hJ j ((le_max_left _ _).trans hj) r hr

theorem boundedMassPrimeRow_no_prime_divisor (j p a : ℕ) (hp : Nat.Prime p)
    (hnot : p ∉ boundedMassAlphabet j)
    (ha : a ∈ divisorCube (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes) :
    ¬ p ∣ a := by
  let R := boundedMassPrimeRow j
  obtain ⟨d, hd, rfl⟩ := mem_image.mp ha
  intro hpa
  rcases hp.dvd_mul.mp hpa with hpq | hpd
  · have heq := (Nat.prime_dvd_prime_iff_eq hp R.q_prime).mp hpq
    apply hnot
    change p ∈ insert R.q R.primes
    rw [heq]
    exact mem_insert_self _ _
  · have hpM := hpd.trans (Nat.dvd_of_mem_divisors hd)
    have hP : ∀ r ∈ R.primes, Nat.Prime r := fun r hr => (R.primes_spec r hr).1
    have hmem : p ∈ (R.primes.prod id).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpM, (prime_product_pos _ hP).ne'⟩
    change p ∈ (∏ r ∈ R.primes, r).primeFactors at hmem
    rw [Nat.primeFactors_prod hP] at hmem
    exact hnot (mem_insert_of_mem hmem)

theorem boundedMassPrimeRow_weighted_sum (b : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (j : ℕ)
    (havoid : ∀ p ∈ P, p ∉ boundedMassAlphabet j) :
    (∑ a ∈ divisorCube (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes,
      primeWeightedTerm b P a) =
    (∑ a ∈ divisorCube (boundedMassPrimeRow j).q (boundedMassPrimeRow j).primes,
      (1 : ℝ) / a) / ((b : ℝ) - 1) := by
  rw [sum_div]
  apply sum_congr rfl
  intro a ha
  have hpart : primeSetPart P a = 1 := by
    unfold primeSetPart
    apply prod_eq_one
    intro p hp
    rw [Nat.factorization_eq_zero_of_not_dvd
      (boundedMassPrimeRow_no_prime_divisor j p a (hP p hp) (havoid p hp) ha), pow_zero]
  unfold primeWeightedTerm
  rw [hpart]
  simp only [Nat.cast_one, pow_one]
  rw [div_div]

theorem boundedMassHost_no_weighted_sum (b : ℕ) (hb : 2 ≤ b)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ¬ Summable (Set.indicator boundedMassHost (primeWeightedTerm b P)) := by
  have hbR : 0 < (b : ℝ) - 1 := by
    have hbc : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  obtain ⟨J, hJ⟩ := boundedMassAlphabet_eventually_avoids_finset P
  apply boundedMassHost_not_summable_of_row_lower _ (1 / ((b : ℝ) - 1))
    (one_div_pos.mpr hbR) J
  intro j hj
  rw [boundedMassPrimeRow_weighted_sum b P hP j (hJ j hj)]
  exact div_le_div_of_nonneg_right (boundedMassPrimeRow_reciprocal_bounds j).1 hbR.le

theorem boundedMassHost_not_finitePrimeWeighted (b : ℕ) (hb : 2 ≤ b) :
    ¬ FinitePrimeWeighted b boundedMassHost := by
  rintro ⟨P, _, hP, hs⟩
  exact boundedMassHost_no_weighted_sum b hb P hP hs

/-- The actual printed row construction supplies the cover-only witness. -/
theorem boundedMassHost_complete :
    boundedMassHost.Infinite ∧ 0 ∉ boundedMassHost ∧
      HasStrengthenedPositiveCover boundedMassHost ∧
      (¬ Summable (Set.indicator boundedMassHost (fun a : ℕ => (1 : ℝ) / a))) ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b boundedMassHost) := by
  exact ⟨boundedMassHost_infinite, boundedMassHost_positive,
    boundedMassPrimeRows_hasStrengthenedPositiveCover,
    boundedMassHost_reciprocal_not_summable, boundedMassHost_not_finitePrimeWeighted⟩

#print axioms boundedMassHost_complete

end ErdosProblems.Erdos257.PaperCompleteR8
end
