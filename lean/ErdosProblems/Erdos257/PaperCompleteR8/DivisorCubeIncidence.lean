import Mathlib
import ErdosProblems.Erdos257.PaperCompleteR8.DyadicDivisorFrames

/-!
# Literal divisor cubes and logarithmic incidence

The subsets counted below are actual prime subsets, not independent random
variables supplied as an extra assumption. The multiplier q may have common
prime factors with the cube: the relevant rank counts q*p dividing n.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset

/-- The literal finite divisor cube used in the paper. -/
def divisorCube (q : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (P.prod id).divisors.image (fun d => q * d)

/-- Primes which can be inserted after the mandatory factor q. -/
def cubePrimeRank (q : ℕ) (P : Finset ℕ) (n : ℕ) : ℕ :=
  (P.filter (fun p => q * p ∣ n)).card

/-- Logarithms of natural cardinalities are nonnegative, including log 0 = 0. -/
theorem log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

/-- A prime-subset product uniquely identifies that subset. -/
theorem prime_subset_product_injective (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (q : ℕ) (hq : 0 < q) :
    Set.InjOn (fun S : Finset ℕ => q * S.prod id) (P.powerset : Set (Finset ℕ)) := by
  intro S hS T hT hST
  have hSP : S ⊆ P := mem_powerset.mp hS
  have hTP : T ⊆ P := mem_powerset.mp hT
  have hSprime : ∀ p ∈ S, Nat.Prime p := fun p hp => hP p (hSP hp)
  have hTprime : ∀ p ∈ T, Nat.Prime p := fun p hp => hP p (hTP hp)
  have heq : S.prod id = T.prod id := Nat.eq_of_mul_eq_mul_left hq hST
  calc
    S = (S.prod id).primeFactors := (Nat.primeFactors_prod hSprime).symm
    _ = (T.prod id).primeFactors := congrArg Nat.primeFactors heq
    _ = T := Nat.primeFactors_prod hTprime

/-- Every subset of available primes produces a different selected divisor.
No coprimality between q and the prime set is needed. -/
theorem two_pow_cubePrimeRank_le_incidence (q : ℕ) (P : Finset ℕ) (n : ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hn : 0 < n) (hqn : q ∣ n) :
    2 ^ cubePrimeRank q P n ≤ ((divisorCube q P).filter (fun a => a ∣ n)).card := by
  classical
  obtain ⟨t, rfl⟩ := hqn
  have ht0 : t ≠ 0 := by
    intro ht
    simp only [ht, mul_zero] at hn
    omega
  let B := P.filter (fun p => q * p ∣ q * t)
  have hBP : B ⊆ P := fun p hp => (mem_filter.mp hp).1
  have hBt : B ⊆ t.primeFactors := by
    intro p hp
    obtain ⟨hpP, u, hu⟩ := mem_filter.mp hp
    have htu : t = p * u := Nat.eq_of_mul_eq_mul_left hq (by
      simpa only [mul_assoc] using hu)
    exact Nat.mem_primeFactors.mpr ⟨hP p hpP, ⟨u, htu⟩, ht0⟩
  have hM0 : P.prod id ≠ 0 := (prod_pos (fun p hp => (hP p hp).pos)).ne'
  have hsub : B.powerset.image (fun S => q * S.prod id) ⊆
      (divisorCube q P).filter (fun a => a ∣ q * t) := by
    intro a ha
    obtain ⟨S, hS, rfl⟩ := mem_image.mp ha
    have hSB : S ⊆ B := mem_powerset.mp hS
    have hSP : S ⊆ P := hSB.trans hBP
    have hSt : S ⊆ t.primeFactors := hSB.trans hBt
    have hdivM : S.prod id ∣ P.prod id :=
      Finset.prod_dvd_prod_of_subset _ _ _ hSP
    have hdivt : S.prod id ∣ t :=
      (Finset.prod_dvd_prod_of_subset _ _ _ hSt).trans (Nat.prod_primeFactors_dvd t)
    refine mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_image.mpr ⟨S.prod id, Nat.mem_divisors.mpr ⟨hdivM, hM0⟩, rfl⟩
    · obtain ⟨v, hv⟩ := hdivt
      refine ⟨v, ?_⟩
      rw [hv]
      ring
  have hcard : (B.powerset.image (fun S => q * S.prod id)).card = 2 ^ B.card := by
    rw [card_image_of_injOn, card_powerset]
    exact prime_subset_product_injective B (fun p hp => hP p (hBP hp)) q hq
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact hle

/-- A containing finite support inherits the cube's first logarithmic moment. -/
theorem cube_log_incidence_lower (q : ℕ) (P F : Finset ℕ) (n : ℕ)
    (hq : 0 < q) (hP : ∀ p ∈ P, Nat.Prime p) (hn : 0 < n) (hqn : q ∣ n)
    (hF : divisorCube q P ⊆ F) :
    Real.log 2 * (cubePrimeRank q P n : ℝ) ≤
      Real.log ((F.filter (fun a => a ∣ n)).card : ℝ) := by
  have hsub : (divisorCube q P).filter (fun a => a ∣ n) ⊆
      F.filter (fun a => a ∣ n) := by
    intro a ha
    exact mem_filter.mpr ⟨hF (mem_filter.mp ha).1, (mem_filter.mp ha).2⟩
  have hnat := (two_pow_cubePrimeRank_le_incidence q P n hq hP hn hqn).trans
    (Finset.card_le_card hsub)
  have hreal : (2 : ℝ) ^ cubePrimeRank q P n ≤
      ((F.filter (fun a => a ∣ n)).card : ℝ) := by exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ cubePrimeRank q P n) hreal
  simpa only [Real.log_pow, mul_comm] using hlog

/-- Exact dyadic row events, counted as a finite cardinality. -/
def dyadicBlockCount (P : Finset ℕ) (r n : ℕ) : ℕ :=
  (P.filter (fun p => 2 ^ r * p ∣ n ∧ ¬ 2 * (2 ^ r * p) ∣ n)).card

theorem dyadicBlockCount_cast (P : Finset ℕ) (r n : ℕ) :
    (dyadicBlockCount P r n : ℝ) =
      ∑ p ∈ P, if 2 ^ r * p ∣ n ∧ ¬ 2 * (2 ^ r * p) ∣ n then (1 : ℝ) else 0 := by
  classical
  symm
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one, dyadicBlockCount]

/-- An event supplies the exact odd cofactor; density is not assumed. -/
theorem odd_cofactor_of_dyadic_event (r p n : ℕ) (hp : ¬ 2 ∣ p)
    (he : 2 ^ r * p ∣ n ∧ ¬ 2 * (2 ^ r * p) ∣ n) :
    ∃ u : ℕ, ¬ 2 ∣ u ∧ n = 2 ^ r * u := by
  obtain ⟨m, hm⟩ := he.1
  have hm2 : ¬ 2 ∣ m := by
    rintro ⟨v, hv⟩
    apply he.2
    refine ⟨v, ?_⟩
    rw [hm, hv]
    ring
  refine ⟨p * m, ?_, ?_⟩
  · intro h
    rcases Nat.prime_two.dvd_mul.mp h with h | h
    · exact hp h
    · exact hm2 h
  · simpa only [mul_assoc] using hm

/-- Row events at different exact dyadic valuations cannot coexist. -/
theorem dyadic_event_row_unique (k l p q n : ℕ) (hp : ¬ 2 ∣ p) (hq : ¬ 2 ∣ q)
    (he : 2 ^ (k + 2) * p ∣ n ∧ ¬ 2 * (2 ^ (k + 2) * p) ∣ n)
    (hf : 2 ^ (l + 2) * q ∣ n ∧ ¬ 2 * (2 ^ (l + 2) * q) ∣ n) : k = l := by
  obtain ⟨u, hu, hnu⟩ := odd_cofactor_of_dyadic_event (k + 2) p n hp he
  obtain ⟨v, hv, hnv⟩ := odd_cofactor_of_dyadic_event (l + 2) q n hq hf
  have h := dyadic_exponent_eq_of_odd_cofactors hu hv (hnu.symm.trans hnv)
  omega

/-- First-moment lower bound over any finite collection of dyadic rows. -/
theorem dyadic_union_log_pointwise (P : ℕ → Finset ℕ) (J : Finset ℕ) (n : ℕ)
    (hn : 0 < n) (hP : ∀ k p, p ∈ P k → Nat.Prime p ∧ 2 < p) :
    Real.log 2 * (∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) ≤
      Real.log (((J.biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)).filter
        (fun a => a ∣ n)).card : ℝ) := by
  classical
  let F := J.biUnion (fun k => dyadicDivisorFrame ((P k).prod id) k)
  have hpodd : ∀ k p, p ∈ P k → ¬ 2 ∣ p := by
    intro k p hp hd
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (hP k p hp).1).mp hd
    have hlt := (hP k p hp).2
    omega
  by_cases hex : ∃ k ∈ J, ∃ p ∈ P k,
      2 ^ (k + 2) * p ∣ n ∧ ¬ 2 * (2 ^ (k + 2) * p) ∣ n
  · obtain ⟨k, hk, p, hp, he⟩ := hex
    have hz : ∀ l ∈ J, l ≠ k → dyadicBlockCount (P l) (l + 2) n = 0 := by
      intro l hl hlk
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      obtain ⟨hqP, hf⟩ := mem_filter.mp hq
      exact hlk (dyadic_event_row_unique l k q p n (hpodd l q hqP) (hpodd k p hp) hf he)
    have hsum : (∑ l ∈ J, (dyadicBlockCount (P l) (l + 2) n : ℝ)) =
        (dyadicBlockCount (P k) (k + 2) n : ℝ) := by
      apply Finset.sum_eq_single k
      · intro l hl hlk
        simp only [hz l hl hlk, Nat.cast_zero]
      · intro hnot
        exact False.elim (hnot hk)
    rw [hsum]
    have hcount : dyadicBlockCount (P k) (k + 2) n ≤
        cubePrimeRank (2 ^ (k + 2)) (P k) n := by
      apply Finset.card_le_card
      intro q hq
      exact mem_filter.mpr ⟨(mem_filter.mp hq).1, (mem_filter.mp hq).2.1⟩
    have hqn : 2 ^ (k + 2) ∣ n := (dvd_mul_right _ p).trans he.1
    have hF : divisorCube (2 ^ (k + 2)) (P k) ⊆ F := by
      intro a ha
      exact mem_biUnion.mpr ⟨k, hk, ha⟩
    have hlog := cube_log_incidence_lower (2 ^ (k + 2)) (P k) F n
      (Nat.pow_pos (by decide)) (fun p hp => (hP k p hp).1) hn hqn hF
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcount)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))).trans hlog
  · have hz : ∀ k ∈ J, dyadicBlockCount (P k) (k + 2) n = 0 := by
      intro k hk
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hex ⟨k, hk, p, (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
    have hs : (∑ k ∈ J, (dyadicBlockCount (P k) (k + 2) n : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [hz k hk, Nat.cast_zero]
    rw [hs, mul_zero]
    exact log_nat_nonneg _

end ErdosProblems.Erdos257.PaperCompleteR8
end
