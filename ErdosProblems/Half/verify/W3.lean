/-
Adversarial verification of `ErdosProblems/Half/H3.lean`.

This file is a *checker*, not a contribution.  It imports H3 (it does not
re-declare anything from it), prints the axiom dependencies of every theorem H3
declares, pins the exact statements with `#check`, and then proves — from
scratch — the sharp non-vacuity / triviality facts that decide how much H3
actually buys.
-/
import ErdosProblems.Half.H3

namespace Erdos249257
namespace VerifyW3

open Erdos249257.HalfH3
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## 1. Axiom audit: every theorem declared in H3 -/

#print axioms two_dvd_two_pow
#print axioms four_dvd_two_pow
#print axioms geometricCore_eq_twoPow_mul_add_one
#print axioms truncatedMersenneWeight_eq_twoPow_mul_geom
#print axioms truncatedMersenneWeight_mod_two
#print axioms truncatedMersenneWeight_mod_four
#print axioms truncatedMersenneWeight_two_mod_two
#print axioms wordWeightSum_add_seamIntegerGreedyRemainder
#print axioms seamSubsetTarget_mod_two
#print axioms sum_seamWordSupport_mod_two
#print axioms seamIntegerGreedyRemainder_mod_two
#print axioms eq_two_of_dvd_two_mul_of_prime
#print axioms divisorSelected_prime
#print axioms seamIntegerGreedyRemainder_odd_of_prime
#print axioms seamExcess_ne_two_of_prime
#print axioms seamExcess_ne_zero_of_prime
#print axioms finalMiddleCell_neg_two_impossible_of_prime_succ
#print axioms dvd_two_mul_not_late
#print axioms dvd_two_mul_half_eq_cofThree
#print axioms dvd_two_mul_sub_one_not_late
#print axioms four_dvd_truncatedMersenneWeight_of_late
#print axioms truncatedMersenneWeight_mod_twoPow_of_late
#print axioms four_dvd_lateBlock
#print axioms lateBlock_mod_four_indep
#print axioms sum_seamWordSupport_mod_four_of_late
#print axioms exists_lowerPrefix_sum_mod_four_of_largestSkipLate

/-! ## 2. Statement pinning -/

#check @seamIntegerGreedyRemainder_mod_two
#check @seamIntegerGreedyRemainder_odd_of_prime
#check @seamExcess_ne_two_of_prime
#check @finalMiddleCell_neg_two_impossible_of_prime_succ
#check @exists_lowerPrefix_sum_mod_four_of_largestSkipLate

/-! ## 3. Non-vacuity of the prime family

`seamExcess_ne_two_of_prime` has hypotheses `13 ≤ s` and `Nat.Prime s`.  Those
are satisfiable, so the theorem is not vacuous; here are three witnesses whose
conclusions are genuine closed statements about the concrete greedy. -/

theorem witness_13 : Recon257.seamExcess 13 ≠ 2 :=
  seamExcess_ne_two_of_prime (by norm_num) (by norm_num)

theorem witness_17 : Recon257.seamExcess 17 ≠ 2 :=
  seamExcess_ne_two_of_prime (by norm_num) (by norm_num)

theorem witness_101 : Recon257.seamExcess 101 ≠ 2 :=
  seamExcess_ne_two_of_prime (by norm_num) (by norm_num)

theorem witness_odd_13 : seamIntegerGreedyRemainder 13 % 2 = 1 :=
  seamIntegerGreedyRemainder_odd_of_prime (by norm_num) (by norm_num)

/-- The family is infinite: every prime `≥ 13` is a witness, and there are
infinitely many. -/
theorem witnesses_unbounded (N : ℕ) : ∃ s : ℕ, N ≤ s ∧ Recon257.seamExcess s ≠ 2 := by
  obtain ⟨p, hp13, hp⟩ := Nat.exists_infinite_primes (max N 13)
  exact ⟨p, le_trans (le_max_left N 13) hp13,
    seamExcess_ne_two_of_prime (le_trans (le_max_right N 13) hp13) hp⟩

/-! ## 4. How much the headline theorem actually buys

H3 admits in prose that the `D + 1` prime family is disjoint from
`Recon257.SurvivorPhase`.  That admission is correct, and here it is proved
rather than asserted: a survivor class forces `3 ∣ D + 1`, so `D + 1` prime
with `D ≥ 12` is never a survivor.  Consequently
`finalMiddleCell_neg_two_impossible_of_prime_succ` removes **zero** classes
from the 412-class survivor list; its only content is that the exclusion holds
without the all-right tail hypothesis and without an ineffective threshold. -/

theorem survivorPhase_three_dvd_succ {D : ℕ} (h : Recon257.SurvivorPhase D) :
    (D + 1) % 3 = 0 := by
  have h21 := h.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h21
  have h3 : D % 21 % 3 = 2 := by rcases h21 with h | h | h | h <;> simp [h]
  have : D % 3 = 2 := by
    rw [← Nat.mod_mod_of_dvd D (by norm_num : (3 : ℕ) ∣ 21)]
    exact h3
  omega

theorem prime_succ_not_survivorPhase {D : ℕ} (hD : 12 ≤ D) (hp : Nat.Prime (D + 1)) :
    ¬ Recon257.SurvivorPhase D := by
  intro h
  have hmod := survivorPhase_three_dvd_succ h
  have hdvd : (3 : ℕ) ∣ (D + 1) := Nat.dvd_of_mod_eq_zero hmod
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdvd) with h1 | h2
  · omega
  · omega

/-- Contrapositive packaging: on the family H3's headline addresses, the
corpus's own ratchet already returns a dead budget, unconditionally on the
phase side.  (What the ratchet *cannot* do without `hright` is convert that
into `False`; that conversion is exactly H3's contribution.) -/
theorem ratchet_already_dead_on_prime_family {D : ℕ} (hD : 12 ≤ D)
    (hp : Nat.Prime (D + 1)) : Recon257.ratchetRun D 3 = 0 :=
  Recon257.ratchetRun_eq_zero_of_not_survivorPhase D (prime_succ_not_survivorPhase hD hp)

/-! ## 5. Triviality check on the "blindness" theorem

`lateBlock_mod_four_indep` is presented as a blindness statement.  It is a
restatement of `four_dvd_lateBlock`: both sides are literally `0`.  Proved here
without using H3's version, to show there is no extra content. -/

theorem lateBlock_mod_four_is_zero {s d₀ : ℕ} (hlate : 2 * s < 3 * d₀) :
    (∑ d ∈ Finset.Ico (d₀ + 1) s, truncatedMersenneWeight s d) % 4 = 0 := by
  obtain ⟨a, ha⟩ := four_dvd_lateBlock hlate
  omega

theorem lateBlock_indep_is_trivial {s d₀ d₁ : ℕ}
    (h0 : 2 * s < 3 * d₀) (h1 : 2 * s < 3 * d₁) :
    (∑ d ∈ Finset.Ico (d₀ + 1) s, truncatedMersenneWeight s d) % 4 =
      (∑ d ∈ Finset.Ico (d₁ + 1) s, truncatedMersenneWeight s d) % 4 := by
  rw [lateBlock_mod_four_is_zero h0, lateBlock_mod_four_is_zero h1]

/-! ## 6. Independent re-derivation of the parity law's key step

Checked against H3's `truncatedMersenneWeight_mod_two` on a concrete row where
the answer is computable by kernel reduction, to make sure the abstract law is
not stating something the concrete objects contradict. -/

example : truncatedMersenneWeight 13 2 % 2 = 1 := by decide +kernel
example : truncatedMersenneWeight 13 3 % 2 = 0 := by decide +kernel
example : truncatedMersenneWeight 13 26 % 2 = 1 := by decide +kernel

/-- The abstract law agrees with the concrete value at `s = 13, d = 3`
(`3 ∤ 26`, so the weight must be even). -/
example : truncatedMersenneWeight 13 3 % 2 = 0 := by
  rw [truncatedMersenneWeight_mod_two (by norm_num) (by norm_num),
    if_neg (by decide)]

/-! ## 7. What is NOT proved

H3's prose claims (§3) that the finer reduction modulo `2 ^ (s+1)` "produces no
obstruction either" because the late weight's low half "is absorbed by the
unconstrained low support".  No theorem in H3 states that.  The only formal
content on that line is `truncatedMersenneWeight_mod_twoPow_of_late`, which
computes the low half and says nothing about absorption.  Recorded here as a
`#check` of what does exist, with no claim about what does not. -/

#check @truncatedMersenneWeight_mod_twoPow_of_late

#print axioms witness_13
#print axioms witnesses_unbounded
#print axioms prime_succ_not_survivorPhase
#print axioms ratchet_already_dead_on_prime_family
#print axioms lateBlock_indep_is_trivial

end VerifyW3
end Erdos249257
