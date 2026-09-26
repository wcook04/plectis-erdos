import Mathlib

/-! # Disjoint dyadic divisor frames for the weighted separating host

These are the actual frames F_k = {2^(k+2) d : d divides M_k}. Positive odd
M_k make them pairwise disjoint and give an infinite positive union. The
prime-block harmonic bounds, weighted summability and divergent logarithmic
means are further obligations, not hypotheses hidden in a class-separation
conclusion.
-/
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset

/-- Odd cofactors uniquely determine the dyadic exponent. -/
theorem dyadic_exponent_eq_of_odd_cofactors {k l d e : ℕ}
    (hd : ¬ 2 ∣ d) (he : ¬ 2 ∣ e)
    (h : 2 ^ k * d = 2 ^ l * e) : k = l := by
  have hnotlt : ∀ {a b u v : ℕ}, ¬ 2 ∣ u →
      2 ^ a * u = 2 ^ b * v → ¬ a < b := by
    intro a b u v hu huv hab
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hab)
    have heq : 2 ^ a * u = 2 ^ a * (2 * (2 ^ r * v)) := by
      rw [hr, pow_add, pow_succ] at huv
      nlinarith only [huv]
    have hcancel : u = 2 * (2 ^ r * v) :=
      Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) heq
    exact hu ⟨2 ^ r * v, hcancel⟩
  have hkl := hnotlt hd h
  have hlk := hnotlt he h.symm
  omega

def dyadicDivisorFrame (M k : ℕ) : Finset ℕ :=
  M.divisors.image (fun d => 2 ^ (k + 2) * d)

def dyadicDivisorHost (M : ℕ → ℕ) : Set ℕ :=
  {a | ∃ k, a ∈ dyadicDivisorFrame (M k) k}

/-- Distinct rows have disjoint supports, without any disjointness assumption on primes. -/
theorem dyadicDivisorFrames_disjoint (M : ℕ → ℕ)
    (hodd : ∀ k, ¬ 2 ∣ M k) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (dyadicDivisorFrame (M k) k) (dyadicDivisorFrame (M l) l) := by
  apply Finset.disjoint_left.mpr
  intro a hak hal
  obtain ⟨d, hd, hda⟩ := Finset.mem_image.mp hak
  obtain ⟨e, he, hea⟩ := Finset.mem_image.mp hal
  have hdodd : ¬ 2 ∣ d := fun hh => hodd k (hh.trans (Nat.dvd_of_mem_divisors hd))
  have heodd : ¬ 2 ∣ e := fun hh => hodd l (hh.trans (Nat.dvd_of_mem_divisors he))
  have hh := dyadic_exponent_eq_of_odd_cofactors hdodd heodd (hda.trans hea.symm)
  exact hkl (by omega)

theorem zero_not_mem_dyadicDivisorHost (M : ℕ → ℕ) :
    0 ∉ dyadicDivisorHost M := by
  rintro ⟨k, hk⟩
  obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hk
  have hp : 0 < 2 ^ (k + 2) * d :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pos_of_mem_divisors hd)
  omega

/-- Every positive row contributes its least dyadic point; hence the host is infinite. -/
theorem dyadicDivisorHost_infinite (M : ℕ → ℕ) (hM : ∀ k, 0 < M k) :
    (dyadicDivisorHost M).Infinite := by
  have hi : Function.Injective (fun k : ℕ => 2 ^ (k + 2)) := by
    intro k l h
    have hh := dyadic_exponent_eq_of_odd_cofactors
      (by decide : ¬ 2 ∣ 1) (by decide : ¬ 2 ∣ 1)
      (by simpa only [mul_one] using h)
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro a ⟨k, rfl⟩
  refine ⟨k, Finset.mem_image.mpr ⟨1, ?_, by simp⟩⟩
  exact Nat.one_mem_divisors.mpr (hM k).ne'

end ErdosProblems.Erdos257.PaperCompleteR8
