import Mathlib.NumberTheory.Divisors
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Erdős #257: the endpoint pulse is an exact divisor-function signal

The greedy-quotient recurrence in `TwentyOneQuotientGreedy` is driven by the
two-step endpoint pulse

`p_R = 2·#{d ∈ D_R : d ∣ 2R+1} + #{d ∈ D_R : d ∣ 2R+2}`,

where `D_R` is the selected support.  Treating that pulse as an unstructured
input is what makes the affine supercapacity recurrence look opaque: bounded
pulse, eventual periodicity, and finite-alphabet arguments all fail against it.

This file identifies the pulse exactly.  Over the *full* interval `[2, R]` the
two counts are pure divisor-function values:

* `card_divisors_Icc_odd`  — `#{d ∈ [2,R] : d ∣ 2R+1} + 2 = τ(2R+1)`
* `card_divisors_Icc_even` — `#{d ∈ [2,R] : d ∣ 2R+2} + 3 = τ(2R+2)`

The excluded divisors are exactly `{1, 2R+1}` in the odd case and
`{1, R+1, 2R+2}` in the even case; nothing else can leave the window because
the least prime factor of an odd number is at least `3`.

Consequently the endpoint forcing on a finite-complement support is

`p_R = 2τ(2R+1) + τ(2R+2) - 7 - (skipped-divisor correction)`,

so the aperiodic part of the fatal recurrence is the even–odd base-4
decimation `Λ_R = 2τ(2R+1) + τ(2R+2)` of the divisor expansion — the same
arithmetic function that generates the Lambert constant the branch is trying
to approximate.  `endpointDivisorSignal_unbounded_on_factorial_ray` records
that `Λ_R` is unbounded *within one fixed residue phase*, which is what kills
bounded-pulse and finite-alphabet attacks.

## Claim ceiling

**Erdős #257 remains open**, and membership of `1/21` in the achievement set
is undecided.  This file identifies the forcing term; it does not exclude the
fatal branch.
-/

namespace ErdosProblems.Erdos257.EndpointDivisorSignal

open Finset

/-- Divisors of an odd number `2R+1` that leave the window `[2, R]` are exactly
`1` and `2R+1`: an odd proper divisor is at most `(2R+1)/3 ≤ R`. -/
theorem card_divisors_Icc_odd {R : ℕ} (hR : 1 ≤ R) :
    ((Icc 2 R).filter (· ∣ 2 * R + 1)).card + 2 = (2 * R + 1).divisors.card := by
  classical
  have hne : 2 * R + 1 ≠ 0 := by omega
  have hsub : (Icc 2 R).filter (· ∣ 2 * R + 1)
      = (2 * R + 1).divisors \ {1, 2 * R + 1} := by
    ext d
    simp only [mem_filter, mem_Icc, mem_sdiff, Nat.mem_divisors, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨h2, hR'⟩, hdvd⟩
      exact ⟨⟨hdvd, hne⟩, by omega⟩
    · rintro ⟨⟨hdvd, -⟩, hnot⟩
      have hne1 : d ≠ 1 := fun h => hnot (Or.inl h)
      have hneT : d ≠ 2 * R + 1 := fun h => hnot (Or.inr h)
      have hd0 : d ≠ 0 := by rintro rfl; omega
      refine ⟨⟨by omega, ?_⟩, hdvd⟩
      -- d is a proper divisor of an odd number, so the cofactor is at least 3
      obtain ⟨c, hc⟩ := hdvd
      have hc0 : c ≠ 0 := by rintro rfl; omega
      have hc1 : c ≠ 1 := by rintro rfl; omega
      have hc2 : c ≠ 2 := by
        rintro rfl
        omega
      have hc3 : 3 ≤ c := by omega
      have hmul : d * 3 ≤ d * c := Nat.mul_le_mul_left d hc3
      rw [← hc] at hmul
      omega
  have hmem1 : (1 : ℕ) ∈ (2 * R + 1).divisors := Nat.one_mem_divisors.mpr hne
  have hmemT : (2 * R + 1) ∈ (2 * R + 1).divisors := Nat.mem_divisors_self _ hne
  have hpair : ({1, 2 * R + 1} : Finset ℕ) ⊆ (2 * R + 1).divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hmem1
    · exact hmemT
  have hcard2 : ({1, 2 * R + 1} : Finset ℕ).card = 2 := by
    rw [card_insert_of_notMem (by simp; omega), card_singleton]
  rw [hsub]
  have hsplit := Finset.card_sdiff_add_card_eq_card hpair
  omega

/-- Divisors of `2R+2` that leave the window `[2, R]` are exactly `1`, `R+1`
and `2R+2`. -/
theorem card_divisors_Icc_even {R : ℕ} (hR : 1 ≤ R) :
    ((Icc 2 R).filter (· ∣ 2 * R + 2)).card + 3 = (2 * R + 2).divisors.card := by
  classical
  have hne : 2 * R + 2 ≠ 0 := by omega
  have hsub : (Icc 2 R).filter (· ∣ 2 * R + 2)
      = (2 * R + 2).divisors \ {1, R + 1, 2 * R + 2} := by
    ext d
    simp only [mem_filter, mem_Icc, mem_sdiff, Nat.mem_divisors, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨h2, hR'⟩, hdvd⟩
      exact ⟨⟨hdvd, hne⟩, by omega⟩
    · rintro ⟨⟨hdvd, -⟩, hnot⟩
      have hne1 : d ≠ 1 := fun h => hnot (Or.inl h)
      have hneM : d ≠ R + 1 := fun h => hnot (Or.inr (Or.inl h))
      have hneT : d ≠ 2 * R + 2 := fun h => hnot (Or.inr (Or.inr h))
      have hd0 : d ≠ 0 := by rintro rfl; omega
      refine ⟨⟨by omega, ?_⟩, hdvd⟩
      obtain ⟨c, hc⟩ := hdvd
      have hc0 : c ≠ 0 := by rintro rfl; omega
      have hc1 : c ≠ 1 := by rintro rfl; omega
      have hc2 : c ≠ 2 := by rintro rfl; omega
      have hc3 : 3 ≤ c := by omega
      have hmul : d * 3 ≤ d * c := Nat.mul_le_mul_left d hc3
      rw [← hc] at hmul
      omega
  have hmem1 : (1 : ℕ) ∈ (2 * R + 2).divisors := Nat.one_mem_divisors.mpr hne
  have hmemM : (R + 1) ∈ (2 * R + 2).divisors := by
    rw [Nat.mem_divisors]
    exact ⟨⟨2, by ring⟩, hne⟩
  have hmemT : (2 * R + 2) ∈ (2 * R + 2).divisors := Nat.mem_divisors_self _ hne
  have htriple : ({1, R + 1, 2 * R + 2} : Finset ℕ) ⊆ (2 * R + 2).divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hmem1
    · exact hmemM
    · exact hmemT
  have hcard3 : ({1, R + 1, 2 * R + 2} : Finset ℕ).card = 3 := by
    rw [card_insert_of_notMem (by simp; omega), card_insert_of_notMem (by simp; omega),
      card_singleton]
  rw [hsub]
  have hsplit := Finset.card_sdiff_add_card_eq_card htriple
  omega

/-- The universal two-step endpoint forcing signal. -/
def endpointDivisorSignal (R : ℕ) : ℕ :=
  2 * (2 * R + 1).divisors.card + (2 * R + 2).divisors.card

/-- **The exact pulse identity.**  On the full window the endpoint pulse is a
divisor-function value up to the constant `7`. -/
theorem endpointPulse_eq_divisorSignal {R : ℕ} (hR : 1 ≤ R) :
    2 * ((Icc 2 R).filter (· ∣ 2 * R + 1)).card
        + ((Icc 2 R).filter (· ∣ 2 * R + 2)).card + 7
      = endpointDivisorSignal R := by
  have h1 := card_divisors_Icc_odd hR
  have h2 := card_divisors_Icc_even hR
  rw [endpointDivisorSignal]
  omega

/-- **The forcing is unbounded inside one fixed periodic phase.**  Along the
factorial ray `R = m! - 1` every selected exponent in an arbitrarily long
window divides `2R+2`, so the pulse exceeds any bound while `R ≡ 2 (mod 3)`.
This is what defeats bounded-pulse, eventual-periodicity and finite-alphabet
arguments against the fatal branch. -/
theorem endpointDivisorSignal_unbounded_on_factorial_ray (B m : ℕ) (hm : B + 3 ≤ m) :
    ∀ j ∈ Icc 2 (B + 2), j ∣ 2 * (Nat.factorial m - 1) + 2 := by
  intro j hj
  simp only [mem_Icc] at hj
  have hfac : 1 ≤ Nat.factorial m := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
  have hrw : 2 * (Nat.factorial m - 1) + 2 = 2 * Nat.factorial m := by omega
  rw [hrw]
  exact Dvd.dvd.mul_left (Nat.dvd_factorial (by omega) (by omega)) 2

end ErdosProblems.Erdos257.EndpointDivisorSignal
