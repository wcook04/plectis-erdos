import Mathlib

/-!
# Finite arithmetic interface for separated divisibility cuts

CANDIDATE: this file contains only hereditary cut bookkeeping and
power-difference divisibility. A focused Lean check is required before
admission; the first check exposed a parser error in the returned field name.
It does NOT formalise the number-field Subspace Theorem, infinite Lambert
series, or the transcendence conclusion in RETURN.md. No axiom or `sorry`
is introduced to impersonate that conclusion.

Proposed native home after successful private validation:
  lean/ErdosProblems/Erdos257/DivisibilityCuts.lean
-/
namespace ErdosProblems.Erdos257.DivisibilityCuts

/-- Every supplied exponent is positive; the prefix divides `L`, and the
suffix is divisible by `M`. Infinite limiting conditions are separate. -/
structure Cut (A : Set ℕ) (L M : ℕ) : Prop where
  left_pos : 0 < L
  separated : L < M
  positive : ∀ n ∈ A, 0 < n
  prefix_dvd : ∀ n ∈ A, n ≤ L → n ∣ L
  suffix_multiple : ∀ n ∈ A, L < n → M ∣ n

theorem Cut.mono {A B : Set ℕ} {L M : ℕ}
    (h : Cut A L M) (hBA : B ⊆ A) : Cut B L M where
  left_pos := h.left_pos
  separated := h.separated
  positive := fun n hn => h.positive n (hBA hn)
  prefix_dvd := fun n hn hle => h.prefix_dvd n (hBA hn) hle
  suffix_multiple := fun n hn hlt => h.suffix_multiple n (hBA hn) hlt

/-- Natural-number formulation of `L_j -> infinity` and
`M_j - L_j -> infinity`. The existence of cuts alone does not state a
transcendence claim. -/
def HasSeparatedCuts (A : Set ℕ) : Prop :=
  ∃ L M : ℕ → ℕ,
    (∀ j, Cut A (L j) (M j)) ∧
    (∀ C : ℕ, ∃ J : ℕ, ∀ j, J ≤ j → C ≤ L j) ∧
    (∀ C : ℕ, ∃ J : ℕ, ∀ j, J ≤ j → C ≤ M j - L j)

theorem HasSeparatedCuts.mono {A B : Set ℕ}
    (h : HasSeparatedCuts A) (hBA : B ⊆ A) : HasSeparatedCuts B := by
  rcases h with ⟨L, M, hcut, hL, hgap⟩
  exact ⟨L, M, fun j => (hcut j).mono hBA, hL, hgap⟩

/-- If a support exponent divides a cut exponent, its homogeneous
rational-base denominator divides the common cut denominator. -/
theorem exponent_divisibility_denominator {u v : ℤ} {n L : ℕ}
    (h : n ∣ L) : u ^ n - v ^ n ∣ u ^ L - v ^ L := by
  rcases h with ⟨k, rfl⟩
  simpa only [pow_mul] using
    sub_dvd_pow_sub_pow (u ^ n) (v ^ n) k

example : (2 : ℕ) ∣ 6 ∧ (3 : ℕ) ∣ 6 ∧ ¬ (2 : ℕ) ∣ 3 ∧ ¬ (3 : ℕ) ∣ 2 := by
  decide

#print axioms Cut.mono
#print axioms HasSeparatedCuts.mono
#print axioms exponent_divisibility_denominator
#check Cut.mono
#check HasSeparatedCuts.mono
#check exponent_divisibility_denominator
end ErdosProblems.Erdos257.DivisibilityCuts
