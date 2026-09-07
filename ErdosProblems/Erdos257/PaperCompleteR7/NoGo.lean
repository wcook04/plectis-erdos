import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-!
# Literal-statement obstructions in the long record

New, uncompiled proof candidates. Each theorem below states its *actual*
counterexample or quantifier obstruction. It does not silently replace a paper
statement by a corrected version and does not claim to refute Erdős 257.

`prop:exponent-gap` asserts quadratic skip-set size in a row with at most n
positions. `lem:denominator-survival` omits positivity of the displayed
denominator. The unlabelled divisor-power bound quantifies over n=k=0.
The manuscript is left unchanged; see the coverage ledger for the distinctions.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR7

/-- A skip set in an n-position row has at most n elements. -/
theorem skip_card_le_row (F : Finset ℕ) (n : ℕ)
    (hF : F ⊆ Finset.range n) : F.card ≤ n := by
  simpa using Finset.card_le_card hF

/-- Long `prop:exponent-gap`: even the much weaker n²/8 lower bound is
impossible once the row has at least nine positions. -/
theorem skip_card_lt_quadratic_eighth (F : Finset ℕ) (n : ℕ)
    (hF : F ⊆ Finset.range n) (hn : 9 ≤ n) :
    8 * F.card < n * n := by
  have hcard := skip_card_le_row F n hF
  have hmul : 8 * F.card ≤ 8 * n := Nat.mul_le_mul_left 8 hcard
  have hnpos : 0 < n := by omega
  have hsquare : 8 * n < n * n := Nat.mul_lt_mul_of_pos_right (by omega) hnpos
  exact lt_of_le_of_lt hmul hsquare

/-- A quantified no-go for the quadratic-size clause, not an interpretation
of the undefined approximation symbol as exact equality. An asymptotic n²/4
would in particular imply the eventual lower bound excluded here. -/
theorem no_eventual_quadratic_skip_size (skip : ℕ → Finset ℕ)
    (hskip : ∀ n, skip n ⊆ Finset.range n) :
    ¬ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → n * n ≤ 8 * (skip n).card := by
  rintro ⟨N, hN⟩
  have hlarge := hN (max N 9) (le_max_left _ _)
  have hsmall := skip_card_lt_quadratic_eighth
    (skip (max N 9)) (max N 9) (hskip _) (le_max_right _ _)
  omega

/-- Long `lem:denominator-survival`: 2 divides the displayed zero denominator
and is coprime to the numerator, but does not divide the reduced denominator.
The missing hypothesis is 0 < D, as in the actual library theorem. -/
theorem denominator_zero_counterexample :
    2 ∣ (0 : ℕ) ∧ Nat.Coprime 2 (1 : ℤ).natAbs ∧
      ¬ 2 ∣ (Rat.divInt 1 0).den := by
  norm_num [Rat.divInt]

/-- The displayed universal implication is false under Lean's total division
when no nonzero-denominator hypothesis is supplied. -/
theorem denominator_survival_requires_nonzero :
    ¬ (∀ (a : ℤ) (D m : ℕ), m ∣ D → Nat.Coprime m a.natAbs →
      m ∣ (Rat.divInt a (D : ℤ)).den) := by
  intro h
  have hbad := h 1 0 2 (by norm_num) (by norm_num)
  norm_num [Rat.divInt] at hbad

/-- Unlabelled long result 137: the literal bound with all natural n,k fails
at n=k=0, independently of the convention for the divisor count at zero. -/
theorem divisor_power_zero_counterexample :
    ¬ ((0 : ℕ).divisors.card ^ (0 : ℕ) ≤
      ((0 : ℕ) ^ (2 ^ (0 : ℕ))) ^ (0 : ℕ) * (0 : ℕ)) := by
  norm_num

/-- Quantified version of the same literal-statement obstruction. -/
theorem divisor_power_bound_requires_domain :
    ¬ (∀ n k : ℕ,
      n.divisors.card ^ k ≤ (k ^ (2 ^ k)) ^ k * n) := by
  intro h
  have hbad := h 0 0
  norm_num at hbad

/-- Unlabelled long result 176: the exact three-cell complement. Unlike the
no-go results above, this proves the displayed finite arithmetic equivalence. -/
theorem three_cell_complement (R P : ℤ) :
    (¬ (4 * R - P - 4 ≤ -4 ∨ 0 ≤ 4 * R - P - 4)) ↔
      (4 * R - P - 4 = -3 ∨
        4 * R - P - 4 = -2 ∨ 4 * R - P - 4 = -1) := by
  omega


end ErdosProblems.Erdos257.PaperCompleteR7
