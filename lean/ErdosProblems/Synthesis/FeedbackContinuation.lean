import ErdosProblems.Erdos251.ResidueFeedbackCore
import Mathlib.Tactic

/-!
# Eventual congruences from the existing feedback construction

The #251 feedback theorem supplies bounded digits, their weighted sum, and a
prescribed divisor of every cumulative prefix. Nested moduli turn these
prefix divisibilities into eventual divisibility of both the individual
digits and all preceding cumulative sums.

This is the analytic continuation mechanism used by the factorial
tail-capacity argument. It does not formalize the choice of factorial
allowances, active positions, moduli, or continuation intervals in that
ordinary proof. Those inputs remain explicit hypotheses here. No feedback
selector is duplicated.
-/

noncomputable section

open Filter Topology Finset

namespace ErdosProblems.Synthesis.FeedbackContinuation

open ErdosProblems.Erdos251.ResidueFeedback

/-- Once `q` divides one modulus, it divides every later modulus. The prefix
after the corresponding digit is therefore divisible by `q`; subtracting
successive prefixes gives the individual-digit divisibility as well. The
explicit cutoff `J + 1` depends only on the modulus schedule. -/
theorem prefix_and_digit_dvd_of_nested_moduli
    (M d : ℕ → ℕ)
    (hnested : ∀ n, M n ∣ M (n + 1))
    (hprefix : ∀ n, (M n : ℤ) ∣ ((∑ i ∈ range (n + 1), d i : ℕ) : ℤ))
    (q J : ℕ) (hqJ : q ∣ M J) :
    ∀ n, J + 1 ≤ n →
      (q : ℤ) ∣ (d n : ℤ) ∧
        (q : ℤ) ∣ ((∑ i ∈ range n, d i : ℕ) : ℤ) := by
  have htail : ∀ k : ℕ, q ∣ M (J + k) := by
    intro k
    induction k with
    | zero => simpa using hqJ
    | succ k ih =>
        simpa only [Nat.add_succ] using ih.trans (hnested (J + k))
  have hmod : ∀ n : ℕ, J ≤ n → (q : ℤ) ∣ (M n : ℤ) := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact_mod_cast htail k
  intro n hn
  have hpred : n - 1 + 1 = n := by omega
  have hbefore : (q : ℤ) ∣ ((∑ i ∈ range n, d i : ℕ) : ℤ) := by
    have hdiv := (hmod (n - 1) (by omega)).trans (hprefix (n - 1))
    simpa only [hpred] using hdiv
  have hafter : (q : ℤ) ∣ ((∑ i ∈ range (n + 1), d i : ℕ) : ℤ) :=
    (hmod n (by omega)).trans (hprefix n)
  have hdifference := dvd_sub hafter hbefore
  have htel :
      ((∑ i ∈ range (n + 1), d i : ℕ) : ℤ) -
        ((∑ i ∈ range n, d i : ℕ) : ℤ) = (d n : ℤ) := by
    rw [sum_range_succ]
    push_cast
    ring
  rw [htel] at hdifference
  exact ⟨hdifference, hbefore⟩

/-- The existing interval feedback theorem with both eventual congruences.
Every target in the supplied continuation interval has bounded digits and
the prescribed sum. Nested moduli eventually containing every positive
integer preserve each fixed-modulus digit and cumulative congruence. -/
theorem exists_feedback_digits_hasSum_eventual_congruences
    {A M : ℕ → ℕ} {w lo hi : ℕ → ℝ} {y : ℝ}
    (hM : ∀ n, 0 < M n) (hA : ∀ n, 2 * M n ≤ A n)
    (hw : ∀ n, 0 < w n) (hlo : ∀ n, 0 ≤ lo n)
    (hl : ∀ n, lo n = (M n : ℝ) * w n + lo (n + 1))
    (hu : ∀ n, hi n = ((A n : ℝ) - M n) * w n + hi (n + 1))
    (hov : ∀ n, (M n : ℝ) * w n ≤ hi (n + 1) - lo (n + 1))
    (hvanish : Tendsto hi atTop (𝓝 0))
    (hnested : ∀ n, M n ∣ M (n + 1))
    (hcofinal : ∀ q : ℕ, 0 < q → ∃ J : ℕ, q ∣ M J)
    (hyl : lo 0 ≤ y) (hyu : y ≤ hi 0) :
    ∃ d : ℕ → ℕ,
      (∀ n, d n ≤ A n) ∧
      HasSum (fun n => (d n : ℝ) * w n) y ∧
      ∀ q : ℕ, 0 < q → ∃ N : ℕ, ∀ n, N ≤ n →
        (q : ℤ) ∣ (d n : ℤ) ∧
          (q : ℤ) ∣ ((∑ i ∈ range n, d i : ℕ) : ℤ) := by
  obtain ⟨d, hd, hprefix, hsum⟩ :=
    exists_feedback_digits_hasSum hM hA hw hlo hl hu hov hvanish hyl hyu
  refine ⟨d, hd, hsum, ?_⟩
  intro q hq
  obtain ⟨J, hqJ⟩ := hcofinal q hq
  exact ⟨J + 1, prefix_and_digit_dvd_of_nested_moduli M d hnested hprefix q J hqJ⟩

#print axioms prefix_and_digit_dvd_of_nested_moduli
#print axioms exists_feedback_digits_hasSum_eventual_congruences

end ErdosProblems.Synthesis.FeedbackContinuation
