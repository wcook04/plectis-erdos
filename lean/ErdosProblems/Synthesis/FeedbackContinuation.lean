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

/-- The properties used by the continuation argument, independent of a selector.
This relation does not promise that an additional constraint has a witness. -/
def Admissible (A M C d : ℕ) (w lo hi r : ℝ) : Prop :=
  d ≤ A ∧ (M : ℤ) ∣ (C : ℤ) + (d : ℤ) ∧
    lo ≤ r - (d : ℝ) * w ∧ r - (d : ℝ) * w ≤ hi

/-- The existing selector witnesses non-emptiness under its original overlap
hypotheses. The relation itself permits every digit satisfying the contract. -/
theorem admissible_nonempty {A M C : ℕ} {w lo hi r : ℝ}
    (hM : 0 < M) (hA : 2 * M ≤ A) (hw : 0 < w)
    (hov : (M : ℝ) * w ≤ hi - lo)
    (hrl : (M : ℝ) * w + lo ≤ r)
    (hru : r ≤ ((A : ℝ) - M) * w + hi) :
    ∃ d, Admissible A M C d w lo hi r :=
  ⟨feedbackDigit A M C w lo r, feedbackDigit_spec hM hA hw hov hrl hru⟩

/-- Any digit sequence satisfying the step contract has the prescribed sum.
The policy can depend on the full history; only its actual choices matter.
Vanishing continuation bounds are an infinite hypothesis, never inferred
from a finite execution. -/
theorem admissible_digits_hasSum
    {A M d : ℕ → ℕ} {w lo hi : ℕ → ℝ} {y : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hlo : ∀ n, 0 ≤ lo n)
    (hvanish : Tendsto hi atTop (𝓝 0))
    (hstep : ∀ n, Admissible (A n) (M n) (∑ i ∈ range n, d i) (d n)
      (w n) (lo (n + 1)) (hi (n + 1))
      (y - ∑ i ∈ range n, (d i : ℝ) * w i)) :
    (∀ n, d n ≤ A n) ∧
      (∀ n, (M n : ℤ) ∣ ((∑ i ∈ range (n + 1), d i : ℕ) : ℤ)) ∧
      HasSum (fun n => (d n : ℝ) * w n) y := by
  have hb : ∀ n, 0 ≤ y - ∑ i ∈ range (n + 1), (d i : ℝ) * w i ∧
      y - ∑ i ∈ range (n + 1), (d i : ℝ) * w i ≤ hi (n + 1) := by
    intro n
    have hs := hstep n
    dsimp [Admissible] at hs
    rw [sum_range_succ]
    constructor <;> linarith [hlo (n + 1), hs.2.2.1, hs.2.2.2]
  refine ⟨fun n => (hstep n).1, ?_, ?_⟩
  · intro n
    simpa only [sum_range_succ, Nat.cast_add] using (hstep n).2.1
  · have hr : Tendsto
        (fun n => y - ∑ i ∈ range (n + 1), (d i : ℝ) * w i) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hvanish.comp (tendsto_add_atTop_nat 1))
        (fun n => (hb n).1) (fun n => (hb n).2)
    have ht : Tendsto (fun n => y - (y - ∑ i ∈ range (n + 1), (d i : ℝ) * w i))
        atTop (𝓝 (y - 0)) := tendsto_const_nhds.sub hr
    have ht' : Tendsto (fun n => ∑ i ∈ range (n + 1), (d i : ℝ) * w i)
        atTop (𝓝 y) := by
      simpa only [sub_sub_cancel, sub_zero] using ht
    rw [hasSum_iff_tendsto_nat_of_nonneg
      (fun n => mul_nonneg (Nat.cast_nonneg _) (hw n))]
    exact (tendsto_add_atTop_iff_nat 1).mp ht'

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

/-- Reuse of the congruence transport for every admissible policy. Adding
restrictions on digits is allowed only when the resulting sequence still
satisfies all step hypotheses. -/
theorem admissible_digits_hasSum_eventual_congruences
    {A M d : ℕ → ℕ} {w lo hi : ℕ → ℝ} {y : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hlo : ∀ n, 0 ≤ lo n)
    (hvanish : Tendsto hi atTop (𝓝 0))
    (hstep : ∀ n, Admissible (A n) (M n) (∑ i ∈ range n, d i) (d n)
      (w n) (lo (n + 1)) (hi (n + 1))
      (y - ∑ i ∈ range n, (d i : ℝ) * w i))
    (hnested : ∀ n, M n ∣ M (n + 1))
    (hcofinal : ∀ q : ℕ, 0 < q → ∃ J : ℕ, q ∣ M J) :
    (∀ n, d n ≤ A n) ∧ HasSum (fun n => (d n : ℝ) * w n) y ∧
      ∀ q : ℕ, 0 < q → ∃ N : ℕ, ∀ n, N ≤ n →
        (q : ℤ) ∣ (d n : ℤ) ∧
          (q : ℤ) ∣ ((∑ i ∈ range n, d i : ℕ) : ℤ) := by
  obtain ⟨hA, hp, hs⟩ := admissible_digits_hasSum hw hlo hvanish hstep
  refine ⟨hA, hs, ?_⟩
  intro q hq
  obtain ⟨J, hJ⟩ := hcofinal q hq
  exact ⟨J + 1, prefix_and_digit_dvd_of_nested_moduli M d hnested hp q J hJ⟩

#print axioms admissible_nonempty
#print axioms admissible_digits_hasSum
#print axioms admissible_digits_hasSum_eventual_congruences

end ErdosProblems.Synthesis.FeedbackContinuation
