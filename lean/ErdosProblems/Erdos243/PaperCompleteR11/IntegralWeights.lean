import ErdosProblems.Erdos243.PaperCompleteR11.UncentredSeries
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The improper-integral bridge for record weights

A finite nonnegative decreasing function on [1,∞) has
an unbounded improper integral precisely in the direction needed below:
its integer samples, and then every arithmetic progression of samples,
are nonsummable. No continuity, strict positivity, or regular variation is
assumed. Value zero is extended by the value at one, not by an undefined
value of the original weight.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open MeasureTheory Set
open scoped BigOperators

noncomputable def natWeight (f : ℝ → ℝ) (n : ℕ) : ℝ := f (max 1 n : ℕ)

/-- For a nonnegative locally integrable function this is the usual
statement that the improper integral from one to infinity is +∞. -/
def IntegralUnbounded (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, 1 ≤ R ∧ M < ∫ t in (1 : ℝ)..R, f t

theorem natWeight_nonneg (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) : ∀ n, 0 ≤ natWeight f n := by
  intro n
  apply hf
  exact_mod_cast (le_max_left 1 n)

theorem natWeight_antitone (f : ℝ → ℝ)
    (hf : AntitoneOn f (Ici 1)) : Antitone (natWeight f) := by
  intro n m hnm
  apply hf
  · simpa only [mem_Ici] using (show (1 : ℝ) ≤ (max 1 n : ℕ) by exact_mod_cast le_max_left 1 n)
  · simpa only [mem_Ici] using (show (1 : ℝ) ≤ (max 1 m : ℕ) by exact_mod_cast le_max_left 1 m)
  · exact_mod_cast (max_le_max_left 1 hnm)

/-- Blockwise comparison, including the finite prefix before a progression
starts. This is independent of any integral representation. -/
theorem sum_range_le_progression
    (f : ℕ → ℝ) (hf : Antitone f) (x P N : ℕ) :
    ∑ j ∈ Finset.range (x + N * P), f j ≤
      (∑ j ∈ Finset.range x, f j) +
        (P : ℝ) * ∑ k ∈ Finset.range N, f (x + k * P) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show x + (N + 1) * P = (x + N * P) + P by ring,
        Finset.sum_range_add, Finset.sum_range_succ]
      have hblock : ∑ j ∈ Finset.range P, f (x + N * P + j) ≤
          (P : ℝ) * f (x + N * P) := by
        calc
          ∑ j ∈ Finset.range P, f (x + N * P + j) ≤
              ∑ _j ∈ Finset.range P, f (x + N * P) :=
            Finset.sum_le_sum (fun j _ ↦ hf (by omega))
          _ = _ := by simp
      nlinarith [hblock]

/-- A summable arithmetic progression of a nonnegative antitone sequence
forces the entire sequence to be summable. There is no density assumption. -/
theorem summable_of_summable_progression
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ n, 0 ≤ f n)
    (x P : ℕ) (hP : 0 < P)
    (hs : Summable (fun k : ℕ ↦ f (x + k * P))) : Summable f := by
  classical
  apply summable_of_sum_le hpos
  intro s
  let N := s.sup id + 1
  have hNP : N ≤ N * P := by
    have h1 : 1 ≤ P := by omega
    simpa using Nat.mul_le_mul_left N h1
  have hsub : s ⊆ Finset.range (x + N * P) := by
    intro j hj
    have hh : j ≤ s.sup id := Finset.le_sup (f := id) hj
    apply Finset.mem_range.mpr
    dsimp [N] at *
    omega
  calc
    ∑ j ∈ s, f j ≤ ∑ j ∈ Finset.range (x + N * P), f j :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ ↦ hpos j)
    _ ≤ (∑ j ∈ Finset.range x, f j) +
        (P : ℝ) * ∑ k ∈ Finset.range N, f (x + k * P) :=
      sum_range_le_progression f hf x P N
    _ ≤ (∑ j ∈ Finset.range x, f j) +
        (P : ℝ) * ∑' k : ℕ, f (x + k * P) := by
      gcongr
      exact hs.sum_le_tsum (Finset.range N) (fun k _ ↦ hpos _)

theorem divergesOnProgressions_of_not_summable
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ n, 0 ≤ f n)
    (hs : ¬ Summable f) : DivergesOnProgressions f := by
  intro x P hP hprog
  exact hs (summable_of_summable_progression f hf hpos x P hP hprog)

/-- The integral comparison is performed on bounded intervals, where
monotonicity supplies integrability. The final passage is an explicit
unboundedness contradiction, not an exchange of an integral and an infinite sum. -/
theorem natWeight_not_summable_of_integral
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : IntegralUnbounded f) : ¬ Summable (natWeight f) := by
  intro hs
  have hshift0 : Summable (fun n : ℕ ↦ natWeight f (n + 1)) :=
    (summable_nat_add_iff 1).2 hs
  have hshift : Summable (fun n : ℕ ↦ f (1 + (n : ℝ))) := by
    apply hshift0.congr
    intro n
    simp [natWeight, max_eq_right (show 1 ≤ n + 1 by omega), add_comm]
  let S : ℝ := ∑' n : ℕ, f (1 + (n : ℝ))
  obtain ⟨R, hR, hbig⟩ := hdiv (S + 1)
  obtain ⟨N, hN⟩ := exists_nat_gt R
  have hRN : R ≤ 1 + (N : ℝ) := by linarith
  have hI1R : IntervalIntegrable f volume 1 R := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le hR]
    exact hf.mono (fun x hx ↦ hx.1)
  have hIRN : IntervalIntegrable f volume R (1 + (N : ℝ)) := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le hRN]
    exact hf.mono (fun x hx ↦ hR.trans hx.1)
  have htail : 0 ≤ ∫ t in R..(1 + (N : ℝ)), f t :=
    intervalIntegral.integral_nonneg hRN (fun x hx ↦ hpos x (hR.trans hx.1))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI1R hIRN
  have hmono : AntitoneOn f (Icc (1 : ℝ) (1 + (N : ℝ))) :=
    hf.mono (fun x hx ↦ hx.1)
  have hupper : (∫ t in (1 : ℝ)..(1 + (N : ℝ)), f t) ≤ S := by
    calc
      (∫ t in (1 : ℝ)..(1 + (N : ℝ)), f t) ≤
          ∑ i ∈ Finset.range N, f (1 + (i : ℝ)) := hmono.integral_le_sum
      _ ≤ S := hshift.sum_le_tsum (Finset.range N)
        (fun n _ ↦ hpos _ (by norm_num))
  linarith

theorem natWeight_divergesOnProgressions
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : IntegralUnbounded f) : DivergesOnProgressions (natWeight f) :=
  divergesOnProgressions_of_not_summable (natWeight f)
    (natWeight_antitone f hf) (natWeight_nonneg f hpos)
    (natWeight_not_summable_of_integral f hf hpos hdiv)

/-- Full integral-weighted mixed/raw equivalence for the actual LCM state.
All arithmetic suppliers and the integral-to-progression passage are
constructed in the preceding proofs. At positive U, natWeight f (U n)
is exactly the paper's f(U n). -/
theorem uncentred_integral_equivalence
    (q : ℕ) (a U : ℕ → ℕ) (b : ℕ → ℤ) (B : ℕ)
    (hq : 0 < q) (ha : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ a n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) =
      (a n : ℤ) * U n - b n * (cumulativeDigitLcm q a n : ℤ))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : IntegralUnbounded f) :
    ((∃ H : ℕ, ∀ n, U n ≤ H) ↔
      Summable (mixedCharge U (lcmOverlap q a) B (natWeight f))) ∧
    ((∃ H : ℕ, ∀ n, U n ≤ H) ↔
      Summable (rawCharge U (lcmOverlap q a) B (natWeight f))) := by
  have hd := natWeight_divergesOnProgressions f hf hpos hdiv
  exact ⟨bounded_iff_summable_mixed q a U b B ha hstep
    (natWeight f) (natWeight_antitone f hf) (natWeight_nonneg f hpos) hd,
    bounded_iff_summable_raw q a U b B hq ha hstep
    (natWeight f) (natWeight_antitone f hf) (natWeight_nonneg f hpos) hd⟩

/-- Zero-height extension does not alter any weight in a positive orbit. -/
theorem natWeight_eq_at_positive (f : ℝ → ℝ) {u : ℕ} (hu : 0 < u) :
    natWeight f u = f (u : ℝ) := by
  simp [natWeight, max_eq_right (show 1 ≤ u by omega)]

/-- Normalised vanishing is used only for discreteness *after* the global
height theorem; it is not smuggled into the uncentred charging argument. -/
theorem zero_error_of_summable_raw_integral
    (q : ℕ) (a U : ℕ → ℕ) (b V : ℕ → ℤ) (B : ℕ)
    (hq : 0 < q) (ha : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ a n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) =
      (a n : ℤ) * U n - b n * (cumulativeDigitLcm q a n : ℤ))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : IntegralUnbounded f)
    (hs : Summable (rawCharge U (lcmOverlap q a) B (natWeight f)))
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * (V n).natAbs < U n) :
    ∃ N, ∀ n, N ≤ n → V n = 0 := by
  exact PaperCompleteR7.zero_digit_of_bounded_height U V
    ((uncentred_integral_equivalence q a U b B hq ha hstep f hf hpos hdiv).2.2 hs)
    hvanish

/-- The weighted recurrence is composed from the global raw-charge endpoint,
without dividing by b and without imposing a sign on b. -/
theorem weighted_recurrence_of_summable_raw_integral
    (q : ℕ) (a U : ℕ → ℕ) (b V : ℕ → ℤ) (B : ℕ)
    (hq : 0 < q) (ha : ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ a n) (hU : ∀ n, 0 < U n)
    (hstep : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) = (U n : ℤ) - V n)
    (herror : ∀ n, V n = b n * (cumulativeDigitLcm q a n : ℤ) -
      ((a n : ℤ) - 1) * U n)
    (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : IntegralUnbounded f)
    (hs : Summable (rawCharge U (lcmOverlap q a) B (natWeight f)))
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * (V n).natAbs < U n) :
    ∃ N, ∀ n, N ≤ n → b n * ((a (n + 1) : ℤ) - 1) =
      b (n + 1) * (a n : ℤ) * ((a n : ℤ) - 1) := by
  have harith : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) =
      (a n : ℤ) * U n - b n * (cumulativeDigitLcm q a n : ℤ) := by
    intro n
    have hh := hstep n
    rw [herror n] at hh
    nlinarith
  obtain ⟨N, hzero⟩ := zero_error_of_summable_raw_integral q a U b V B
    hq ha harith f hf hpos hdiv hs hvanish
  refine ⟨N, fun n hn ↦ ?_⟩
  apply PaperCompleteR9.weighted_recurrence_of_zero_pair
    (a n : ℤ) (a (n + 1) : ℤ) (b n) (b (n + 1))
    (cumulativeDigitLcm q a n : ℤ) (cumulativeDigitLcm q a (n + 1) : ℤ)
    (U n : ℤ) (U (n + 1) : ℤ) (lcmOverlap q a n : ℤ)
  · exact_mod_cast (Nat.ne_of_gt (hU n))
  · exact_mod_cast PaperCompleteR9.overlap_times_next_lcm q a n
  · simpa only [hzero n hn, sub_zero] using hstep n
  · have hh := herror n
    rw [hzero n hn] at hh
    omega
  · have hh := herror (n + 1)
    rw [hzero (n + 1) (by omega)] at hh
    omega

end ErdosProblems.Erdos243.PaperCompleteR11
