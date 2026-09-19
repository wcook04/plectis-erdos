import ErdosProblems.Erdos243.LcmRecordCrossing

/-!
# From finite first crossings to divergent record mass

This module transfers nonsummability of the actual progression weights to
the record-excess series. The sequence need only reach arbitrarily large
heights; no monotonicity or limit at infinity is assumed. The analytic input
that a particular weight has divergent progression sum remains explicit.
-/

namespace ErdosProblems.Erdos243.LcmRecordCrossing

/-- The nonnegative charge at a strict record, zero at every other step. -/
noncomputable def recordExcessWeight (U : ℕ → ℕ) (B : ℕ) (f : ℕ → ℝ)
    (n : ℕ) : ℝ :=
  if (∀ j ≤ n, U j < U (n + 1)) then
    ((U (n + 1) - U n - B : ℕ) : ℝ) * f (U n) else 0

/-- An unbounded sequence satisfying the actual arithmetic covering and
feedback cannot have summable record charges when the progression weights
are nonsummable. The finite bound supplies the charge; it is not a premise. -/
theorem not_summable_recordExcessWeight_of_progression
    (U : ℕ → ℕ) (a L : ℕ → ℤ) (x P B : ℕ) (hP : B < P)
    (hzero : U 0 < x)
    (hunbounded : ∀ t : ℕ, ∃ n, t ≤ U n)
    (hfeedback : ∀ n, (∀ j ≤ n, U j < U (n + 1)) →
      ((U (n + 1) - U n : ℕ) : ℤ) = (a n - 1) * U n - L n)
    (hcover : ∀ n k : ℕ, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L n ∧ m ∣ z)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u)
    (hdiverges : ¬ Summable (fun k : ℕ => f (x + k * P))) :
    ¬ Summable (recordExcessWeight U B f) := by
  classical
  intro hsum
  apply hdiverges
  have hcharge : ∀ n, 0 ≤ recordExcessWeight U B f n := by
    intro n
    unfold recordExcessWeight
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (hpos _)
    · exact le_refl 0
  apply summable_of_sum_le (fun k => hpos (x + k * P))
  intro s
  obtain ⟨N, hN⟩ := hunbounded (s.sup (fun k => x + k * P))
  have hfinite := finite_record_weighted_bound s U a L x P B N hP
    (fun k _hk => lt_of_lt_of_le hzero (Nat.le_add_right x (k * P)))
    (fun k hk => ⟨N, le_refl N, (Finset.le_sup hk).trans hN⟩)
    (fun n _hn => hfeedback n)
    (fun n _hn k _hk => hcover n k) f hf hpos
  calc
    ∑ k ∈ s, f (x + k * P) ≤
        ∑ n ∈ Finset.range N, recordExcessWeight U B f n := by
      simpa only [recordExcessWeight] using hfinite
    _ ≤ ∑' n, recordExcessWeight U B f n :=
      hsum.sum_le_tsum (Finset.range N) (fun n _hn => hcharge n)

end ErdosProblems.Erdos243.LcmRecordCrossing
