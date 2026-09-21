import ErdosProblems.Erdos251.NonconcentrationConsequencesR11
import ErdosProblems.Erdos251.RealPrimeGapTail

/-!
# Erdős #251: the two-window event at the actual prime gaps

Paper restatement of `long251:res:sparse` ("sparsity of the two-window
event").  Fix `h ≥ 1`.  The set of `N ≥ 1` at which the three hypotheses of
`long251:res:smallpair` hold for the ACTUAL prime gaps has density zero, and
for the same `h` the set of `N` with `g_{N+h+1} = g_{N+1}` has density zero.

The general transfer theorem `small_mismatch_zeroDensity` is already in the
tree; what is added here is the specialisation to the actual gaps and their
actual real dyadic tail `realPrimeGapTail`, whose recurrence is
`realPrimeGapTail_recurrence`.

Schlage-Puchta's Lemma 4 for the actual gaps is not in Mathlib, so it is
carried as the explicit named hypothesis `hSP` and never assumed silently.
-/

noncomputable section

namespace ErdosProblems.Erdos251.PaperCompleteR21

open ErdosProblems.Erdos251
open PaperR11.Nonconcentration

/-- The actual prime-gap tail satisfies the recurrence in the form the
nonconcentration consumers use. -/
theorem primeGap_tail_recurrence :
    Recurrence (fun n => (primeGap0 n : ℤ)) realPrimeGapTail :=
  realPrimeGapTail_recurrence

/-- **`long251:res:sparse`.**  Both clauses, at the actual prime gaps.  The
first set is exactly the three displayed hypotheses of `long251:res:smallpair`
(`-1 < σ_h(N) < 1`, `-1 < σ_h(N+1) < 1`, `g_{N+h+1} ≠ g_{N+1}`) together with
`N ≥ 1`, with `σ_h(N) = shift realPrimeGapTail h N = T(N+h) - T(N)`. -/
theorem prime_gap_two_window_sparse (h : ℕ) (hh : 0 < h)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))) :
    ZeroDensity {N | 1 ≤ N ∧
        (-1 < shift realPrimeGapTail h N ∧ shift realPrimeGapTail h N < 1) ∧
        (-1 < shift realPrimeGapTail h (N + 1) ∧
          shift realPrimeGapTail h (N + 1) < 1) ∧
        (primeGap0 (N + h + 1) : ℤ) ≠ (primeGap0 (N + 1) : ℤ)} ∧
      ZeroDensity {N | (primeGap0 (N + h + 1) : ℤ) = (primeGap0 (N + 1) : ℤ)} :=
  small_mismatch_zeroDensity (fun n => (primeGap0 n : ℤ)) realPrimeGapTail hSP
    primeGap_tail_recurrence h hh

/-- The second clause with the gaps compared in `ℕ`, as the paper writes it. -/
theorem prime_gap_equal_shift_zeroDensity (h : ℕ) (hh : 0 < h)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))) :
    ZeroDensity {N | primeGap0 (N + h + 1) = primeGap0 (N + 1)} := by
  have hset : {N : ℕ | primeGap0 (N + h + 1) = primeGap0 (N + 1)} =
      {N : ℕ | (primeGap0 (N + h + 1) : ℤ) = (primeGap0 (N + 1) : ℤ)} := by
    ext N
    simp
  rw [hset]
  exact (prime_gap_two_window_sparse h hh hSP).2

end ErdosProblems.Erdos251.PaperCompleteR21

#print axioms ErdosProblems.Erdos251.PaperCompleteR21.primeGap_tail_recurrence
#print axioms ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_two_window_sparse
#print axioms ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_equal_shift_zeroDensity
