import ErdosProblems.Erdos249.FullDepthRayAmplifier
import ErdosProblems.Erdos249.CyclotomicAnchoredKill
import ErdosProblems.Erdos249.RankOneSharpFloor
import ErdosProblems.Erdos249.ParityPerturbedRationalControl
import Mathlib

/-!
# Whole displayed statements assembled from the landed libraries

No new certificate supply is asserted. The equivalences below retain their
universal quantifiers. In particular, an implication whose premise is a supply
is not a proof of that supply. No paper source is modified.

Build status: NOT RUN. These are complete proof-source candidates, not a
claim of a successful Lean or Comparator run.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7

open scoped BigOperators
open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.TotientTailPeriodKiller
open FullDepthRayAmplifier

/-- The first clause of short-note res:fulldepth starts with nonintegrality,
not an already-given finite certificate. Completeness supplies that certificate. -/
theorem fullDepth_pairs_of_nonintegral {d N : ℕ} (hd : 0 < d)
    (hnot : totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
      certifiedKill (t * d) N (t * d) ∨
        certifiedKill ((t + 1) * d) N ((t + 1) * d) := by
  obtain ⟨L, hL⟩ := exists_certifiedKill_of_tail_diff_notMem_int hnot
  exact exists_adjacent_fullDepthKill_of_seed hd hL

/-- All three clauses of short-note res:fulldepth in a single declaration. -/
theorem fullDepth_amplification :
    (∀ d N : ℕ, 0 < d →
      (totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) →
      ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
        certifiedKill (t * d) N (t * d) ∨
          certifiedKill ((t + 1) * d) N ((t + 1) * d)) ∧
    (∀ d N : ℕ, 0 < d →
      ((∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
        totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ))) ∧
    ((∀ d : ℕ, 0 < d → ∀ N : ℕ,
        ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by
  exact ⟨fun _ _ hd hn => fullDepth_pairs_of_nonintegral hd hn,
    fun _ _ hd => exists_fullDepthKill_on_ray_iff_shift_notMem_int hd,
    apFullDepthEscape_iff_irrational⟩

/-! ## Rank-one floor: denominator positivity and the complete conjunction -/

open RankOneSubrankObstruction
open Erdos257PeriodNoncollapse.SignedQMomentObstruction

/-- A displayed denominator is positive, rather than merely nonzero.
The already-proved rung lower bound and uniform tail bound suffice. -/
theorem rankOne_denominator_pos {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    0 < mobiusMersennePrefix Y (2 * e + 2) := by
  have hr : 3 ≤ 2 * e + 2 := by omega
  have hlow := mobiusMersenneTheta_ge_alpha hr
  have herr := abs_mobiusMersenneTheta_sub_prefix_le hY hr
  have hup := (abs_le.mp herr).2
  linarith

/-- The entire short-note positive rank-one theorem, with arbitrary finite
positive weights, not just monomials or rational weights. -/
theorem positive_rankOne_floor :
    (∀ e Y : ℕ, 1 ≤ e → 4 ≤ Y →
      0 < mobiusMersennePrefix Y (2 * e + 2) ∧
      rankOneSubrankQuotient 1 5 ≤ rankOneSubrankQuotient e Y ∧
      (rankOneSubrankQuotient e Y = rankOneSubrankQuotient 1 5 ↔ e = 1 ∧ Y = 5) ∧
      (21 : ℝ) / 320 < rankOneSubrankQuotient e Y - mobiusMersenneTheta 2) ∧
    (∀ {ι : Type} [DecidableEq ι], ∀ s : Finset ι, s.Nonempty →
      ∀ (w : ι → ℝ) (e Y : ι → ℕ),
      (∀ i ∈ s, 0 < w i) → (∀ i ∈ s, 1 ≤ e i) → (∀ i ∈ s, 4 ≤ Y i) →
      (21 : ℝ) / 320 <
        (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) - mobiusMersenneTheta 2) ∧
    rankOneSubrankQuotient 1 5 - mobiusMersenneTheta 2 < (1 : ℝ) / 15 := by
  refine ⟨?_, ?_, rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen⟩
  · intro e Y he hY
    exact ⟨rankOne_denominator_pos he hY,
      rankOneSubrankQuotient_ge_one_five he hY,
      rankOneSubrankQuotient_eq_one_five_iff he hY,
      rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty he hY⟩
  · intro ι inst s hs w e Y hw he hY
    exact positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty s hs w e Y hw he hY

/-- The two additional quantitative clauses in long-record thm:rankonefloor.
Combined with positive_rankOne_floor, this covers the complete displayed claim. -/
theorem long_record_rankOne_additional_clauses :
    (∀ e Y : ℕ, 1 ≤ e → 4 ≤ Y →
      (1 : ℝ) / 16 < rankOneSubrankQuotient e Y - mobiusMersenneTheta 2) ∧
    (∀ e Y q : ℕ, ∀ p : ℤ, 1 ≤ e → 4 ≤ Y → 1 ≤ q →
      rankOneSubrankQuotient e Y = (p : ℝ) / q →
      (q : ℝ) * 21 / 320 < |(q : ℝ) * mobiusMersenneTheta 2 - p|) := by
  exact ⟨fun _ _ he hY => rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen he hY,
    fun _ _ _ _ he hY hq hh => primitive_form_abs_gt_twentyOne_div_threeTwenty he hY hq hh⟩

/-! ## Long-record thm:parity-perturbed-control: the SAME sequence has all clauses -/

/-- A single existential witness for every clause of the displayed rational
control theorem. It does not combine unrelated rational countermodels. -/
theorem odd_agreement_rational_control :
    ∃ c : ℕ → ℕ,
      (∀ n, c n ≤ n) ∧
      (∀ n, n % 2 = 1 → c n = Nat.totient n) ∧
      (∀ n, |(c n : ℤ) - Nat.totient n| ≤ 2) ∧
      binaryCoeffSeries c = 5 / 4 ∧
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
        IsTemperedBinaryOrbit c v u ∧
        ∀ e : ℕ, 2 ^ e - 1 ≤
          Module.finrank ℚ
            (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by
  obtain ⟨hbound, hodd, hdiff, hvalue⟩ :=
    ParityPerturbedRationalControl.parity_perturbed_rational_control
  exact ⟨ParityPerturbedRationalControl.control, hbound, hodd, hdiff, hvalue,
    ParityPerturbedRationalControl.control_temperedOrbit_carryRank_unbounded⟩

end ErdosProblems.Erdos249.PaperCompleteR7
