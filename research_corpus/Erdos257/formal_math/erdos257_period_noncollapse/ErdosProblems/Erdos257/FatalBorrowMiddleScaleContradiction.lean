import ErdosProblems.Erdos257.FatalBorrowPositiveResidualPacket
import Erdos257PeriodNoncollapse.HalfResetSqrtEscapeScaleProducers

/-!
# Erdős #257: fatal borrows collide with the middle reset scale

A fatal selected-ancestry borrow has a square-root-small midpoint residual,
and its aligned seam remainder is one larger.  The same fatality hypothesis
also bounds the paired pulse linearly in that residual.  Since the seam
remainder is smaller than its row, the row cannot be an upper reset; it is a
middle reset.  The middle reset scale producer then forces an exponential
lower bound on four times this square-root-small remainder, a contradiction.

Thus the selected-ancestry route needs only the middle half of reset
square-root escape.  The upper reset scale producer is not needed to exclude
a fatal borrow.
-/

namespace ErdosProblems.Erdos257

open Erdos257PeriodNoncollapse
open Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy
open Erdos257PeriodNoncollapse.HalfUpperResetCriticalBand

noncomputable section

private theorem nat_le_two_pow_self (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ n + 2 ^ n :=
          Nat.add_le_add_left Nat.one_le_two_pow (2 ^ n)
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

private theorem fatal_linear_lt_middleScale_even (k : ℕ) :
    16 * (13 + 2 * k) + 12 < 3 * 2 ^ (9 + k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show 9 + (k + 1) = (9 + k) + 1 by omega, pow_succ]
      omega

private theorem fatal_linear_lt_middleScale_odd (k : ℕ) :
    16 * (14 + 2 * k) + 12 < 3 * 2 ^ (9 + k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show 9 + (k + 1) = (9 + k) + 1 by omega, pow_succ]
      omega

/-- **Fatal-borrow/row-escape contradiction.**  The selected-ancestry
midpoint transfer makes every mature fatal skip a row-small seam reset.  An
upper reset is impossible because its remainder lies above `2^d`; on the
middle branch, the existing row-escape producer contradicts row-smallness
directly.  This is the weakest producer interface consumed by the
selected-ancestry fatal-row route. -/
theorem nonpositiveComplementBudget_false_of_middleProducerRowEscape
    (hrowEscape : SeamMiddleProducerRowEscape)
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0) :
    False := by
  obtain ⟨R, hrow, _halign, _hrem⟩ :=
    nonpositiveComplementBudget_forces_midpointRow
      (d := d) (by omega) hskip hfatal
  have hseamSmall := midpointRealSkip_forces_seamRemainder_lt_rank
    (d := d) (R := R) (by omega) hskip hrow
  have hreset := seamRowSmall_upperOrMiddle (by omega) hseamSmall
  rcases hreset with hcarry | ⟨hncarry, hmiddle⟩
  · have hlarge := seamSuccessorCarries_remainder_gt_pow
      (s := d) (by omega) hcarry
    have hdPow := nat_le_two_pow_self d
    omega
  · have hrowLarge := hrowEscape d (by omega) hd hncarry hmiddle
    have hcutRem := seamAdjacentCut_remainder (s := d) (by omega : 5 ≤ d)
    rw [hcutRem] at hrowLarge
    omega

/-- The upper-reset critical-band producer is already strong enough to
exclude a mature fatal selected-ancestry borrow.  This is the direct fan-in
from the critical-band lane to the weakest row-escape consumer above. -/
theorem nonpositiveComplementBudget_false_of_upperResetCriticalBandEscape
    (hcritical : SeamUpperResetCriticalBandEscape)
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0) :
    False := by
  apply nonpositiveComplementBudget_false_of_middleProducerRowEscape
    ((seamUpperResetCriticalBandEscape_iff.mp hcritical).toMiddleProducerRowEscape)
    hd hskip hfatal

/-- **Fatal borrow emits a critical dyadic danger witness.**  If a mature
selected-ancestry complement budget is nonpositive at a real skip, then some
actual upper reset has its charge in the narrow forbidden interval immediately
below its nearest dyadic boundary.  The witness carries the critical-index
certificate, so it is not an arbitrary member of the former all-`j` family.

This theorem does not assert that the witness is the last upper ancestor of
the fatal row; it is the exact global obstruction obtained by contraposing
the all-depth critical-band producer. -/
theorem exists_upperResetCriticalDanger_of_nonpositiveComplementBudget
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0) :
    ∃ (s : ℕ) (hs13 : 13 ≤ s) (j : ℕ),
      (seamAdjacentCut s (by omega)).successorCarries ∧
      CriticalDyadicBandIndex s
        (seamUpperResetCharge s (by omega)) j ∧
      2 ^ (s - j + 1) <
        seamUpperResetCharge s (by omega) + 2 * (s + j) := by
  classical
  by_contra hnone
  have hcritical : SeamUpperResetCriticalBandEscape := by
    intro s hs5 hs13 hcarry
    obtain ⟨j, hj⟩ := exists_criticalDyadicBandIndex
      (seamUpperResetCharge_le hs5 hcarry)
    refine ⟨j, hj, ?_⟩
    by_contra hgap
    have hdanger :
        2 ^ (s - j + 1) <
          seamUpperResetCharge s hs5 + 2 * (s + j) :=
      Nat.lt_of_not_ge hgap
    apply hnone
    refine ⟨s, hs13, j, ?_, ?_, ?_⟩
    · simpa using hcarry
    · simpa using hj
    · simpa using hdanger
  exact nonpositiveComplementBudget_false_of_upperResetCriticalBandEscape
    hcritical hd hskip hfatal

/-- **Fatal borrow exposes the last upper ancestor and its complete actual
right run.**  Apply the first-bad-row localization to the row-small seam
state emitted by a fatal selected-ancestry borrow.  The witness is stronger
than mere bounded critical danger in a different direction: its band index
is the literal number of right recurrences from the last upper reset to the
first row-small endpoint, and all those recurrences are returned for direct
use by the exact cylinder and endpoint-packet identities.

No claim is made here that the actual run length is the nearest dyadic
critical index.  Establishing that equality is exactly the remaining
endpoint-packet inequality. -/
theorem exists_lastUpperAncestorRightRunDanger_before_of_nonpositiveComplementBudget
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0) :
    ∃ (s : ℕ) (hs13 : 13 ≤ s) (k : ℕ),
      s < d ∧ k ≤ s ∧ s + k + 1 ≤ d ∧
        (seamAdjacentCut s (by omega)).successorCarries ∧
        (∀ j : ℕ, j < k →
          seamIntegerGreedyRemainder (s + j + 2) +
              2 ^ (s + j + 2) +
              (seamAdjacentCut (s + j + 1) (by omega)).belowPulse + 4 =
            4 * seamIntegerGreedyRemainder (s + j + 1)) ∧
        seamIntegerGreedyRemainder (s + k + 1) < s + k + 1 ∧
        2 ^ (s - k + 1) <
          seamUpperResetCharge s (by omega) + 2 * (s + k) := by
  obtain ⟨R, hrow, _halign, _hrem⟩ :=
    nonpositiveComplementBudget_forces_midpointRow
      (d := d) (by omega) hskip hfatal
  have hseamSmall := midpointRealSkip_forces_seamRemainder_lt_rank
    (d := d) (R := R) (by omega) hskip hrow
  obtain ⟨s, hs13, k, hsd, hk, hend, hcarry, hrun,
      hendpointSmall, hdanger⟩ :=
    exists_lastUpperAncestorRightRun_danger_of_rowSmall hd hseamSmall
  refine ⟨s, hs13, k, hsd, hk, hend, hcarry, hrun,
    hendpointSmall, ?_⟩
  simpa [seamUpperResetCharge] using hdanger

/-- **Fatal borrow emits a critical danger strictly before its row.**  The
first-bad-row/last-ancestor argument only consumes upper-reset band
certificates below the target row.  Consequently the global witness above
can be localized: a fatal row `d` forces an actual upper reset `s < d` whose
charge lies in the forbidden interval below its nearest dyadic boundary. -/
theorem exists_upperResetCriticalDanger_before_of_nonpositiveComplementBudget
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0) :
    ∃ (s : ℕ) (hs13 : 13 ≤ s) (hsd : s < d) (j : ℕ),
      (seamAdjacentCut s (by omega)).successorCarries ∧
      CriticalDyadicBandIndex s
        (seamUpperResetCharge s (by omega)) j ∧
      2 ^ (s - j + 1) <
        seamUpperResetCharge s (by omega) + 2 * (s + j) := by
  classical
  obtain ⟨R, hrow, _halign, _hrem⟩ :=
    nonpositiveComplementBudget_forces_midpointRow
      (d := d) (by omega) hskip hfatal
  have hseamSmall := midpointRealSkip_forces_seamRemainder_lt_rank
    (d := d) (R := R) (by omega) hskip hrow
  by_contra hnone
  have hbandBelow :
      ∀ (s : ℕ) (hs5 : 5 ≤ s), 13 ≤ s → s < d →
        (seamAdjacentCut s hs5).successorCarries →
          ∀ j : ℕ, j ≤ s →
            2 ^ (s - j + 1) <
                4 * (seamAdjacentCut s hs5).overshoot +
                  (seamAdjacentCut s hs5).abovePulse ∨
              4 * (seamAdjacentCut s hs5).overshoot +
                    (seamAdjacentCut s hs5).abovePulse + 2 * (s + j) ≤
                2 ^ (s - j + 1) := by
    intro s hs5 hs13 hsd hcarry
    obtain ⟨j₀, hj₀⟩ := exists_criticalDyadicBandIndex
      (seamUpperResetCharge_le hs5 hcarry)
    have hgap :
        seamUpperResetCharge s hs5 + 2 * (s + j₀) ≤
          2 ^ (s - j₀ + 1) := by
      by_contra hnotGap
      have hdanger :
          2 ^ (s - j₀ + 1) <
            seamUpperResetCharge s hs5 + 2 * (s + j₀) :=
        Nat.lt_of_not_ge hnotGap
      apply hnone
      refine ⟨s, hs13, hsd, j₀, ?_, ?_, ?_⟩
      · simpa using hcarry
      · simpa using hj₀
      · simpa using hdanger
    have hall := dyadicBandEscape_of_critical hj₀ hgap
    intro j hj
    simpa [seamUpperResetCharge] using hall j hj
  have hlarge :=
    seamIntegerGreedyRemainder_ge_row_of_upperResetDyadicBandEscape_below
      hd hbandBelow
  omega

/-- From row thirteen onward, even the deliberately coarse linear envelope
for a fatal seam remainder lies below the middle-reset half-row scale. -/
theorem fatal_linear_lt_middleResetScale (d : ℕ) (hd : 13 ≤ d) :
    16 * d + 12 < 3 * 2 ^ ((d + 5) / 2) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (d - 13)
  · have hdEq : d = 13 + 2 * k := by omega
    rw [hdEq, show (13 + 2 * k + 5) / 2 = 9 + k by omega]
    exact fatal_linear_lt_middleScale_even k
  · have hdEq : d = 14 + 2 * k := by omega
    rw [hdEq, show (14 + 2 * k + 5) / 2 = 9 + k by omega]
    exact fatal_linear_lt_middleScale_odd k

/-- **Fatal-borrow/middle-scale contradiction.**  The middle reset
remainder-scale producer alone excludes every mature nonpositive complement
budget at an actual half-greedy skip.  This simultaneously removes the
positive residual packet and the unit residual packet; no upper-reset scale
hypothesis is used. -/
theorem nonpositiveComplementBudget_false_of_middleResetRemainderScaleProducer
    (hmid : SeamMiddleResetRemainderScaleProducer)
    {d : ℕ} (hd : 13 ≤ d)
    (hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1))
    (hfatal : halfSelectedAncestryComplementBudget d ≤ 0) :
    False := by
  obtain ⟨R, hrow, _halign, hrem⟩ :=
    nonpositiveComplementBudget_forces_midpointRow
      (d := d) (by omega) hskip hfatal
  have hD := halfGreedyPrefixSupport_pred_below d (by omega)
  have hcross :=
    insert_halfGreedyPrefixSupport_gt_half_of_realSkip (by omega) hskip
  have hRsmall :=
    aboveMidpointResidual_lt_two_natSqrt_add_three_of_real_crossing
      (D := halfGreedyPrefixSupport (d - 1)) (d := d) (R := R)
      (by omega) hD hrow hcross
  have hsqrtSelf : Nat.sqrt (2 * d) ≤ 2 * d := Nat.sqrt_le_self _
  have hRlinear : R ≤ 4 * d + 2 := by omega
  have hseamSmall := midpointRealSkip_forces_seamRemainder_lt_rank
    (d := d) (R := R) (by omega) hskip hrow
  have hreset := seamRowSmall_upperOrMiddle (by omega) hseamSmall
  rcases hreset with hcarry | ⟨hncarry, hmiddle⟩
  · have hlarge := seamSuccessorCarries_remainder_gt_pow
      (s := d) (by omega) hcarry
    have hdPow := nat_le_two_pow_self d
    omega
  · have hscale := hmid d (by omega) (by omega) hncarry hmiddle
    have hcutRem := seamAdjacentCut_remainder (s := d) (by omega : 5 ≤ d)
    have hfourUpper :
        4 * (seamAdjacentCut d (by omega : 5 ≤ d)).remainder ≤
          16 * d + 12 := by
      rw [hcutRem, hrem]
      omega
    have hmainLower :
        3 * 2 ^ ((d + 5) / 2) ≤
          4 * (seamAdjacentCut d (by omega : 5 ≤ d)).remainder := by
      omega
    have hlinear := fatal_linear_lt_middleResetScale d hd
    omega

/-- Global consumer form.  Once the finite rows below thirteen are known to
survive, the middle reset scale producer by itself proves one-half
membership.  A least nonpositive complement budget must be created by a
skip; the local contradiction above then removes it. -/
theorem half_mem_mersenneAchievementSet_of_base_and_middleResetRemainderScale
    (hbase : ∀ n : ℕ, n < 13 →
      0 < halfSelectedAncestryComplementBudget n)
    (hmid : SeamMiddleResetRemainderScaleProducer) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  rw [half_mem_mersenneAchievementSet_iff_selectedAncestryTailSurvival]
  intro n
  by_contra hn
  have hnFatal : halfSelectedAncestryComplementBudget n ≤ 0 :=
    le_of_not_gt hn
  let P : ℕ → Prop := fun m ↦
    halfSelectedAncestryComplementBudget m ≤ 0
  have hexists : ∃ m : ℕ, P m := ⟨n, hnFatal⟩
  let d := Nat.find hexists
  have hdFatal : P d := Nat.find_spec hexists
  have hd13 : 13 ≤ d := by
    by_contra hnot
    have hpositive := hbase d (by omega)
    exact (not_lt_of_ge hdFatal) hpositive
  have hdpos : 0 < d := by omega
  have hprevNot : ¬ P (d - 1) := by
    exact Nat.find_min hexists (by omega)
  have hprevPos : 0 < halfSelectedAncestryComplementBudget (d - 1) := by
    exact lt_of_not_ge hprevNot
  have hskip : ¬ mersenneWeight d ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
    intro htake
    have hrec := halfSelectedAncestryComplementBudget_succ (d - 1)
    have hdEq : d - 1 + 1 = d := Nat.sub_add_cancel hdpos
    have htake' : mersenneWeight (d - 1 + 1) ≤
        greedyMersenneRemainder (1 / 2 : ℝ) (d - 1) := by
      simpa [hdEq] using htake
    rw [if_pos htake', hdEq] at hrec
    exact (not_lt_of_ge hdFatal) (by simpa [hrec] using hprevPos)
  exact nonpositiveComplementBudget_false_of_middleResetRemainderScaleProducer
    hmid hd13 hskip hdFatal

/-- The finite base required by the least-fatal-row argument.  Three future
Mersenne weights already strictly dominate the exact half-greedy remainder
at every row below thirteen. -/
theorem halfSelectedAncestryComplementBudget_pos_below_thirteen
    (n : ℕ) (hn : n < 13) :
    0 < halfSelectedAncestryComplementBudget n := by
  rw [halfSelectedAncestryComplementBudget_eq_tail_sub_remainder]
  have htail1 := mersenneTail_eq_weight_add n
  have htail2 := mersenneTail_eq_weight_add (n + 1)
  have htail3 := mersenneTail_eq_weight_add (n + 2)
  have htailNonneg := mersenneTail_nonneg (n + 3)
  have hfinite :
      greedyMersenneRemainder (1 / 2 : ℝ) n <
        mersenneWeight (n + 1) + mersenneWeight (n + 2) +
          mersenneWeight (n + 3) := by
    interval_cases n <;>
      norm_num [greedyMersenneRemainder_succ, mersenneWeight]
  rw [htail1, htail2, htail3]
  linarith

/-- **Reduced one-half endpoint.**  Proving only the middle-reset remainder
scale producer is sufficient for the desired one-half membership.  The
upper-reset charge scale producer present in the general reset-sqrt route is
strictly unnecessary for this selected-ancestry fatal-borrow fan-in. -/
theorem half_mem_mersenneAchievementSet_of_middleResetRemainderScaleProducer
    (hmid : SeamMiddleResetRemainderScaleProducer) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_base_and_middleResetRemainderScale
    halfSelectedAncestryComplementBudget_pos_below_thirteen hmid

#print axioms fatal_linear_lt_middleResetScale
#print axioms nonpositiveComplementBudget_false_of_middleProducerRowEscape
#print axioms nonpositiveComplementBudget_false_of_upperResetCriticalBandEscape
#print axioms exists_upperResetCriticalDanger_of_nonpositiveComplementBudget
#print axioms exists_lastUpperAncestorRightRunDanger_before_of_nonpositiveComplementBudget
#print axioms exists_upperResetCriticalDanger_before_of_nonpositiveComplementBudget
#print axioms nonpositiveComplementBudget_false_of_middleResetRemainderScaleProducer
#print axioms half_mem_mersenneAchievementSet_of_base_and_middleResetRemainderScale
#print axioms halfSelectedAncestryComplementBudget_pos_below_thirteen
#print axioms half_mem_mersenneAchievementSet_of_middleResetRemainderScaleProducer

end

end ErdosProblems.Erdos257
