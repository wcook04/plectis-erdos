/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.RankOneSharpFloor

/-!
# Source transport for the sharp positive rank-one floor in Erdős #249
-/

namespace Erdos249257.ExternalVerification249RankOneSharpFloor

open scoped BigOperators
open ArithmeticFunction

noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) / (((2 : ℝ) ^ (n + 1) - 1) ^ r)

noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n

noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n

noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)

theorem rankOneSubrankQuotient_eq_one_five_iff
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient e Y = rankOneSubrankQuotient 1 5 ↔
      e = 1 ∧ Y = 5 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_eq_one_five_iff
      he hY

theorem rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (21 : ℝ) / 320 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
      he hY

theorem rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 16 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen
      he hY

theorem not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen :
    ¬ ∀ {e Y : ℕ}, 1 ≤ e → 4 ≤ Y →
      (1 : ℝ) / 15 <
        rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen

theorem positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (21 : ℝ) / 320 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2 := by
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
      s hs w e Y hw he hY

theorem primitive_form_abs_gt_twentyOne_div_threeTwenty
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot : rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) * (21 : ℝ) / 320 <
      |(q : ℝ) * mobiusMersenneTheta 2 - p| := by
  have hquot' :
      ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient e Y =
        (p : ℝ) / q := by
    simpa [rankOneSubrankQuotient, mobiusMersennePrefix, mobiusMersenneTerm,
      ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
      ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
      Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using hquot
  simpa [rankOneSubrankQuotient, mobiusMersennePrefix,
    mobiusMersenneTheta, mobiusMersenneTerm,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient,
    ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTheta,
    Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm] using
    ErdosProblems.Erdos249.RankOneSubrankObstruction.primitive_form_abs_gt_twentyOne_div_threeTwenty
      he hY hq hquot'

end Erdos249257.ExternalVerification249RankOneSharpFloor
