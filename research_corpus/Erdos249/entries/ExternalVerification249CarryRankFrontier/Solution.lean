/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.TotientTailCarryPeriod

/-! Exact source transport for the #249 carry-rank frontier. -/

namespace Erdos249257.ExternalVerification249CarryRankFrontier

noncomputable section

noncomputable abbrev binaryCoeffSeries :=
  Erdos257PeriodNoncollapse.binaryCoeffSeries
abbrev IsTemperedBinaryOrbit :=
  Erdos257PeriodNoncollapse.IsTemperedBinaryOrbit
abbrev totientKernelSeq := Erdos257PeriodNoncollapse.totientKernelSeq
abbrev carryKernelSeq := Erdos257PeriodNoncollapse.carryKernelSeq
abbrev TotientCanonicalIndex := Erdos257PeriodNoncollapse.TotientCanonicalIndex
abbrev canonicalTotientKernelFamily :=
  Erdos257PeriodNoncollapse.canonicalTotientKernelFamily
abbrev TotientCarryIndex := Erdos257PeriodNoncollapse.TotientCarryIndex
abbrev canonicalCarryKernelFamily :=
  Erdos257PeriodNoncollapse.canonicalCarryKernelFamily
abbrev SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) :=
  Erdos257PeriodNoncollapse.SeparatedMinorCertificate family
noncomputable abbrev totientTail :=
  Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail
abbrev CarrySectionsEventuallyPeriodicMod :=
  Erdos257PeriodNoncollapse.CarrySectionsEventuallyPeriodicMod

theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ¬ Irrational (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
        IsTemperedBinaryOrbit c v u :=
  Erdos257PeriodNoncollapse.not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    c hgrowth

theorem totient_carryKernel_diff
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u)
    {j r : ℕ} (hr : 0 < r) :
    (fun n => (v : ℚ) * totientKernelSeq j r n) =
      fun n => 2 * carryKernelSeq u j (r - 1) n -
        carryKernelSeq u j r n :=
  Erdos257PeriodNoncollapse.totient_carryKernel_diff hu hr

theorem finrank_canonicalCarryKernel_ge_of_certificate
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (e : ℕ)
    (cert : SeparatedMinorCertificate (canonicalTotientKernelFamily e)) :
    2 ^ e - 1 ≤
      Module.finrank ℚ
        (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) :=
  Erdos257PeriodNoncollapse.finrank_canonicalCarryKernel_ge_of_certificate
    hv hu e cert

theorem not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e))) :=
  Erdos257PeriodNoncollapse.not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    hirr

theorem carryShift_dvd_iff_tailDiff_mem_int
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    (v : ℤ) ∣ u (N + k) - u N ↔
      totientTail (N + k) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) :=
  Erdos257PeriodNoncollapse.carryShift_dvd_iff_tailDiff_mem_int
    hv hu N k

theorem not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u :=
  Erdos257PeriodNoncollapse.not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
    hirr

end

end Erdos249257.ExternalVerification249CarryRankFrontier
