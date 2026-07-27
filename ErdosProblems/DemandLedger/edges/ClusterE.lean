/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.DemandLedger.Basic

/-!
# Demand-ledger cluster E — Erdős #257 greedy Mersenne

Implication order on the open antecedents
`G073, G075, G076, G083, G084, G085`.

All six are sufficient conditions for `(1/2 : ℝ) ∈ mersenneAchievementSet`.
The computed order has three levels:

* `G083 ↔ G084` (dyadic block safety at every skipped rank — strongest),
* `G085` (two-channel cap at every skipped rank),
* `G073 ↔ G075 ↔ G076` (all three are *equivalent to* half-membership itself,
  hence weakest).

Nothing here weakens a statement: every edge below is stated between the
kernel-extracted `DemandLedger.G0xx` constants verbatim.
-/

open Erdos249257 Erdos249257.TotientTailPeriodKiller
open Erdos249257.HalfCarryReachability
open Filter

namespace DemandLedger.ClusterE

/-! ## Shared vocabulary

The hub of the cluster is `(1/2 : ℝ) ∈ mersenneAchievementSet`.  Every gap in
the cluster is a producer for it; three of them are also consumers of it.
-/

/-- Exponent one is never taken by the greedy half orbit. -/
private theorem one_not_mem_greedyHalf :
    (1 : ℕ) ∉ greedyMersenneSupport (1 / 2 : ℝ) := by
  intro hone
  have htake :=
    (succ_mem_greedyMersenneSupport_iff (1 / 2 : ℝ) 0).mp (by simpa using hone)
  norm_num [mersenneWeight, greedyMersenneRemainder] at htake

/-- Half-membership pins the value of the *canonical greedy* support series,
not merely of some support: membership forces greedy survival, and survival
forces the greedy prefix sums to converge to the target. -/
private theorem greedyHalf_series_half_of_mem
    (hmem : (1 / 2 : ℝ) ∈ mersenneAchievementSet) :
    erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) = (1 : ℝ) / 2 := by
  obtain ⟨hx, hsurvive⟩ :=
    (mem_mersenneAchievementSet_iff_greedy_survival (1 / 2 : ℝ)).1 hmem
  have hsum := summable_positiveMersenneSupportIndicator
    (greedyMersenneSupport (1 / 2 : ℝ))
  have htoSum : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        Set.indicator (greedyMersenneSupport (1 / 2 : ℝ)) mersenneWeight (k + 1))
      atTop
      (nhds (positiveMersenneSupportValue (greedyMersenneSupport (1 / 2 : ℝ)))) := by
    simpa [positiveMersenneSupportValue] using hsum.tendsto_sum_tsum_nat
  have hrem := tendsto_greedyMersenneRemainder_zero hx hsurvive
  have htoX : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        Set.indicator (greedyMersenneSupport (1 / 2 : ℝ)) mersenneWeight (k + 1))
      atTop (nhds ((1 : ℝ) / 2)) := by
    have hsub : Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) - greedyMersenneRemainder (1 / 2 : ℝ) n)
        atTop (nhds ((1 / 2 : ℝ) - 0)) := tendsto_const_nhds.sub hrem
    convert hsub using 1
    · funext n
      have hprefix := greedyMersenne_prefix_add_remainder (1 / 2 : ℝ) n
      linarith
    · simp
  rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
  exact tendsto_nhds_unique htoSum htoX

/-- Converse packaging: the greedy support realizing `1/2` is a membership
witness. -/
private theorem greedyHalf_mem_of_series_half
    (hhalf : erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) = (1 : ℝ) / 2) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  refine ⟨greedyMersenneSupport (1 / 2 : ℝ),
    zero_not_mem_greedyMersenneSupport _, ?_⟩
  rw [positiveMersenneSupportValue_eq_erdosSupportSeries]
  exact hhalf.symm

/-- Exact value forces the tempered centred carry.  This is the converse of
`support_half_of_mobiusCenteredHalfCarry_tempered`, obtained from the
`support_half_iff_affineBinaryOrbit_tempered` equivalence together with the
`U = 2V` identification at exponent one. -/
private theorem tempered_of_series_half
    (hhalf : erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) = (1 : ℝ) / 2) :
    Tendsto (fun N : ℕ ↦
        (mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ)
          / (2 : ℝ) ^ N)
      atTop (nhds 0) := by
  have hone := one_not_mem_greedyHalf
  have horbit :=
    (support_half_iff_affineBinaryOrbit_tempered
      (greedyMersenneSupport (1 / 2 : ℝ))).1 hhalf
  have hgeom : Tendsto (fun N : ℕ ↦ (1 : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hshift := (tendsto_add_atTop_iff_nat 1).2 horbit.2
  have hfun : (fun N : ℕ ↦
      ((affineBinaryOrbit
        (fun n : ℕ ↦ ((2 * supportCoeff (greedyMersenneSupport (1 / 2 : ℝ)) n : ℕ) : ℤ))
          1 (N + 1) : ℤ) : ℝ) / (2 : ℝ) ^ (N + 1)) =
      (fun N : ℕ ↦
        (mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ)
          / (2 : ℝ) ^ N + (1 : ℝ) / (2 : ℝ) ^ N) := by
    funext N
    rw [halfDenominatorCarry_eq_two_mul_integerCarry
      (greedyMersenneSupport (1 / 2 : ℝ)) hone N]
    change ((2 * integerHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N : ℤ) : ℝ)
        / (2 : ℝ) ^ (N + 1) = _
    push_cast
    rw [pow_succ]
    simp only [mobiusCenteredHalfCarry]
    push_cast
    ring
  rw [hfun] at hshift
  have hfinal := hshift.sub hgeom
  simpa using hfinal

/-- Exact value also forces the *quantitative* square-root bound.  The scaled
residual term of `integerHalfCarry_eq_scaled_residual_add_tail` vanishes, and
the remaining analytic tail obeys the unconditional divisor-count envelope. -/
private theorem sqrtBound_of_series_half
    (hhalf : erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) = (1 : ℝ) / 2) :
    ∀ N : ℕ,
      (mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ)
        ≤ 2 * Real.sqrt (N : ℝ) + 4 := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hone := one_not_mem_greedyHalf
  have hid := integerHalfCarry_eq_scaled_residual_add_tail
    (greedyMersenneSupport (1 / 2 : ℝ)) hone N
  rw [hhalf] at hid
  have htail := binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    (greedyMersenneSupport (1 / 2 : ℝ)) (N + 1)
  have hcast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  rw [hcast] at htail
  have hone_le : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hN1
  have hsqsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hnn : (0 : ℝ) ≤ Real.sqrt (N : ℝ) + 1 / 2 := by positivity
  have hstep : Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt (N : ℝ) + 1 / 2 := by
    have hsq : ((N : ℝ) + 1) ≤ (Real.sqrt (N : ℝ) + 1 / 2) ^ 2 := by nlinarith
    calc Real.sqrt ((N : ℝ) + 1)
        ≤ Real.sqrt ((Real.sqrt (N : ℝ) + 1 / 2) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (N : ℝ) + 1 / 2 := Real.sqrt_sq hnn
  have hm : (mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ)
      = (integerHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) - 1 := by
    simp only [mobiusCenteredHalfCarry]
    push_cast
    ring
  rw [hm, hid]
  simp only [sub_self, mul_zero, zero_add]
  linarith

/-! ## The hub: each gap as a producer of half-membership -/

private theorem hub_of_G073 (h : G073) : (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  unfold G073 at h
  exact greedyHalf_mem_of_series_half
    (greedy_half_infinite_of_mobiusCenteredHalfCarry_tempered h).2

private theorem hub_of_G075 (h : G075) : (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  unfold G075 at h
  exact greedyHalf_mem_of_series_half
    (greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound h).2

private theorem hub_of_G076 (h : G076) : (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  unfold G076 at h
  exact half_mem_mersenneAchievementSet_of_unboundedTerminalFalse h

private theorem hub_of_G083 (h : G083) : (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  unfold G083 at h
  exact half_mem_mersenneAchievementSet_of_actualBlockSafe h

private theorem hub_of_G084 (h : G084) : (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  unfold G084 at h
  exact half_mem_mersenneAchievementSet_of_skipped_dyadicCap h

private theorem hub_of_G085 (h : G085) : (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  unfold G085 at h
  exact half_mem_mersenneAchievementSet_of_skipped_twoChannelCap h

/-! ## The hub as a consumer: `G073`, `G075`, `G076` are *equivalent* to it -/

private theorem G073_of_hub (h : (1 / 2 : ℝ) ∈ mersenneAchievementSet) : G073 := by
  unfold G073
  exact tempered_of_series_half (greedyHalf_series_half_of_mem h)

private theorem G075_of_hub (h : (1 / 2 : ℝ) ∈ mersenneAchievementSet) : G075 := by
  unfold G075
  exact sqrtBound_of_series_half (greedyHalf_series_half_of_mem h)

private theorem G076_of_hub (h : (1 / 2 : ℝ) ∈ mersenneAchievementSet) : G076 := by
  unfold G076
  exact half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse.mp h

/-! ## Edges out of `G073` -/

theorem e_G073_G075 : G073 → G075 := fun h => G075_of_hub (hub_of_G073 h)

theorem e_G073_G076 : G073 → G076 := fun h => G076_of_hub (hub_of_G073 h)

/-! ## Edges out of `G075` -/

theorem e_G075_G073 : G075 → G073 := fun h => G073_of_hub (hub_of_G075 h)

theorem e_G075_G076 : G075 → G076 := fun h => G076_of_hub (hub_of_G075 h)

/-! ## Edges out of `G076` -/

theorem e_G076_G073 : G076 → G073 := fun h => G073_of_hub (hub_of_G076 h)

theorem e_G076_G075 : G076 → G075 := fun h => G075_of_hub (hub_of_G076 h)

/-! ## Edges out of `G083` -/

/-- Block dyadic safety at the actual displayed state *is* the dyadic cap;
this is the packaged direction already present in the corpus. -/
theorem e_G083_G084 : G083 → G084 := by
  unfold G083 G084
  intro h n hskip
  exact greedyHalfRemainder_le_nextDyadic_of_BlockSafe n (h n hskip)

theorem e_G083_G085 : G083 → G085 := by
  unfold G083 G085
  intro h n hskip
  exact (greedyHalfRemainder_le_nextDyadic_of_BlockSafe n (h n hskip)).trans
    (halfDyadicCap_le_halfTwoChannelCap (n + 1))

theorem e_G083_G073 : G083 → G073 := fun h => G073_of_hub (hub_of_G083 h)

theorem e_G083_G075 : G083 → G075 := fun h => G075_of_hub (hub_of_G083 h)

theorem e_G083_G076 : G083 → G076 := fun h => G076_of_hub (hub_of_G083 h)

/-! ## Edges out of `G084` -/

/-- The reverse of `e_G083_G084`: the displayed-numerator block test and the
real dyadic cap are the same inequality after clearing denominators, so the
two ledger entries are mutually implied. -/
theorem e_G084_G083 : G084 → G083 := by
  unfold G084 G083
  intro h n hskip
  have hexc := (greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos n).1 (h n hskip)
  have hp0 := halfGreedyResidualDisplayedNumerator_nonneg n
  have hpcast :
      (((halfGreedyResidualDisplayedNumerator n).natAbs : ℕ) : ℤ) =
        halfGreedyResidualDisplayedNumerator n := by
    simp [Int.natAbs_of_nonneg hp0]
  unfold halfGreedyNextDyadicExcessNumerator nextDyadicExcessIntNumerator at hexc
  push_cast at hexc
  unfold BlockDyadicSafeAt
  have hZ :
      (((halfGreedyResidualDisplayedNumerator n).natAbs : ℕ) : ℤ) *
          (((2 ^ (n + 1) : ℕ) : ℤ)) ≤
        2 * (halfGreedyPrefixDenominator n : ℤ) := by
    rw [hpcast]
    push_cast
    rw [pow_succ]
    ring_nf
    ring_nf at hexc
    linarith
  exact_mod_cast hZ

theorem e_G084_G085 : G084 → G085 := by
  unfold G084 G085
  intro h n hskip
  exact (h n hskip).trans (halfDyadicCap_le_halfTwoChannelCap (n + 1))

theorem e_G084_G073 : G084 → G073 := fun h => G073_of_hub (hub_of_G084 h)

theorem e_G084_G075 : G084 → G075 := fun h => G075_of_hub (hub_of_G084 h)

theorem e_G084_G076 : G084 → G076 := fun h => G076_of_hub (hub_of_G084 h)

/-! ## Edges out of `G085` -/

theorem e_G085_G073 : G085 → G073 := fun h => G073_of_hub (hub_of_G085 h)

theorem e_G085_G075 : G085 → G075 := fun h => G075_of_hub (hub_of_G085 h)

theorem e_G085_G076 : G085 → G076 := fun h => G076_of_hub (hub_of_G085 h)

/-! ## Collapses

The three weakest entries are pairwise equivalent, and the two strongest are
equivalent to each other. -/

theorem eq_G073_G076 : G073 ↔ G076 := ⟨e_G073_G076, e_G076_G073⟩

theorem eq_G073_G075 : G073 ↔ G075 := ⟨e_G073_G075, e_G075_G073⟩

theorem eq_G075_G076 : G075 ↔ G076 := ⟨e_G075_G076, e_G076_G075⟩

theorem eq_G083_G084 : G083 ↔ G084 := ⟨e_G083_G084, e_G084_G083⟩

end DemandLedger.ClusterE
