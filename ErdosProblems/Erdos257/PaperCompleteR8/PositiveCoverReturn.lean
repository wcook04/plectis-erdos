import Mathlib.Analysis.Normed.Group.Tannery
import ErdosProblems.Erdos257.PaperCompleteR8.CoverPotentialBounds
import ErdosProblems.Erdos257.PaperCompleteR8.CommonScale

/-!
# End-to-end strengthened positive-cover theorem

UNCOMPILED, but no new Prop target or unproved bridge is a hypothesis of the
final theorem. Input is exactly the desk PositiveCoverData and its one-inverse-
power cost. Finite prefixes, the actual host, the potential comparison,
summability, one common finite observation mean, and all-base heredity are
assembled here. This module does not assert the weighted or mixed producer.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset Filter Set
open Erdos249257
open ErdosProblems.Erdos257.PaperCompleteR7

/-- Finite union of the first J cover frames, with a structural recursion. -/
def coverPrefix (C : PositiveCoverData) : ℕ → Finset ℕ
  | 0 => ∅
  | J + 1 => coverPrefix C J ∪ C.frame J

theorem mem_coverPrefix_iff (C : PositiveCoverData) (J d : ℕ) :
    d ∈ coverPrefix C J ↔ ∃ j < J, d ∈ C.frame j := by
  induction J with
  | zero => simp only [coverPrefix, Finset.notMem_empty, Nat.not_lt_zero, false_and, exists_false]
  | succ J ih =>
    rw [coverPrefix, Finset.mem_union, ih]
    constructor
    · rintro (⟨j, hj, hd⟩ | hd)
      · exact ⟨j, Nat.lt_trans hj (Nat.lt_succ_self J), hd⟩
      · exact ⟨J, Nat.lt_succ_self J, hd⟩
    · rintro ⟨j, hj, hd⟩
      rcases (show j < J ∨ j = J by omega) with hlt | heq
      · exact Or.inl ⟨j, hlt, hd⟩
      · exact Or.inr (heq ▸ hd)

theorem coverPrefix_subset_host (C : PositiveCoverData) (J : ℕ) :
    (coverPrefix C J : Set ℕ) ⊆ C.host := by
  intro d hd
  obtain ⟨j, _, hj⟩ := (mem_coverPrefix_iff C J d).mp hd
  exact ⟨j, hj⟩

theorem zero_not_mem_coverPrefix (C : PositiveCoverData) (J : ℕ) :
    0 ∉ coverPrefix C J := by
  intro h
  obtain ⟨j, _, hj⟩ := (mem_coverPrefix_iff C J 0).mp h
  exact C.frame_positive j hj

/-- A completely explicit common multiple exists and is positive. -/
theorem coverPrefix_common_multiple (C : PositiveCoverData) (J : ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∀ d ∈ coverPrefix C J, d ∣ L := by
  let L := (coverPrefix C J).prod id
  have hL : 0 < L := by
    apply Finset.prod_pos
    intro d hd
    exact Nat.pos_of_ne_zero (fun h => zero_not_mem_coverPrefix C J (h ▸ hd))
  refine ⟨L, hL, ?_⟩
  intro d hd
  -- Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean: dvd_prod_of_mem.
  exact Finset.dvd_prod_of_mem id hd

/-- Increasing the finite frame prefix recovers the ACTUAL host displacement.
The dominating series is the existing host displacement, not reciprocal mass. -/
theorem tendsto_displacement_coverPrefix (C : PositiveCoverData) (N : ℕ) :
    Tendsto (fun J => displacement 2 (coverPrefix C J : Set ℕ) N)
      atTop (nhds (displacement 2 C.host N)) := by
  classical
  let v : ℕ → ℕ → ℝ := fun J d =>
    Set.indicator (coverPrefix C J : Set ℕ) (displacementAtom 2 N) d
  let a : ℕ → ℝ := Set.indicator C.host (displacementAtom 2 N)
  have ha : Summable a := summable_displacementAtom 2 C.host N (by norm_num)
  have ht : ∀ d, Tendsto (fun J => v J d) atTop (nhds (a d)) := by
    intro d
    by_cases hd : d ∈ C.host
    · obtain ⟨j, hj⟩ := hd
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop j] with J hJ
      have hp : d ∈ (coverPrefix C J : Set ℕ) :=
        (mem_coverPrefix_iff C J d).mpr ⟨j, hJ, hj⟩
      have hh : d ∈ C.host := ⟨j, hj⟩
      simp only [v, a, Set.indicator_of_mem hp, Set.indicator_of_mem hh]
    · have hv : ∀ J, v J d = 0 := by
        intro J
        have hp : d ∉ (coverPrefix C J : Set ℕ) :=
          fun h => hd (coverPrefix_subset_host C J h)
        simp [v, hp]
      have ha0 : a d = 0 := by simp [a, hd]
      simp only [hv, ha0]
      exact tendsto_const_nhds
  have hb : ∀ J d, ‖v J d‖ ≤ a d := by
    intro J d
    have hnn := displacementAtom_nonneg 2 N d (by norm_num)
    by_cases hp : d ∈ (coverPrefix C J : Set ℕ)
    · have hh := coverPrefix_subset_host C J hp
      simp only [v, a, Set.indicator_of_mem hp, Set.indicator_of_mem hh,
        Real.norm_eq_abs, abs_of_nonneg hnn, le_refl]
    · have ha0 : 0 ≤ a d := Set.indicator_nonneg (fun d _ =>
        displacementAtom_nonneg 2 N d (by norm_num)) d
      simpa [v, hp] using ha0
  -- Mathlib/Analysis/Normed/Group/Tannery.lean:
  -- tendsto_tsum_of_dominated_convergence (also used in the desk library).
  have hlim := tendsto_tsum_of_dominated_convergence ha ht
    (Filter.Eventually.of_forall hb)
  have hl : (fun J => ∑' d, v J d) =
      (fun J => displacement 2 (coverPrefix C J : Set ℕ) N) := by
    funext J
    exact (displacement_eq_tsum 2 (coverPrefix C J : Set ℕ) N (by norm_num)).symm
  have hr : (∑' d, a d) = displacement 2 C.host N :=
    (displacement_eq_tsum 2 C.host N (by norm_num)).symm
  rw [hl, hr] at hlim
  exact hlim

/-- Bound each enlarged prefix after the first J frames have vanished. -/
theorem displacement_coverPrefix_le_tail_sum (C : PositiveCoverData) (J N : ℕ)
    (hzero : displacement 2 (coverPrefix C J : Set ℕ) N = 0) (k : ℕ) :
    displacement 2 (coverPrefix C (J + k) : Set ℕ) N ≤
      ∑ i ∈ Finset.range k, framePotential (C.frame (i + J)) N := by
  induction k with
  | zero => simp only [Nat.add_zero, Finset.range_zero, Finset.sum_empty, hzero, le_refl]
  | succ k ih =>
    have hp : coverPrefix C (J + (k + 1)) =
        coverPrefix C (J + k) ∪ C.frame (k + J) := by
      rw [show J + (k + 1) = (J + k) + 1 by omega, coverPrefix]
      rw [show C.frame (J + k) = C.frame (k + J) from
        congrArg C.frame (Nat.add_comm J k)]
    rw [hp, Finset.coe_union, Finset.sum_range_succ]
    have hu := displacement_union_le 2 (coverPrefix C (J + k) : Set ℕ)
      (C.frame (k + J) : Set ℕ) N (by norm_num)
    have hf := displacement_finset_le_framePotential (C.frame (k + J)) N
    linarith only [hu, hf, ih]

/-- The passage to the entire host uses a proved dominated limit and a
summable potential tail. Overlapping frames are allowed. -/
theorem displacement_host_le_tsum_tail (C : PositiveCoverData) (J N : ℕ)
    (hzero : displacement 2 (coverPrefix C J : Set ℕ) N = 0)
    (hs : Summable (fun k => framePotential (C.frame (k + J)) N)) :
    displacement 2 C.host N ≤ ∑' k, framePotential (C.frame (k + J)) N := by
  apply le_of_tendsto (tendsto_displacement_coverPrefix C N)
  filter_upwards [eventually_ge_atTop J] with K hK
  have hb := displacement_coverPrefix_le_tail_sum C J N hzero (K - J)
  have heq : J + (K - J) = K := by omega
  rw [heq] at hb
  exact hb.trans (hs.sum_le_tsum (Finset.range (K - J))
    (fun k _ => framePotential_nonneg (C.frame (k + J)) N))

/-- Passing a countable tail test bounds every frame's potential, with the
actual fractional exponent and threshold. -/
theorem framePotential_lt_threshold_of_tailTest (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) {ε : ℝ} (hε : 0 < ε)
    (J N : ℕ) (hsmall : coverTailTest C ε J N < 1) (k : ℕ) :
    framePotential (C.frame (k + J)) N < coverThreshold ε (k + J) := by
  have hs := summable_coverTailTest_terms C hC hε J N
  have hterm : coverScale C ε (k + J) * coverPotential C (k + J) N ≤
      coverTailTest C ε J N := hs.le_tsum k (fun i _ =>
        mul_nonneg (coverScale_pos C hε (i + J)).le (coverPotential_nonneg C (i + J) N))
  have hbridge := positiveCover_frame_bridge C (k + J) N
  have hscale := coverScale_pos C hε (k + J)
  have hp : coverScale C ε (k + J) * framePotential (C.frame (k + J)) N ^ C.exponent (k + J) < 1 :=
    (mul_le_mul_of_nonneg_left hbridge hscale.le).trans_lt (hterm.trans_lt hsmall)
  have ht : 0 < coverThreshold ε (k + J) := coverThreshold_pos hε (k + J)
  have hone : coverScale C ε (k + J) *
      coverThreshold ε (k + J) ^ C.exponent (k + J) = 1 := by
    unfold coverScale
    rw [Real.rpow_neg ht.le]
    exact inv_mul_cancel₀ (Real.rpow_pos_of_pos ht _).ne'
  by_contra hbad
  have hge : coverThreshold ε (k + J) ≤ framePotential (C.frame (k + J)) N := le_of_not_gt hbad
  have hpow := Real.rpow_le_rpow ht.le hge (C.exponent_bounds (k + J)).1.le
  have hmult := mul_le_mul_of_nonneg_left hpow hscale.le
  rw [hone] at hmult
  exact (not_lt_of_ge hmult) hp

/-- A good sample gives a bound for the WHOLE actual host. -/
theorem displacement_host_le_of_coverTailTest (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) {ε : ℝ} (hε : 0 < ε)
    (J N : ℕ) (hdiv : ∀ d ∈ coverPrefix C J, d ∣ N)
    (hsmall : coverTailTest C ε J N < 1) : displacement 2 C.host N ≤ ε := by
  have hbound := framePotential_lt_threshold_of_tailTest C hC hε J N hsmall
  have ht : Summable (fun k => coverThreshold ε (k + J)) :=
    (summable_nat_add_iff J).mpr (summable_coverThreshold ε)
  have hu : Summable (fun k => framePotential (C.frame (k + J)) N) :=
    Summable.of_nonneg_of_le
      (fun k => framePotential_nonneg (C.frame (k + J)) N)
      (fun k => (hbound k).le) ht
  have hzero := displacement_finset_eq_zero 2 (coverPrefix C J) N (by norm_num) hdiv
  have hsum := Summable.tsum_le_tsum (fun k => (hbound k).le) hu ht
  have hsplit := (summable_coverThreshold ε).sum_add_tsum_nat_add J
  rw [tsum_coverThreshold] at hsplit
  have hpre : 0 ≤ ∑ k ∈ Finset.range J, coverThreshold ε k :=
    Finset.sum_nonneg (fun k _ => (coverThreshold_pos hε k).le)
  have htail : (∑' k, coverThreshold ε (k + J)) ≤ ε := by
    linarith only [hsplit, hpre]
  exact (displacement_host_le_tsum_tail C J N hzero hu).trans (hsum.trans htail)

/-- Choose the finite prefix before selecting the common sampling modulus. -/
theorem exists_coverScaledCost_tail_lt (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ J : ℕ, (∑' k, coverScaledCost C ε (k + J)) < δ := by
  have ht := tendsto_sum_nat_add (coverScaledCost C ε)
  -- Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean: tendsto_sum_nat_add.
  -- Mathlib/Topology/Order/Basic.lean: gt_mem_nhds.
  have he : ∀ᶠ J : ℕ in atTop, (∑' k, coverScaledCost C ε (k + J)) < δ :=
    ht.eventually (gt_mem_nhds hδ)
  exact he.exists

/-- Positive covers produce actual small displacements. The sole analytic
input (S) is a theorem candidate, not a hypothesis of this declaration. -/
theorem positiveCover_binary_returns (C : PositiveCoverData)
    (hC : C.StrengthenedCostSummable) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ displacement 2 C.host N < ε := by
  intro ε hε
  let ρ := ε / 2
  have hρ : 0 < ρ := div_pos hε (by norm_num)
  obtain ⟨J, hJ⟩ := exists_coverScaledCost_tail_lt C hC hρ (by norm_num : (0 : ℝ) < 1/4)
  obtain ⟨L, hL, hdiv⟩ := coverPrefix_common_multiple C J
  let M := 4 * L
  have hM : 0 < M := Nat.mul_pos (by decide) hL
  have hK : 1 + 4 * (L : ℝ) / M ≤ 2 := one_add_four_ratio_le_two L M hM le_rfl
  have hcost0 : 0 ≤ ∑' k, coverScaledCost C ρ (k + J) :=
    tsum_nonneg (fun k => coverScaledCost_nonneg C hρ (k + J))
  have hbound := dyadicMean_coverTailTest_le C hC hρ J L 0 M hL hM
  have hprod := mul_le_mul_of_nonneg_right hK hcost0
  have hmean : dyadicMean L 0 M (coverTailTest C ρ J) < 1 := by
    nlinarith only [hbound, hprod, hJ]
  obtain ⟨j, m, _, _, _, hsample⟩ :=
    exists_sample_lt_of_dyadicMean_lt L 0 M hM (coverTailTest C ρ J) 1 hmean
  let N := (m + 1) * L
  have hN : 0 < N := Nat.mul_pos (Nat.succ_pos m) hL
  have hLN : L ∣ N := ⟨m + 1, by dsimp [N]; ring⟩
  have hdN : ∀ d ∈ coverPrefix C J, d ∣ N := fun d hd => (hdiv d hd).trans hLN
  have hret := displacement_host_le_of_coverTailTest C hC hρ J N hdN hsample
  refine ⟨N, hN, ?_⟩
  dsimp [ρ] at hret
  linarith only [hret, hε]

/-- FULL short-note `thm:variable-fractional-cover`, including all bases and
all infinite thinnings. Candidate proof text; no local compilation claimed. -/
theorem strengthenedPositiveCoverClaim : StrengthenedPositiveCoverClaim := by
  intro C hC
  exact all_base_hereditary_of_binary_returns C.host (positiveCover_binary_returns C hC)

end ErdosProblems.Erdos257.PaperCompleteR8
end
