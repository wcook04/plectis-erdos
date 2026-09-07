import Erdos257PeriodNoncollapse.AllBaseReciprocalSupportIrrationality
import ErdosProblems.Erdos257.BatchReturnSynthesis

/-!
# Infinite displacement and the exact arithmetic consumer

Uncompiled R7 proof candidates against the supplied Lean 4.29.1 tree.
Unlike the already supplied finite rational tail-budget draft, this file
uses the actual infinite real support series. All summability hypotheses
needed to interchange infinite sums are proved from the existing library.

The arithmetic endgame reuses BatchReturnSynthesis's existing general
close-return consumer, translated into displacement notation. No reciprocal-
summability hypothesis is added or removed from that consumer. The ordinary
positive-cover and mixed-support arguments must still establish its analytic
input. No admission, new axiom, or parent claim is used.
-/

noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR7

open Erdos257PeriodNoncollapse Filter Set

/-- Pointwise nonnegative displacement, with the existing zero-index convention. -/
def displacementAtom (b N d : ℕ) : ℝ :=
  shiftedRadixAtom b N d - shiftedRadixAtom b 0 d

/-- The actual infinite support displacement, not a free abstract error stream. -/
def displacement (b : ℕ) (A : Set ℕ) (N : ℕ) : ℝ :=
  (∑' d : ℕ, shiftedRadixSupportAtom b A N d) - erdosSupportSeries b A

theorem displacementAtom_nonneg (b N d : ℕ) (hb : 2 ≤ b) :
    0 ≤ displacementAtom b N d := by
  exact sub_nonneg.mpr (shiftedRadixAtom_zero_le b N d hb)

/-- Infinite sums of displacement atoms are absolutely summable. -/
theorem summable_displacementAtom (b : ℕ) (A : Set ℕ) (N : ℕ) (hb : 2 ≤ b) :
    Summable (Set.indicator A (displacementAtom b N)) := by
  have hs := (summable_shiftedRadixSupportAtom b A N hb).sub
    (summable_shiftedRadixSupportAtom b A 0 hb)
  apply hs.congr
  intro d
  classical
  by_cases hd : d ∈ A <;>
    simp [shiftedRadixSupportAtom, displacementAtom, hd]

theorem displacement_eq_tsum (b : ℕ) (A : Set ℕ) (N : ℕ) (hb : 2 ≤ b) :
    displacement b A N = ∑' d : ℕ, Set.indicator A (displacementAtom b N) d := by
  rw [displacement, ← tsum_shiftedRadixSupportAtom_zero b A]
  rw [← (summable_shiftedRadixSupportAtom b A N hb).tsum_sub
    (summable_shiftedRadixSupportAtom b A 0 hb)]
  apply tsum_congr
  intro d
  classical
  by_cases hd : d ∈ A <;>
    simp [shiftedRadixSupportAtom, displacementAtom, hd]

theorem displacement_nonneg (b : ℕ) (A : Set ℕ) (N : ℕ) (hb : 2 ≤ b) :
    0 ≤ displacement b A N := by
  rw [displacement_eq_tsum b A N hb]
  exact tsum_nonneg fun d =>
    Set.indicator_nonneg (fun d _ => displacementAtom_nonneg b N d hb) d

theorem displacement_pos (b : ℕ) (A : Set ℕ) (N : ℕ)
    (hb : 2 ≤ b) (hA : A.Infinite) (hN : 0 < N) :
    0 < displacement b A N := by
  have h := shiftedRadixSupportAtom_zero_strictMinimum b A hb hA N hN
  rw [tsum_shiftedRadixSupportAtom_zero] at h
  exact sub_pos.mpr h

/-- Hereditary control follows from positivity of actual displacement atoms. -/
theorem displacement_mono (b : ℕ) (A B : Set ℕ) (N : ℕ)
    (hb : 2 ≤ b) (hAB : A ⊆ B) :
    displacement b A N ≤ displacement b B N := by
  rw [displacement_eq_tsum b A N hb, displacement_eq_tsum b B N hb]
  apply Summable.tsum_le_tsum _
    (summable_displacementAtom b A N hb) (summable_displacementAtom b B N hb)
  intro d
  classical
  by_cases hA : d ∈ A
  · have hB := hAB hA
    simp [hA, hB]
  · by_cases hB : d ∈ B
    · simpa [hA, hB] using displacementAtom_nonneg b N d hb
    · simp [hA, hB]

/-- Exact disjoint decomposition; this is not an irrationality claim about sums. -/
theorem displacement_partition (b : ℕ) (A B : Set ℕ) (N : ℕ)
    (hb : 2 ≤ b) (hBA : B ⊆ A) :
    displacement b A N = displacement b B N + displacement b (A \ B) N := by
  rw [displacement_eq_tsum b A N hb, displacement_eq_tsum b B N hb,
    displacement_eq_tsum b (A \ B) N hb,
    ← (summable_displacementAtom b B N hb).tsum_add
      (summable_displacementAtom b (A \ B) N hb)]
  apply tsum_congr
  intro d
  classical
  by_cases hB : d ∈ B
  · have hA := hBA hB
    simp [hA, hB]
  · by_cases hA : d ∈ A <;> simp [hA, hB]

/-- Union subadditivity without a disjointness hypothesis. -/
theorem displacement_union_le (b : ℕ) (A B : Set ℕ) (N : ℕ) (hb : 2 ≤ b) :
    displacement b (A ∪ B) N ≤ displacement b A N + displacement b B N := by
  have heq := displacement_partition b (A ∪ B) A N hb Set.subset_union_left
  have hsub : ((A ∪ B) \ A) ⊆ B := by
    intro d hd
    rcases hd.1 with hA | hB
    · exact False.elim (hd.2 hA)
    · exact hB
  have hmono := displacement_mono b ((A ∪ B) \ A) B N hb hsub
  linarith

/-- A finite prefix is annihilated at any common multiple. -/
theorem displacement_finset_eq_zero (b : ℕ) (F : Finset ℕ) (N : ℕ)
    (hb : 2 ≤ b) (hdiv : ∀ d ∈ F, d ∣ N) :
    displacement b (↑F : Set ℕ) N = 0 := by
  classical
  rw [displacement_eq_tsum b (↑F : Set ℕ) N hb]
  have hzero : (fun d => Set.indicator (↑F : Set ℕ) (displacementAtom b N) d)
      = fun _ : ℕ => (0 : ℝ) := by
    funext d
    by_cases hd : d ∈ F
    · have hmod := Nat.mod_eq_zero_of_dvd (hdiv d hd)
      simp [hd, displacementAtom, shiftedRadixAtom, hmod]
    · simp [hd]
  rw [hzero, tsum_zero]

/-- Every atom is bounded by amplified initial mass, even if it has wrapped. -/
theorem displacementAtom_le_amplified (b N d : ℕ) (hb : 2 ≤ b) :
    displacementAtom b N d ≤
      ((b : ℝ) ^ N - 1) * (1 / ((b : ℝ) ^ d - 1)) := by
  have h := shiftedRadixAtom_le_pow_mul_zero b N d hb
  rw [displacementAtom, shiftedRadixAtom_zero]
  nlinarith

/-- The infinite residual-mass budget, extending the supplied finite draft. -/
theorem displacement_le_amplified_mass (b : ℕ) (A : Set ℕ) (N : ℕ)
    (hb : 2 ≤ b) :
    displacement b A N ≤ ((b : ℝ) ^ N - 1) * erdosSupportSeries b A := by
  have hs := summable_erdosSupport_indicator b A hb
  rw [displacement_eq_tsum b A N hb, erdosSupportSeries, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    (summable_displacementAtom b A N hb) (hs.mul_left _)
  intro d
  classical
  by_cases hd : d ∈ A
  · simpa [hd] using displacementAtom_le_amplified b N d hb
  · simp [hd]

/-- Exact future-tail identity. The no-wrap hypothesis is stated for every
selected exponent and is not hidden in a free error term. -/
theorem displacement_future_eq (b : ℕ) (A : Set ℕ) (N : ℕ)
    (hb : 2 ≤ b) (hfuture : ∀ d ∈ A, N < d) :
    displacement b A N = ((b : ℝ) ^ N - 1) * erdosSupportSeries b A := by
  rw [displacement_eq_tsum b A N hb, erdosSupportSeries, ← tsum_mul_left]
  apply tsum_congr
  intro d
  classical
  by_cases hd : d ∈ A
  · have hNd := hfuture d hd
    have hd0 : d ≠ 0 := by omega
    simp only [Set.indicator_of_mem hd, displacementAtom,
      shiftedRadixAtom, if_neg hd0, Nat.mod_eq_of_lt hNd,
      Nat.zero_mod, pow_zero]
    ring
  · simp [hd]

/-- R6 amplified-tail inequality, now for the actual infinite series. -/
theorem displacement_residual_budget (b : ℕ) (A B : Set ℕ) (N : ℕ)
    (hb : 2 ≤ b) (hBA : B ⊆ A) :
    displacement b A N ≤ displacement b B N +
      ((b : ℝ) ^ N - 1) * erdosSupportSeries b (A \ B) := by
  rw [displacement_partition b A B N hb hBA]
  have h := displacement_le_amplified_mass b (A \ B) N hb
  linarith

/-- The packet's pointwise radix comparison, lifted to infinite supports. -/
theorem displacement_le_two_mul_binary (b : ℕ) (A : Set ℕ) (N : ℕ)
    (hb : 2 ≤ b) : displacement b A N ≤ 2 * displacement 2 A N := by
  have hrN := summable_shiftedRadixSupportAtom b A N hb
  have hr0 := summable_shiftedRadixSupportAtom b A 0 hb
  have hbinN := summable_shiftedSupportAtom A N
  have hbin0 := summable_shiftedSupportAtom A 0
  have hsumle := Summable.tsum_le_tsum
    (fun d => shiftedRadixSupportAtom_sub_zero_le_two_mul_binary_sub_zero b A N d hb)
    (hrN.sub hr0) ((hbinN.sub hbin0).mul_left 2)
  rw [hrN.tsum_sub hr0, (hbinN.sub hbin0).tsum_mul_left,
    hbinN.tsum_sub hbin0, tsum_shiftedRadixSupportAtom_zero] at hsumle
  have heq : ∀ K, (∑' d, shiftedRadixSupportAtom 2 A K d) =
      ∑' d, shiftedSupportAtom A K d := by
    intro K
    apply tsum_congr
    intro d
    classical
    by_cases hd : d ∈ A <;>
      simp [shiftedRadixSupportAtom, shiftedSupportAtom,
        shiftedRadixAtom, shiftedMersenneAtom, hd]
  have heq0 := heq 0
  rw [tsum_shiftedRadixSupportAtom_zero] at heq0
  simpa only [displacement, heq N, heq0] using hsumle

/-- General arithmetic consumer. The analytic input is *exactly* arbitrarily
small positive-time displacements; no summable-reciprocal assumption remains. -/
theorem irrational_of_displacement_returns (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (hA : A.Infinite)
    (hreturn : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ displacement b A N < ε) :
    Irrational (erdosSupportSeries b A) := by
  apply irrational_erdosSupportSeries_of_radix_closeReturn b A hb hA
  intro ε hε
  obtain ⟨N, hN, hsmall⟩ := hreturn ε hε
  refine ⟨N, hN, ?_⟩
  rw [tsum_shiftedRadixSupportAtom_zero]
  unfold displacement at hsmall
  linarith

/-- Exact all-base hereditary consumer for both short-note analytic producers. -/
theorem all_base_hereditary_of_binary_returns (H : Set ℕ)
    (hreturn : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, 0 < N ∧ displacement 2 H N < ε) :
    ∀ (A : Set ℕ), A ⊆ H → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A) := by
  intro A hAH hA b hb
  apply irrational_of_displacement_returns b A hb hA
  intro ε hε
  obtain ⟨N, hN, hsmall⟩ := hreturn (ε / 2) (by linarith)
  refine ⟨N, hN, ?_⟩
  have hbnd := displacement_le_two_mul_binary b A N hb
  have hmono := displacement_mono 2 A H N (by norm_num) hAH
  linarith

end ErdosProblems.Erdos257.PaperCompleteR7

end
