import ErdosProblems.Erdos68.PaperCompleteLowKernel
import ErdosProblems.Erdos68.PrimeUnitTranslator
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
The actual convergent full channel residual, not a newly defined surrogate.
Finite corrections are summed only after proving their finite support.
New Lean compilation and axiom checks: UNRUN.
-/
namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
open Finsupp

noncomputable def fullResidualTerm (f : ℕ →₀ ℤ) (d : ℕ) : ℝ :=
  if 1 < d then (channelNumerator f d : ℝ) /
    ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ) else 0

noncomputable def fullResidual (f : ℕ →₀ ℤ) : ℝ :=
  ∑' d : ℕ, fullResidualTerm f d

noncomputable def coordinateMass (z : ℕ →₀ ℤ) : ℤ :=
  integerEvaluation (fun _ => 1) z

noncomputable def tailCoordinateTerm (z : ℕ →₀ ℤ) (d : ℕ) : ℝ :=
  if 1 < d then (z (d - 1) : ℝ) else 0

lemma tailCoordinateTerm_outside (z : ℕ →₀ ℤ) (d : ℕ)
    (hd : d ∉ z.support.image (fun j => j + 1)) : tailCoordinateTerm z d = 0 := by
  classical
  by_cases h : 1 < d
  · have hz : z (d - 1) = 0 := by
      by_contra hn
      apply hd
      exact Finset.mem_image.mpr ⟨d - 1, Finsupp.mem_support_iff.mpr hn, by omega⟩
    simp [tailCoordinateTerm, h, hz]
  · simp [tailCoordinateTerm, h]

lemma summable_tailCoordinateTerm (z : ℕ →₀ ℤ) : Summable (tailCoordinateTerm z) := by
  classical
  apply summable_of_ne_finset_zero (s := z.support.image (fun j => j + 1))
  exact tailCoordinateTerm_outside z

lemma tsum_tailCoordinateTerm {D : ℕ} (hD : 1 ≤ D)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    (∑' d : ℕ, tailCoordinateTerm z d) = (coordinateMass z : ℝ) := by
  classical
  rw [tsum_eq_sum (s := z.support.image (fun j => j + 1))]
  · rw [Finset.sum_image]
    · have he : (∑ j ∈ z.support, tailCoordinateTerm z (j + 1)) =
          ∑ j ∈ z.support, (z j : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjp : 0 < j := by
          by_contra h
          have hj0 : j = 0 := by omega
          subst j
          exact (Finsupp.mem_support_iff.mp hj) (hz 0 (by omega))
        simp [tailCoordinateTerm, show 1 < j + 1 by omega]
      rw [he]
      simp [coordinateMass, integerEvaluation, Finsupp.sum]
    · intro i hi j hj he
      dsimp only at he
      omega
  · exact tailCoordinateTerm_outside z

lemma residual_term_low_kernel {D : ℕ} (hD : 1 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) (d : ℕ) :
    fullResidualTerm (t • canonicalKernel D + channelSynthesis z) d =
      ((t : ℝ) * (channelLCM D : ℝ)) * _root_.Erdos68.factorialGapTailTerm D d +
        tailCoordinateTerm z d := by
  by_cases hd : 1 < d
  · have hd2 : 2 ≤ d := by omega
    rw [fullResidualTerm, if_pos hd, channelNumerator_add, channelNumerator_smul,
      canonicalKernel_channel hd2, synthesis_channel _ _ hd2, hz 0 (by omega),
      zero_add, tailCoordinateTerm, if_pos hd]
    by_cases hdD : d ≤ D
    · have hzj := hz (d - 1) (by omega)
      simp [hdD, hzj, _root_.Erdos68.factorialGapTailTerm, show ¬ D < d by omega]
    · rw [if_neg hdD, _root_.Erdos68.factorialGapTailTerm,
        if_pos (show D < d by omega)]
      have hf : (1 : ℝ) < (d.factorial : ℝ) := by
        exact_mod_cast Nat.one_lt_factorial.mpr hd2
      have hn : (d.factorial : ℝ) - 1 ≠ 0 := by linarith
      push_cast
      field_simp [hn] <;> ring
  · have hn : ¬ D < d := by omega
    simp [fullResidualTerm, hd, _root_.Erdos68.factorialGapTailTerm, hn,
      tailCoordinateTerm]

lemma summable_fullResidual_low_kernel {D : ℕ} (hD : 1 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    Summable (fullResidualTerm (t • canonicalKernel D + channelSynthesis z)) := by
  have h := ((_root_.Erdos68.summable_factorialGapTailTerm D).mul_left
    ((t : ℝ) * (channelLCM D : ℝ))).add (summable_tailCoordinateTerm z)
  exact h.congr (fun d => (residual_term_low_kernel hD t hz d).symm)

/-- Exact residual, including the integral translate and actual infinite tail. -/
theorem fullResidual_low_kernel {D : ℕ} (hD : 1 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) * _root_.Erdos68.factorialGapTail D +
        (coordinateMass z : ℝ) := by
  unfold fullResidual
  simp_rw [residual_term_low_kernel hD t hz]
  rw [((_root_.Erdos68.summable_factorialGapTailTerm D).mul_left
    ((t : ℝ) * (channelLCM D : ℝ))).tsum_add (summable_tailCoordinateTerm z)]
  rw [(_root_.Erdos68.summable_factorialGapTailTerm D).tsum_mul_left,
    tsum_tailCoordinateTerm hD hz]
  rfl

noncomputable def gapPrefixReal (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 D, (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)

/-- The displayed short-note identity R=t L (S-H_D)+sum z_n, literally. -/
theorem residual_transparency {D : ℕ} (hD : 2 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) *
        (_root_.Erdos68.factorialGapSeries - gapPrefixReal D) +
      (coordinateMass z : ℝ) := by
  rw [fullResidual_low_kernel (by omega) t hz]
  have hs := _root_.Erdos68.factorialGapSeries_eq_sum_add_tail hD
  change _root_.Erdos68.factorialGapSeries = gapPrefixReal D +
    _root_.Erdos68.factorialGapTail D at hs
  rw [hs]
  ring

lemma canonicalKernel_one : canonicalKernel 1 = single 1 1 := by
  rw [canonicalKernel_expansion]
  norm_num [channelLCM]

lemma coordinateMass_sub (a b : ℕ →₀ ℤ) :
    coordinateMass (a - b) = coordinateMass a - coordinateMass b := by
  have hn : integerEvaluation (fun _ => 1) (-b) =
      -integerEvaluation (fun _ => 1) b := by
    simpa using integerEvaluation_smul (fun _ => 1) (-1) b
  unfold coordinateMass
  rw [sub_eq_add_neg, integerEvaluation_add, hn, sub_eq_add_neg]

/-- Full synthesis identity; the correction mass excludes the e_1 coordinate. -/
theorem fullResidual_synthesis (a : ℕ →₀ ℤ) :
    fullResidual (channelSynthesis a) =
      (a 0 : ℝ) * _root_.Erdos68.factorialGapSeries +
      ((coordinateMass a - a 0 : ℤ) : ℝ) := by
  let z := a - single 0 (a 0)
  have hz : TailCoordinates 1 z := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simp [z]
  have he : a 0 • canonicalKernel 1 + channelSynthesis z = channelSynthesis a := by
    dsimp [z]
    rw [canonicalKernel_one, channelSynthesis_sub, channelSynthesis_single]
    simp only [channelBasisColumn, if_pos rfl]
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hr := fullResidual_low_kernel (D := 1) (by decide) (a 0) hz
  rw [he] at hr
  have hmass : coordinateMass z = coordinateMass a - a 0 := by
    dsimp [z]
    rw [coordinateMass_sub]
    simp [coordinateMass, integerEvaluation_single]
  simpa [channelLCM, _root_.Erdos68.factorialGapSeries, hmass] using hr

/-- Every paper-domain finite vector has a convergent full residual. -/
theorem summable_fullResidual {f : ℕ →₀ ℤ} (h0 : f 0 = 0) :
    Summable (fullResidualTerm f) := by
  obtain ⟨a, ha, _⟩ := existsUnique_channel_coordinates f h0
  let z := a - single 0 (a 0)
  have hz : TailCoordinates 1 z := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simp [z]
  have he : a 0 • canonicalKernel 1 + channelSynthesis z = f := by
    dsimp [z]
    rw [canonicalKernel_one, channelSynthesis_sub, channelSynthesis_single]
    simp only [channelBasisColumn, if_pos rfl]
    rw [ha]
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  rw [← he]
  exact summable_fullResidual_low_kernel (D := 1) (by decide) (a 0) hz

/-- An actual zero-moment correction contributes an integer, not a new real coordinate. -/
theorem zero_moment_residual_integral {f : ℕ →₀ ℤ}
    (h0 : f 0 = 0) (hm : factorialMoment f = 0) :
    ∃ k : ℤ, fullResidual f = (k : ℝ) := by
  obtain ⟨a, ha, _⟩ := existsUnique_channel_coordinates f h0
  have ha0 : a 0 = 0 := by rw [← synthesis_moment a, ha, hm]
  refine ⟨coordinateMass a, ?_⟩
  rw [← ha, fullResidual_synthesis, ha0]
  simp

/-- Equal moments give equal residual classes modulo the integers. -/
theorem equal_moment_residual_integer_difference {f g : ℕ →₀ ℤ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hm : factorialMoment f = factorialMoment g) :
    ∃ k : ℤ, fullResidual f - fullResidual g = (k : ℝ) := by
  obtain ⟨a, ha, _⟩ := existsUnique_channel_coordinates f hf0
  obtain ⟨b, hb, _⟩ := existsUnique_channel_coordinates g hg0
  have h0 : a 0 = b 0 := by
    rw [← synthesis_moment a, ← synthesis_moment b, ha, hb, hm]
  refine ⟨coordinateMass a - coordinateMass b, ?_⟩
  rw [← ha, ← hb, fullResidual_synthesis, fullResidual_synthesis, h0]
  push_cast
  ring

end ErdosProblems.Erdos68.PaperComplete
