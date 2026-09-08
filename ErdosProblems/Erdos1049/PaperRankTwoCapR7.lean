import ErdosProblems.Erdos1049.BezoutPluckerJets
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

/-!
# R7: the rank-two obstruction inside the degree-budget cap

Uncompiled proof-source candidate. No admitted proofs.

This completes the INTEGER-SEQUENCE part of the cap argument. It does not
silently assume the paper's degree/height/logarithmic limits imply the two
cross-product limits: that analytic transfer remains a coverage obligation.
-/

namespace ErdosProblems.Erdos1049.PaperR7

open Filter
open scoped Topology

/-- Integer discreteness applied to an actual convergent sequence. -/
theorem eventually_int_zero_of_tendsto_zero (D : ℕ → ℤ)
    (hlim : Tendsto (fun n => (D n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, D n = 0 := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim 1 (by norm_num)
  apply eventually_atTop.2
  refine ⟨N, ?_⟩
  intro n hn
  have hs : |(D n : ℝ)| < 1 := by
    simpa only [Real.dist_eq, sub_zero] using hN n hn
  have hsZ : |D n| < (1 : ℤ) := by exact_mod_cast hs
  have hab := abs_nonneg (D n)
  have hz : |D n| = 0 := by omega
  exact abs_eq_zero.mp hz

/-- A nonzero sufficiently small integral form must have nonzero first
coefficient. In particular this does not assume nonvanishing polynomials. -/
theorem eventually_first_coefficient_ne_zero (A B : ℕ → ℤ) (ξ : ℝ)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * ξ - B n ≠ 0)
    (hlim : Tendsto (fun n => (A n : ℝ) * ξ - B n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, A n ≠ 0 := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim 1 (by norm_num)
  have hsmall : ∀ᶠ n in atTop, |(A n : ℝ) * ξ - B n| < 1 := by
    apply eventually_atTop.2
    exact ⟨N, fun n hn => by simpa only [Real.dist_eq, sub_zero] using hN n hn⟩
  filter_upwards [hne, hsmall] with n hn hs
  intro hz
  have hs' : |(B n : ℝ)| < 1 := by simpa [hz] using hs
  have hsZ : |B n| < (1 : ℤ) := by exact_mod_cast hs'
  have hB : B n = 0 := by
    have hab := abs_nonneg (B n)
    apply abs_eq_zero.mp
    omega
  exact hn (by simp [hz, hB])

/-- Nonzero integral forms tending to zero cannot have adjacent determinants
that ALSO tend to zero. This is independent of the particular real target. -/
theorem no_small_forms_with_adjacent_determinants_tending_zero
    (A B : ℕ → ℤ) (ξ : ℝ)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * ξ - B n ≠ 0)
    (hlim : Tendsto (fun n => (A n : ℝ) * ξ - B n) atTop (𝓝 0))
    (hdet : Tendsto (fun n =>
      ((A n * B (n + 1) - A (n + 1) * B n : ℤ) : ℝ)) atTop (𝓝 0)) :
    False := by
  have ha := eventually_first_coefficient_ne_zero A B ξ hne hlim
  have hd := eventually_int_zero_of_tendsto_zero
    (fun n => A n * B (n + 1) - A (n + 1) * B n) hdet
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hne.and (ha.and hd))
  let w : ℕ → ℝ × ℝ := fun i => ((B (N + i) : ℝ), (A (N + i) : ℝ))
  have hunit : ∀ i, IsUnit (w i).2 := by
    intro i
    apply isUnit_iff_ne_zero.mpr
    change (A (N + i) : ℝ) ≠ 0
    exact_mod_cast (hN (N + i) (by omega)).2.1
  have hadj : ∀ i,
      (w i).1 * (w (i + 1)).2 - (w i).2 * (w (i + 1)).1 = 0 := by
    intro i
    have hi := (hN (N + i) (by omega)).2.2
    have hiR : (A (N + i) : ℝ) * B (N + i + 1) -
        (A (N + i + 1) : ℝ) * B (N + i) = 0 := by exact_mod_cast hi
    change (B (N + i) : ℝ) * A (N + (i + 1)) -
      (A (N + i) : ℝ) * B (N + (i + 1)) = 0
    simp only [Nat.add_assoc] at hiR ⊢
    nlinarith
  have hall := BezoutPluckerJets.adjacent_det_zero_forces_all_det_zero w hunit hadj
  have hAN : (A N : ℝ) ≠ 0 := by exact_mod_cast (hN N le_rfl).2.1
  let η : ℝ := ξ - (B N : ℝ) / (A N : ℝ)
  have herr : ∀ i,
      (A (N + i) : ℝ) * ξ - B (N + i) = (A (N + i) : ℝ) * η := by
    intro i
    have hrel := hall 0 i
    change (B (N + 0) : ℝ) * A (N + i) -
      (A (N + 0) : ℝ) * B (N + i) = 0 at hrel
    simp only [Nat.add_zero] at hrel
    have hB : (B (N + i) : ℝ) = (A (N + i) : ℝ) * (B N : ℝ) / (A N : ℝ) := by
      apply (eq_div_iff hAN).2
      nlinarith
    change (A (N + i) : ℝ) * ξ - B (N + i) =
      (A (N + i) : ℝ) * (ξ - (B N : ℝ) / (A N : ℝ))
    rw [hB]
    ring
  have hη : η ≠ 0 := by
    intro hz
    have he := herr 0
    simp only [Nat.add_zero, hz, mul_zero] at he
    exact (hN N le_rfl).1 he
  have hbound : ∀ i, |η| ≤ |(A (N + i) : ℝ) * ξ - B (N + i)| := by
    intro i
    have hz : A (N + i) ≠ 0 := (hN (N + i) (by omega)).2.1
    have hZ : (1 : ℤ) ≤ |A (N + i)| := Int.one_le_abs hz
    have hR : (1 : ℝ) ≤ |(A (N + i) : ℝ)| := by exact_mod_cast hZ
    rw [herr i, abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hR (abs_nonneg η)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hlim |η| (abs_pos.mpr hη)
  have hs : |(A (N + M) : ℝ) * ξ - B (N + M)| < |η| := by
    simpa only [Real.dist_eq, sub_zero] using hM (N + M) (by omega)
  exact (not_lt_of_ge (hbound M)) hs

/-- These are the two cross-product limits produced by the super-decay
branch of the paper's coefficient-height argument. The conclusion uses no
external irrationality theorem at an integer base. -/
theorem no_small_forms_of_cross_product_limits
    (A B : ℕ → ℤ) (ξ : ℝ)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * ξ - B n ≠ 0)
    (hlim : Tendsto (fun n => (A n : ℝ) * ξ - B n) atTop (𝓝 0))
    (hleft : Tendsto (fun n => (A n : ℝ) *
      ((A (n + 1) : ℝ) * ξ - B (n + 1))) atTop (𝓝 0))
    (hright : Tendsto (fun n => (A (n + 1) : ℝ) *
      ((A n : ℝ) * ξ - B n)) atTop (𝓝 0)) :
    False := by
  apply no_small_forms_with_adjacent_determinants_tending_zero A B ξ hne hlim
  have ht := hright.sub hleft
  have hid : (fun n => (A (n + 1) : ℝ) * ((A n : ℝ) * ξ - B n) -
      (A n : ℝ) * ((A (n + 1) : ℝ) * ξ - B (n + 1))) =
      (fun n => ((A n * B (n + 1) - A (n + 1) * B n : ℤ) : ℝ)) := by
    funext n
    push_cast
    ring
  rw [hid] at ht
  simpa only [sub_zero] using ht

/-- The arithmetic translation of the sufficient homogenisation region. -/
theorem logarithmic_region_iff_negative_balance
    (a b σ δ : ℝ) (ha : 1 < a) (hb : 0 < b) (hσ : 0 < σ) (hδ : 0 < δ) :
    Real.log b / Real.log a < σ / (σ + δ) ↔
      δ * Real.log b - σ * Real.log (a / b) < 0 := by
  have hlog : 0 < Real.log a := Real.log_pos ha
  have hsum : 0 < σ + δ := by linarith
  rw [div_lt_div_iff₀ hlog hsum,
    Real.log_div (ne_of_gt (by linarith : (0:ℝ) < a)) hb.ne']
  constructor <;> intro h <;> nlinarith

/-- Final numerical clause of either cap once σ ≤ δ has been established. -/
theorem half_cap_iff (σ δ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) :
    σ / (σ + δ) ≤ 1 / 2 ↔ σ ≤ δ := by
  rw [div_le_iff₀ (show 0 < σ + δ by linarith)]
  constructor <;> intro h <;> nlinarith

end ErdosProblems.Erdos1049.PaperR7
