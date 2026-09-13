import ErdosProblems.Erdos68.PaperCompleteRadiusLimit
import Mathlib.Data.EReal.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Literal liminf statements, without silently assuming finite liminf values

The displayed asymptotic theorems allow the value +infinity. The wrappers use
EReal for the liminf and prove equivalence with the epsilon/eventual assertions
in the main proof files. Thus no unproved upper-boundedness assumption is
introduced merely to fit a real-valued liminf API.
STATUS: uncompiled proof candidates, like their imported new proofs.
-/
namespace ErdosProblems.Erdos68.PaperComplete

open Filter
open scoped Topology

lemma lowerLimitAtLeast_iff_ereal (f : ℕ → ℝ) (c : ℝ) :
    LowerLimitAtLeast f c ↔
      (c : EReal) ≤ Filter.liminf (fun n : ℕ => (f n : EReal)) atTop := by
  rw [Filter.le_liminf_iff]
  constructor
  · intro h a ha
    cases a using EReal.rec with
    | bot => exact Eventually.of_forall (fun _ => by simp)
    | coe a =>
      have haa : a < c := by exact_mod_cast ha
      simpa only [EReal.coe_lt_coe_iff] using h a haa
    | top => simp at ha
  · intro h a ha
    have he := h (a : EReal) (by exact_mod_cast ha)
    simpa only [EReal.coe_lt_coe_iff] using he

lemma three_halves_power {x : ℝ} (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
    Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Literal displayed res:lcm-growth, including the real exponent 3/2. -/
theorem common_denominator_growth_liminf :
    ((2 * Real.sqrt 2 / 3 : ℝ) : EReal) ≤
      Filter.liminf (fun N : ℕ =>
        ((Real.log (_root_.Erdos68.channelLCM N : ℝ) /
          ((N : ℝ) ^ ((3 : ℝ) / 2) * Real.log (N : ℝ)) : ℝ) : EReal)) atTop := by
  apply (lowerLimitAtLeast_iff_ereal _ _).mp
  intro a ha
  filter_upwards [common_denominator_growth a ha, eventually_ge_atTop 1] with N hN hpos
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rwa [three_halves_power hn]

/-- Literal displayed res:radius-constant, with the paper's eventual hypotheses. -/
theorem asymptotic_radius_constant_liminf (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ _root_.Erdos68.channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    (((16 : ℝ) / 9) : EReal) ≤
      Filter.liminf (fun t : ℕ =>
        ((((R t + 1 : ℕ) : ℝ) / (t : ℝ) ^ 3 : ℝ) : EReal)) atTop := by
  apply (lowerLimitAtLeast_iff_ereal _ _).mp
  exact asymptotic_radius_constant M R (eventually_atTop.mpr hH)

end ErdosProblems.Erdos68.PaperComplete
