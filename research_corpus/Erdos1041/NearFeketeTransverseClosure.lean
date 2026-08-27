import Mathlib

/-!
# Erdős #1041: the asymptotic sign-transfer kernel

The analytic companion proves that, on every transverse cone at the regular
polygon, the length deficit divided by the cusp scale tends to a strictly
positive number.  This file formalizes the last order-theoretic step: a
positive scaled limit and a positive scale force an eventually positive
deficit, hence an eventually strict length bound.

No complex-analytic branch-convergence claim is encoded here.
-/

open Filter Topology

namespace ErdosProblems.Erdos1041

/-- A positive limit for a deficit divided by a positive vanishing scale
eventually makes the unscaled deficit positive. -/
theorem eventually_pos_of_scaled_deficit_tendsto_pos
    {α : Type*} {l : Filter α} [NeBot l]
    (deficit scale : α → ℝ) (κ : ℝ)
    (hscale : ∀ᶠ x in l, 0 < scale x)
    (hlim : Tendsto (fun x => deficit x / scale x) l (𝓝 κ))
    (hκ : 0 < κ) :
    ∀ᶠ x in l, 0 < deficit x := by
  filter_upwards [hscale, hlim.eventually_const_lt hκ] with x hxscale hxratio
  exact (div_pos_iff_of_pos_right hxscale).mp hxratio

/-- The form used by the near-Fekete application: if
`(2 * radius - length) / scale` tends to a positive constant, then the
constructed path is eventually shorter than the comparison diameter. -/
theorem eventually_length_lt_twice_radius
    {α : Type*} {l : Filter α} [NeBot l]
    (length radius scale : α → ℝ) (κ : ℝ)
    (hscale : ∀ᶠ x in l, 0 < scale x)
    (hlim : Tendsto (fun x => (2 * radius x - length x) / scale x) l (𝓝 κ))
    (hκ : 0 < κ) :
    ∀ᶠ x in l, length x < 2 * radius x := by
  have hpos : ∀ᶠ x in l, 0 < 2 * radius x - length x :=
    eventually_pos_of_scaled_deficit_tendsto_pos
      (fun x => 2 * radius x - length x) scale κ hscale hlim hκ
  filter_upwards [hpos] with x hx
  linarith

/-- If the comparison radius is eventually strictly below one, the same
asymptotic deficit yields the strict constant-two conclusion. -/
theorem eventually_length_lt_two
    {α : Type*} {l : Filter α} [NeBot l]
    (length radius scale : α → ℝ) (κ : ℝ)
    (hscale : ∀ᶠ x in l, 0 < scale x)
    (hradius : ∀ᶠ x in l, radius x < 1)
    (hlim : Tendsto (fun x => (2 * radius x - length x) / scale x) l (𝓝 κ))
    (hκ : 0 < κ) :
    ∀ᶠ x in l, length x < 2 := by
  filter_upwards
    [eventually_length_lt_twice_radius length radius scale κ hscale hlim hκ,
      hradius] with x hxlength hxradius
  linarith

end ErdosProblems.Erdos1041
