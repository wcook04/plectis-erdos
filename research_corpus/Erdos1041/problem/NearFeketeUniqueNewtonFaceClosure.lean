import Mathlib.Tactic

/-!
# Erdős #1041: the unique Newton-face transfer kernel

For an analytic coefficient arc, write the valuation of the `k`-th Fourier
mode as `q k`.  If mode `m` uniquely minimizes `q k / (n-k)`, reparameterize
the arc by `ε = u^(n-m)` and space by `z = u^(q m) ζ`.  The active `m`-term
and the degree-`n` baseline then both have weight `n * q m`, whereas every
competing mode has weight

`(n-m) * q k + q m * k`.

This module checks the exact integer separation, its power factorization, and
the final strict error absorption.  The analytic companion proves that the
origin-anchored logarithmic remainder and the root-direction displacement have
positive excess weight on the claimed monotone arcs, where `m<n/2` is also the
first nonzero polynomial degree.  The integer lemmas are deliberately more
general. Complex branch matching is not encoded here.
-/

namespace ErdosProblems.Erdos1041.NearFeketeUniqueNewtonFaceClosure

/-- The common weight of the active lower mode and the degree-`n` baseline. -/
def activeWeight (n qm : ℕ) : ℕ := n * qm

/-- The weight of mode `k` after the unique-face reparameterization
`ε = u^(n-m)`, `z = u^qm ζ`. -/
def competitorWeight (n m qm k qk : ℕ) : ℕ :=
  (n - m) * qk + qm * k

/-- Cross multiplication of the strict Newton-slope inequality gives a
strict integer weight gap after the common reparameterization. -/
theorem activeWeight_lt_competitorWeight
    {n m qm k qk : ℕ} (hk : k ≤ n)
    (hface : qm * (n - k) < qk * (n - m)) :
    activeWeight n qm < competitorWeight n m qm k qk := by
  have hn_split : n = (n - k) + k := (Nat.sub_add_cancel hk).symm
  calc
    activeWeight n qm = qm * n := by
      simp only [activeWeight, Nat.mul_comm]
    _ = qm * ((n - k) + k) := by rw [← hn_split]
    _ = qm * (n - k) + qm * k := by rw [Nat.mul_add]
    _ < qk * (n - m) + qm * k := Nat.add_lt_add_right hface (qm * k)
    _ = competitorWeight n m qm k qk := by
      simp only [competitorWeight, Nat.mul_comm]

/-- Every competing mode carries at least one additional integral power of
the scale parameter. -/
theorem competitorWeight_eq_activeWeight_add_gap
    {n m qm k qk : ℕ} (hk : k ≤ n)
    (hface : qm * (n - k) < qk * (n - m)) :
    ∃ gap : ℕ, 1 ≤ gap ∧
      competitorWeight n m qm k qk = activeWeight n qm + gap := by
  have hlt := activeWeight_lt_competitorWeight hk hface
  obtain ⟨gap, hgapEq⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hlt)
  refine ⟨gap, ?_, hgapEq⟩
  omega

/-- The integer weight gap is an exact multiplicative small factor.  This is
the algebraic core of the `o(active scale)` statement used in the analytic
proof. -/
theorem competitorPower_factors_through_activePower
    {n m qm k qk : ℕ} (u : ℝ) (hk : k ≤ n)
    (hface : qm * (n - k) < qk * (n - m)) :
    ∃ gap : ℕ, 1 ≤ gap ∧
      u ^ competitorWeight n m qm k qk =
        u ^ activeWeight n qm * u ^ gap := by
  obtain ⟨gap, hgap, hweight⟩ :=
    competitorWeight_eq_activeWeight_add_gap hk hface
  refine ⟨gap, hgap, ?_⟩
  rw [hweight, pow_add]

/-- A strict model margin survives any total perturbation costing at most half
that margin.  In the application `scale = u^(n*qm)` and all nonactive modes,
the anchored nonlinear remainder, and the moving-ray error are placed in
`error`. -/
theorem uniqueFace_margin_absorbs_error
    {model error margin scale : ℝ}
    (hmargin : 0 < margin) (hscale : 0 < scale)
    (hmodel : model ≤ -margin * scale)
    (herror : error ≤ margin * scale / 2) :
    model + error < 0 := by
  nlinarith [mul_pos hmargin hscale]

/-- A finite family of error terms may first be summed and then absorbed by
the same strict unique-face margin. -/
theorem uniqueFace_sum_absorbs
    {ι : Type*} (s : Finset ι) (err : ι → ℝ)
    {model margin scale : ℝ}
    (hmargin : 0 < margin) (hscale : 0 < scale)
    (hmodel : model ≤ -margin * scale)
    (herr : ∑ i ∈ s, err i ≤ margin * scale / 2) :
    model + ∑ i ∈ s, err i < 0 := by
  exact uniqueFace_margin_absorbs_error hmargin hscale hmodel herr

end ErdosProblems.Erdos1041.NearFeketeUniqueNewtonFaceClosure
