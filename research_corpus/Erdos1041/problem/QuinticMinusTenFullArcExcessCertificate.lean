import ErdosProblems.Erdos1041.QuinticMinusTenEndpointExcessCertificate

/-!
# Erdős 1041: Lean replay for the full `μ = -10` phase-arc certificate

The companion Python checker owns the exact rational interval atlas: selected
branch isolation, regularity and orientation, quadrature, and mean-value
transport over the whole signed phase arc.  This module does not formalize
that analytic atlas or the support--oscillation lemma in Lean.  It checks the
two algebraic identities used to turn the implicit transverse curve into the
checker’s nonnegative fixed-box integrand, and the final implication from the
externally certified uniform bound to strict negativity.

Thus a green build here is an algebraic replay and status firewall, not an
end-to-end Lean proof of the full phase-arc estimate.
-/

namespace ErdosProblems.Erdos1041

/-- The tangent determinant collapses to the square of the terminal gap.
This is the coordinate-free algebraic identity reused by the full-arc
checker after setting `Y = w S_w - (k-t) S_t` and
`X = tY + w(k-t)S_w`. -/
theorem quintic_minusTen_fullArc_determinant_identity
    (k t w St Sw : ℝ) :
    let Y := w * Sw - (k - t) * St
    let X := t * Y + w * (k - t) * Sw
    k * Y - X = -(k - t) ^ 2 * St := by
  dsimp
  ring

/-- If implicit differentiation gives `S_w w_y = -(k-r) S_t`, then the
half-angle factor times transverse variation is exactly the nonnegative
squared integrand used by the rational atlas. -/
theorem quintic_minusTen_fullArc_squared_integrand_identity
    (r k y St Sw Delta wy : ℝ)
    (hrk : r ≤ k)
    (hSw : 0 < Sw)
    (hDelta : Delta ≠ 0)
    (himplicit : Sw * wy = -(k - r) * St) :
    (((k - r) ^ 2 * (1 - y) ^ 2 * |St|) / Delta) * |wy| =
      ((k - r) ^ 3 * (1 - y) ^ 2 * St ^ 2) / (Sw * Delta) := by
  have hSw0 : Sw ≠ 0 := ne_of_gt hSw
  have hgap : 0 ≤ k - r := sub_nonneg.mpr hrk
  have habs : Sw * |wy| = (k - r) * |St| := by
    have h := congrArg abs himplicit
    simpa only [abs_mul, abs_neg, abs_of_pos hSw, abs_of_nonneg hgap] using h
  have hwy : |wy| = ((k - r) * |St|) / Sw := by
    apply (eq_div_iff hSw0).2
    simpa [mul_comm] using habs
  rw [hwy, ← sq_abs St]
  field_simp [hSw0, hDelta]

/-- Status firewall at the exact rational target used by the interval atlas.
The hypotheses deliberately expose the external certificate boundary: Lean
deduces negativity once the atlas supplies an upper bound below `-1/100`.-/
theorem quintic_minusTen_fullArc_excess_negative_of_atlas
    {excess upper : ℝ}
    (hexcess : excess ≤ upper)
    (hupper : upper < (-1 : ℝ) / 100) :
    excess < 0 := by
  nlinarith

end ErdosProblems.Erdos1041
