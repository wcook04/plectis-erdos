import ErdosProblems.Erdos1041.SexticCanonicalMixedSlice

/-!
# Erdős #1041: the pure cubic sextic face forces a radius-zero stratum

For `H(z) = Re (z^3 - z^6)`, every positive equal-radius chord between
non-antipodal sixth-root directions crosses a half-step direction.  At such a
point `z^3` is nonzero and purely imaginary, so `H(z) > 0`.  This module
formalizes the load-bearing algebra and one canonical adjacent midpoint.
-/

namespace ErdosProblems.Erdos1041.SexticCubicFaceConnectorNoGo

noncomputable section

abbrev sqrtThree : ℝ :=
  ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.sqrtThree

def cubicFaceValue (z : ℂ) : ℝ := (z ^ 3 - z ^ 6).re

/-- The midpoint of the equal-radius chord from direction `1` to direction
`exp(π i/3)`, written without trigonometric functions. -/
def adjacentMidpoint (r : ℝ) : ℂ :=
  ⟨3 * r / 4, sqrtThree * r / 4⟩

theorem sqrtThree_sq : sqrtThree ^ 2 = 3 :=
  ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.sqrtThree_sq

/-- Any nonzero point whose cube is purely imaginary lies strictly outside
the nonpositive pure-cubic sextic model. -/
theorem cubicFaceValue_pos_of_cube_eq_mul_I {z : ℂ} {x : ℝ}
    (hx : x ≠ 0) (hcube : z ^ 3 = (x : ℂ) * Complex.I) :
    0 < cubicFaceValue z := by
  have hsix : z ^ 6 = (z ^ 3) ^ 2 := by ring
  rw [cubicFaceValue, hsix, hcube]
  simp [pow_two]
  exact hx

theorem adjacentMidpoint_cube (r : ℝ) :
    adjacentMidpoint r ^ 3 =
      ((3 * sqrtThree * r ^ 3 / 8 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [adjacentMidpoint, pow_succ, Complex.mul_re, Complex.mul_im]
    linear_combination (-9 * r ^ 3 / 64) * sqrtThree_sq
  · simp [adjacentMidpoint, pow_succ, Complex.mul_re, Complex.mul_im]
    linear_combination (-sqrtThree * r ^ 3 / 64) * sqrtThree_sq

/-- The canonical adjacent chord already contains a strict escaping point at
its midpoint, at every positive radius. -/
theorem adjacentMidpoint_cubicFaceValue_pos {r : ℝ} (hr : 0 < r) :
    0 < cubicFaceValue (adjacentMidpoint r) := by
  refine cubicFaceValue_pos_of_cube_eq_mul_I
    (z := adjacentMidpoint r) (x := 3 * sqrtThree * r ^ 3 / 8) ?_ ?_
  · have hspos : 0 < sqrtThree :=
      ErdosProblems.Erdos1041.SexticCanonicalMixedSlice.sqrtThree_pos
    positivity
  · exact adjacentMidpoint_cube r

/-- Any proposed connector set containing a nonzero half-step point cannot be
contained in the nonpositive model. -/
theorem not_all_nonpos_of_halfStep_mem {Γ : Set ℂ} {z : ℂ} {x : ℝ}
    (hz : z ∈ Γ) (hx : x ≠ 0) (hcube : z ^ 3 = (x : ℂ) * Complex.I) :
    ¬ ∀ w ∈ Γ, cubicFaceValue w ≤ 0 := by
  intro hall
  have hnonpos := hall z hz
  have hpos := cubicFaceValue_pos_of_cube_eq_mul_I hx hcube
  linarith

end

end ErdosProblems.Erdos1041.SexticCubicFaceConnectorNoGo
