import Mathlib.Tactic

/-! The exact scalar defect surviving from the retired three-point proof.
This does not assume or assert the missing Hölder step. It is an independent
algebraic certificate, not a replacement for the whole alternative argument.
All Lean checks in this return are UNRUN. -/
set_option autoImplicit false
noncomputable section
namespace ErdosProblems.Erdos1041

/-- `x,y,z` are the three squared radii and `t` is the squared centroid norm. -/
def threePointDefect (x y z t : ℝ) : ℝ :=
  ((x - y) ^ 2 + (x - z) ^ 2 + (y - z) ^ 2) / 2 +
    (x + y + z) * (x * y + x * z + y * z) + (3 - (x + y + z)) * t

theorem threePointDefect_identity (x y z t : ℝ) :
    (3 - (x + y + z)) *
      (3 + (x + y + z) - t + (x * y + x * z + y * z)) =
        9 - threePointDefect x y z t := by
  unfold threePointDefect
  ring

theorem threePointDefect_nonneg {x y z t : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (hQ : x + y + z ≤ 3) : 0 ≤ threePointDefect x y z t := by
  unfold threePointDefect
  exact add_nonneg
    (add_nonneg (div_nonneg (by positivity) (by norm_num))
      (mul_nonneg (by positivity) (by positivity)))
    (mul_nonneg (sub_nonneg.mpr hQ) ht)

theorem threePointDefect_majorant_le {x y z t : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (hQ : x + y + z ≤ 3) :
    (3 - (x + y + z)) *
      (3 + (x + y + z) - t + (x * y + x * z + y * z)) ≤ 9 := by
  rw [threePointDefect_identity]
  linarith [threePointDefect_nonneg hx hy hz ht hQ]

/-- The sharp scalar equality also forces `t = 0`; when the radii vanish this
is automatically the value of the squared centroid norm. -/
theorem threePointDefect_eq_zero_iff {x y z t : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (ht : 0 ≤ t)
    (hQ : x + y + z ≤ 3) :
    threePointDefect x y z t = 0 ↔ x = 0 ∧ y = 0 ∧ z = 0 ∧ t = 0 := by
  constructor
  · intro he
    have hp : 0 ≤ (x + y + z) * (x * y + x * z + y * z) := by positivity
    have hqt : 0 ≤ (3 - (x + y + z)) * t :=
      mul_nonneg (sub_nonneg.mpr hQ) ht
    have hxy : x = y := by
      dsimp [threePointDefect] at he
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
    have hxz : x = z := by
      dsimp [threePointDefect] at he
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
    have hx0 : x = 0 := by
      by_contra hne
      have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
      have hprod : 0 < (x + y + z) * (x * y + x * z + y * z) := by
        rw [← hxy, ← hxz]
        positivity
      dsimp [threePointDefect] at he
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]
    have hy0 : y = 0 := hxy.symm.trans hx0
    have hz0 : z = 0 := hxz.symm.trans hx0
    have ht0 : t = 0 := by
      dsimp [threePointDefect] at he
      rw [hx0, hy0, hz0] at he
      nlinarith
    exact ⟨hx0, hy0, hz0, ht0⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num [threePointDefect]

end ErdosProblems.Erdos1041
