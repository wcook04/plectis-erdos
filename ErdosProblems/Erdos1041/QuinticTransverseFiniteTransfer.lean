import ErdosProblems.Erdos1041.QuinticEqualityCubicExtension
import ErdosProblems.Erdos1041.QuinticFinitePerturbationTransfer
import ErdosProblems.Erdos1041.QuinticMixedGlobalAtlas
import Mathlib.Tactic

/-!
# Erdős #1041: finite transfer of the transverse quintic atlas

The companion proof combines the exact mixed-model atlas with the anchored
finite expansion.  This module checks its load-bearing numerical absorptions:
the common strict-box margin, the two complementary equality-corner regimes,
the intermediate arm budget, and the final radial/transverse split.
-/

namespace ErdosProblems.Erdos1041.QuinticTransverseFiniteTransfer

/-- The exact `10⁻⁸` strict-atlas margin absorbs the deliberately coarse
`10⁶ rho` finite-transfer error at `rho ≤ 10⁻²⁰`. -/
theorem strictAtlas_absorbs_transfer {model error rho : ℝ}
    (hrhoMax : rho ≤ (1 : ℝ) / 10 ^ 20)
    (hmodel : model ≤ -(1 : ℝ) / 10 ^ 8)
    (herror : error ≤ 10 ^ 6 * rho) :
    model + error < 0 := by
  nlinarith

/-- Outside the `delta < 10⁹ rho` core, the old tetrahedral linear margin
absorbs its quadratic chord shift and the complete finite-transfer error. -/
theorem equality_largeDelta_absorption {model error delta rho : ℝ}
    (hdelta0 : 0 < delta)
    (hdeltaMax : delta ≤ (17 : ℝ) / 2500)
    (hlarge : 10 ^ 9 * rho ≤ delta)
    (hmodel : model ≤ -((59 : ℝ) / 1000) * delta + 8 * delta ^ 2)
    (herror : error ≤ 10 ^ 6 * rho) :
    model + error < 0 := by
  have hquad : delta ^ 2 ≤ ((17 : ℝ) / 2500) * delta := by
    nlinarith [mul_nonneg (le_of_lt hdelta0) (sub_nonneg.mpr hdeltaMax)]
  have herr : error ≤ delta / 1000 := by
    nlinarith
  nlinarith

/-- Inside the `delta < 10⁹ rho` core, the paired-cubic average margin
`rho/4` absorbs the quadratic and anchored finite remainders. -/
theorem equality_smallDelta_absorption {extended remainder delta rho : ℝ}
    (hdelta0 : 0 ≤ delta) (hrho0 : 0 < rho)
    (hrhoMax : rho ≤ (1 : ℝ) / 10 ^ 20)
    (hsmall : delta ≤ 10 ^ 9 * rho)
    (hextended : extended ≤ -rho / 4)
    (hremainder : remainder ≤
      8 * delta ^ 2 + 10 ^ 6 * rho * delta + 10 ^ 6 * rho ^ 2) :
    extended + remainder < 0 := by
  have hdeltaSq : delta ^ 2 ≤ (10 ^ 9 * rho) ^ 2 :=
    (sq_le_sq₀ hdelta0 (by positivity)).2 hsmall
  have hrhoSq : rho ^ 2 ≤ ((1 : ℝ) / 10 ^ 20) * rho := by
    nlinarith [mul_nonneg (le_of_lt hrho0) (sub_nonneg.mpr hrhoMax)]
  nlinarith

/-- The exact cubic contact margin is stronger than `rho/4` as soon as
`12 y³ > 1/4`.  The companion exact interval replay proves this premise for
the algebraic equality contact (in fact `12 y³ = 3/10`). -/
theorem cubicMargin_stronger_than_quarter {rho y : ℝ}
    (hrho : 0 ≤ rho) (hy : (1 : ℝ) / 4 < 12 * y ^ 3) :
    -12 * rho * y ^ 3 < -rho / 4 ∨ rho = 0 := by
  by_cases hzero : rho = 0
  · exact Or.inr hzero
  · left
    have hrho' : 0 < rho := lt_of_le_of_ne hrho (Ne.symm hzero)
    nlinarith [mul_pos hrho' (sub_pos.mpr hy)]

/-- On the intermediate arms the `t⁵/50` analytic budget is far smaller than
the certified `998 t⁵/1000` Fourier margin. -/
theorem intermediateArm_absorption {model remainder t : ℝ}
    (ht : 0 < t)
    (hmodel : model ≤ -((998 : ℝ) / 1000) * t ^ 5)
    (hremainder : remainder ≤ t ^ 5 / 50) :
    model + remainder < 0 := by
  have ht5 : 0 < t ^ 5 := pow_pos ht 5
  nlinarith

/-- The old far-half telescope needs only `95 eta < 1/32`; the fifth-power
lower bound is imported from the radial finite transfer. -/
theorem farArm_of_eta_budget {value eta t : ℝ}
    (heta : 95 * eta < (1 : ℝ) / 32)
    (ht : 1 / 2 ≤ t)
    (hvalue : value ≤ 1 - t ^ 5 + 95 * eta) :
    value < 1 := by
  have ht5 :=
    ErdosProblems.Erdos1041.QuinticFinitePerturbationTransfer.one_over_thirtyTwo_le_fifth ht
  nlinarith

/-- Every nonnegative deficit belongs to the transverse or radial cone. -/
theorem transverse_or_radial {delta rho : ℝ} :
    delta ≤ 4 * rho ^ 3 ∨ 4 * rho ^ 3 ≤ delta := by
  exact le_total delta (4 * rho ^ 3)

end ErdosProblems.Erdos1041.QuinticTransverseFiniteTransfer
