import ErdosProblems.Erdos1041.QuinticRadialDominantCone
import Mathlib.Tactic

/-!
# Erdős #1041: finite transfer of the radial-dominant quintic cone

The companion proof transfers the radial cone to actual perturbed quintics.
This module formalizes its load-bearing numerical absorptions: Fourier
inversion, the near logarithmic budget, the far telescoping budget, and the
fifth-power lower bound on the far half.
-/

namespace ErdosProblems.Erdos1041.QuinticFinitePerturbationTransfer

/-- Fourier inversion plus a `5 Delta` nonconstant-mode budget gives
`eta ≤ 6 Delta / 5`. -/
theorem eta_le_six_fifths_delta {eta delta modeSum : ℝ}
    (hfourier : 5 * eta ≤ delta + modeSum)
    (hmodes : modeSum ≤ 5 * delta) :
    eta ≤ 6 * delta / 5 := by
  linarith

/-- A nonnegative real at least `1/2` has fifth power at least `1/32`.
The factorization avoids invoking transcendental monotonicity. -/
theorem one_over_thirtyTwo_le_fifth {t : ℝ} (ht : 1 / 2 ≤ t) :
    (1 / 32 : ℝ) ≤ t ^ 5 := by
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hfactor :
      t ^ 5 - (1 / 32 : ℝ) =
        (t - 1 / 2) *
          (t ^ 4 + t ^ 3 / 2 + t ^ 2 / 4 + t / 8 + 1 / 16) := by
    ring
  have hpoly :
      0 ≤ t ^ 4 + t ^ 3 / 2 + t ^ 2 / 4 + t / 8 + 1 / 16 := by
    positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) hpoly]

/-- The exact rational separation used on the far half:
`95 * (6/5) / 4096 < 1/32`. -/
theorem farArm_margin {value eta delta t : ℝ}
    (heta : eta ≤ 6 * delta / 5) (hdelta : delta ≤ 1 / 4096)
    (ht : 1 / 2 ≤ t) (hvalue : value ≤ 1 - t ^ 5 + 95 * eta) :
    value < 1 := by
  have ht5 := one_over_thirtyTwo_le_fifth ht
  nlinarith

/-- The near-arm error budget is strictly absorbed by the radial model margin.
The coefficient `53/2` is `(5/2)+4+20` from the origin, phase, and anchored
logarithmic errors. -/
theorem nearArm_log_margin {core denominatorError quadraticError eta delta : ℝ}
    (heta0 : 0 ≤ eta) (hdelta0 : 0 < delta)
    (heta : eta ≤ 6 * delta / 5) (hdelta : delta ≤ 1 / 4096)
    (hcore : core ≤ -delta / 2)
    (hdenominator : denominatorError ≤ delta / 10)
    (hquadratic : quadraticError ≤ (53 / 2 : ℝ) * eta ^ 2) :
    core + denominatorError + quadraticError < -(3 * delta / 8) := by
  have hetaSq : eta ^ 2 ≤ (6 * delta / 5) ^ 2 :=
    (sq_le_sq₀ heta0 (by positivity)).2 heta
  have hdeltaSq : delta ^ 2 ≤ delta / 4096 := by
    have h := mul_le_mul_of_nonneg_left hdelta (le_of_lt hdelta0)
    nlinarith
  nlinarith

/-- The connector-disk errors are absorbed by the exact negative constant. -/
theorem connectorDisk_log_margin {baseline quadratic delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta : delta ≤ 1 / 4096)
    (hbaseline : baseline ≤ -9 * delta / 10)
    (hquadratic : quadratic ≤ 5 * delta ^ 2) :
    baseline + quadratic < -(3 * delta / 4) := by
  have hdeltaSq : delta ^ 2 ≤ delta / 4096 := by
    have h := mul_le_mul_of_nonneg_left hdelta (le_of_lt hdelta0)
    nlinarith
  nlinarith

end ErdosProblems.Erdos1041.QuinticFinitePerturbationTransfer
