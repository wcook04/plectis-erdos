import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Erdős #1041: exact stationary-system no-go kernel

The companion note gives an exact quartic with an interior one-contact KKT
point above `Gcrit`, while another feasible hub lies below it.  This module
checks the exact Gaussian-rational algebra and the reusable second-order
same-cone sign kernel.  It does not formalize Schur--Cohn, Bernstein positivity,
Danskin's theorem, or CE--GM.
-/

namespace ErdosProblems.Erdos1041.CriticalEllipseStationaryNoGo

noncomputable section

def cStar : ℂ := -(7 / 10) - (9 / 20) * Complex.I
def badHub : ℂ := -(3 / 10) - (1 / 5) * Complex.I
def rootA : ℂ := -(13 / 20) - (3 / 4) * Complex.I
def rootB : ℂ := -(9 / 10) - (1 / 5) * Complex.I
def otherCritical : ℂ := 4831 / 9700 + (623 / 2425) * Complex.I

def poly (z : ℂ) : ℂ :=
  z ^ 4 + (1623 / 2425 + (1271 / 2425) * Complex.I) * z ^ 3 +
    (-(5118 / 12125) - (59293 / 97000) * Complex.I) * z ^ 2 +
    (5279 / 121250 - (325513 / 485000) * Complex.I) * z -
    3847 / 194000 + (229487 / 1940000) * Complex.I

def polyDeriv (z : ℂ) : ℂ :=
  4 * z ^ 3 + 3 * (1623 / 2425 + (1271 / 2425) * Complex.I) * z ^ 2 +
    2 * (-(5118 / 12125) - (59293 / 97000) * Complex.I) * z +
    5279 / 121250 - (325513 / 485000) * Complex.I

theorem derivative_factorization (z : ℂ) :
    polyDeriv z = 4 * (z - cStar) * (z - badHub) * (z - otherCritical) := by
  dsimp [polyDeriv, cStar, badHub, otherCritical]
  ring_nf
  norm_num [Complex.I_sq]
  ring

theorem rootA_zero : poly rootA = 0 := by
  dsimp [poly, rootA]
  ring_nf
  norm_num [Complex.I_sq]
  ring

theorem rootB_zero : poly rootB = 0 := by
  dsimp [poly, rootB]
  ring_nf
  norm_num [Complex.I_sq]
  ring

theorem cStar_critical : polyDeriv cStar = 0 := by
  rw [derivative_factorization]
  ring

theorem badHub_critical : polyDeriv badHub = 0 := by
  rw [derivative_factorization]
  ring

theorem otherCritical_critical : polyDeriv otherCritical = 0 := by
  rw [derivative_factorization]
  ring

def vStarSq : ℝ := 310713136913 / 12416000000000
def badHubSq : ℝ := 27084213 / 485000000
def otherCriticalSq : ℝ :=
  87929920831854142093 / 1416468496000000000000

theorem critical_value_ordering :
    0 < vStarSq ∧ vStarSq < badHubSq ∧ vStarSq < otherCriticalSq := by
  norm_num [vStarSq, badHubSq, otherCriticalSq]

/-- The above-threshold test for a quartic stationary critical contact:
`H > (V* H V₂)^(1/3)` is equivalent, after positive squaring, to
`H² > V* V₂`. -/
theorem badHub_above_geometricMean_squared :
    0 < badHubSq ^ 2 - vStarSq * otherCriticalSq := by
  norm_num [badHubSq, vStarSq, otherCriticalSq]

def qA : ℝ := -(7748379 / 97000000)
def qB : ℝ := -(546719301 / 6062500000)
def mixedAB : ℝ := -(7986141 / 50000000)

theorem exact_same_negative_cone : qA < 0 ∧ qB < 0 ∧ mixedAB < 0 := by
  norm_num [qA, qB, mixedAB]

/-- If two quadratic arm directions and their mixed term are all negative,
their sum is a strict common descent direction for the quadratic saddle model. -/
theorem sameCone_descent_signs
    {qa qb bab : ℝ} (hqa : qa < 0) (hqb : qb < 0) (hbab : bab < 0) :
    qa + 2 * bab + qb < 0 ∧ qa + bab < 0 ∧ qb + bab < 0 := by
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem exact_badHub_has_quadratic_descent :
    qA + 2 * mixedAB + qB < 0 ∧
      qA + mixedAB < 0 ∧ qB + mixedAB < 0 := by
  rcases exact_same_negative_cone with ⟨ha, hb, hab⟩
  exact sameCone_descent_signs ha hb hab

end

end ErdosProblems.Erdos1041.CriticalEllipseStationaryNoGo
