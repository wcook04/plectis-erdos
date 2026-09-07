import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Erdős #1041: fixed-nearest-pair CE--GM quartic no-go kernel

The companion exact checker owns the Rouché discs and positive-half-line
Bernstein certificate.  This module checks the Gaussian-rational polynomial,
its critical values and threshold inequalities, the negative-half-line circle
polynomial, and the topological circle-crossing consumer.  It does not assert
the free-pair inequality or Erdős #1041.
-/

namespace ErdosProblems.Erdos1041.CEGMQuarticFixedPairNoGo

noncomputable section

open Set

def quartic (z : ℂ) : ℂ :=
  z^4-(1321/5000+(33/125)*Complex.I)*z^2-
    (33/12500+(1183/12500)*Complex.I)*z-16/25-(9/50)*Complex.I

def quarticDeriv (z : ℂ) : ℂ :=
  4*z^3-2*(1321/5000+(33/125)*Complex.I)*z-
    (33/12500+(1183/12500)*Complex.I)

def c1 : ℂ := 11/25+(1/5)*Complex.I
def c2 : ℂ := -(7/20)-(1/10)*Complex.I
def cStar : ℂ := -(9/100)-(1/10)*Complex.I

theorem derivative_factorization (z : ℂ) :
    quarticDeriv z = 4*(z-c1)*(z-c2)*(z-cStar) := by
  dsimp [quarticDeriv, c1, c2, cStar]
  ring_nf
  norm_num [Complex.I_sq]
  ring

def v1 : ℂ := -(243646/390625)-(15947/62500)*Complex.I
def v2 : ℂ := -(521621/800000)-(11191/62500)*Complex.I
def vStar : ℂ := -(64429281/100000000)-(109713/625000)*Complex.I

theorem critical_values :
    quartic c1 = v1 ∧ quartic c2 = v2 ∧ quartic cStar = vStar := by
  constructor
  · dsimp [quartic, c1, v1]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  constructor
  · dsimp [quartic, c2, v2]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  · dsimp [quartic, cStar, vStar]
    ring_nf
    norm_num [Complex.I_sq]
    ring

def V1 : ℝ := 1108755728681/2441406250000
def V2 : ℝ := 7315188509201/16000000000000
def VStar : ℝ := 4459277974823361/10000000000000000

theorem critical_value_normSq :
    Complex.normSq v1 = V1 ∧ Complex.normSq v2 = V2 ∧
      Complex.normSq vStar = VStar := by
  norm_num [v1, v2, vStar, V1, V2, VStar, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]

theorem cStar_unique_least_scalar : VStar < V1 ∧ VStar < V2 := by
  norm_num [VStar, V1, V2]

/-- Exact power comparison `Gcrit < 27/40 < |F(c₂)|`. -/
theorem separating_threshold :
    V1*V2*VStar < (27/40 : ℝ)^6 ∧ (27/40 : ℝ)^2 < V2 := by
  norm_num [V1, V2, VStar]

def circlePoly (t : ℝ) : ℝ :=
  10874172360773*t^8-10022578403256*t^7+
  11403058106654*t^6-4349728276488*t^5+
  2240976658314*t^4-335445488208*t^3+
  129719679758*t^2-24307214976*t+1427842325

/-- The alternating coefficient certificate covers the entire negative
half-line of the rational circle parametrization. -/
theorem circlePoly_pos_of_nonpos {t : ℝ} (ht : t ≤ 0) : 0 < circlePoly t := by
  have hu : 0 ≤ -t := by linarith
  rw [show circlePoly t =
      10874172360773*(-t)^8+10022578403256*(-t)^7+
      11403058106654*(-t)^6+4349728276488*(-t)^5+
      2240976658314*(-t)^4+335445488208*(-t)^3+
      129719679758*(-t)^2+24307214976*(-t)+1427842325 by
        dsimp [circlePoly]
        ring]
  positivity

/-- Any continuous path from strictly inside a circle to strictly outside it
meets the boundary.  This is the topological consumer of the exact barrier. -/
theorem path_crosses_circle
    {gamma : ℝ → ℂ} {m : ℂ} {R : ℝ}
    (hcontinuous : ContinuousOn gamma (Icc 0 1))
    (hinside : ‖gamma 0-m‖ < R) (houtside : R < ‖gamma 1-m‖) :
    ∃ t ∈ Ioo (0:ℝ) 1, ‖gamma t-m‖ = R := by
  let p : ℝ → ℝ := fun t => ‖gamma t-m‖
  have hp : ContinuousOn p (Icc 0 1) :=
    (continuous_norm.comp_continuousOn
      (hcontinuous.sub continuousOn_const))
  have hRmem : R ∈ Icc (p 0) (p 1) := ⟨hinside.le, houtside.le⟩
  obtain ⟨t, ht, hpt⟩ := (Set.mem_image p (Icc (0:ℝ) 1) R).mp
    (intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hp hRmem)
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro h
    subst t
    dsimp [p] at hpt
    linarith)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by
    intro h
    subst t
    dsimp [p] at hpt
    linarith)
  exact ⟨t, ⟨ht0, ht1⟩, hpt⟩

end

end ErdosProblems.Erdos1041.CEGMQuarticFixedPairNoGo
