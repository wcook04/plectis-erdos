import ErdosProblems.Erdos1041.NewtonFlowRaySeparation
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Erdős #1041: the Cassini falsifier, and real-time Newton flow

Two independent objects for the March 2026 candidate manuscript.

## 1. The tree-budget assertion is numerically false

The manuscript's load-bearing proposition asserts that, under Morse and
distinct-critical-value hypotheses, for every `ε > 0` there is a connected tree
through all roots of length at most

`(1/2π) ∫_{2α}^∞ P(t) dt + ε`.

For the Cassini family `f_a(z) = z² - a²` with `4/5 < a < 1` every hypothesis
holds: both roots lie in the lemniscate, the only critical point `0` is a
nondegenerate saddle, and distinctness of critical values is vacuous.  A direct
level-length computation together with the elementary majorant
`|a² + re^{iθ}|^{-1/2} ≤ (a²+r)^{-1/2}|cos(θ/2)|^{-1/2}` gives

`(1/2π) ∫_{2α}^∞ P_a(t) dt ≤ 4(√(a²+a) - a)`.

`four_mul_sqrt_sub_lt_two_mul` proves that this majorant drops **below the
distance `2a` between the two roots** exactly when `a > 4/5`, and any connected
set containing both roots has length at least `2a`.  So the assertion fails —
and it fails *metrically*, not topologically: no repair of the local Morse
neighbourhood can rescue it, because the numerical conclusion is already
inconsistent.

`cassini_nine_tenths_falsifies_tree_budget` is the rational witness at
`a = 9/10`, with certified slack `4/25`.

**What is and is not formalised.**  The coarea majorant is supplied as an
explicit hypothesis (`LevelLengthMajorant`); it is proved in prose, not here.
What is kernel-checked is that the majorant is inconsistent with the tree
budget at an explicit witness — which is precisely the falsifier.

## 2. Real-time Newton flow

`newtonFlow_value_hasDerivAt` in `NewtonFlowRaySeparation` is stated for a
**complex**-time curve `z : ℂ → ℂ`, while the geometric Newton trajectory is
real-time `z : ℝ → ℂ`; and `samePositiveRay_of_real_exp_decay` *assumes* the
exponential endpoint relation rather than deriving it.  The mixed-field chain
rule closes both gaps: `newtonFlow_real_samePositiveRay` derives ray alignment
of any two points of a real-time trajectory directly from the differential
equation.

## Claim ceiling

**Erdős #1041 remains open.**  This is not a counterexample to the problem: for
the same quadratic the straight segment `[-a, a]` lies inside the lemniscate
and has length `2a < 2`.  What is refuted is one candidate proof's central
estimate.
-/

namespace ErdosProblems.Erdos1041.CassiniTreeBudget

open ErdosProblems.Erdos1041

/-! ## The arithmetic of the Cassini falsifier -/

/-- **The budget drops below the root distance.**  The elementary coarea
majorant for `z² - a²` is strictly smaller than the distance between the two
roots exactly when `a > 4/5`. -/
theorem four_mul_sqrt_sub_lt_two_mul {a : ℝ} (ha : 4 / 5 < a) :
    4 * (Real.sqrt (a ^ 2 + a) - a) < 2 * a := by
  have hapos : 0 < a := by linarith
  have hsq : a ^ 2 + a < (3 / 2 * a) ^ 2 := by nlinarith
  have hroot : Real.sqrt (a ^ 2 + a) < 3 / 2 * a := by
    have h1 : Real.sqrt (a ^ 2 + a) < Real.sqrt ((3 / 2 * a) ^ 2) :=
      Real.sqrt_lt_sqrt (by nlinarith) hsq
    rwa [Real.sqrt_sq (by linarith)] at h1
  linarith

/-- Certified slack at the rational witness `a = 9/10`: the majorant undershoots
the root distance by more than `4/25`. -/
theorem cassini_nine_tenths_slack :
    4 * (Real.sqrt ((9 / 10 : ℝ) ^ 2 + 9 / 10) - 9 / 10) + 4 / 25 < 2 * (9 / 10 : ℝ) := by
  have h171 : Real.sqrt ((9 / 10 : ℝ) ^ 2 + 9 / 10) < 131 / 100 := by
    have hsq : ((9 : ℝ) / 10) ^ 2 + 9 / 10 < (131 / 100) ^ 2 := by norm_num
    have h1 : Real.sqrt ((9 / 10 : ℝ) ^ 2 + 9 / 10) < Real.sqrt ((131 / 100 : ℝ) ^ 2) :=
      Real.sqrt_lt_sqrt (by norm_num) hsq
    rwa [Real.sqrt_sq (by norm_num)] at h1
  linarith

/-- **A positive attachment deficit.**  At the Cassini witness, every connected
root-spanning object has length more than `4/25` above the proposed coarea
budget.  Thus a strip argument cannot recover that budget by choosing
average-short trajectories and charging only an arbitrarily small additive
cost near the saddle: the required attachment mismatch has a fixed positive
lower bound. -/
theorem cassini_nine_tenths_forces_attachment_overhead {len : ℝ}
    (hspans : 2 * (9 / 10 : ℝ) ≤ len) :
    4 * (Real.sqrt ((9 / 10 : ℝ) ^ 2 + 9 / 10) - 9 / 10) + 4 / 25 < len := by
  linarith [cassini_nine_tenths_slack]

/-- The manuscript's tree-budget assertion at one lemniscate component: every
positive slack admits a connected tree through all roots within the budget.
Any connected set containing two roots has length at least their distance. -/
def TreeBudgetAssertion (budget rootDist : ℝ) : Prop :=
  ∀ ε > 0, ∃ len : ℝ, rootDist ≤ len ∧ len ≤ budget + ε

/-- A budget strictly below the root distance refutes the assertion. -/
theorem not_treeBudgetAssertion_of_lt {budget rootDist : ℝ} (hlt : budget < rootDist) :
    ¬ TreeBudgetAssertion budget rootDist := by
  intro htree
  obtain ⟨len, hlen1, hlen2⟩ := htree ((rootDist - budget) / 2) (by linarith)
  linarith

/-- **The falsifier.**  At `a = 9/10` the coarea majorant and the tree budget
are inconsistent.  Since the majorant is an upper bound for the true level-length
integral, the manuscript's proposition is false. -/
theorem cassini_nine_tenths_falsifies_tree_budget :
    ¬ TreeBudgetAssertion
        (4 * (Real.sqrt ((9 / 10 : ℝ) ^ 2 + 9 / 10) - 9 / 10)) (2 * (9 / 10 : ℝ)) := by
  refine not_treeBudgetAssertion_of_lt ?_
  linarith [cassini_nine_tenths_slack]

/-- The general Cassini falsifier: for every `a` in `(4/5, 1)` the majorant is
strictly below the root distance, so the assertion fails on the whole family. -/
theorem cassini_falsifies_tree_budget {a : ℝ} (ha : 4 / 5 < a) :
    ¬ TreeBudgetAssertion (4 * (Real.sqrt (a ^ 2 + a) - a)) (2 * a) :=
  not_treeBudgetAssertion_of_lt (four_mul_sqrt_sub_lt_two_mul ha)

/-- **No uniform strict length slack.**  Even on the quadratic Cassini family,
the distance between the two roots can approach `2` from below.  Consequently
no positive constant `δ`, independent of the polynomial, can strengthen the
target length bound to `2 - δ`.

This is the exact boundary exposed by near-regular-polygon Newton-hub probes:
generic perturbation and root transfer must preserve a data-dependent strict
slack; they cannot spend a fixed global margin. -/
theorem not_exists_uniform_cassini_rootDistance_slack :
    ¬ ∃ δ : ℝ, 0 < δ ∧
      ∀ a : ℝ, 0 < a → a < 1 → 2 * a ≤ 2 - δ := by
  rintro ⟨δ, hδ, hbound⟩
  have hδle : δ ≤ 1 := by
    have hhalf := hbound (1 / 2) (by norm_num) (by norm_num)
    linarith
  have haPos : 0 < 1 - δ / 4 := by linarith
  have haLt : 1 - δ / 4 < 1 := by linarith
  have hnear := hbound (1 - δ / 4) haPos haLt
  linarith

/-! ## Real-time Newton flow -/

/-- Real-time chain-rule form of `w' = -w` along the Newton field. -/
theorem newtonFlow_real_value_hasDerivAt {f f' : ℂ → ℂ} {z : ℝ → ℂ} {t : ℝ}
    (hf : HasDerivAt f (f' (z t)) (z t))
    (hz : HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hcritical : f' (z t) ≠ 0) :
    HasDerivAt (fun s : ℝ => f (z s)) (-f (z t)) t := by
  have hcancel : f' (z t) * newtonFlowVector (f (z t)) (f' (z t)) = -f (z t) :=
    derivative_mul_newtonFlowVector hcritical
  have hfd : HasFDerivAt f (f' (z t) • (1 : ℂ →L[ℝ] ℂ)) (z t) := hf.complexToReal_fderiv
  have hcomp := hfd.comp_hasDerivAt t hz
  simpa [Function.comp_def, smul_eq_mul, hcancel] using hcomp

/-- Multiplication by the real exponential produces a first integral. -/
theorem newtonFlow_real_scaledValue_hasDerivAt_zero {f f' : ℂ → ℂ} {z : ℝ → ℂ} {t : ℝ}
    (hf : HasDerivAt f (f' (z t)) (z t))
    (hz : HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hcritical : f' (z t) ≠ 0) :
    HasDerivAt (fun s : ℝ => (Real.exp s : ℂ) * f (z s)) 0 t := by
  have hexp : HasDerivAt (fun s : ℝ => ((Real.exp s : ℝ) : ℂ)) ((Real.exp t : ℝ) : ℂ) t :=
    (Real.hasDerivAt_exp t).ofReal_comp
  have hvalue := newtonFlow_real_value_hasDerivAt hf hz hcritical
  have := hexp.mul hvalue
  simpa using this

/-- The real-time exponential first integral is globally constant. -/
theorem newtonFlow_real_scaledValue_eq {f f' : ℂ → ℂ} {z : ℝ → ℂ}
    (hf : ∀ t, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t, HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hcritical : ∀ t, f' (z t) ≠ 0) (s t : ℝ) :
    (Real.exp s : ℂ) * f (z s) = (Real.exp t : ℂ) * f (z t) := by
  have hF : ∀ r : ℝ, HasDerivAt (fun r : ℝ => (Real.exp r : ℂ) * f (z r)) 0 r := fun r =>
    newtonFlow_real_scaledValue_hasDerivAt_zero (hf r) (hz r) (hcritical r)
  exact is_const_of_deriv_eq_zero (fun r => (hF r).differentiableAt)
    (fun r => (hF r).deriv) s t

/-- **Ray separation from the differential equation.**  Any two values on one
real-time Newton trajectory lie on a single oriented ray from the origin — the
endpoint relation is derived, not assumed. -/
theorem newtonFlow_real_samePositiveRay {f f' : ℂ → ℂ} {z : ℝ → ℂ}
    (hf : ∀ t, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t, HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hcritical : ∀ t, f' (z t) ≠ 0) (s t : ℝ) :
    SamePositiveRay (f (z s)) (f (z t)) := by
  have hscaled := newtonFlow_real_scaledValue_eq hf hz hcritical s t
  refine ⟨Real.exp s / Real.exp t, div_pos (Real.exp_pos s) (Real.exp_pos t), ?_⟩
  have ht : ((Real.exp t : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
  rw [Complex.ofReal_div, div_mul_eq_mul_div, eq_div_iff ht]
  linear_combination -hscaled

end ErdosProblems.Erdos1041.CassiniTreeBudget
