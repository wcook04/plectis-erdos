/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-! Independent theorem statements for external replay. Proof holes belong only
to this challenge template; the solution is checked under the permitted axioms. -/

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Erdos249257.ExternalVerification1041AnalyticBridges

noncomputable def powerSeriesPath (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' n, a n * (t : ℂ) ^ (n + 1)

noncomputable def quadraticExpRemainder (t : ℝ) : ℝ :=
  ∫ s : ℝ in 0..1, (1 - s) * Real.exp (s * t)

/-- Subradius coefficient energy bounds control the actual derivative and
length of the power-series path; coefficient summability is a conclusion. -/
theorem powerSeries_length_from_subradius_energy
    (a : ℕ → ℂ) (E : ℝ → ℝ) {S : ℝ} (hS : 1 < S)
    (hE : ContinuousOn E (Icc 1 S))
    (henergy : ∀ T ∈ Ioo 1 S, ∀ s : Finset ℕ,
      ∑ k ∈ s, (((k + 1 : ℕ) : ℝ) * T ^ (k + 1)) * ‖a k‖ ^ 2 ≤ E T) :
    IntervalIntegrable (deriv (powerSeriesPath a)) volume (-1) 1 ∧
    (∫ x : ℝ in (-1)..1, ‖deriv (powerSeriesPath a) x‖) ≤
      2 * Real.sqrt (E S * Real.log (S / (S - 1))) := by
  sorry

/-- An adaptive certificate stated entirely in the actual logarithmic
interactions bounds the geometric row means of any finite disk configuration. -/
theorem freePointMean_from_adaptive_log_certificate
    {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ) (hc : ∀ i, ‖c i‖ < 1)
    (M : Fin m → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hcap : ∀ i, (∑ j, Real.log ‖1 - conj (c i) * c j‖) / m ≤ M i)
    (hcertificate :
      (∑ i, quadraticExpRemainder (M i) * (-Real.log ‖1 - conj (c i) * c i‖)) ≤ m) :
    (∑ i, (∏ j, ‖1 - conj (c i) * c j‖) ^ (1 / (m : ℝ))) ≤ m := by
  sorry

end Erdos249257.ExternalVerification1041AnalyticBridges
