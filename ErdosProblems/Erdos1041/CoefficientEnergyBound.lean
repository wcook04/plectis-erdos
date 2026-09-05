import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
# Coefficient energy and the logarithmic connector bound

This is the weighted Cauchy--Schwarz step in the first-merge argument.
Uniform bounds on finite coefficient energies imply absolute summability;
no convention for a divergent `tsum` enters the hypotheses.  The application
uses weights `(k+1) S^(k+1)`, where `S` is the square of the analytic radius.
The geometric area bound and the existence of the inverse branch remain
separate hypotheses of the surrounding, ordinary mathematical argument.
-/

namespace ErdosProblems.Erdos1041

/-- A finite-energy bound with summable reciprocal weights controls the
absolute coefficient sum, including its existence. -/
theorem summable_norm_and_tsum_le_of_coefficient_energy
    (a : ℕ → ℂ) (w : ℕ → ℝ) {E : ℝ}
    (hw : ∀ k, 0 < w k) (hinv : Summable (fun k => (w k)⁻¹))
    (henergy : ∀ s : Finset ℕ, ∑ k ∈ s, w k * ‖a k‖ ^ 2 ≤ E) :
    Summable (fun k => ‖a k‖) ∧
      (∑' k, ‖a k‖) ≤ Real.sqrt (E * ∑' k, (w k)⁻¹) := by
  have hE : 0 ≤ E := by simpa using henergy ∅
  have hfinite (s : Finset ℕ) :
      (∑ k ∈ s, ‖a k‖) ^ 2 ≤ E * ∑' k, (w k)⁻¹ := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s
      (r := fun k => ‖a k‖) (f := fun k => w k * ‖a k‖ ^ 2)
      (g := fun k => (w k)⁻¹)
      (fun k _ => mul_nonneg (hw k).le (sq_nonneg _))
      (fun k _ => (inv_pos.mpr (hw k)).le)
      (fun k _ => by field_simp [ne_of_gt (hw k)] <;> ring)
    have hsum := hinv.sum_le_tsum s (fun k _ => (inv_pos.mpr (hw k)).le)
    exact hcs.trans (mul_le_mul (henergy s) hsum
      (Finset.sum_nonneg fun k _ => (inv_pos.mpr (hw k)).le) hE)
  have hbound (s : Finset ℕ) :
      ∑ k ∈ s, ‖a k‖ ≤ Real.sqrt (E * ∑' k, (w k)⁻¹) := by
    exact Real.le_sqrt_of_sq_le (hfinite s)
  exact ⟨summable_of_sum_le (fun k => norm_nonneg _) hbound,
    Real.tsum_le_of_sum_le (fun k => norm_nonneg _) hbound⟩

/-- The reciprocal coefficient weights sum to the exact logarithmic factor. -/
theorem hasSum_inverse_coefficient_weights {S : ℝ} (hS : 1 < S) :
    HasSum (fun k : ℕ => (((k + 1 : ℕ) : ℝ) * S ^ (k + 1))⁻¹)
      (Real.log (S / (S - 1))) := by
  have hpos : 0 < S := by linarith
  have habs : |S⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr hpos)]
    exact (inv_lt_one₀ hpos).2 hS
  have hseries := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hlog : -Real.log (1 - S⁻¹) = Real.log (S / (S - 1)) := by
    rw [← Real.log_inv]
    congr 1
    rw [show 1 - S⁻¹ = (S - 1) / S by
      field_simp [ne_of_gt hpos]]
    exact inv_div _ _
  rw [hlog] at hseries
  convert hseries using 1
  ext k
  simp [mul_inv_rev, inv_pow, div_eq_mul_inv, mul_comm]

/-- The sharp logarithmic absolute-coefficient estimate at squared radius
`S > 1`.  This formalizes the energy-to-coefficient step without assuming
absolute convergence in advance. -/
theorem summable_norm_and_log_bound_of_coefficient_energy
    (a : ℕ → ℂ) {S E : ℝ} (hS : 1 < S)
    (henergy : ∀ s : Finset ℕ,
      ∑ k ∈ s, (((k + 1 : ℕ) : ℝ) * S ^ (k + 1)) * ‖a k‖ ^ 2 ≤ E) :
    Summable (fun k => ‖a k‖) ∧
      (∑' k, ‖a k‖) ≤ Real.sqrt (E * Real.log (S / (S - 1))) := by
  have hs := hasSum_inverse_coefficient_weights hS
  have h := summable_norm_and_tsum_le_of_coefficient_energy a
    (fun k => ((k + 1 : ℕ) : ℝ) * S ^ (k + 1))
    (fun k => by
      have hpos : 0 < S := by linarith
      dsimp
      positivity) hs.summable henergy
  simpa only [hs.tsum_eq] using h

/-- Squared form for the numerical connector-length consumer. -/
theorem tsum_norm_sq_le_log_of_coefficient_energy
    (a : ℕ → ℂ) {S E : ℝ} (hS : 1 < S)
    (henergy : ∀ s : Finset ℕ,
      ∑ k ∈ s, (((k + 1 : ℕ) : ℝ) * S ^ (k + 1)) * ‖a k‖ ^ 2 ≤ E) :
    (∑' k, ‖a k‖) ^ 2 ≤ E * Real.log (S / (S - 1)) := by
  have h := (summable_norm_and_log_bound_of_coefficient_energy a hS henergy).2
  have hE : 0 ≤ E := by simpa using henergy ∅
  have hlog : 0 ≤ Real.log (S / (S - 1)) := by
    apply Real.log_nonneg
    have hden : 0 < S - 1 := by linarith
    apply (le_div_iff₀ hden).2
    linarith
  exact (Real.le_sqrt (tsum_nonneg fun k => norm_nonneg _) (mul_nonneg hE hlog)).1 h

/-- Bounds proved only at strictly smaller radii suffice at the limiting
radius.  The limit is taken on each finite energy sum, so no boundary
convergence of the holomorphic series is assumed. -/
theorem log_bound_of_subradius_coefficient_energy
    (a : ℕ → ℂ) (E : ℝ → ℝ) {S : ℝ} (hS : 1 < S)
    (hE : ContinuousOn E (Set.Icc 1 S))
    (henergy : ∀ T ∈ Set.Ioo 1 S, ∀ s : Finset ℕ,
      ∑ k ∈ s, (((k + 1 : ℕ) : ℝ) * T ^ (k + 1)) * ‖a k‖ ^ 2 ≤ E T) :
    Summable (fun k => ‖a k‖) ∧
      (∑' k, ‖a k‖) ≤ Real.sqrt (E S * Real.log (S / (S - 1))) := by
  apply summable_norm_and_log_bound_of_coefficient_energy a hS
  intro s
  have hc : closure (Set.Ioo (1 : ℝ) S) = Set.Icc 1 S :=
    closure_Ioo (ne_of_lt hS)
  apply le_on_closure (fun T hT => henergy T hT s)
  · exact (by fun_prop : Continuous
      (fun T : ℝ => ∑ k ∈ s, (((k + 1 : ℕ) : ℝ) * T ^ (k + 1)) * ‖a k‖ ^ 2)).continuousOn
  · simpa only [hc] using hE
  · rw [hc]
    exact ⟨hS.le, le_rfl⟩

end ErdosProblems.Erdos1041
