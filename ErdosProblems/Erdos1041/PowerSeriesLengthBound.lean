import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import ErdosProblems.Erdos1041.CoefficientEnergyBound

/-!
# Length control by absolutely summable power-series coefficients

The coefficient indexed by `n` is the coefficient of the positive power
`z^(n+1)`. The derivative representation is an explicit almost-everywhere
`HasSum` hypothesis. No holomorphic continuation, injectivity, or existence of
an inverse branch is asserted here. The estimate is the termwise integration
step following equation (8) in the short #1041 paper.
-/

open MeasureTheory Filter Set ENNReal
open scoped Topology Interval

namespace ErdosProblems.Erdos1041

/-- An almost-everywhere sum of integrable complex functions is integrable
when the sum of their L1 norms is finite, with the expected triangle bound. -/
theorem integrable_and_integral_norm_le_of_hasSum
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → α → ℂ) (D : α → ℂ)
    (hF : ∀ n, Integrable (F n) μ)
    (hL1 : Summable (fun n => ∫ x, ‖F n x‖ ∂μ))
    (hD : ∀ᵐ x ∂μ, HasSum (fun n => F n x) (D x)) :
    Integrable D μ ∧ (∫ x, ‖D x‖ ∂μ) ≤ ∑' n, ∫ x, ‖F n x‖ ∂μ := by
  have hfinite : (∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ) ≠ ∞ := by
    have heq (n : ℕ) :
        ∫⁻ x, ‖F n x‖ₑ ∂μ = ‖∫ x, ‖F n x‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hF n).norm, coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (F n x)))]
      simp only [coe_nnnorm]
    rw [funext heq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <| NNReal.summable_coe.1 hL1.abs
  have hmeas (n : ℕ) : AEMeasurable (fun x => ‖F n x‖ₑ) μ := (hF n).1.enorm
  have hnormsum : ∀ᵐ x ∂μ, Summable (fun n => ‖F n x‖) := by
    rw [← lintegral_tsum hmeas] at hfinite
    refine (ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hfinite).mono ?_
    intro x hx
    change Summable (fun n => (‖F n x‖₊ : ℝ))
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  have hbound_int : Integrable (fun x => ∑' n, ‖F n x‖) μ := by
    refine ⟨?_, ?_⟩
    · simp_rw [← coe_nnnorm, ← NNReal.coe_tsum]
      rw [aestronglyMeasurable_iff_aemeasurable]
      apply AEMeasurable.coe_nnreal_real
      exact AEMeasurable.nnreal_tsum (fun n => (hF n).1.nnnorm.aemeasurable)
    · dsimp [HasFiniteIntegral]
      have hlt : (∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ) < ∞ := by
        rwa [lintegral_tsum hmeas, lt_top_iff_ne_top]
      convert hlt using 1
      apply lintegral_congr_ae
      simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm, NNReal.nnnorm_eq]
      filter_upwards [hnormsum] with x hx
      exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)
  have hDmeas : AEStronglyMeasurable D μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (fun k => (Finset.range k).aestronglyMeasurable_fun_sum (fun n _ => (hF n).1))
    filter_upwards [hD] with x hx using hx.tendsto_sum_nat
  have hbound : ∀ᵐ x ∂μ, ‖D x‖ ≤ ∑' n, ‖F n x‖ := by
    filter_upwards [hD, hnormsum] with x hx hs
    exact hx.norm_le_of_bounded hs.hasSum (fun _ => le_rfl)
  have hDi := hbound_int.mono' hDmeas hbound
  refine ⟨hDi, (integral_mono_ae hDi.norm hbound_int hbound).trans_eq ?_⟩
  exact (integral_tsum_of_summable_integral_norm
    (fun n => (hF n).norm) (by simpa only [norm_norm] using hL1)).symm

/-- The exact scalar integral accounting for the factor two. -/
theorem integral_abs_pow_neg_one_one (n : ℕ) :
    (∫ x : ℝ in (-1)..1, |x| ^ n) = 2 / (n + 1 : ℝ) := by
  have hc : Continuous (fun x : ℝ => |x| ^ n) := continuous_abs.pow n
  have hp : (∫ x : ℝ in 0..1, |x| ^ n) = 1 / (n + 1 : ℝ) := by
    calc
      _ = ∫ x : ℝ in 0..1, x ^ n := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
        dsimp
        rw [abs_of_nonneg hx.1]
      _ = _ := by simp
  have hn : (∫ x : ℝ in (-1)..0, |x| ^ n) = ∫ x : ℝ in 0..1, |x| ^ n := by
    simpa only [neg_zero, abs_neg] using
      (intervalIntegral.integral_comp_neg (f := fun x : ℝ => |x| ^ n)
        (a := 0) (b := 1)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1), hn, hp]
  ring

/-- The derivative of the monomial with coefficient `a` has L1 norm `2‖a‖`. -/
theorem integral_norm_derivative_monomial (a : ℂ) (n : ℕ) :
    (∫ x : ℝ in (-1)..1, ‖((n + 1 : ℕ) : ℂ) * a * (x : ℂ) ^ n‖) =
      2 * ‖a‖ := by
  simp only [norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs]
  rw [intervalIntegral.integral_const_mul, integral_abs_pow_neg_one_one]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  <;> ring

/-- The termwise-integration estimate for an explicitly represented derivative
series. In an analytic application `D x = Z' x` and `a n` is the coefficient
of `z^(n+1)`; proving that representation is a separate obligation. -/
theorem powerSeries_derivative_integrable_and_length_le
    (a : ℕ → ℂ) (D : ℝ → ℂ) (ha : Summable (fun n => ‖a n‖))
    (hD : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioc (-1 : ℝ) 1),
      HasSum (fun n => ((n + 1 : ℕ) : ℂ) * a n * (x : ℂ) ^ n) (D x)) :
    IntervalIntegrable D volume (-1) 1 ∧
      (∫ x : ℝ in (-1)..1, ‖D x‖) ≤ 2 * ∑' n, ‖a n‖ := by
  let F : ℕ → ℝ → ℂ := fun n x => ((n + 1 : ℕ) : ℂ) * a n * (x : ℂ) ^ n
  have hF (n : ℕ) : IntegrableOn (F n) (Ioc (-1 : ℝ) 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).1
    exact (show Continuous (F n) by fun_prop).intervalIntegrable _ _
  have hFi (n : ℕ) : (∫ x in Ioc (-1 : ℝ) 1, ‖F n x‖) = 2 * ‖a n‖ := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact integral_norm_derivative_monomial (a n) n
  have hs : Summable (fun n => ∫ x in Ioc (-1 : ℝ) 1, ‖F n x‖) := by
    simpa only [hFi] using ha.mul_left 2
  obtain ⟨hDi, hle⟩ := integrable_and_integral_norm_le_of_hasSum F D hF hs hD
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 hDi, ?_⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simpa only [hFi, tsum_mul_left] using hle

/-- The analytic length estimate from energy bounds at smaller radii.  This
combines finite-energy closure, logarithmic Cauchy--Schwarz and termwise
integration.  Inverse-branch existence and its derivative representation
remain explicit inputs, as does the geometric producer of the energy bound. -/
theorem powerSeries_length_le_log_of_subradius_energy
    (a : ℕ → ℂ) (D : ℝ → ℂ) (E : ℝ → ℝ) {S : ℝ} (hS : 1 < S)
    (hE : ContinuousOn E (Icc 1 S))
    (henergy : ∀ T ∈ Ioo 1 S, ∀ s : Finset ℕ,
      ∑ k ∈ s, (((k + 1 : ℕ) : ℝ) * T ^ (k + 1)) * ‖a k‖ ^ 2 ≤ E T)
    (hD : ∀ᵐ (x : ℝ) ∂volume.restrict (Ioc (-1 : ℝ) 1),
      HasSum (fun n => ((n + 1 : ℕ) : ℂ) * a n * (x : ℂ) ^ n) (D x)) :
    IntervalIntegrable D volume (-1) 1 ∧
      (∫ x : ℝ in (-1)..1, ‖D x‖) ≤
        2 * Real.sqrt (E S * Real.log (S / (S - 1))) := by
  obtain ⟨ha, hcoeff⟩ := log_bound_of_subradius_coefficient_energy a E hS hE henergy
  obtain ⟨hint, hlength⟩ := powerSeries_derivative_integrable_and_length_le a D ha hD
  exact ⟨hint, hlength.trans (mul_le_mul_of_nonneg_left hcoeff (by norm_num))⟩

end ErdosProblems.Erdos1041
