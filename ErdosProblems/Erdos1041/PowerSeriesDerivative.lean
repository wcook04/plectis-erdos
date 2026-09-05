import ErdosProblems.Erdos1041.PowerSeriesLengthBound
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Termwise differentiation and length of an absolutely convergent power series

The coefficient `a n` multiplies `z^(n+1)`. Absolute summability of the
coefficients gives termwise differentiation strictly inside the unit disk.
Restricting to the real interval supplies the derivative-series representation
needed by `PowerSeriesLengthBound`, without any endpoint differentiability
assumption. This does not construct the inverse branch in the #1041 paper.
-/

open MeasureTheory Filter Set Metric
open scoped Topology Interval

namespace ErdosProblems.Erdos1041

/-- The positive-power series, with its constant term omitted. -/
noncomputable def positivePowerSeries (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' n, a n * z ^ (n + 1)

/-- A summable coefficient family defines a differentiable function throughout
the open unit disk, and both the original and derivative series converge. -/
theorem positivePowerSeries_hasDerivAt
    (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖))
    {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => a n * z ^ (n + 1)) ∧
    Summable (fun n => ((n + 1 : ℕ) : ℂ) * a n * z ^ n) ∧
    HasDerivAt (positivePowerSeries a)
      (∑' n, ((n + 1 : ℕ) : ℂ) * a n * z ^ n) z := by
  obtain ⟨r, hzr, hr1⟩ := exists_between hz
  have hr0 : 0 < r := (norm_nonneg z).trans_lt hzr
  have hrnorm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0.le]
  let A : ℝ := ∑' n, ‖a n‖
  have hA : 0 ≤ A := tsum_nonneg (fun _ => norm_nonneg _)
  have hcoeff (n : ℕ) : ‖a n‖ ≤ A :=
    ha.le_tsum n (fun j _ => norm_nonneg (a j))
  let u : ℕ → ℝ := fun n => (n + 1 : ℝ) * A * r ^ n
  have hu : Summable u := by
    have hgeom : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hr0.le hr1
    have hpoly : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
      simpa only [pow_one] using
        summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm
    convert (hpoly.add hgeom).mul_left A using 1
    ext n
    dsimp [u]
    ring
  let g : ℕ → ℂ → ℂ := fun n y => a n * y ^ (n + 1)
  let g' : ℕ → ℂ → ℂ := fun n y => ((n + 1 : ℕ) : ℂ) * a n * y ^ n
  have hg (n : ℕ) (y : ℂ) (_hy : y ∈ ball (0 : ℂ) r) :
      HasDerivAt (g n) (g' n y) y := by
    simpa [g, g', mul_assoc, mul_left_comm, mul_comm] using
      ((hasDerivAt_id y).pow (n + 1)).const_mul (a n)
  have hbound (n : ℕ) (y : ℂ) (hy : y ∈ ball (0 : ℂ) r) :
      ‖g' n y‖ ≤ u n := by
    have hyr : ‖y‖ ≤ r := by
      exact (by simpa only [mem_ball, dist_zero_right] using hy : ‖y‖ < r).le
    calc
      ‖g' n y‖ = (n + 1 : ℝ) * ‖a n‖ * ‖y‖ ^ n := by
        change ‖((n + 1 : ℕ) : ℂ) * a n * y ^ n‖ = _
        rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
        simp only [Nat.cast_add, Nat.cast_one]
      _ ≤ (n + 1 : ℝ) * A * r ^ n := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hcoeff n) (by positivity)
        · exact pow_le_pow_left₀ (norm_nonneg y) hyr n
        · positivity
        · positivity
      _ = u n := rfl
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) r := by simpa using hr0
  have hzmem : z ∈ ball (0 : ℂ) r := by
    simpa only [mem_ball, dist_zero_right] using hzr
  have hsumzero : Summable (fun n => g n 0) := by
    simpa only [g, zero_pow (Nat.succ_ne_zero _), mul_zero] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℂ)))
  refine ⟨?_, ?_, ?_⟩
  · exact summable_of_summable_hasDerivAt_of_isPreconnected
      (g := g) (g' := g') (t := ball (0 : ℂ) r) (y₀ := 0) (y := z) hu isOpen_ball
      isPreconnected_ball hg hbound hzero hsumzero hzmem
  · exact hu.of_norm_bounded (fun n => hbound n z hzmem)
  · exact hasDerivAt_tsum_of_isPreconnected
      (g := g) (g' := g') (t := ball (0 : ℂ) r) (y₀ := 0) (y := z) hu isOpen_ball isPreconnected_ball
      hg hbound hzero hsumzero hzmem

/-- The derivative series represents the actual derivative along the real
segment almost everywhere. The endpoint `1` has zero Lebesgue measure. -/
theorem positivePowerSeries_derivative_hasSum_ae
    (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    ∀ᵐ (x : ℝ) ∂volume.restrict (Ioc (-1 : ℝ) 1),
      HasSum (fun n => ((n + 1 : ℕ) : ℂ) * a n * (x : ℂ) ^ n)
        (deriv (fun t : ℝ => positivePowerSeries a (t : ℂ)) x) := by
  refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hxnorm : ‖(x : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using (abs_lt.mpr hx)
  obtain ⟨_, hsum, hderiv⟩ := positivePowerSeries_hasDerivAt a ha hxnorm
  rw [hderiv.comp_ofReal.deriv]
  exact hsum.hasSum

/-- The actual real derivative of the power series is interval integrable and
its length integral is bounded by twice the coefficient norm sum. -/
theorem positivePowerSeries_length_le
    (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) :
    IntervalIntegrable (deriv (fun t : ℝ => positivePowerSeries a (t : ℂ)))
      volume (-1) 1 ∧
    (∫ x : ℝ in (-1)..1,
      ‖deriv (fun t : ℝ => positivePowerSeries a (t : ℂ)) x‖) ≤
      2 * ∑' n, ‖a n‖ := by
  exact powerSeries_derivative_integrable_and_length_le a _ ha
    (positivePowerSeries_derivative_hasSum_ae a ha)

/-- Energy bounds at all smaller radii control the length integral of the
actual power series. Neither coefficient summability nor derivative-series
identification is assumed: both follow from the energy bounds. -/
theorem positivePowerSeries_length_le_of_subradius_energy
    (a : ℕ → ℂ) (E : ℝ → ℝ) {S : ℝ} (hS : 1 < S)
    (hE : ContinuousOn E (Icc 1 S))
    (henergy : ∀ T ∈ Ioo 1 S, ∀ s : Finset ℕ,
      ∑ k ∈ s, (((k + 1 : ℕ) : ℝ) * T ^ (k + 1)) * ‖a k‖ ^ 2 ≤ E T) :
    IntervalIntegrable (deriv (fun t : ℝ => positivePowerSeries a (t : ℂ)))
      volume (-1) 1 ∧
    (∫ x : ℝ in (-1)..1,
      ‖deriv (fun t : ℝ => positivePowerSeries a (t : ℂ)) x‖) ≤
        2 * Real.sqrt (E S * Real.log (S / (S - 1))) := by
  have ha := (log_bound_of_subradius_coefficient_energy a E hS hE henergy).1
  exact powerSeries_length_le_log_of_subradius_energy a _ E hS hE henergy
    (positivePowerSeries_derivative_hasSum_ae a ha)

end ErdosProblems.Erdos1041
