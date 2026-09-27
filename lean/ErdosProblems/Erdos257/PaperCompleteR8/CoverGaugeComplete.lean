import ErdosProblems.Erdos257.PaperCompleteR8.CoverScalarGauge
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib

/-!
# Complete scalar minimisation, sharp power-of-two bound and asymptotic

The existing infimum and small branch are imported without modification.
The large-parameter minimum follows from real Bernoulli's inequality, so
there is no differentiation of an infimum or unproved minimiser premise.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperCompleteR8
open Filter
open ErdosProblems.Erdos257.PaperCompleteR7

/-- The base-two logarithmic parameter, with exactly the paper's normalisation. -/
def coverLogParameter (t : ℝ) : ℝ := Real.log t / Real.log 2

def coverLargeMinimizer (t : ℝ) : ℝ :=
  Real.log (coverLogParameter t / (coverLogParameter t - 1)) / Real.log 2

def coverLargeValue (u : ℝ) : ℝ := (u / (u - 1)) ^ u * (u - 1)

private theorem log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

/-- Bernoulli's supporting-line inequality identifies the global minimum. -/
theorem optimal_power_quotient {u x : ℝ} (hu : 1 < u) (hx : 1 < x) :
    coverLargeValue u ≤ x ^ u / (x - 1) := by
  let a : ℝ := u / (u - 1)
  have hu0 : 0 < u := by linarith
  have hv : 0 < u - 1 := sub_pos.mpr hu
  have ha : 0 < a := div_pos hu0 hv
  have hy : 0 < x / a := div_pos (by linarith) ha
  have hB := _root_.one_add_mul_self_le_rpow_one_add
    (s := x / a - 1) (by linarith : -1 ≤ x / a - 1) hu.le
  have hbase : 1 + (x / a - 1) = x / a := by ring
  have hline : 1 + u * (x / a - 1) = (u - 1) * (x - 1) := by
    dsimp [a]
    field_simp [hu0.ne', hv.ne']
    <;> ring
  rw [hbase, hline, Real.div_rpow (by linarith : 0 ≤ x) ha.le] at hB
  have haPow : 0 < a ^ u := Real.rpow_pos_of_pos ha u
  have hm := (le_div_iff₀ haPow).mp hB
  apply (le_div_iff₀ (sub_pos.mpr hx)).mpr
  change a ^ u * (u - 1) * (x - 1) ≤ x ^ u
  nlinarith only [hm]

theorem coverLargeValue_eq_quotient {u : ℝ} (hu : 1 < u) :
    coverLargeValue u = u ^ u / (u - 1) ^ (u - 1) := by
  have hu0 : 0 < u := by linarith
  have hv : 0 < u - 1 := sub_pos.mpr hu
  have hp : (u - 1) ^ (u - 1) = (u - 1) ^ u / (u - 1) := by
    rw [Real.rpow_sub hv, Real.rpow_one]
  rw [coverLargeValue, Real.div_rpow hu0.le hv.le, hp]
  field_simp [hv.ne', (Real.rpow_pos_of_pos hv u).ne']
  <;> ring

/-- Convert the original real-power cost, not a surrogate objective. -/
theorem scalar_cost_log_parameter {t α : ℝ} (ht : 0 < t) :
    t ^ α / ((2 : ℝ) ^ α - 1) =
      ((2 : ℝ) ^ α) ^ coverLogParameter t / ((2 : ℝ) ^ α - 1) := by
  congr 1
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold coverLogParameter
  field_simp [log_two_pos.ne']
  <;> ring

theorem coverLogParameter_gt_two {t : ℝ} (ht : 4 < t) :
    2 < coverLogParameter t := by
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 4) ht
  have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hfour] at hlog
  exact (lt_div_iff₀ log_two_pos).mpr hlog

/-- The minimiser is genuinely inside the admissible interval. -/
theorem coverLargeMinimizer_bounds {t : ℝ} (ht : 4 < t) :
    0 < coverLargeMinimizer t ∧ coverLargeMinimizer t < 1 := by
  let u := coverLogParameter t
  have hu : 2 < u := coverLogParameter_gt_two ht
  have hv : 0 < u - 1 := by linarith
  have hratio1 : 1 < u / (u - 1) := (lt_div_iff₀ hv).mpr (by linarith)
  have hratio2 : u / (u - 1) < 2 := (div_lt_iff₀ hv).mpr (by linarith)
  constructor
  · exact div_pos (Real.log_pos hratio1) log_two_pos
  · apply (div_lt_iff₀ log_two_pos).mpr
    simpa only [one_mul] using Real.log_lt_log (by linarith : 0 < u / (u - 1)) hratio2

theorem two_rpow_coverLargeMinimizer {t : ℝ} (ht : 4 < t) :
    (2 : ℝ) ^ coverLargeMinimizer t =
      coverLogParameter t / (coverLogParameter t - 1) := by
  have hu := coverLogParameter_gt_two ht
  have hp : 0 < coverLogParameter t / (coverLogParameter t - 1) :=
    div_pos (by linarith) (by linarith)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  unfold coverLargeMinimizer
  have he : Real.log 2 *
      (Real.log (coverLogParameter t / (coverLogParameter t - 1)) / Real.log 2) =
      Real.log (coverLogParameter t / (coverLogParameter t - 1)) := by
    field_simp [log_two_pos.ne']
  rw [he, Real.exp_log hp]

/-- Equality at the minimiser; in particular the infimum is attained. -/
theorem scalar_cost_at_large_minimizer {t : ℝ} (ht : 4 < t) :
    t ^ coverLargeMinimizer t / ((2 : ℝ) ^ coverLargeMinimizer t - 1) =
      coverLargeValue (coverLogParameter t) := by
  rw [scalar_cost_log_parameter (by linarith : 0 < t), two_rpow_coverLargeMinimizer ht]
  have hu := coverLogParameter_gt_two ht
  have hv : coverLogParameter t - 1 ≠ 0 := by linarith
  have hd : coverLogParameter t / (coverLogParameter t - 1) - 1 =
      1 / (coverLogParameter t - 1) := by field_simp [hv] <;> ring
  rw [hd, coverLargeValue]
  field_simp [hv]
  <;> ring

theorem coverGauge_eq_largeValue {t : ℝ} (ht : 4 < t) :
    coverGauge t = coverLargeValue (coverLogParameter t) := by
  have ht0 : 0 < t := by linarith
  have hα := coverLargeMinimizer_bounds ht
  apply le_antisymm
  · exact (coverGauge_le_cost ht0.le hα.1 hα.2.le).trans_eq
      (scalar_cost_at_large_minimizer ht)
  · rw [coverGauge, if_neg ht0.ne']
    apply le_csInf (scalarCoverCosts_nonempty t)
    rintro _ ⟨α, hα0, hα1, rfl⟩
    rw [scalar_cost_log_parameter ht0]
    exact optimal_power_quotient (by have := coverLogParameter_gt_two ht; linarith)
      (Real.one_lt_rpow (by norm_num) hα0)

/-- Exact large branch in the paper's displayed form. -/
theorem coverGauge_eq_large {t : ℝ} (ht : 4 < t) :
    coverGauge t = (coverLogParameter t) ^ (coverLogParameter t) /
      (coverLogParameter t - 1) ^ (coverLogParameter t - 1) := by
  rw [coverGauge_eq_largeValue ht, coverLargeValue_eq_quotient]
  have := coverLogParameter_gt_two ht
  linarith

@[simp] theorem coverLargeValue_two : coverLargeValue 2 = 4 := by
  norm_num [coverLargeValue]

/-- A sharp lower bound useful on divisor cubes, including ranks zero and one. -/
theorem exp_one_mul_sub_one_le_coverGauge_two_rpow (z : ℝ) :
    Real.exp 1 * (z - 1) ≤ coverGauge ((2 : ℝ) ^ z) := by
  have ht : 0 < (2 : ℝ) ^ z := Real.rpow_pos_of_pos (by norm_num) z
  by_cases hz : z ≤ 1
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos 1).le (sub_nonpos.mpr hz)).trans
      (coverGauge_nonneg ht.le)
  have hz1 : 1 < z := lt_of_not_ge hz
  rw [coverGauge, if_neg ht.ne']
  apply le_csInf (scalarCoverCosts_nonempty _)
  rintro _ ⟨α, hα, hα1, rfl⟩
  let β := Real.log 2 * α
  have hβ : 0 < β := mul_pos log_two_pos hα
  have hd : 0 < Real.exp β - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hβ)
  have hD : Real.exp β - 1 ≤ β * Real.exp β := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-β)) (Real.exp_pos β).le
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
    nlinarith only [h]
  have hT := exp_one_mul_le_exp (mul_pos hβ (sub_pos.mpr hz1))
  have hTm := mul_le_mul_of_nonneg_right hT (Real.exp_pos β).le
  have he : Real.exp (β * (z - 1)) * Real.exp β = Real.exp (β * z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hTm
  have hscale := mul_le_mul_of_nonneg_left hD
    (mul_nonneg (Real.exp_pos 1).le (sub_pos.mpr hz1).le)
  have hpow : ((2 : ℝ) ^ z) ^ α = Real.exp (β * z) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [β]
    ring
  have hb : (2 : ℝ) ^ α = Real.exp β := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [hpow, hb]
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hTm, hscale]

/-- Elementary two-sided logarithm bound, avoiding an implicit l'Hôpital step. -/
theorem log_one_add_inv_squeeze {u : ℝ} (hu : 1 < u) :
    1 - 1 / u ≤ (u - 1) * Real.log (1 + 1 / (u - 1)) ∧
      (u - 1) * Real.log (1 + 1 / (u - 1)) ≤ 1 := by
  have hv : 0 < u - 1 := sub_pos.mpr hu
  have hu0 : 0 < u := by linarith
  let x : ℝ := 1 + 1 / (u - 1)
  have hx : 0 < x := by dsimp [x]; positivity
  have hU := Real.log_le_sub_one_of_pos hx
  have hL := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hL
  have hUm := mul_le_mul_of_nonneg_left hU hv.le
  have hLm := mul_le_mul_of_nonneg_left hL hv.le
  have hUx : (u - 1) * (x - 1) = 1 := by
    dsimp [x]
    field_simp [hv.ne']
    <;> ring
  have hLx : (u - 1) * (1 - x⁻¹) = 1 - 1 / u := by
    dsimp [x]
    field_simp [hv.ne', hu0.ne']
    <;> ring
  constructor
  · change 1 - 1 / u ≤ (u - 1) * Real.log x
    rw [← hLx]
    nlinarith only [hLm]
  · change (u - 1) * Real.log x ≤ 1
    exact hUm.trans_eq hUx

theorem tendsto_large_log_factor :
    Tendsto (fun u : ℝ => (u - 1) * Real.log (1 + 1 / (u - 1)))
      atTop (nhds 1) := by
  have hi : Tendsto (fun u : ℝ => (1 : ℝ) / u) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hl : Tendsto (fun u : ℝ => 1 - 1 / u) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    exact (log_one_add_inv_squeeze hu).1
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    exact (log_one_add_inv_squeeze hu).2

theorem coverLargeValue_div_parameter {u : ℝ} (hu : 1 < u) :
    coverLargeValue u / u = Real.exp ((u - 1) * Real.log (1 + 1 / (u - 1))) := by
  have hu0 : 0 < u := by linarith
  have hv : 0 < u - 1 := sub_pos.mpr hu
  let a : ℝ := u / (u - 1)
  have ha : 0 < a := div_pos hu0 hv
  have he : a = 1 + 1 / (u - 1) := by
    dsimp [a]
    field_simp [hv.ne']
    <;> ring
  have hsplit : a ^ u = a ^ (u - 1) * a := by
    calc
      a ^ u = a ^ ((u - 1) + 1) := by congr 1; ring
      _ = a ^ (u - 1) * a ^ (1 : ℝ) := Real.rpow_add ha _ _
      _ = a ^ (u - 1) * a := by rw [Real.rpow_one]
  change a ^ u * (u - 1) / u = _
  rw [hsplit]
  have heq : a * (u - 1) / u = 1 := by
    dsimp [a]
    field_simp [hv.ne', hu0.ne']
  calc
    a ^ (u - 1) * a * (u - 1) / u = a ^ (u - 1) * (a * (u - 1) / u) := by ring
    _ = a ^ (u - 1) := by rw [heq, mul_one]
    _ = Real.exp ((u - 1) * Real.log (1 + 1 / (u - 1))) := by
      rw [Real.rpow_def_of_pos ha, he]
      congr 1
      ring

theorem tendsto_coverLargeValue_div_parameter :
    Tendsto (fun u : ℝ => coverLargeValue u / u) atTop (nhds (Real.exp 1)) := by
  apply (Real.continuous_exp.tendsto 1 |>.comp tendsto_large_log_factor).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
  exact (coverLargeValue_div_parameter hu).symm

/-- Psi(t)/(e log_2 t) tends to one, with no omitted constant or base change. -/
theorem tendsto_coverGauge_div_exp_logTwo :
    Tendsto (fun t : ℝ => coverGauge t / (Real.exp 1 * coverLogParameter t))
      atTop (nhds 1) := by
  have hu : Tendsto coverLogParameter atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro R
    filter_upwards [Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (R * Real.log 2))] with t ht
    exact (le_div_iff₀ log_two_pos).mpr ht
  have hh := tendsto_coverLargeValue_div_parameter.comp hu
  have hd := hh.div_const (Real.exp 1)
  have hlim : Tendsto (fun t : ℝ => coverLargeValue (coverLogParameter t) /
      coverLogParameter t / Real.exp 1) atTop (nhds 1) := by
    simpa only [div_self (Real.exp_pos 1).ne'] using hd
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (4 : ℝ)] with t ht
  rw [coverGauge_eq_largeValue ht]
  ring

end ErdosProblems.Erdos257.PaperCompleteR8
end
