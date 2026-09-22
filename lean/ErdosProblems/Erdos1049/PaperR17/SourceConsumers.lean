import ErdosProblems.Erdos1049.PaperR17.Constants
import ErdosProblems.Erdos1049.IrrationalityExponentR11
import ErdosProblems.Erdos1049.PaperNoDecayR9

/-!
# The literal G02 supplier, the original R7 consumer, and the power-uniform measure

Proves F(a/b) irrational on the contour region and F((31/4)^r) irrational.
No source-supply, rate, nonvanishing or positivity hypothesis is left in the
source endpoints. Homogeneous evaluations use the actual pair width.
-/
namespace ErdosProblems.Erdos1049.PaperR17
open PaperR7 PaperR9 PaperR10 PaperR11 PaperR12 PaperR13 PaperR16
open Filter
open scoped Topology BigOperators
set_option maxHeartbeats 3000000

noncomputable def clearedA (a b n : ℕ) : ℤ :=
  homEval a b (pairWidth sourceU sourceV n) (sourceU n)
noncomputable def clearedB (a b n : ℕ) : ℤ :=
  homEval a b (pairWidth sourceU sourceV n) (sourceV n)
noncomputable def decayRate (a b : ℕ) : ℝ :=
  sourceC0R16 * Real.log a - sourceC1R16 * Real.log b
noncomputable def coefficientRate (a : ℕ) : ℝ := sourceDeltaR16 * Real.log a

lemma rational_base_gt_one (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    1 < (a : ℝ) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  apply (lt_div_iff₀ hbR).2
  simpa only [one_mul] using (show (b : ℝ) < a by exact_mod_cast hab)

lemma sourceU_le_width (n : ℕ) :
    (sourceU n).natDegree ≤ pairWidth sourceU sourceV n := le_max_left _ _
lemma sourceV_le_width (n : ℕ) :
    (sourceV n).natDegree ≤ pairWidth sourceU sourceV n := le_max_right _ _

theorem clearedA_cast (a b n : ℕ) (hb : 0 < b) :
    (clearedA a b n : ℝ) =
      (b : ℝ) ^ pairWidth sourceU sourceV n * sourceUEvalR16 ((a : ℝ) / b) n :=
  homEval_cast_eq_real_eval a b _ _ hb.ne' (sourceU_le_width n)

theorem clearedB_cast (a b n : ℕ) (hb : 0 < b) :
    (clearedB a b n : ℝ) =
      (b : ℝ) ^ pairWidth sourceU sourceV n * sourceVEvalR16 ((a : ℝ) / b) n :=
  homEval_cast_eq_real_eval a b _ _ hb.ne' (sourceV_le_width n)

/-- Both integer coordinates and the literal remainder occur in the same identity. -/
theorem cleared_error_identity (a b n : ℕ) (hb : 0 < b) :
    (clearedA a b n : ℝ) * paperLambert ((a : ℝ) / b) - clearedB a b n =
      (b : ℝ) ^ pairWidth sourceU sourceV n * sourceRemainderR16 ((a : ℝ) / b) n :=
  cleared_linear_form_identity a b _ _ _ _ hb.ne'
    (sourceU_le_width n) (sourceV_le_width n)

theorem cleared_error_pos (a b n : ℕ) (hb : 0 < b) (hab : b < a) :
    0 < (clearedA a b n : ℝ) * paperLambert ((a : ℝ) / b) - clearedB a b n := by
  rw [cleared_error_identity a b n hb]
  exact mul_pos (pow_pos (by exact_mod_cast hb) _)
    (actual_remainder_posR16 _ (rational_base_gt_one a b hb hab) n)

theorem cleared_error_rate (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    QuadLogRate
      (fun n => (clearedA a b n : ℝ) * paperLambert ((a : ℝ) / b) - clearedB a b n)
      (-decayRate a b) := by
  have h := actual_cleared_remainder_rateR16 (a : ℝ) (b : ℝ)
    (by exact_mod_cast hb) (by exact_mod_cast hab)
  have hc : sourceC1R16 * Real.log b - sourceC0R16 * Real.log a = -decayRate a b := by
    unfold decayRate
    ring
  rw [hc] at h
  exact quadLogRate_congrR16 h
    (Eventually.of_forall (fun n => (cleared_error_identity a b n hb).symm))

/-- Exact coefficient rate; a polynomial degree alone is not used as a lower bound. -/
theorem clearedA_rate (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    QuadLogRate (fun n => (clearedA a b n : ℝ)) (coefficientRate a) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have haR : (0 : ℝ) < a := by exact_mod_cast (hb.trans hab)
  have hp := rational_base_gt_one a b hb hab
  have hw := quadLogRate_powerR16 (pairWidth sourceU sourceV)
    sourceDeltaR16 (b : ℝ) hbR actual_pairWidth_rateR16
  have hu := actual_U_quadLogRateR16 ((a : ℝ) / b) hp
  have hn : ∀ᶠ n in atTop, (b : ℝ) ^ pairWidth sourceU sourceV n ≠ 0 :=
    Eventually.of_forall (fun n => pow_ne_zero _ hbR.ne')
  have h := quadLogRate_mulR16 hw hu hn
    (actual_U_eventually_nonzeroR16 ((a : ℝ) / b) hp)
  have hc : sourceDeltaR16 * Real.log b + sourceDeltaR16 * Real.log ((a : ℝ) / b) =
      coefficientRate a := by
    rw [Real.log_div haR.ne' hbR.ne']
    unfold coefficientRate
    ring
  rw [hc] at h
  exact quadLogRate_congrR16 h
    (Eventually.of_forall (fun n => (clearedA_cast a b n hb).symm))

/-- This is a witness of the original source-supply definition, not a replacement definition. -/
theorem actual_cancelled_supply (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) : CancelledApproximationSupply a b := by
  have hp := rational_base_gt_one a b hb hab
  have hd : 0 < decayRate a b := (region_iff_positive_decay a b hb hab).mp hr
  refine ⟨sourceU, sourceV, pairWidth sourceU sourceV,
    sourceU_le_width, sourceV_le_width, ?_, ?_⟩
  · exact Eventually.of_forall (fun n => (actual_remainder_posR16 _ hp n).ne')
  · have h := (cleared_error_rate a b hb hab).exp_upper.tendsto_zero
      (neg_neg_of_pos hd)
    simpa only [cleared_error_identity a b _ hb, sourceRemainderR16, polynomialRemainder] using h

/-- Closes exactly the R7 obligation named in the old paper coverage ledger. -/
theorem actual_contour_source_supply : ContourSourceSupply := by
  intro a b hb hab _hcop hr
  exact actual_cancelled_supply a b hb hab hr

/-- The paper's region, now with the supplier applied rather than assumed. -/
theorem rational_base_region (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) : Irrational (paperLambert ((a : ℝ) / b)) :=
  irrational_paperLambert_of_supply a b hb (actual_cancelled_supply a b hb hab hr)

theorem thirtyone_four_powers (r : ℕ) (hr : 0 < r) :
    Irrational (paperLambert (((31 : ℝ) / 4) ^ r)) :=
  thirtyone_four_powers_of_source_supply actual_contour_source_supply r hr

theorem thirtyone_four : Irrational (paperLambert ((31 : ℝ) / 4)) := by
  simpa using thirtyone_four_powers 1 (by norm_num)

lemma coefficientRate_nonneg (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    0 ≤ coefficientRate a := by
  have ha : 1 < a := by omega
  exact (mul_pos sourceDelta_posR16 (Real.log_pos (by exact_mod_cast ha))).le

lemma source_measure_quotient (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) :
    1 + coefficientRate a / decayRate a b = rationalBaseMeasureBound a b := by
  have ha : 1 < a := by omega
  have hla : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha)
  have hd : 0 < decayRate a b := (region_iff_positive_decay a b hb hab).mp hr
  have hd' : 0 < zudilinC0 * Real.log a - zudilinC1 * Real.log b := by
    simpa only [decayRate, supplier_C0_eq, supplier_C1_eq] using hd
  simpa only [coefficientRate, decayRate, supplier_delta_eq,
    supplier_C0_eq, supplier_C1_eq] using rate_quotient_eq_contour a b hla hd'

/-- Quantified rational separation, before taking a supremum of exponents. -/
theorem rational_base_approximation_upper (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) :
    ApproximationExponentUpper (paperLambert ((a : ℝ) / b)) (rationalBaseMeasureBound a b) := by
  have hd : 0 < decayRate a b := (region_iff_positive_decay a b hb hab).mp hr
  have h := approximationExponentUpper_of_quadratic_forms
    (clearedA a b) (clearedB a b) (paperLambert ((a : ℝ) / b))
    (coefficientRate a) (decayRate a b)
    (coefficientRate_nonneg a b hb hab) hd
    (Eventually.of_forall (fun n => (cleared_error_pos a b n hb hab).ne'))
    (clearedA_rate a b hb hab).exp_upper (cleared_error_rate a b hb hab)
  rwa [source_measure_quotient a b hb hab hr] at h

/-- The actual supremum definition from R11, not merely a named rate quotient. -/
theorem rational_base_measure (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) :
    irrationalityExponent (paperLambert ((a : ℝ) / b)) ≤ rationalBaseMeasureBound a b :=
  irrationalityExponent_le_of_exponentUpper (rational_base_approximation_upper a b hb hab hr)

theorem rational_base_extended_measure (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : ZudilinContourRegion a b) :
    extendedIrrationalityExponent (paperLambert ((a : ℝ) / b)) ≤
      (rationalBaseMeasureBound a b : EReal) :=
  extendedIrrationalityExponent_le_of_exponentUpper
    (rational_base_approximation_upper a b hb hab hr)

/-- The numerical bound is uniform in r; no uniform error constant is asserted. -/
theorem rational_base_power_measure (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : 0 < r) (hregion : ZudilinContourRegion a b) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      rationalBaseMeasureBound a b := by
  have h := rational_base_measure (a ^ r) (b ^ r) (Nat.pow_pos hb)
    (Nat.pow_lt_pow_left hab hr.ne') (zudilinContourRegion_pow a b r hr hregion)
  rw [rationalBaseMeasureBound_pow a b r hr] at h
  simpa only [Nat.cast_pow, div_pow] using h

theorem thirtyone_four_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301 :=
  (rational_base_power_measure 31 4 r (by norm_num) (by norm_num) hr
    thirtyoneFour_mem_zudilinContourRegion).trans_lt thirtyoneFour_measureBound_lt_301

theorem thirtyone_four_power_measure_lt_paper_fraction (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < (2981509 : ℝ) / 9909 :=
  (rational_base_power_measure 31 4 r (by norm_num) (by norm_num) hr
    thirtyoneFour_mem_zudilinContourRegion).trans_lt thirtyoneFour_measureBound_lt_paper_fraction

end ErdosProblems.Erdos1049.PaperR17
