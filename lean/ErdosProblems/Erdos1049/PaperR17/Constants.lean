import ErdosProblems.Erdos1049.G02SourceRatesR16
import ErdosProblems.Erdos1049.MeasureConstantsR10
import ErdosProblems.Erdos1049.FirstNewBaseR10

/-!
# Exact identification of the supplier and retained-paper constants

Each theorem identifies a supplier constant with a retained-paper constant.
These are equalities of the literal definitions, not decimal comparisons.
-/
namespace ErdosProblems.Erdos1049.PaperR17
open PaperR9 PaperR10 PaperR11 PaperR12 PaperR16
open scoped BigOperators Topology
open Filter
set_option maxHeartbeats 4000000

@[simp] theorem supplier_trigamma_eq (u : ℝ) :
    trigammaSeriesR16 u = trigammaSeries u := rfl

/-- The finite-set enumeration and the printed ordered sum are exactly equal. -/
@[simp] theorem supplier_J_eq : sourceJR16 = zudilinJ := by
  norm_num [sourceJR16, sourceIntervals, zudilinJ, zudilinJTerm,
    trigammaSeriesR16, trigammaSeries]
  <;> ring

@[simp] theorem supplier_C1_eq : sourceC1R16 = zudilinC1 := rfl

@[simp] theorem supplier_C0_eq : sourceC0R16 = zudilinC0 := by
  unfold sourceC0R16 sourceGammaR16 totientConstantR16 zudilinC0
  rw [supplier_J_eq]

@[simp] theorem supplier_delta_eq :
    sourceDeltaR16 = zudilinC1 - zudilinC0 := by
  unfold sourceDeltaR16
  rw [supplier_C1_eq, supplier_C0_eq]

/-- No threshold defined from rounded digits is introduced. -/
theorem supplier_threshold_eq :
    sourceC0R16 / sourceC1R16 = zudilinContour := by
  rw [supplier_C0_eq, supplier_C1_eq]
  rfl

theorem supplier_gamma_pos : 0 < sourceGammaR16 := by
  unfold sourceGammaR16 totientConstantR16
  rw [supplier_J_eq]
  exact mul_pos (div_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
    (sub_pos.mpr zudilinJ_lt)

theorem supplier_C0_lt_266 : sourceC0R16 < 266 := by
  unfold sourceC0R16
  linarith [supplier_gamma_pos]

theorem supplier_delta_gt_C0 : sourceC0R16 < sourceDeltaR16 := by
  have h := supplier_C0_lt_266
  unfold sourceDeltaR16 sourceC1R16
  linarith

/-- Exact first-block sum used in the short paper. -/
theorem first_block_sum_exact :
    sourceJPrefixR16 1 = (2015640690251 : ℝ) / 25971865920 := by
  norm_num [sourceJPrefixR16, sourceIntervals, blockKernelR16,
    Finset.sum_range_succ]

/-- Both exact thresholds in the statement are the same strict inequality. -/
theorem region_iff_positive_decay (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    ZudilinContourRegion a b ↔
      0 < sourceC0R16 * Real.log a - sourceC1R16 * Real.log b := by
  have ha : 1 < a := by omega
  have hla : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha)
  have hC1 : 0 < sourceC1R16 := by unfold sourceC1R16; norm_num
  change Real.log b / Real.log a < zudilinContour ↔ _
  rw [← supplier_threshold_eq, div_lt_div_iff₀ hla hC1]
  constructor <;> intro h <;> nlinarith

theorem supplier_threshold_bounds :
    (81 : ℝ) / 200 < sourceC0R16 / sourceC1R16 ∧
      sourceC0R16 / sourceC1R16 < 1 / 2 := by
  rw [supplier_threshold_eq]
  exact ⟨eightyOne_twoHundredths_lt_zudilinContour, zudilinContour_lt_half⟩

/-- The 3/2 source's cleared exponent is strictly positive, not merely nonnegative. -/
theorem three_halves_cleared_rate_pos :
    0 < sourceC1R16 * Real.log 2 - sourceC0R16 * Real.log 3 := by
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hC1 : 0 < sourceC1R16 := by unfold sourceC1R16; norm_num
  have hratio : sourceC0R16 / sourceC1R16 < Real.log 2 / Real.log 3 :=
    supplier_threshold_bounds.2.trans half_lt_threeHalves_log_ratio
  have h := (div_lt_div_iff₀ hC1 hlog3).mp hratio
  nlinarith

end ErdosProblems.Erdos1049.PaperR17
