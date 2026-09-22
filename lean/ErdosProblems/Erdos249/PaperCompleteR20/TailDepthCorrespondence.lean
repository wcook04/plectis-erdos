import ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates
import Erdos249257.LcmConeFlatness
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257 Erdos249257.TotientTailPeriodKiller

theorem prefix_fractional_part (N : ℕ) :
    Int.fract ((2 : ℝ)^N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2^n)) =
      Int.fract (totientTail N) := by
  rw [two_pow_mul_totient_series_eq, Int.fract_natCast_add]

theorem totient_scaled_truncation_error (h N L : ℕ) :
    |(2 : ℝ)^L * (totientTail (N+h) - totientTail N) -
      (windowDiscrepancy h N L : ℝ)| ≤ (N : ℝ)+h+L+2 := by
  simpa [binaryCoeffTail, totientTail, GenericTailCertificates.discrepancy,
    windowDiscrepancy, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    GenericTailCertificates.truncation_error_bound Nat.totient Nat.totient_le h N L

theorem certificate_logarithmic_depth {h N L : ℕ} (hc : certifiedKill h N L) :
    1 + Real.logb 2 ((N : ℝ)+h+L+2) < L := by
  have hf := certifiedKill_depth_floor hc
  have hr : (2 : ℝ)*((N : ℝ)+h+L+2) < 2^L := by exact_mod_cast hf
  have hp : (0 : ℝ) < (N : ℝ)+h+L+2 := by positivity
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ)<2) (by positivity) hr
  rw [Real.logb_mul (by norm_num) hp.ne', Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at hl
  simpa using hl

theorem fixed_depth_bounds_indices {h N L : ℕ} (hc : certifiedKill h N L) :
    N + h < 2^L := by
  have hf := certifiedKill_depth_floor hc
  have hn : 2 * (N+h+L+2) < 2^L := by exact_mod_cast hf
  omega

end ErdosProblems.Erdos249.PaperCompleteR20
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.prefix_fractional_part
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.totient_scaled_truncation_error
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.certificate_logarithmic_depth
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.fixed_depth_bounds_indices
#print axioms Erdos249257.TotientTailPeriodKiller.two_pow_mul_totient_series_eq
#print axioms Erdos249257.TotientTailPeriodKiller.tail_diff_mem_int_iff_scaled_series_mem_int
#print axioms Erdos249257.TotientTailPeriodKiller.certifiedKill_depth_floor
#print axioms Erdos249257.TotientTailPeriodKiller.tail_diff_notMem_int_of_certifiedKill
