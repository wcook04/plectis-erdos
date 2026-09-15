import ErdosProblems.Erdos1049.ActualSourceResiduesR14
import ErdosProblems.Erdos1049.SourcePositiveHBoundsR10
import Mathlib

/-!
# The actual analytic identity A_n F - B_n = H_n

Proves A_n F - B_n = H_n for the literal source at every 0 < q < 1.

The proof uses the actual residues, proves that the first 12*n terms vanish,
and shifts the absolutely convergent series. The last Pochhammer has length
13*n+1, including n=0. No source identity or summability assertion is assumed.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset
open PaperR10 PaperR11 PaperR12
open scoped BigOperators

lemma power_quotient_eq (q : ℝ) (hq : q ≠ 0) {a b : ℕ} (h : b ≤ a) :
    q ^ a / q ^ b = q ^ (a - b) := by
  rw [div_eq_mul_inv, ← inv_pow]
  simpa only [mul_comm] using inverse_power_mul_power q hq h

lemma source_shifted_pole (q : ℝ) (hq : q ≠ 0) (n s t : ℕ) :
    q ^ (14 * n + 1 + s) * (q ^ t / q ^ (12 * n)) =
      q ^ (2 * n + s + 1 + t) := by
  rw [← mul_div_assoc, ← pow_add, power_quotient_eq q hq (by omega)]
  congr 1
  omega

lemma source_shifted_residue_power (q : ℝ) (hq : q ≠ 0) (n s t : ℕ) :
    (q ^ ((14 * n + 1) * t) / q ^ ((14 * n + 1) * (12 * n))) *
      q ^ ((14 * n + 1) * (14 * n + 1 + s)) =
        q ^ ((14 * n + 1) * (2 * n + s + 1 + t)) := by
  rw [div_mul_eq_mul_div, ← pow_add]
  have hle : (14 * n + 1) * (12 * n) ≤
      (14 * n + 1) * t + (14 * n + 1) * (14 * n + 1 + s) := by nlinarith
  rw [power_quotient_eq q hq hle]
  congr 1
  have he : (14 * n + 1) * t + (14 * n + 1) * (14 * n + 1 + s) =
      (14 * n + 1) * (12 * n) + (14 * n + 1) * (2 * n + s + 1 + t) := by ring
  omega

noncomputable def sourceExtendedKernelTerm (q : ℝ) (n t : ℕ) : ℝ :=
  (q ^ ((14 * n + 1) * t) / q ^ ((14 * n + 1) * (12 * n))) *
    sourceRationalKernel q n (q ^ t / q ^ (12 * n))

lemma sourcePoleSeriesTerm_eq_extended {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (n t : ℕ) : sourcePoleSeriesTerm q n t = sourceExtendedKernelTerm q n t := by
  have hz : ∀ s ∈ range (13 * n + 1),
      1 - q ^ (14 * n + 1 + s) * (q ^ t / q ^ (12 * n)) ≠ 0 := by
    intro s hs
    rw [source_shifted_pole q hq0.ne']
    exact (sub_pos.mpr
      (positive_shift_power_lt_one hq0 hq1 (2 * n + s + 1 + t) (by omega))).ne'
  unfold sourceExtendedKernelTerm
  rw [actual_source_partial_fractions hq0 hq1 n _ hz, mul_sum]
  unfold sourcePoleSeriesTerm
  apply sum_congr rfl
  intro s hs
  rw [source_shifted_pole q hq0.ne']
  unfold lambertWindowTerm
  have he := source_shifted_residue_power q hq0.ne' n s t
  calc
    _ = (sourceASummand n s).eval₂ (Int.castRingHom ℝ) q⁻¹ *
      (((q ^ ((14 * n + 1) * t) / q ^ ((14 * n + 1) * (12 * n))) *
        q ^ ((14 * n + 1) * (14 * n + 1 + s))) /
          (1 - q ^ (2 * n + s + 1 + t))) := by rw [he]
    _ = _ := by ring

lemma sourceExtendedKernelTerm_initial_zero (q : ℝ) (hq : q ≠ 0)
    (n t : ℕ) (ht : t < 12 * n) : sourceExtendedKernelTerm q n t = 0 := by
  have hi : 12 * n - t - 1 ∈ range (12 * n) := mem_range.mpr (by omega)
  have hf :
      1 - q ^ ((12 * n - t - 1) + 1) * (q ^ t / q ^ (12 * n)) = 0 := by
    have he : (12 * n - t - 1) + 1 + t = 12 * n := by omega
    rw [← mul_div_assoc, ← pow_add, he, div_self (pow_ne_zero _ hq), sub_self]
  have hprod :
      (poleProduct (fun i : ℕ => q ^ (i + 1)) (range (12 * n))).eval
        (q ^ t / q ^ (12 * n)) = 0 := by
    rw [poleProduct_eval]
    exact prod_eq_zero hi hf
  simp [sourceExtendedKernelTerm, sourceRationalKernel, sourceKernelNumerator, hprod]

lemma sourcePoleProduct_eval_power (q : ℝ) (a m t : ℕ) :
    (poleProduct (fun i : ℕ => q ^ (a + i)) (range m)).eval (q ^ t) =
      qPochhammer q (q ^ (a + t)) m := by
  rw [poleProduct_eval, finite_qPochhammer_product]
  apply prod_congr rfl
  intro i hi
  rw [← pow_add, ← pow_add]
  congr 2
  omega

lemma sourceExtendedKernelTerm_shift (q : ℝ) (hq : q ≠ 0) (n t : ℕ) :
    sourceExtendedKernelTerm q n (12 * n + t) = sourcePositiveHTerm q n t := by
  have hz : q ^ (12 * n + t) / q ^ (12 * n) = q ^ t := by
    rw [pow_add]
    field_simp [hq]
  have hw :
      q ^ ((14 * n + 1) * (12 * n + t)) /
        q ^ ((14 * n + 1) * (12 * n)) = q ^ ((14 * n + 1) * t) := by
    rw [Nat.mul_add, pow_add]
    field_simp [hq]
  unfold sourceExtendedKernelTerm
  rw [hz, hw]
  unfold sourceRationalKernel sourceKernelNumerator sourceKernelDenominator
  simp only [eval_mul, eval_C, sourcePoleParameter]
  have hnum :
      (poleProduct (fun i : ℕ => q ^ (i + 1)) (range (12 * n))).eval (q ^ t) =
        qPochhammer q (q ^ (t + 1)) (12 * n) := by
    simpa only [Nat.add_comm] using sourcePoleProduct_eval_power q 1 (12 * n) t
  rw [hnum]
  unfold sourcePoleParameter
  rw [sourcePoleProduct_eval_power]
  unfold sourcePositiveHTerm
  simp only [qPochhammerFinite_eq]
  ring

/-- The source's positive H is the same analytic series as the literal pole
summation, with the initial zero block proved rather than dropped. -/
theorem actual_source_pole_series_eq_H {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    sourcePoleSeries q n = sourcePositiveH q n := by
  have hsum := (sourcePoleSeriesTerm_summable hq0 hq1 n).sum_add_tsum_nat_add (12 * n)
  have hzero : (∑ t ∈ range (12 * n), sourcePoleSeriesTerm q n t) = 0 := by
    apply sum_eq_zero
    intro t ht
    rw [sourcePoleSeriesTerm_eq_extended hq0 hq1]
    exact sourceExtendedKernelTerm_initial_zero q hq0.ne' n t (mem_range.mp ht)
  have htail : (∑' t : ℕ, sourcePoleSeriesTerm q n (t + 12 * n)) = sourcePositiveH q n := by
    unfold sourcePositiveH
    apply tsum_congr
    intro t
    rw [sourcePoleSeriesTerm_eq_extended hq0 hq1, Nat.add_comm t (12 * n),
      sourceExtendedKernelTerm_shift q hq0.ne']
  rw [hzero, htail, zero_add] at hsum
  exact hsum.symm

/-- The requested all-index analytic identity for the actual A_n and B_n.
The sole analytic parameter assumptions are 0<q<1. -/
theorem actual_A_F_sub_B_eq_H {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    (sourceA n).eval₂ (Int.castRingHom ℝ) q⁻¹ * PaperR7.paperLambert q⁻¹ -
      sourceBReal n q⁻¹ = sourcePositiveH q n := by
  rw [actual_A_Lambert_sub_B_eq_pole_series hq0 hq1, actual_source_pole_series_eq_H hq0 hq1]

/-- Equivalent statement on the paper's p>1 domain. -/
theorem actual_A_F_sub_B_eq_H_real (p : ℝ) (hp : 1 < p) (n : ℕ) :
    (sourceA n).eval₂ (Int.castRingHom ℝ) p * PaperR7.paperLambert p -
      sourceBReal n p = sourcePositiveH p⁻¹ n := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  simpa only [inv_inv] using
    actual_A_F_sub_B_eq_H (inv_pos.mpr hp0) ((inv_lt_one₀ hp0).mpr hp) n

/-- Positivity/nonvanishing is now for the actual source error, not an
unidentified positive comparison series. -/
theorem actual_source_error_pos (p : ℝ) (hp : 1 < p) (n : ℕ) :
    0 < (sourceA n).eval₂ (Int.castRingHom ℝ) p * PaperR7.paperLambert p -
      sourceBReal n p := by
  rw [actual_A_F_sub_B_eq_H_real p hp n]
  have hp0 : 0 < p := zero_lt_one.trans hp
  exact sourcePositiveH_pos (inv_pos.mpr hp0) ((inv_lt_one₀ hp0).mpr hp) n

end ErdosProblems.Erdos1049.PaperR14
