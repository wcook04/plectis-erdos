import ErdosProblems.Erdos1049.CyclotomicCircleHeightR13
import ErdosProblems.Erdos1049.PaperLongCapR9
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Subquadratic coefficient heights of the actual cancelled source pair

Proves the cancelled pair's coefficient heights have zero quadratic log rate.

This file uses the actual `sourceU` and `sourceV`, the all-index coefficient
bound from R13, and the unchanged maximum/l1 height definitions of the papers.
The analytic limit and the degree+1 transport are proved here, not assumed.
The intentionally conservative numerical envelope is 5000*n*(1+log(n+2))^2.
-/
namespace ErdosProblems.Erdos1049.PaperR14
set_option maxHeartbeats 1000000
open Polynomial Finset Filter Asymptotics
open PaperR11 PaperR12 PaperR13
open scoped BigOperators Topology

noncomputable def sourceRadius (n : ℕ) : ℝ := 1 + 1 / (n : ℝ)
noncomputable def sourceLogScale (n : ℕ) : ℝ := 1 + Real.log ((n : ℝ) + 2)
noncomputable def sourceCoefficientEnvelope (n : ℕ) : ℝ :=
  sourceHeightMajorant n (sourceRadius n)

lemma sourceRadius_gt_one (n : ℕ) (hn : 1 ≤ n) : 1 < sourceRadius n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  dsimp [sourceRadius]
  exact lt_add_of_pos_right _ (one_div_pos.mpr hn0)

lemma sourceLogScale_ge_one (n : ℕ) : 1 ≤ sourceLogScale n := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by linarith)
  dsimp [sourceLogScale]
  linarith

lemma sourceK_le_quadratic (n : ℕ) (hn : 1 ≤ n) : sourceK n ≤ 1200 * n ^ 2 := by
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have h1 : 1 ≤ n ^ 2 := one_le_pow₀ hn
  have hdiv : (1091 * n ^ 2 + 81 * n + 2) / 2 ≤
      1091 * n ^ 2 + 81 * n + 2 := Nat.div_le_self _ _
  unfold sourceK
  omega

lemma sourceRadius_log_le (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ Real.log (sourceRadius n) ∧ Real.log (sourceRadius n) ≤ 1 / (n : ℝ) := by
  have hR := sourceRadius_gt_one n hn
  refine ⟨Real.log_nonneg hR.le, ?_⟩
  have h := Real.log_le_sub_one_of_pos (zero_lt_one.trans hR)
  simpa only [sourceRadius, add_sub_cancel_left] using h

lemma sourceCircleBase_log_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (cyclotomicCircleBase (15 * n) (sourceRadius n)) ≤
      15 * sourceLogScale n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hR := sourceRadius_gt_one n hn
  have hR0 := zero_lt_one.trans hR
  have hbase : cyclotomicCircleBase (15 * n) (sourceRadius n) =
      sourceRadius n ^ (15 * n) * ((n : ℝ) + 2) := by
    simp [cyclotomicCircleBase, sourceRadius, hn0.ne', add_comm]
  rw [hbase, Real.log_mul (pow_ne_zero _ hR0.ne') (by positivity), Real.log_pow]
  have h := mul_le_mul_of_nonneg_left (sourceRadius_log_le n hn).2
    (show (0 : ℝ) ≤ (15 * n : ℕ) by positivity)
  have he : ((15 * n : ℕ) : ℝ) * (1 / (n : ℝ)) = 15 := by
    push_cast
    field_simp
  rw [he] at h
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 2 by linarith)
  unfold sourceLogScale
  linarith

lemma sourceDivisorIncidence_le (n : ℕ) (hn : 1 ≤ n) :
    (divisorIncidence (15 * n) : ℝ) ≤ 225 * (n : ℝ) * sourceLogScale n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log hn0 (by linarith)
  have hlog15 : Real.log (15 : ℝ) ≤ 14 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 15 by norm_num)]
  have hlognonneg : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have h := divisorIncidence_le (15 * n)
  have he : Real.log ((15 * n : ℕ) : ℝ) = Real.log 15 + Real.log (n : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hn0.ne']
  rw [he, Nat.cast_mul, Nat.cast_ofNat] at h
  have hfactor : 1 + Real.log 15 + Real.log (n : ℝ) ≤ 15 * sourceLogScale n := by
    unfold sourceLogScale
    linarith
  have hm := mul_le_mul_of_nonneg_left hfactor (show (0 : ℝ) ≤ 15 * n by positivity)
  nlinarith

lemma sourceACircle_log_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (sourceACircleMajorant n (sourceRadius n)) ≤ 1253 * (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hR0 := zero_lt_one.trans (sourceRadius_gt_one n hn)
  have hN : (0 : ℝ) < (13 * n + 1 : ℕ) := by positivity
  unfold sourceACircleMajorant
  rw [Real.log_mul (mul_ne_zero hN.ne' (pow_ne_zero _ (by norm_num)))
      (pow_ne_zero _ hR0.ne'),
    Real.log_mul hN.ne' (pow_ne_zero _ (by norm_num)), Real.log_pow, Real.log_pow]
  have hfirst := Real.log_le_sub_one_of_pos hN
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hk : (sourceK n : ℝ) ≤ 1200 * (n : ℝ) ^ 2 := by
    exact_mod_cast sourceK_le_quadratic n hn
  have hklog := mul_le_mul_of_nonneg_left (sourceRadius_log_le n hn).2
    (show (0 : ℝ) ≤ sourceK n by positivity)
  have hkr := mul_le_mul_of_nonneg_right hk (one_div_pos.mpr hn0).le
  have he : 1200 * (n : ℝ) ^ 2 * (1 / (n : ℝ)) = 1200 * (n : ℝ) := by
    field_simp
    <;> ring
  rw [he] at hkr
  have ht := mul_le_mul_of_nonneg_left htwo (show (0 : ℝ) ≤ (40 * n : ℕ) by positivity)
  push_cast at hfirst ht ⊢
  nlinarith

lemma sourceBFactor_log_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (1 + ((29 * n : ℕ) : ℝ) * (sourceRadius n - 1)⁻¹) ≤ 31 * (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have he : 1 + ((29 * n : ℕ) : ℝ) * (sourceRadius n - 1)⁻¹ =
      1 + 29 * (n : ℝ) ^ 2 := by
    simp [sourceRadius, pow_two]
    ring
  rw [he]
  have hb : 1 + 29 * (n : ℝ) ^ 2 ≤ 30 * (n : ℝ) ^ 2 := by nlinarith
  have h := Real.log_le_log (show 0 < 1 + 29 * (n : ℝ) ^ 2 by positivity) hb
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'), Real.log_pow] at h
  have h30 : Real.log (30 : ℝ) ≤ 29 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 30 by norm_num)]
  have hln := Real.log_le_sub_one_of_pos hn0
  norm_num at h
  nlinarith

lemma sourceCoefficientEnvelope_ge_one (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ sourceCoefficientEnvelope n := by
  have hR := sourceRadius_gt_one n hn
  have hC := one_le_pow₀ (cyclotomicCircleBase_ge_one (15 * n) (sourceRadius n) hR)
    (n := divisorIncidence (15 * n))
  have hN : (1 : ℝ) ≤ (13 * n + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ 13 * n + 1)
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (40 * n) := one_le_pow₀ (by norm_num)
  have hpow : (1 : ℝ) ≤ sourceRadius n ^ sourceK n := one_le_pow₀ hR.le
  have hA : 1 ≤ sourceACircleMajorant n (sourceRadius n) := by
    have hNT : 1 ≤ ((13 * n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (40 * n) := by
      simpa only [one_mul] using mul_le_mul hN htwo zero_le_one (zero_le_one.trans hN)
    unfold sourceACircleMajorant
    simpa only [one_mul] using
      mul_le_mul hNT hpow zero_le_one (zero_le_one.trans hNT)
  have hi : 0 ≤ (sourceRadius n - 1)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hR).le
  have hB : 1 ≤ 1 + ((29 * n : ℕ) : ℝ) * (sourceRadius n - 1)⁻¹ := by
    have h := mul_nonneg (Nat.cast_nonneg (29 * n) : (0 : ℝ) ≤ (29 * n : ℕ)) hi
    linarith
  have hCA : 1 ≤ cyclotomicCircleBase (15 * n) (sourceRadius n) ^ divisorIncidence (15 * n) *
      sourceACircleMajorant n (sourceRadius n) := by
    simpa only [one_mul] using mul_le_mul hC hA zero_le_one (zero_le_one.trans hC)
  unfold sourceCoefficientEnvelope sourceHeightMajorant
  simpa only [one_mul] using mul_le_mul hCA hB zero_le_one (zero_le_one.trans hCA)

/-- A fully explicit logarithmic envelope for every positive source index. -/
theorem actual_coefficient_envelope_log_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log (sourceCoefficientEnvelope n) ≤
      5000 * (n : ℝ) * sourceLogScale n ^ 2 := by
  have hR := sourceRadius_gt_one n hn
  have hC1 := cyclotomicCircleBase_ge_one (15 * n) (sourceRadius n) hR
  have hC0 : 0 < cyclotomicCircleBase (15 * n) (sourceRadius n) := zero_lt_one.trans_le hC1
  have hA0 : 0 < sourceACircleMajorant n (sourceRadius n) := by
    unfold sourceACircleMajorant
    have hR0 : 0 < sourceRadius n := zero_lt_one.trans hR
    positivity
  have hB0 : 0 < 1 + ((29 * n : ℕ) : ℝ) * (sourceRadius n - 1)⁻¹ := by
    have hi : 0 ≤ (sourceRadius n - 1)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hR).le
    positivity
  have hbase := sourceCircleBase_log_le n hn
  have hcount := sourceDivisorIncidence_le n hn
  have hlogC : 0 ≤ Real.log (cyclotomicCircleBase (15 * n) (sourceRadius n)) :=
    Real.log_nonneg hC1
  have hscale := sourceLogScale_ge_one n
  have hscale0 : 0 ≤ sourceLogScale n := zero_le_one.trans hscale
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hprod := mul_le_mul hcount hbase hlogC (by positivity :
    0 ≤ 225 * (n : ℝ) * sourceLogScale n)
  unfold sourceCoefficientEnvelope sourceHeightMajorant
  rw [Real.log_mul (mul_ne_zero (pow_ne_zero _ hC0.ne') hA0.ne') hB0.ne',
    Real.log_mul (pow_ne_zero _ hC0.ne') hA0.ne', Real.log_pow]
  have ha := sourceACircle_log_le n hn
  have hb := sourceBFactor_log_le n hn
  have hsquared : 1 ≤ sourceLogScale n ^ 2 := one_le_pow₀ hscale
  have hnm := mul_le_mul_of_nonneg_left hsquared hn0
  nlinarith

/-- The limit is proved from the pinned logarithm-versus-power theorem.
No growth or little-o premise is attached to the source sequence. -/
theorem source_n_log_squared_isLittleO :
    (fun n : ℕ => (n : ℝ) * sourceLogScale n ^ 2) =o[atTop] PaperR9.sqScale := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge b
    filter_upwards [eventually_ge_atTop N] with n hn
    have h : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hl : (fun x : ℝ => Real.log x ^ (2 : ℕ)) =o[atTop] (fun x : ℝ => x) := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop ((2 : ℕ) : ℝ) (s := 1) (by norm_num))
  have hseq := hl.comp_tendsto ht
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hseq.def (show 0 < ε / 12 by positivity),
    (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with n hn hln hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) ≤ n := hnR.trans' zero_le_one
  have hx0 : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  simp only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (Real.log ((n : ℝ) + 2))), abs_of_nonneg hx0] at hn hln
  have hscale : sourceLogScale n ^ 2 ≤ 4 * Real.log ((n : ℝ) + 2) ^ 2 := by
    unfold sourceLogScale
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hn (show (0 : ℝ) ≤ 4 * n by positivity)
  have hlast : 4 * (n : ℝ) * (ε / 12 * ((n : ℝ) + 2)) ≤ ε * (n : ℝ) ^ 2 := by
    have hx : (n : ℝ) + 2 ≤ 3 * (n : ℝ) := by linarith
    have h := mul_le_mul_of_nonneg_left hx (show 0 ≤ 4 * (n : ℝ) * (ε / 12) by positivity)
    nlinarith
  have hfirst := mul_le_mul_of_nonneg_left hscale hn0
  simpa only [PaperR9.sqScale, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hn0 (sq_nonneg _)), abs_of_nonneg (sq_nonneg (n : ℝ))] using
      hfirst.trans (by nlinarith)

/-- The envelope itself has exact zero quadratic logarithmic rate. -/
theorem actual_coefficient_envelope_quadLogRate_zero :
    PaperR9.QuadLogRate sourceCoefficientEnvelope 0 := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [source_n_log_squared_isLittleO.def
      (show 0 < ε / 5000 by positivity), eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hE := sourceCoefficientEnvelope_ge_one n hn1
  have hlog := Real.log_nonneg hE
  have hb := actual_coefficient_envelope_log_le n hn1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [PaperR9.sqScale, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hn0 (sq_nonneg _)), abs_of_nonneg (sq_nonneg (n : ℝ))] at hn
  simp only [zero_mul, sub_zero, abs_of_nonneg (zero_le_one.trans hE),
    Real.norm_eq_abs, abs_of_nonneg hlog, PaperR9.sqScale,
    abs_of_nonneg (sq_nonneg (n : ℝ))]
  nlinarith

lemma finite_nat_sup_cast_le {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (H : ℝ) (hH : 0 ≤ H) (hf : ∀ i ∈ s, (f i : ℝ) ≤ H) :
    ((s.sup f : ℕ) : ℝ) ≤ H := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hH
  · obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup s hs f
    rw [hsup]
    exact hf i hi

lemma maxCoeffNat_le_of_coefficients (P : ℤ[X]) (H : ℝ) (hH : 0 ≤ H)
    (h : ∀ k, (|P.coeff k| : ℝ) ≤ H) : (PaperR9.maxCoeffNat P : ℝ) ≤ H := by
  apply finite_nat_sup_cast_le P.support (fun k => (P.coeff k).natAbs) H hH
  intro k _
  simpa only [Nat.cast_natAbs, Int.cast_abs] using h k

/-- The exact maximum height used by the long paper is bounded by H_n. -/
theorem actual_maxPairHeight_le_envelope (n : ℕ) (hn : 1 ≤ n) :
    PaperR9.maxPairHeight sourceU sourceV n ≤ sourceCoefficientEnvelope n := by
  have hR := sourceRadius_gt_one n hn
  have hH := (sourceHeightMajorant_nonneg n (sourceRadius n) hR)
  have h (k : ℕ) := actual_cancelled_pair_coefficients_le n k (sourceRadius n) hR
  have hu := maxCoeffNat_le_of_coefficients (sourceU n) _ hH (fun k => (h k).1)
  have hv := maxCoeffNat_le_of_coefficients (sourceV n) _ hH (fun k => (h k).2)
  simpa only [PaperR9.maxPairHeight, Nat.cast_max, sourceCoefficientEnvelope] using max_le hu hv

/-- No replacement notion of coefficient height is introduced. -/
theorem actual_maxPairHeight_log_upper_zero :
    PaperR9.QuadUpper (fun n => Real.log (PaperR9.maxPairHeight sourceU sourceV n)) 0 := by
  intro ε hε
  filter_upwards [actual_coefficient_envelope_quadLogRate_zero.upper ε hε,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hE := sourceCoefficientEnvelope_ge_one n hn1
  have hH := actual_maxPairHeight_le_envelope n hn1
  by_cases hz : PaperR9.maxPairHeight sourceU sourceV n = 0
  · simp only [hz, Real.log_zero, zero_add]
    exact mul_nonneg hε.le (PaperR9.sqScale_nonneg n)
  · have hH0 : 0 < PaperR9.maxPairHeight sourceU sourceV n :=
      lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hz)
    have hh := Real.log_le_log hH0 hH
    rw [abs_of_nonneg (zero_le_one.trans hE)] at hn
    exact hh.trans hn

lemma sourceComplement_degree_le_square (n : ℕ) :
    (sourceComplement n).natDegree ≤ 225 * n ^ 2 := by
  rw [(sourceComplement_monic_degree n).2]
  calc
    _ ≤ ∑ _l ∈ Icc 1 (15 * n), 15 * n := by
      apply sum_le_sum
      intro l hl
      split_ifs
      · exact (Nat.totient_le l).trans (mem_Icc.mp hl).2
      · exact Nat.zero_le _
    _ = 225 * n ^ 2 := by simp; ring

/-- A coarse quadratic degree bound is enough to pay for l1 transport. -/
theorem actual_pairWidth_le_quadratic (n : ℕ) (hn : 1 ≤ n) :
    PaperR9.pairWidth sourceU sourceV n ≤ 1425 * n ^ 2 := by
  have hu : (sourceU n).natDegree ≤ 1425 * n ^ 2 := by
    rw [actual_U_degree]
    have hk := sourceK_le_quadratic n hn
    have hc := sourceComplement_degree_le_square n
    rw [(sourceComplement_monic_degree n).2] at hc
    omega
  have hv := (actual_V_degree_and_leadingCoeff n hn).1
  exact max_le hu (by rw [hv]; omega)

lemma actual_pairWidth_quadUpper :
    PaperR9.QuadUpper (fun n => (PaperR9.pairWidth sourceU sourceV n : ℝ)) 1425 := by
  intro ε hε
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have h : (PaperR9.pairWidth sourceU sourceV n : ℝ) ≤ 1425 * (n : ℝ) ^ 2 := by
    exact_mod_cast actual_pairWidth_le_quadratic n hn
  unfold PaperR9.sqScale
  nlinarith [sq_nonneg (n : ℝ)]

/-- The exact l1 height used by the short paper also has zero upper rate.
The degree+1 factor is discharged, rather than silently omitted. -/
theorem actual_pairHeight_log_upper_zero :
    PaperR9.QuadUpper (fun n => Real.log (PaperR9.pairHeight sourceU sourceV n)) 0 := by
  have hw := PaperR9.log_width_plus_one_rate (PaperR9.pairWidth sourceU sourceV)
    1425 (by norm_num) actual_pairWidth_quadUpper
  have hh := hw.add actual_maxPairHeight_log_upper_zero
  intro ε hε
  filter_upwards [hh ε hε] with n hn
  simpa only [zero_add] using (PaperR9.log_pairHeight_le sourceU sourceV n).trans hn

/-- Direct composition with the unchanged paper evaluation consumer. -/
theorem actual_U_eval_quadExpUpper (x : ℝ) (hx : 1 < x) :
    PaperR9.QuadExpUpper (fun n => (sourceU n).eval₂ (Int.castRingHom ℝ) x)
      (1425 * Real.log x) := by
  simpa only [zero_add] using PaperR9.polynomial_eval_exp_upper sourceU sourceV
    1425 0 x hx actual_pairWidth_quadUpper actual_pairHeight_log_upper_zero

lemma actual_U_leadingCoeff (n : ℕ) :
    (sourceU n).leadingCoeff = (-1 : ℤ) ^ (13 * n) := by
  have h := congrArg Polynomial.leadingCoeff (sourceA_factor n)
  rw [leadingCoeff_mul, leadingCoeff_X_pow, one_mul,
    (actual_A_degree_and_leadingCoeff n).2] at h
  unfold sourceU
  rw [leadingCoeff_mul, (sourceComplement_monic_degree n).1.leadingCoeff,
    one_mul, ← h]

lemma actual_pairHeight_ge_one (n : ℕ) :
    1 ≤ PaperR9.pairHeight sourceU sourceV n := by
  have hcoeff : (sourceU n).coeff (sourceU n).natDegree = (-1 : ℤ) ^ (13 * n) := by
    rw [coeff_natDegree, actual_U_leadingCoeff]
  have hm : (sourceU n).natDegree ∈ (sourceU n).support := by
    rw [mem_support_iff, hcoeff]
    exact pow_ne_zero _ (by norm_num)
  have h := Finset.single_le_sum
    (f := fun k => |((sourceU n).coeff k : ℝ)|)
    (fun k (_ : k ∈ (sourceU n).support) => abs_nonneg _) hm
  have hv : |((sourceU n).coeff (sourceU n).natDegree : ℝ)| = 1 := by
    rw [hcoeff]
    simp
  simp only [hv] at h
  exact h.trans (le_max_left _ _)

/-- Exact zero logarithmic rate for the short paper's actual l1 height. -/
theorem actual_pairHeight_quadLogRate_zero :
    PaperR9.QuadLogRate (PaperR9.pairHeight sourceU sourceV) 0 := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [actual_pairHeight_log_upper_zero ε hε] with n hn
  have hH := actual_pairHeight_ge_one n
  have hlog := Real.log_nonneg hH
  simpa only [zero_add, zero_mul, sub_zero,
    abs_of_nonneg (zero_le_one.trans hH), Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg (PaperR9.sqScale_nonneg n)] using hn

/-- Exact zero logarithmic rate for the long paper's maximum height. -/
theorem actual_maxPairHeight_quadLogRate_zero :
    PaperR9.QuadLogRate (PaperR9.maxPairHeight sourceU sourceV) 0 := by
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [actual_maxPairHeight_log_upper_zero ε hε] with n hn
  have hH : 0 ≤ PaperR9.maxPairHeight sourceU sourceV n := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log (PaperR9.maxPairHeight sourceU sourceV n) :=
    Real.log_natCast_nonneg _
  simpa only [zero_add, zero_mul, sub_zero, abs_of_nonneg hH,
    Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg (PaperR9.sqScale_nonneg n)] using hn

/-- Sharp degree-rate composition is available without paying an artificial
coefficient-height constant. Its only premise is the independent degree rate. -/
theorem actual_U_eval_of_degree_rate (δ x : ℝ) (hx : 1 < x)
    (hd : PaperR9.QuadUpper
      (fun n => (PaperR9.pairWidth sourceU sourceV n : ℝ)) δ) :
    PaperR9.QuadExpUpper (fun n => (sourceU n).eval₂ (Int.castRingHom ℝ) x)
      (δ * Real.log x) := by
  simpa only [zero_add] using PaperR9.polynomial_eval_exp_upper sourceU sourceV
    δ 0 x hx hd actual_pairHeight_log_upper_zero

end ErdosProblems.Erdos1049.PaperR14
