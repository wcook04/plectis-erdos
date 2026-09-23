import ErdosProblems.Erdos1049.PaperR20.SourcePadeAnalytic

/-!
# The all-index source Padé remainder

This module completes the analytic use of the unconditional source Padé
identity.  The global power `p^d` is retained until the kernel-zero correction
has been applied.  Consequently the finite source correction is identified
with the paper polynomial `coefficientBetaPoly` by the already proved Lambert
polynomial-part uniqueness theorem, rather than assumed as certificate data.
-/

namespace ErdosProblems.Erdos1049.PaperR20

open Finset Polynomial
open scoped BigOperators

noncomputable section

private def sourcePositiveCoeffEval (m : ℕ) (p : ℝ) (d j : ℕ) : ℝ :=
  if hj : j < m then
    parameterEval p (sourceQuotientPositiveCoeff m ⟨j, hj⟩) / p ^ d
  else 0

private theorem sourcePade_constant_cancellation (m : ℕ) (p : ℝ)
    (hp : 1 < p) :
    parameterEval p (sourceClearedQuotientCoeff m m) +
      p ^ sourceQuotientClearD m * coefficientAlpha p m = 0 := by
  have hpne : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hD : (∏ j ∈ range (m + 1), p ^ (m + 1 + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ hpne
  have hsumC : (∑ k : Fin (m + 1), parameterEval p (sourceResiduePoly m k.val)) =
      coefficientAlpha p m := by
    have h := congrArg (parameterEval p) (sum_sourceResidue_fin_eq_coefficientAlpha m)
    simpa [coefficientAlpha, parameterEval] using h
  have h_except (k : Fin (m + 1)) :
      p ^ (m + 1 + k.val) *
          (∏ j ∈ (range (m + 1)).erase k.val, p ^ (m + 1 + j)) =
        ∏ j ∈ range (m + 1), p ^ (m + 1 + j) := by
    exact Finset.mul_prod_erase (range (m + 1))
      (fun j : ℕ => p ^ (m + 1 + j)) (Finset.mem_range.mpr k.isLt)
  have h := sourcePade_partial_fraction_at_zero m p
  have hQ := congrArg
    (fun P : BivariatePolynomial => evalBivariate P p 0)
    (sourceClearedQuotientPoly_split m)
  have hX : parameterEval p X = p := by simp [parameterEval]
  simp only [clearedMomentDenominatorPoly, clearedMomentDenominatorExceptPoly,
    residueCertificatePoly, evalBivariate_add, evalBivariate_mul, evalBivariate_C,
    evalBivariate_sum, evalBivariate_prod, evalBivariate_sub, evalBivariate_X,
    evalBivariate_pow, map_mul, map_pow, hX, sub_zero, pow_succ, mul_zero,
    Finset.sum_const_zero, add_zero] at h hQ
  rw [hQ] at h
  have hres : (∑ k : Fin (m + 1), parameterEval p (sourceResiduePoly m k.val) *
      p ^ (m + 1 + k.val) * ∏ j ∈ (range (m + 1)).erase k.val, p ^ (m + 1 + j)) =
      coefficientAlpha p m * ∏ j ∈ range (m + 1), p ^ (m + 1 + j) := by
    rw [← hsumC, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_assoc, h_except k]
  rw [hres] at h
  apply (mul_right_cancel₀ hD)
  linear_combination h

/-- The evaluated source Padé identity after exact normalization by `p^d`.
The only domain condition is the one needed to keep every pole denominator
nonzero; it covers both the summation orbit and all numerator roots. -/
private theorem sourcePade_scaled_kernel_identity (m : ℕ) (p : ℝ)
    (hp : 1 < p) (x : ℝ) (hx : x < p ^ (m + 1)) :
    p ^ sourceQuotientClearD m * momentRationalKernel p⁻¹ m x =
      (∑ j : Fin m,
        parameterEval p (sourceQuotientPositiveCoeff m j) * x ^ (j.val + 1)) +
      p ^ sourceQuotientClearD m *
        ∑ k : Fin (m + 1),
          parameterEval p (sourceResiduePoly m k.val) * x /
            (p ^ (m + 1 + k.val) - x) := by
  let f : ParameterPolynomial →+* ℝ := parameterEval p
  let d := sourceQuotientClearD m
  let e := sourceQuotientClearE m
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hfactor (j : ℕ) (hj : j ∈ range (m + 1)) :
      0 < p ^ (m + 1 + j) - x := by
    have hmono : p ^ (m + 1) ≤ p ^ (m + 1 + j) :=
      pow_le_pow_right₀ hp.le (by omega)
    linarith
  have hden : (∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact ne_of_gt (hfactor j hj)
  have hclear := momentRationalKernel_clear p hpne m d e x
    (by simpa [d, e] using sourceQuotient_clearing_balance m) hden
  have hpoly := congrArg
    (fun P : BivariatePolynomial => evalBivariate P p x)
    (sourcePade_partial_fraction_identity m)
  have hQ := congrArg
    (fun P : BivariatePolynomial => evalBivariate P p x)
    (sourceClearedQuotientPoly_split m)
  have hsumC : (∑ k : Fin (m + 1), f (sourceResiduePoly m k.val)) =
      coefficientAlpha p m := by
    have h := congrArg f (sum_sourceResidue_fin_eq_coefficientAlpha m)
    simpa [coefficientAlpha, f, parameterEval] using h
  have hzero : f (sourceClearedQuotientCoeff m m) +
      p ^ d * coefficientAlpha p m = 0 := by
    simpa [f, d] using sourcePade_constant_cancellation m p hp
  have h_except (k : Fin (m + 1)) :
      (p ^ (m + 1 + k.val) - x) *
          (∏ j ∈ (range (m + 1)).erase k.val,
            (p ^ (m + 1 + j) - x)) =
        ∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x) := by
    exact Finset.mul_prod_erase (range (m + 1))
      (fun j : ℕ => (p ^ (m + 1 + j) - x : ℝ))
      (Finset.mem_range.mpr k.isLt)
  have hresidue (k : Fin (m + 1)) :
      f (sourceResiduePoly m k.val) * p ^ (m + 1 + k.val) /
            (p ^ (m + 1 + k.val) - x) =
        f (sourceResiduePoly m k.val) +
          f (sourceResiduePoly m k.val) * x /
            (p ^ (m + 1 + k.val) - x) := by
    have hn := ne_of_gt (hfactor k.val (Finset.mem_range.mpr k.isLt))
    field_simp [hn]
    ring
  have hresidue_mul (k : Fin (m + 1)) :
      f (sourceResiduePoly m k.val) * p ^ (m + 1 + k.val) *
          (∏ j ∈ (range (m + 1)).erase k.val,
            (p ^ (m + 1 + j) - x)) =
        (f (sourceResiduePoly m k.val) +
          f (sourceResiduePoly m k.val) * x /
            (p ^ (m + 1 + k.val) - x)) *
          (∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x)) := by
    rw [← h_except k, ← hresidue k]
    have hn := ne_of_gt (hfactor k.val (Finset.mem_range.mpr k.isLt))
    field_simp [hn]
  have hpoly' :
      p ^ d * momentRationalKernel p⁻¹ m x *
          (∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x)) =
        (f (sourceClearedQuotientCoeff m m) +
          ∑ j : Fin m,
            f (sourceQuotientPositiveCoeff m j) * x ^ (j.val + 1)) *
            (∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x)) +
          p ^ d * ∑ k : Fin (m + 1),
            f (sourceResiduePoly m k.val) * p ^ (m + 1 + k.val) *
              (∏ j ∈ (range (m + 1)).erase k.val,
                (p ^ (m + 1 + j) - x)) := by
    have hX : parameterEval p X = p := by simp [parameterEval]
    have h1 : evalBivariate (1 : BivariatePolynomial) p x = 1 := by simp [evalBivariate]
    simp only [clearedMomentNumeratorPoly, clearedMomentDenominatorPoly,
      clearedMomentDenominatorExceptPoly, residueCertificatePoly,
      evalBivariate_add, evalBivariate_mul, evalBivariate_C, evalBivariate_sum,
      evalBivariate_prod, evalBivariate_sub, evalBivariate_X, evalBivariate_pow,
      map_mul, map_pow, map_prod, map_sub, map_one, hX, h1] at hpoly hQ
    rw [hQ] at hpoly
    rw [hclear]
    dsimp only [f, d, e]
    linear_combination hpoly
  apply (mul_right_cancel₀ hden)
  rw [hpoly']
  simp_rw [hresidue_mul]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [hsumC]
  linear_combination hzero *
    (∏ j ∈ range (m + 1), (p ^ (m + 1 + j) - x))

/-- The source partial fraction is the exact rational-kernel certificate on
all summation points.  The coefficient normalization includes `p^d`. -/
private theorem sourcePade_rationalKernel_certificate (m : ℕ) (p : ℝ)
    (hp : 1 < p) :
    let d := sourceQuotientClearD m
    let A : Fin m → ℝ := fun j =>
      parameterEval p (sourceQuotientPositiveCoeff m j) / p ^ d
    let Cv : Fin (m + 1) → ℝ := fun k =>
      parameterEval p (sourceResiduePoly m k.val)
    ∀ t : ℕ,
      momentRationalKernel p⁻¹ m (p⁻¹ ^ t) =
        finiteRationalKernel p⁻¹ m A Cv t := by
  dsimp only
  intro t
  let x : ℝ := p⁻¹ ^ t
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hpd : p ^ sourceQuotientClearD m ≠ 0 := pow_ne_zero _ hpne
  have hq0 : 0 < p⁻¹ := inv_pos.mpr hp0
  have hq1 : p⁻¹ < 1 := (inv_lt_one₀ hp0).2 hp
  have hxle : x ≤ 1 := pow_le_one₀ hq0.le hq1.le
  have hx : x < p ^ (m + 1) :=
    lt_of_le_of_lt hxle (one_lt_pow₀ hp (by omega))
  have hscaled := sourcePade_scaled_kernel_identity m p hp x hx
  have htail (k : Fin (m + 1)) :
      parameterEval p (sourceResiduePoly m k.val) *
          p⁻¹ ^ (m + 1 + k.val + t) /
            (1 - p⁻¹ ^ (m + 1 + k.val + t)) =
        parameterEval p (sourceResiduePoly m k.val) * x /
          (p ^ (m + 1 + k.val) - x) := by
    have hfactor : 0 < p ^ (m + 1 + k.val) - x := by
      have hmono : p ^ (m + 1) ≤ p ^ (m + 1 + k.val) :=
        pow_le_pow_right₀ hp.le (by omega)
      linarith
    dsimp [x]
    rw [pow_add, inv_pow]
    field_simp [hpne, ne_of_gt hfactor]
  have hgeom (j : Fin m) :
      p⁻¹ ^ ((j.val + 1) * t) = x ^ (j.val + 1) := by
    simp [x, pow_mul, Nat.mul_comm]
  have hA : p ^ sourceQuotientClearD m *
      (∑ j : Fin m, parameterEval p (sourceQuotientPositiveCoeff m j) /
        p ^ sourceQuotientClearD m * x ^ (j.val + 1)) =
      ∑ j : Fin m, parameterEval p (sourceQuotientPositiveCoeff m j) * x ^ (j.val + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  unfold finiteRationalKernel
  simp_rw [hgeom, htail]
  apply (mul_left_cancel₀ hpd)
  rw [hscaled, mul_add, hA]

/-- The normalized numerator zeros provide exactly the hypotheses of the
finite kernel-zero correction. -/
private theorem sourcePade_kernelZero_correction (m : ℕ) (p : ℝ)
    (hp : 1 < p) :
    let d := sourceQuotientClearD m
    let A : ℕ → ℝ := sourcePositiveCoeffEval m p d
    let Cv : ℕ → ℝ := fun k =>
      parameterEval p (sourceResiduePoly m k)
    (∑ k ∈ range (m + 1),
        ∑ n ∈ range (m + k), Cv k / (p ^ (n + 1) - 1)) -
        ∑ j ∈ range m, A j * p ^ (j + 1) / (p ^ (j + 1) - 1) =
      (∑ k ∈ range (m + 1),
        ∑ n ∈ range k, Cv k / (p ^ (n + 1) - 1)) -
        ∑ j ∈ range m,
          A j * p ^ ((m + 1) * (j + 1)) / (p ^ (j + 1) - 1) := by
  dsimp only
  let d := sourceQuotientClearD m
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hpd : p ^ d ≠ 0 := pow_ne_zero d hpne
  apply kernelZero_correction_identity m p
  · intro j hj
    exact ne_of_gt (one_lt_pow₀ hp (by omega))
  · intro s hs
    let x : ℝ := p ^ (s + 1)
    have hslt : s < m := mem_range.mp hs
    have hx : x < p ^ (m + 1) := by
      exact pow_lt_pow_right₀ hp (by omega)
    have hscaled := sourcePade_scaled_kernel_identity m p hp x hx
    have hkernelzero : momentRationalKernel p⁻¹ m x = 0 := by
      unfold momentRationalKernel
      have hz : ∏ j ∈ range m, (1 - p⁻¹ ^ (j + 1) * x) = 0 := by
        apply Finset.prod_eq_zero (i := s) hs
        dsimp [x]
        rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hpne), sub_self]
      rw [hz, mul_zero, zero_div]
    rw [hkernelzero, mul_zero] at hscaled
    have htail (k : Fin (m + 1)) :
        parameterEval p (sourceResiduePoly m k.val) * x /
              (p ^ (m + 1 + k.val) - x) =
          parameterEval p (sourceResiduePoly m k.val) /
              (p ^ (m + k.val - s) - 1) := by
      have hdiff : m + 1 + k.val = (s + 1) + (m + k.val - s) := by omega
      have hnon : p ^ (m + k.val - s) - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp (by omega)))
      dsimp [x]
      rw [hdiff, pow_add p (s + 1) (m + k.val - s),
        show p ^ (s + 1) * p ^ (m + k.val - s) - p ^ (s + 1) =
          (p ^ (m + k.val - s) - 1) * p ^ (s + 1) by ring,
        mul_div_mul_right _ _ (pow_ne_zero _ hpne)]
    simp_rw [htail] at hscaled
    have hQsum :
        (∑ j ∈ range m,
            sourcePositiveCoeffEval m p d j * p ^ ((s + 1) * (j + 1))) =
          ∑ j : Fin m,
            (parameterEval p (sourceQuotientPositiveCoeff m j) / p ^ d) *
              p ^ ((s + 1) * (j.val + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      simp [sourcePositiveCoeffEval, j.isLt]
    rw [hQsum]
    have hC : (∑ k ∈ range (m + 1),
        parameterEval p (sourceResiduePoly m k) / (p ^ (m + k - s) - 1)) =
        ∑ k : Fin (m + 1),
          parameterEval p (sourceResiduePoly m k.val) / (p ^ (m + k.val - s) - 1) :=
      (Fin.sum_univ_eq_sum_range
        (fun k => parameterEval p (sourceResiduePoly m k) / (p ^ (m + k - s) - 1))
        (m + 1)).symm
    rw [hC]
    simp only [x, ← pow_mul] at hscaled
    have hAsum : p ^ sourceQuotientClearD m *
        (∑ j : Fin m, parameterEval p (sourceQuotientPositiveCoeff m j) /
          p ^ sourceQuotientClearD m * p ^ ((s + 1) * (j.val + 1))) =
        ∑ j : Fin m, parameterEval p (sourceQuotientPositiveCoeff m j) *
          p ^ ((s + 1) * (j.val + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp
    apply (mul_left_cancel₀ hpd)
    dsimp only [d]
    rw [mul_add, hAsum, mul_zero]
    linear_combination -hscaled

/-- Exact source remainder before identifying its finite polynomial with the
paper's `β_m`. -/
theorem sourcePade_actualMoment_remainder (m : ℕ) (p : ℝ) (hp : 1 < p) :
    PaperR12.actualMoment p⁻¹ m =
      coefficientAlpha p m * PaperR16.lambert p⁻¹ -
        parameterEval p (sourceFiniteCorrectionPoly m) := by
  let d := sourceQuotientClearD m
  let q : ℝ := p⁻¹
  let A : Fin m → ℝ := fun j =>
    parameterEval p (sourceQuotientPositiveCoeff m j) / p ^ d
  let Cv : Fin (m + 1) → ℝ := fun k =>
    parameterEval p (sourceResiduePoly m k.val)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hpd : p ^ d ≠ 0 := pow_ne_zero d hpne
  have hq0 : 0 < q := inv_pos.mpr hp0
  have hq1 : q < 1 := (inv_lt_one₀ hp0).2 hp
  have hkernel := sourcePade_rationalKernel_certificate m p hp
  have hmoment := actualMoment_eq_of_rationalKernel_certificate
    hq0 hq1 m A Cv (by simpa [A, Cv, q, d] using hkernel)
  have hsumC : (∑ k, Cv k) = coefficientAlpha p m := by
    have h := congrArg (parameterEval p)
      (sum_sourceResidue_fin_eq_coefficientAlpha m)
    simpa [Cv, coefficientAlpha, parameterEval] using h
  have hprefix (k : Fin (m + 1)) :
      Cv k * finiteLambertPrefix q (m + k.val) =
        ∑ n : Fin (m + k.val),
          parameterEval p (sourceResidueQuotientPoly m k.val n.val) := by
    unfold finiteLambertPrefix
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n _
    have hn0 : p ^ (n.val + 1) - 1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp (by omega)))
    have hd : parameterEval p (sourceResiduePoly m k.val) =
        (p ^ (n.val + 1) - 1) *
          parameterEval p (sourceResidueQuotientPoly m k.val n.val) := by
      simpa [parameterEval] using congrArg (parameterEval p)
        (sourceResidue_factor m k.val n.val (by omega))
    dsimp [q, Cv]
    rw [inv_pow, hd]
    field_simp [hpne, hn0]
  have hgeomCorrection (j : Fin m) :
      A j / (1 - q ^ (j.val + 1)) =
        p ^ (j.val + 1) *
          parameterEval p (sourceQuotientQuotientPoly m j) / p ^ d := by
    have hn : p ^ (j.val + 1) - 1 ≠ 0 :=
      ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp (by omega)))
    have hd : parameterEval p (sourceQuotientPositiveCoeff m j) =
        (p ^ (j.val + 1) - 1) *
          parameterEval p (sourceQuotientQuotientPoly m j) := by
      simpa [parameterEval] using congrArg (parameterEval p)
        (sourceQuotientPositiveCoeff_factor m j)
    dsimp [A, q]
    rw [inv_pow, hd]
    field_simp [hpne, hpd, hn]
  have hkc := sourcePade_kernelZero_correction m p hp
  have hkc' :
      (∑ k : Fin (m + 1),
          ∑ n : Fin (m + k.val),
            parameterEval p (sourceResidueQuotientPoly m k.val n.val)) -
        ∑ j : Fin m,
          p ^ (j.val + 1) *
            parameterEval p (sourceQuotientQuotientPoly m j) / p ^ d =
      parameterEval p (sourceFiniteCorrectionPoly m) := by
    rw [parameterEval_sourceFiniteCorrectionPoly]
    have hshort :
        (∑ k ∈ range (m + 1),
            ∑ n ∈ range k,
              parameterEval p (sourceResiduePoly m k) /
                (p ^ (n + 1) - 1)) =
          ∑ k : Fin (m + 1),
            ∑ n : Fin k.val,
              parameterEval p (sourceResidueQuotientPoly m k.val n.val) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n _
      have hfac := congrArg (parameterEval p)
        (sourceResidue_factor m k.val n.val (by omega))
      have hn : p ^ (n.val + 1) - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp (by omega)))
      apply (div_eq_iff hn).2
      simpa [parameterEval, mul_comm] using hfac
    have hfull :
        (∑ k ∈ range (m + 1),
            ∑ n ∈ range (m + k),
              parameterEval p (sourceResiduePoly m k) /
                (p ^ (n + 1) - 1)) =
          ∑ k : Fin (m + 1),
            ∑ n : Fin (m + k.val),
              parameterEval p (sourceResidueQuotientPoly m k.val n.val) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n _
      have hfac := congrArg (parameterEval p)
        (sourceResidue_factor m k.val n.val (by omega))
      have hn : p ^ (n.val + 1) - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp (by omega)))
      apply (div_eq_iff hn).2
      simpa [parameterEval, mul_comm] using hfac
    have hQbase :
        (∑ j ∈ range m,
            sourcePositiveCoeffEval m p d j *
              p ^ (j + 1) / (p ^ (j + 1) - 1)) =
          ∑ j : Fin m,
            p ^ (j.val + 1) *
              parameterEval p (sourceQuotientQuotientPoly m j) / p ^ d := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [show sourcePositiveCoeffEval m p d j.val =
        parameterEval p (sourceQuotientPositiveCoeff m j) / p ^ d by
          simp [sourcePositiveCoeffEval, j.isLt]]
      have hfac := congrArg (parameterEval p)
        (sourceQuotientPositiveCoeff_factor m j)
      have hn : p ^ (j.val + 1) - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp (by omega)))
      rw [show parameterEval p (sourceQuotientPositiveCoeff m j) =
        (p ^ (j.val + 1) - 1) *
          parameterEval p (sourceQuotientQuotientPoly m j) by
            simpa [parameterEval] using hfac]
      field_simp [hpd, hn]
    have hQshift :
        (∑ j ∈ range m,
            sourcePositiveCoeffEval m p d j *
              p ^ ((m + 1) * (j + 1)) / (p ^ (j + 1) - 1)) =
          ∑ j : Fin m, parameterEval p (sourceShiftedQuotientCorrectionPoly m j) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [show sourcePositiveCoeffEval m p d j.val =
        parameterEval p (sourceQuotientPositiveCoeff m j) / p ^ d by
          simp [sourcePositiveCoeffEval, j.isLt]]
      have hfac := congrArg (parameterEval p)
        (sourceQuotientPositiveCoeff_factor m j)
      have hscale := congrArg (parameterEval p)
        (sourceShiftedQuotientCorrection_scale m j)
      have hn : p ^ (j.val + 1) - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr (one_lt_pow₀ hp (by omega)))
      have hfac' : parameterEval p (sourceQuotientPositiveCoeff m j) =
          (p ^ (j.val + 1) - 1) *
            parameterEval p (sourceQuotientQuotientPoly m j) := by
        simpa [parameterEval] using hfac
      have hscale' : p ^ d *
          parameterEval p (sourceShiftedQuotientCorrectionPoly m j) =
        p ^ ((m + 1) * (j.val + 1)) *
          parameterEval p (sourceQuotientQuotientPoly m j) := by
        simpa [d, parameterEval] using hscale
      rw [hfac']
      field_simp [hpd, hn]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscale'.symm
    dsimp [d] at hkc
    rw [hfull, hQbase, hshort, hQshift] at hkc
    exact hkc
  rw [hmoment, hsumC]
  simp_rw [hgeomCorrection, hprefix]
  rw [← hkc']
  ring

/-- The finite source correction is the paper's literal `β_m`, for every
index `m`, including the exceptional clearing cases `m=0,1`. -/
theorem sourceFiniteCorrectionPoly_eq_coefficientBetaPoly (m : ℕ) :
    sourceFiniteCorrectionPoly m = coefficientBetaPoly m := by
  apply coefficientBetaPoly_eq_of_pade_remainder m
  intro p hp
  simpa [realPolynomialEval, parameterEval] using
    sourcePade_actualMoment_remainder m p hp

/-- Unconditional all-index analytic remainder identity. -/
theorem sourcePade_actualMoment_eq_coefficientLinearForm
    (m : ℕ) (p : ℝ) (hp : 1 < p) :
    PaperR12.actualMoment p⁻¹ m =
      coefficientAlpha p m * PaperR16.lambert p⁻¹ - coefficientBeta p m := by
  rw [coefficientBeta, ← sourceFiniteCorrectionPoly_eq_coefficientBetaPoly m]
  simpa [coefficientBeta, parameterEval] using
    sourcePade_actualMoment_remainder m p hp

#print axioms sourcePade_actualMoment_remainder
#print axioms sourceFiniteCorrectionPoly_eq_coefficientBetaPoly
#print axioms sourcePade_actualMoment_eq_coefficientLinearForm

end
end ErdosProblems.Erdos1049.PaperR20
