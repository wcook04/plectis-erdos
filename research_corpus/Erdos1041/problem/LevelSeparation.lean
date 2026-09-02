import ErdosProblems.Erdos1041.NewtonFlowRaySeparation

/-!
# Erdős #1041: separating critical *levels*, not only critical arguments

`exists_small_translation_separating_arguments` makes an arbitrarily small
translation after which no two critical values lie on one oriented ray.  That
is exactly what excludes finite Newton saddle connections, because the checked
exponential decay puts connection endpoints on one ray.

For the Morse theory of `u = -log |g|` one also needs the saddle **levels** to
be distinct, i.e. the translated critical values to have pairwise distinct
moduli.  The equal-modulus locus of a pair is another real affine line — the
perpendicular bisector — so the same finite-avoidance argument covers it:

`exists_small_translation_separating_arguments_and_norms`.

One infinitesimal translation therefore simultaneously makes every critical
value nonzero, ray-separated, and level-separated.

This does not prove the short-path theorem for Erdős #1041.  It removes one
hypothesis-management obstacle: distinct saddle levels no longer need to be
assumed.
-/

namespace ErdosProblems.Erdos1041

open Complex

/-- **The equal-modulus locus of a translated pair is a real affine line** —
the perpendicular bisector, in the explicit parametrisation consumed by the
finite-avoidance machinery. -/
theorem equal_norm_add_imp_mem_realAffineLine {a b shift : ℂ} (hab : a ≠ b)
    (h : ‖a + shift‖ = ‖b + shift‖) :
    shift ∈ realAffineLine
      ((((Complex.normSq b - Complex.normSq a) /
          (2 * Complex.normSq (a - b)) : ℝ)) • (a - b))
      (Complex.I * (a - b)) := by
  have hd0 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hnd : Complex.normSq (a - b) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hd0
  have hndpos : 0 < Complex.normSq (a - b) :=
    lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hnd)
  -- squaring the modulus equation
  have hsq : Complex.normSq (a + shift) = Complex.normSq (b + shift) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h]
  rw [Complex.normSq_apply, Complex.normSq_apply] at hsq
  simp only [Complex.add_re, Complex.add_im] at hsq
  -- everything in real coordinates
  have hndc : Complex.normSq (a - b)
      = (a.re - b.re) * (a.re - b.re) + (a.im - b.im) * (a.im - b.im) := by
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  set nd : ℝ := Complex.normSq (a - b) with hnddef
  set cst : ℝ := (Complex.normSq b - Complex.normSq a) / (2 * nd) with hcst
  have hnd2 : (2 : ℝ) * nd ≠ 0 := by
    simp only [ne_eq, mul_eq_zero]
    push_neg
    exact ⟨by norm_num, hnd⟩
  -- the linear form cut out by equal moduli
  have hlin : 2 * ((a.re - b.re) * shift.re + (a.im - b.im) * shift.im)
      = Complex.normSq b - Complex.normSq a := by
    rw [Complex.normSq_apply, Complex.normSq_apply]
    linear_combination hsq
  -- residual coordinates
  set wr : ℝ := shift.re - cst * (a.re - b.re) with hwr
  set wi : ℝ := shift.im - cst * (a.im - b.im) with hwi
  have hcstnd : cst * (2 * nd) = Complex.normSq b - Complex.normSq a := by
    rw [hcst]; field_simp
  have horth : (a.re - b.re) * wr + (a.im - b.im) * wi = 0 := by
    rw [hwr, hwi]
    have hexp : (a.re - b.re) * (shift.re - cst * (a.re - b.re))
        + (a.im - b.im) * (shift.im - cst * (a.im - b.im))
        = ((a.re - b.re) * shift.re + (a.im - b.im) * shift.im)
          - cst * ((a.re - b.re) * (a.re - b.re) + (a.im - b.im) * (a.im - b.im)) := by
      ring
    rw [hexp, ← hndc]
    linarith [hlin, hcstnd]
  -- rotate the residual onto `I * (a - b)`
  have hne : ((a.re - b.re) ^ 2 + (a.im - b.im) ^ 2) ≠ 0 := by
    have hnd' := hnd
    rw [hndc] at hnd'
    have hpow : (a.re - b.re) ^ 2 + (a.im - b.im) ^ 2
        = (a.re - b.re) * (a.re - b.re) + (a.im - b.im) * (a.im - b.im) := by ring
    rw [hpow]
    exact hnd'
  have hshiftre : shift.re = wr + cst * (a.re - b.re) := by rw [hwr]; ring
  have hshiftim : shift.im = wi + cst * (a.im - b.im) := by rw [hwi]; ring
  refine ⟨((a.re - b.re) * wi - (a.im - b.im) * wr) / nd, ?_⟩
  apply Complex.ext
  · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im, zero_mul, one_mul, zero_sub, mul_zero, zero_add, sub_zero]
    rw [hndc]
    field_simp
    linear_combination (-(a.re - b.re)) * horth
      - ((a.re - b.re) ^ 2 + (a.im - b.im) ^ 2) * hshiftre
  · simp only [Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.sub_im, zero_mul, one_mul, zero_sub, mul_zero, zero_add, sub_zero]
    rw [hndc]
    field_simp
    linear_combination (-(a.im - b.im)) * horth
      - ((a.re - b.re) ^ 2 + (a.im - b.im) ^ 2) * hshiftim

/-- **One infinitesimal translation separates arguments *and* levels.**
After it, every critical value is nonzero, no two lie on one oriented ray, and
no two have the same modulus. -/
theorem exists_small_translation_separating_arguments_and_norms
    {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℂ)
    (hc : Function.Injective c) {ε : ℝ} (hε : 0 < ε) :
    ∃ shift : ℂ, ‖shift‖ < ε ∧
      (∀ i, c i + shift ≠ 0) ∧
      (∀ i j, i ≠ j → ¬ SamePositiveRay (c i + shift) (c j + shift)) ∧
      (∀ i j, i ≠ j → ‖c i + shift‖ ≠ ‖c j + shift‖) := by
  classical
  let p : ι ⊕ (ι × ι) ⊕ (ι × ι) → ℂ
    | Sum.inl i => -c i
    | Sum.inr (Sum.inl ij) => -c ij.2
    | Sum.inr (Sum.inr ij) =>
        (((Complex.normSq (c ij.2) - Complex.normSq (c ij.1)) /
            (2 * Complex.normSq (c ij.1 - c ij.2)) : ℝ)) • (c ij.1 - c ij.2)
  let v : ι ⊕ (ι × ι) ⊕ (ι × ι) → ℂ
    | Sum.inl _ => 1
    | Sum.inr (Sum.inl ij) => c ij.1 - c ij.2
    | Sum.inr (Sum.inr ij) => Complex.I * (c ij.1 - c ij.2)
  obtain ⟨shift, hsmall, havoid⟩ := exists_small_avoiding_finite_realAffineLines p v hε
  refine ⟨shift, hsmall, ?_, ?_, ?_⟩
  · intro i hi
    have hmem : shift ∈ realAffineLine (p (Sum.inl i)) (v (Sum.inl i)) := by
      refine ⟨0, ?_⟩
      change (0 : ℝ) • (1 : ℂ) + -c i = shift
      simpa using (neg_eq_iff_add_eq_zero.mpr hi)
    exact havoid (Sum.inl i) hmem
  · intro i j hij hray
    have hmem : shift ∈ realAffineLine
        (p (Sum.inr (Sum.inl (i, j)))) (v (Sum.inr (Sum.inl (i, j)))) := by
      simpa [p, v] using samePositiveRay_imp_mem_realAffineLine (hc.ne hij) hray
    exact havoid (Sum.inr (Sum.inl (i, j))) hmem
  · intro i j hij hnorm
    have hmem : shift ∈ realAffineLine
        (p (Sum.inr (Sum.inr (i, j)))) (v (Sum.inr (Sum.inr (i, j)))) := by
      simpa [p, v] using equal_norm_add_imp_mem_realAffineLine (hc.ne hij) hnorm
    exact havoid (Sum.inr (Sum.inr (i, j))) hmem

end ErdosProblems.Erdos1041
