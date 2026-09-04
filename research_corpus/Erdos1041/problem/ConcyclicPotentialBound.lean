import Mathlib

/-!
# Erdős #1041, concyclic zeros: the potential domination kernel

Companion to `ConcyclicFormACutCertificate.md`.  Formalized here are the
load-bearing *sufficient* bounds that turn first-power-sum projections into
containment statements on chords of a concyclic configuration.

* `one_add_log_le` / `one_sub_normSq_le_exp` — the elementary factor bound
  `log|1 - w| <= |w|^2/2 - Re w`, i.e. `|1 - w|^2 <= exp(|w|^2 - 2 Re w)`
  for `|w| < 1`.  This is the only analytic input; everything else is algebra.
* `normSq_sub_eq_normSq_one_sub_mul_conj` — repointing a factor at a
  unit-modulus root to the origin-centred form.
* `prod_normSq_le_exp_sum` — multiplicative fan-in:
  `prod_i |z - v_i|^2 <= exp(n |z|^2 - 2 sum_i Re(z conj(v_i)))`.
* `prod_normSq_le_one_of_projection` — the certificate corollary: if
  `n |z|^2 / 2 <= sum_i Re(z conj(v_i))`, then `prod_i |z - v_i|^2 <= 1`.

Nothing here asserts Erdős #1041, nor the concyclic case of it.
-/

namespace ErdosProblems.Erdos1041

/-- The scalar engine behind every bound in this module: `log(1+u) <= u`
for `u > -1`. -/
theorem one_add_log_le {u : ℝ} (hu : -1 < u) : Real.log (1 + u) ≤ u := by
  have hpos : 0 < 1 + u := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-- **Factor bound.** For `|w| < 1`:
`|1 - w|^2 <= exp(|w|^2 - 2 Re w)`. -/
theorem one_sub_normSq_le_exp {w : ℂ} (hw : Complex.normSq w < 1) :
    Complex.normSq (1 - w) ≤ Real.exp (Complex.normSq w - 2 * Complex.re w) := by
  have hkey : Complex.normSq (1 - w)
      = 1 + (Complex.normSq w - 2 * Complex.re w) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  have hgt : -1 < Complex.normSq w - 2 * Complex.re w := by
    have hwne : w ≠ 1 := by
      intro hc
      rw [hc] at hw
      norm_num at hw
    have hpos : 0 < Complex.normSq (1 - w) :=
      Complex.normSq_pos.mpr (sub_ne_zero_of_ne (Ne.symm hwne))
    linarith [hpos, hkey]
  refine (Real.log_le_iff_le_exp ?_).mp ?_
  · rw [hkey]
    linarith
  · rw [hkey]
    exact one_add_log_le hgt

/-- Norm is invariant under the conjugate (star) automorphism. -/
theorem normSq_star {w : ℂ} :
    Complex.normSq ((starRingEnd ℂ) w) = Complex.normSq w := by
  simp [Complex.normSq_apply, Complex.conj_re, Complex.conj_im]

/-- Repointing: for `|v| = 1`, the factor at `z` equals the origin-centred
factor at `z * conj v`: `|z - v|^2 = |1 - z * conj(v)|^2`. -/
theorem normSq_sub_eq_normSq_one_sub_mul_conj (z v : ℂ)
    (hv : Complex.normSq v = 1) :
    Complex.normSq (z - v) = Complex.normSq (1 - z * (starRingEnd ℂ) v) := by
  have hprod : v * (starRingEnd ℂ) v = 1 := by
    have h := Complex.mul_conj v
    rw [hv] at h
    simpa using h
  have hshift : (1 : ℂ) - z * (starRingEnd ℂ) v
      = (-1 : ℂ) * ((starRingEnd ℂ) v * (z - v)) := by
    rw [mul_sub]
    have h2 : (starRingEnd ℂ) v * v = 1 := by
      rw [mul_comm, Complex.mul_conj, hv]
      simp
    rw [h2]
    ring
  have hsq := congrArg Complex.normSq hshift
  simp only [Complex.normSq_mul, normSq_star, Complex.normSq_neg,
    Complex.normSq_one, one_mul, hv] at hsq
  exact hsq.symm

/-- **Multiplicative fan-in.** With all roots of unit modulus and
`P = ∑_i Re(z * conj(v_i))`,
`∏_i |z - v_i|^2 <= exp(|s| * |z|^2 - 2 P)`. -/
theorem prod_normSq_le_exp_sum {ι : Type*} (s : Finset ι) (v : ι → ℂ)
    (hv : ∀ i ∈ s, Complex.normSq (v i) = 1) {z : ℂ} (hz : Complex.normSq z < 1) :
    ∏ i ∈ s, Complex.normSq (z - v i)
      ≤ Real.exp ((s.card : ℝ) * Complex.normSq z
        - 2 * ∑ i ∈ s, Complex.re (z * (starRingEnd ℂ) (v i))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hv' : ∀ j ∈ s, Complex.normSq (v j) = 1 :=
      fun j hj => hv j (Finset.mem_insert_of_mem hj)
    have hvi : Complex.normSq (v i) = 1 := hv i (Finset.mem_insert_self i s)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hrefl : Complex.normSq (z - v i)
        = Complex.normSq (1 - z * (starRingEnd ℂ) (v i)) :=
      normSq_sub_eq_normSq_one_sub_mul_conj z (v i) hvi
    have hxi : Complex.normSq (z * (starRingEnd ℂ) (v i))
        = Complex.normSq z * Complex.normSq ((starRingEnd ℂ) (v i)) :=
      Complex.normSq_mul z ((starRingEnd ℂ) (v i))
    have hfac : Complex.normSq (z - v i)
        ≤ Real.exp (Complex.normSq z - 2 * Complex.re (z * (starRingEnd ℂ) (v i))) := by
      rw [hrefl]
      have hexact : Complex.normSq (z * (starRingEnd ℂ) (v i)) = Complex.normSq z := by
        rw [hxi, normSq_star, hvi, mul_one]
      have hstep : Complex.normSq (1 - z * (starRingEnd ℂ) (v i))
          ≤ Real.exp (Complex.normSq (z * (starRingEnd ℂ) (v i))
            - 2 * Complex.re (z * (starRingEnd ℂ) (v i))) :=
        one_sub_normSq_le_exp (by rw [hexact]; exact hz)
      rw [hexact] at hstep
      exact hstep
    have hrest : ∏ j ∈ s, Complex.normSq (z - v j)
        ≤ Real.exp ((s.card : ℝ) * Complex.normSq z
          - 2 * ∑ j ∈ s, Complex.re (z * (starRingEnd ℂ) (v j))) := ih hv'
    have hsum : (((s.card : ℕ)) + 1 : ℝ) * Complex.normSq z
        - 2 * (∑ j ∈ insert i s, Complex.re (z * (starRingEnd ℂ) (v j)))
        = (Complex.normSq z - 2 * Complex.re (z * (starRingEnd ℂ) (v i)))
          + ((s.card : ℝ) * Complex.normSq z
            - 2 * ∑ j ∈ s, Complex.re (z * (starRingEnd ℂ) (v j))) := by
      rw [Finset.sum_insert hi]
      ring
    refine le_trans (mul_le_mul_of_nonneg hfac hrest (Complex.normSq_nonneg _)
      (Real.exp_nonneg _)) ?_
    rw [← Real.exp_add, Real.exp_le_exp, Finset.card_insert_of_notMem hi]
    push_cast
    linarith [hsum]

/-- **Certificate corollary (chord form).** If the total projection satisfies
`(card s)/2 * |z|^2 <= ∑_i Re(z conj(v_i))`, then `∏_i |z - v_i|^2 <= 1`. -/
theorem prod_normSq_le_one_of_projection {ι : Type*} (s : Finset ι) (v : ι → ℂ)
    (hv : ∀ i ∈ s, Complex.normSq (v i) = 1) {z : ℂ} (hz : Complex.normSq z < 1)
    (hproj : (s.card : ℝ) * Complex.normSq z / 2
      ≤ ∑ i ∈ s, Complex.re (z * (starRingEnd ℂ) (v i))) :
    ∏ i ∈ s, Complex.normSq (z - v i) ≤ 1 := by
  have hexponent : (s.card : ℝ) * Complex.normSq z
      - 2 * ∑ i ∈ s, Complex.re (z * (starRingEnd ℂ) (v i)) ≤ 0 := by linarith
  have hbound := prod_normSq_le_exp_sum s v hv hz
  refine hbound.trans ?_
  have h1 : Real.exp ((s.card : ℝ) * Complex.normSq z
      - 2 * ∑ i ∈ s, Complex.re (z * (starRingEnd ℂ) (v i)))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr hexponent
  rw [Real.exp_zero] at h1
  exact h1

end ErdosProblems.Erdos1041
