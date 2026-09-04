import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open scoped ComplexConjugate

/-!
# Erdős #1041: complete near-Fekete hub-orbit cancellation

The near-Fekete critical forest has a cyclic family of hub directions.  An
individual directional charge may be negative, so the relevant object is the
complete component fan-in.  This file records the exact algebra behind that
fan-in.

For complex directions `ν` whose squares sum to zero, the oscillating term in
the product of two imaginary parts cancels.  If the directions also have unit
norm, the whole orbit is exactly its cardinality times the real correlation
`re (a * conj b)`.  Thus a nonnegative correlation gives a nonnegative
complete-orbit correlation even when some individual summands are negative.

This is deliberately only the algebraic orbit kernel.  It does not average the
full near-Fekete branch charge: the branch parameter and its positive weight
still depend on the chosen hub direction.  A consumer must first produce a
common parameter or an invariant measure before applying these identities.
-/

namespace ErdosProblems.Erdos1041

/-- Polarization of a product of imaginary parts.  The second term is the
frequency-two oscillation which disappears after summing over a complete
root-of-unity orbit. -/
theorem two_mul_im_mul_im (ν a b : ℂ) :
    2 * (ν * a).im * (ν * b).im =
      Complex.normSq ν * (a * conj b).re - (ν ^ 2 * a * b).re := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply, pow_two]
  ring

/-- A finite family with vanishing square moment has no frequency-two
contribution to its total imaginary-part correlation. -/
theorem two_mul_sum_im_mul_im_of_sum_sq_eq_zero
    {ι : Type*} (s : Finset ι) (ν : ι → ℂ) (a b : ℂ)
    (h_sq : ∑ i ∈ s, ν i ^ 2 = 0) :
    2 * ∑ i ∈ s, (ν i * a).im * (ν i * b).im =
      (∑ i ∈ s, Complex.normSq (ν i)) * (a * conj b).re := by
  have h_osc_complex : ∑ i ∈ s, ν i ^ 2 * a * b = 0 := by
    calc
      ∑ i ∈ s, ν i ^ 2 * a * b = (∑ i ∈ s, ν i ^ 2) * a * b := by
        simp only [Finset.sum_mul]
      _ = 0 := by rw [h_sq]; simp
  have h_osc_real : ∑ i ∈ s, (ν i ^ 2 * a * b).re = 0 := by
    have := congrArg Complex.re h_osc_complex
    simpa using this
  calc
    2 * ∑ i ∈ s, (ν i * a).im * (ν i * b).im =
        ∑ i ∈ s, 2 * ((ν i * a).im * (ν i * b).im) := by
          simp only [Finset.mul_sum]
    _ = ∑ i ∈ s,
        (Complex.normSq (ν i) * (a * conj b).re -
          (ν i ^ 2 * a * b).re) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← two_mul_im_mul_im]
          ring
    _ = (∑ i ∈ s, Complex.normSq (ν i)) * (a * conj b).re -
        ∑ i ∈ s, (ν i ^ 2 * a * b).re := by
          rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = (∑ i ∈ s, Complex.normSq (ν i)) * (a * conj b).re := by
          rw [h_osc_real, sub_zero]

/-- For unit directions, the doubled complete-orbit correlation is exactly
the orbit cardinality times the underlying real correlation. -/
theorem two_mul_sum_im_mul_im_of_unit_sum_sq_eq_zero
    {ι : Type*} (s : Finset ι) (ν : ι → ℂ) (a b : ℂ)
    (h_unit : ∀ i ∈ s, Complex.normSq (ν i) = 1)
    (h_sq : ∑ i ∈ s, ν i ^ 2 = 0) :
    2 * ∑ i ∈ s, (ν i * a).im * (ν i * b).im =
      (s.card : ℝ) * (a * conj b).re := by
  rw [two_mul_sum_im_mul_im_of_sum_sq_eq_zero s ν a b h_sq]
  congr 1
  calc
    ∑ i ∈ s, Complex.normSq (ν i) = ∑ _i ∈ s, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact h_unit i hi
    _ = (s.card : ℝ) := by simp

/-- The complete orbit has nonnegative total correlation whenever the
surviving real correlation is nonnegative.  No sign assumption is imposed on
any individual summand. -/
theorem sum_im_mul_im_nonneg_of_unit_sum_sq_eq_zero
    {ι : Type*} (s : Finset ι) (ν : ι → ℂ) (a b : ℂ)
    (h_unit : ∀ i ∈ s, Complex.normSq (ν i) = 1)
    (h_sq : ∑ i ∈ s, ν i ^ 2 = 0)
    (h_corr : 0 ≤ (a * conj b).re) :
    0 ≤ ∑ i ∈ s, (ν i * a).im * (ν i * b).im := by
  have h_identity :=
    two_mul_sum_im_mul_im_of_unit_sum_sq_eq_zero s ν a b h_unit h_sq
  have h_card : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- A nontrivial finite geometric orbit sums to zero.  The formulation avoids
division, so the only excluded case is the constant orbit `x = 1`. -/
theorem complex_geom_sum_eq_zero_of_pow_eq_one
    (x : ℂ) (m : ℕ) (h_pow : x ^ m = 1) (h_ne : x ≠ 1) :
    ∑ i ∈ Finset.range m, x ^ i = 0 := by
  have h_geom := geom_sum_mul x m
  rw [h_pow, sub_self] at h_geom
  exact (mul_eq_zero.mp h_geom).resolve_right (sub_ne_zero.mpr h_ne)

/-- Rotating a seed by a cyclic generator whose square is nontrivial gives a
family with vanishing square moment.  For a primitive orbit this is precisely
the condition that its cardinality is greater than two. -/
theorem cyclic_orbit_sum_sq_eq_zero
    (ζ ν₀ : ℂ) (m : ℕ)
    (h_pow : ζ ^ m = 1) (h_sq_ne : ζ ^ 2 ≠ 1) :
    ∑ i ∈ Finset.range m, (ζ ^ i * ν₀) ^ 2 = 0 := by
  have h_sq_pow : (ζ ^ 2) ^ m = 1 := by
    calc
      (ζ ^ 2) ^ m = ζ ^ (2 * m) := by rw [pow_mul]
      _ = ζ ^ (m * 2) := by rw [Nat.mul_comm]
      _ = (ζ ^ m) ^ 2 := by rw [pow_mul]
      _ = 1 := by rw [h_pow]; simp
  have h_geom :=
    complex_geom_sum_eq_zero_of_pow_eq_one (ζ ^ 2) m h_sq_pow h_sq_ne
  calc
    ∑ i ∈ Finset.range m, (ζ ^ i * ν₀) ^ 2 =
        (∑ i ∈ Finset.range m, (ζ ^ 2) ^ i) * ν₀ ^ 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = 0 := by rw [h_geom]; simp

/-- Every member of a cyclic orbit has unit squared norm when both its
generator and seed do. -/
theorem cyclic_orbit_normSq_eq_one
    (ζ ν₀ : ℂ) (hζ : Complex.normSq ζ = 1)
    (hν₀ : Complex.normSq ν₀ = 1) (i : ℕ) :
    Complex.normSq (ζ ^ i * ν₀) = 1 := by
  have hζ_pow : Complex.normSq (ζ ^ i) = 1 := by
    induction i with
    | zero => simp [Complex.normSq_apply]
    | succ i ih =>
        rw [pow_succ, Complex.normSq_mul, ih, hζ, one_mul]
  rw [Complex.normSq_mul, hζ_pow, hν₀, one_mul]

/-- Concrete cyclic-orbit form of the averaging identity. -/
theorem two_mul_cyclic_orbit_sum_im_mul_im
    (ζ ν₀ a b : ℂ) (m : ℕ)
    (hζ : Complex.normSq ζ = 1) (hν₀ : Complex.normSq ν₀ = 1)
    (h_pow : ζ ^ m = 1) (h_sq_ne : ζ ^ 2 ≠ 1) :
    2 * ∑ i ∈ Finset.range m,
        (ζ ^ i * ν₀ * a).im * (ζ ^ i * ν₀ * b).im =
      (m : ℝ) * (a * conj b).re := by
  simpa using
    two_mul_sum_im_mul_im_of_unit_sum_sq_eq_zero
      (Finset.range m) (fun i => ζ ^ i * ν₀) a b
      (fun i hi => cyclic_orbit_normSq_eq_one ζ ν₀ hζ hν₀ i)
      (cyclic_orbit_sum_sq_eq_zero ζ ν₀ m h_pow h_sq_ne)

/-- A complete cyclic orbit has nonnegative total correlation when the common
real correlation is nonnegative. -/
theorem cyclic_orbit_sum_im_mul_im_nonneg
    (ζ ν₀ a b : ℂ) (m : ℕ)
    (hζ : Complex.normSq ζ = 1) (hν₀ : Complex.normSq ν₀ = 1)
    (h_pow : ζ ^ m = 1) (h_sq_ne : ζ ^ 2 ≠ 1)
    (h_corr : 0 ≤ (a * conj b).re) :
    0 ≤ ∑ i ∈ Finset.range m,
      (ζ ^ i * ν₀ * a).im * (ζ ^ i * ν₀ * b).im := by
  apply sum_im_mul_im_nonneg_of_unit_sum_sq_eq_zero
  · intro i hi
    exact cyclic_orbit_normSq_eq_one ζ ν₀ hζ hν₀ i
  · exact cyclic_orbit_sum_sq_eq_zero ζ ν₀ m h_pow h_sq_ne
  · exact h_corr

end ErdosProblems.Erdos1041
