import Mathlib

/-!
# Erdős #1041, concyclic zeros: the spoke calculus kernel

Companion to `ConcyclicSpokeCalculus.md`.  Formalized here are the load-bearing
algebraic steps, and only those.

* `spoke_factor_normSq` / `spoke_normSq_prod` — Theorem 1, the spoke normal form
  `‖t w - v‖² = (1-t)² + t ‖w - v‖²` for `w`, `v` on the unit circle, and its
  product over the zeros.  The profile of `|g|` along the radius towards a zero
  therefore depends on the other zeros only through their chord distances to it.
* `sum_pairs_eq_normSq_sum` — the orbit-balance step
  `∑_{j,k} a_j conj(a_k) = ‖∑_j a_j‖²`, applied with `a_j = w_j^m` to collapse
  the double sum over spokes to `|s_m|²`.  This is what makes the deficit in
  Theorem 2 a series with nonnegative coefficients.
* `radial_term_le` — each term of `d/dt log|g(t w_j)|` is at most `1/(1+t)`,
  the difference being `(1-t)(1+c) ≥ 0`, so the antipode is the only equality
  case; and `threshold_bound_nonpos` — the resulting sharp threshold `(n-2)/n`
  of Theorem 3(iii).

Nothing here asserts Erdős #1041, nor the concyclic case of it.  The analytic
companion is explicit that both remain open.
-/

namespace ErdosProblems.Erdos1041

open Finset

/-- **Spoke normal form, one factor.**  For `w`, `v` on the unit circle and real
`t`, the squared distance from `t w` to `v` splits into a purely radial part and
the chord distance `‖w - v‖`. -/
theorem spoke_factor_normSq (w v : ℂ) (hw : Complex.normSq w = 1)
    (hv : Complex.normSq v = 1) (t : ℝ) :
    Complex.normSq ((t : ℂ) * w - v) = (1 - t) ^ 2 + t * Complex.normSq (w - v) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    sub_zero, zero_sub, zero_add, add_zero] at hw hv ⊢
  linear_combination (t * (t - 1)) * hw + (1 - t) * hv

/-- **Spoke normal form, Theorem 1.**  The whole profile of `‖g‖²` along the
radius towards a zero is a function of the chord distances alone. -/
theorem spoke_normSq_prod {ι : Type*} (s : Finset ι) (v : ι → ℂ) (w : ℂ)
    (hw : Complex.normSq w = 1) (hv : ∀ i ∈ s, Complex.normSq (v i) = 1) (t : ℝ) :
    ∏ i ∈ s, Complex.normSq ((t : ℂ) * w - v i)
      = ∏ i ∈ s, ((1 - t) ^ 2 + t * Complex.normSq (w - v i)) :=
  Finset.prod_congr rfl fun i hi => spoke_factor_normSq w (v i) hw (hv i hi) t

/-- **Orbit-balance step.**  The double sum over ordered pairs of
`a_j conj(a_k)` is the squared norm of the sum.  Taken with `a_j = w_j ^ m` this
is the identity `∑_j Re(w_j^m conj(s_m)) = |s_m|²` that makes the deficit of
Theorem 2 a power series with nonnegative coefficients, hence `≤ 0`. -/
theorem sum_pairs_eq_normSq_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    ∑ j ∈ s, ∑ k ∈ s, a j * (starRingEnd ℂ) (a k)
      = (Complex.normSq (∑ j ∈ s, a j) : ℂ) := by
  rw [← Complex.mul_conj, ← map_sum, Finset.sum_mul_sum]

/-- **Radial derivative, one term.**  Every term of
`d/dt log|g(t w_j)| = ∑_k (t - cos θ_k)/(1 - 2 t cos θ_k + t²)` is at most
`1/(1+t)`; the gap is exactly `(1-t)(1+c) ≥ 0`, so equality forces `c = -1`
(the antipode) or `t = 1`. -/
theorem radial_term_le (t c : ℝ) (ht1 : t ≤ 1) (hc : -1 ≤ c)
    (hpos : 0 < 1 - 2 * t * c + t ^ 2) (hden : 0 < 1 + t) :
    (t - c) / (1 - 2 * t * c + t ^ 2) ≤ 1 / (1 + t) := by
  rw [div_le_div_iff hpos hden]
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (by linarith : (0:ℝ) ≤ 1 + c)]

/-- **Threshold, Theorem 3(iii).**  The bound `-(1/(1-t)) + (n-1)/(1+t)` that
`radial_term_le` produces for `d/dt log|g(t w_j)|` is nonpositive exactly from
`t = (n-2)/n` onwards. -/
theorem threshold_bound_nonpos (n : ℕ) (hn : 2 ≤ n) (t : ℝ)
    (ht : ((n : ℝ) - 2) / (n : ℝ) ≤ t) (ht1 : t < 1) (ht0 : 0 ≤ t) :
    -(1 / (1 - t)) + ((n : ℝ) - 1) / (1 + t) ≤ 0 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn
    exact_mod_cast h
  have hA : (0 : ℝ) < 1 - t := by linarith
  have hB : (0 : ℝ) < 1 + t := by linarith
  have hmul : (n : ℝ) - 2 ≤ (n : ℝ) * t := by
    have h := (div_le_iff₀ hn0).mp ht
    linarith
  rw [neg_add_eq_sub, sub_nonpos, div_le_div_iff hB hA]
  nlinarith

end ErdosProblems.Erdos1041
