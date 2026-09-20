import Mathlib

/-! The boundary condition for genuine dyadic tails, with arbitrary real
coefficients and the paper's absolute-convergence hypothesis. -/
namespace ErdosProblems.Erdos251.PaperCompleteR20
open Filter Finset
open scoped BigOperators Topology

noncomputable def realDyadicTail (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, a (N + j + 1) / 2 ^ (j + 1)

theorem dyadic_orbit_prefix_identity (a U : ℕ → ℝ)
    (hrec : ∀ N, U (N + 1) = 2 * U N - a (N + 1)) (N : ℕ) :
    U N / 2 ^ N = U 0 - ∑ j ∈ range N, a (j + 1) / 2 ^ (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [hrec, sum_range_succ]
      calc
        (2 * U N - a (N + 1)) / 2 ^ (N + 1) =
            U N / 2 ^ N - a (N + 1) / 2 ^ (N + 1) := by
              rw [pow_succ]
              field_simp
              <;> ring
        _ = _ := by rw [ih]; ring

theorem realDyadicTail_scaled (a : ℕ → ℝ)
    (hs : Summable (fun j : ℕ => a (j + 1) / (2 : ℝ) ^ (j + 1))) (N : ℕ) :
    realDyadicTail a N / 2 ^ N =
      (∑' j : ℕ, a (j + 1) / (2 : ℝ) ^ (j + 1)) -
        ∑ j ∈ range N, a (j + 1) / (2 : ℝ) ^ (j + 1) := by
  have hsplit := hs.sum_add_tsum_nat_add N
  have htail : realDyadicTail a N =
      (2 : ℝ) ^ N * ∑' j : ℕ, a (j + N + 1) / (2 : ℝ) ^ (j + N + 1) := by
    unfold realDyadicTail
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    rw [show j + N + 1 = N + (j + 1) by omega, pow_add]
    field_simp
    <;> ring
  rw [htail]
  have htwo : (2 : ℝ) ^ N ≠ 0 := by positivity
  field_simp
  nlinarith [hsplit]

theorem realDyadicTail_div_pow_tendsto_zero (a : ℕ → ℝ)
    (hs : Summable (fun j : ℕ => a (j + 1) / (2 : ℝ) ^ (j + 1))) :
    Tendsto (fun N : ℕ => realDyadicTail a N / 2 ^ N) atTop (𝓝 0) := by
  simp_rw [realDyadicTail_scaled a hs]
  have h := hs.hasSum.tendsto_sum_nat
  convert (tendsto_const_nhds.sub h :
    Tendsto (fun N : ℕ => (∑' j : ℕ, a (j + 1) / (2 : ℝ) ^ (j + 1)) -
      ∑ j ∈ range N, a (j + 1) / (2 : ℝ) ^ (j + 1)) atTop _ ) using 1
  simp

theorem real_dyadic_orbit_eq_true_tail_iff (a U : ℕ → ℝ)
    (habs : Summable (fun j : ℕ => |a (j + 1)| / (2 : ℝ) ^ (j + 1)))
    (hrec : ∀ N, U (N + 1) = 2 * U N - a (N + 1)) :
    (∀ N, U N = realDyadicTail a N) ↔
      Tendsto (fun N : ℕ => U N / 2 ^ N) atTop (𝓝 0) := by
  have hs : Summable (fun j : ℕ => a (j + 1) / (2 : ℝ) ^ (j + 1)) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using habs
  constructor
  · intro h
    simpa only [h] using realDyadicTail_div_pow_tendsto_zero a hs
  · intro htemp
    have hlim : Tendsto (fun N : ℕ => U N / 2 ^ N) atTop
        (𝓝 (U 0 - ∑' j : ℕ, a (j + 1) / (2 : ℝ) ^ (j + 1))) := by
      simpa only [dyadic_orbit_prefix_identity a U hrec] using
        tendsto_const_nhds.sub hs.hasSum.tendsto_sum_nat
    have hzero := tendsto_nhds_unique hlim htemp
    have hinit := sub_eq_zero.mp hzero
    intro N
    have heq : U N / (2 : ℝ) ^ N = realDyadicTail a N / (2 : ℝ) ^ N := by
      rw [dyadic_orbit_prefix_identity a U hrec, realDyadicTail_scaled a hs, hinit]
    exact (div_left_inj' (by positivity : (2 : ℝ) ^ N ≠ 0)).mp heq

#print axioms real_dyadic_orbit_eq_true_tail_iff
end ErdosProblems.Erdos251.PaperCompleteR20
