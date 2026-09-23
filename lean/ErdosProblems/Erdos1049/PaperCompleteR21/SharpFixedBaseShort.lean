import ErdosProblems.Erdos1049.PaperR16.LambertBasic
import ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase

/-!
# Erdős #1049: the size of `V_N^*` at a fixed base, as the short paper states it

`res:sharp-fixed-base` of the short paper: for fixed `0 < q < 1` there is `K(q) > 0` with
`V_N^*(q) ∼ K(q) C_N q^{B_N} P^{2N} N^{-8F(1/q)}`, where `P = (q;q)_∞`, `B_N = N(N-1)(2N-1)/6`,
`C_N = (N!)^2 (N+1)!/2^N` and `F(p) = ∑_{n ≥ 1} 1/(p^n - 1)`. With the tree's convention
`F(p) = lambert (1/p)`, the exponent `F(1/q) = ∑_{n ≥ 1} q^n/(1 - q^n)` is `PaperR16.lambert q`.

The theorem is `sharp_fixed_base_exists`. It takes `K(q) = 𝓐(q) 𝓜(q)^3` from `sharp_fixed_base`,
applied to the coefficients `actualGamma q` of `G_q`; `lambertL_eq_lambert` identifies the
long record's `L` with `F(1/q)` and `orderB_eq_closed_form` identifies `B_N`.
-/

namespace ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase

open Filter Finset
open scoped Topology

/-- The long record's `L = ∑_{r ≥ 1} q^r/(1 - q^r)` is `F(1/q)`, the literal Lambert series at `q`. -/
lemma lambertL_eq_lambert {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    lambertL q = PaperR16.lambert q := by
  have h : HasSum (PaperR16.lambertTerm q) (lambertL q) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [PaperR16.lambertTerm, lambertL_eq hq0 hq1] using hasSum_lambert hq0 hq1
  simpa [PaperR16.lambert] using h.tsum_eq.symm

lemma six_mul_orderB_succ (m : ℕ) : 6 * orderB (m + 1) = (m + 1) * m * (2 * m + 1) := by
  induction m with
  | zero => simp [orderB]
  | succ m ih =>
    have hs : orderB (m + 1 + 1) = orderB (m + 1) + (m + 1) ^ 2 := by
      simp only [orderB, Finset.sum_range_succ]
    rw [hs, mul_add, ih]
    ring

/-- `B_N = ∑_{j<N} j^2 = N(N-1)(2N-1)/6`. -/
lemma orderB_eq_closed_form (N : ℕ) : N * (N - 1) * (2 * N - 1) / 6 = orderB N := by
  cases N with
  | zero => simp [orderB]
  | succ m =>
    have h1 : m + 1 - 1 = m := by omega
    have h2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    rw [h1, h2, ← six_mul_orderB_succ m]
    exact Nat.mul_div_cancel_left _ (by norm_num)

/-- `res:sharp-fixed-base` (short paper). For fixed `0 < q < 1` there is `K(q) > 0` with
`V_N^*(q) ∼ K(q) C_N q^{B_N} P^{2N} N^{-8F(1/q)}`: the ratio tends to `1`. Here
`V_N^*(q) = det (v^*_{i+j}(q))_{0 ≤ i,j < N}` (`actualMomentHankel`), `B_N = N(N-1)(2N-1)/6`,
`C_N = (N!)^2 (N+1)!/2^N` (`leadC`), `P = (q;q)_∞` and `F(1/q) = PaperR16.lambert q`. -/
theorem sharp_fixed_base_exists {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun N : ℕ => (PaperR16.actualMomentHankel q N).det /
        (K * leadC N * q ^ (N * (N - 1) * (2 * N - 1) / 6) *
          PaperR10.qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * PaperR16.lambert q))) atTop (𝓝 1) := by
  obtain ⟨-, hA, hmain, -⟩ := sharp_fixed_base hq0 hq1 (PaperR16.actualGamma q)
    (fun w hw0 hw1 => PaperR16.actualGamma_hasSum hq0 hq1 hw0 hw1)
  refine ⟨sharpK q (PaperR16.actualGamma q),
    mul_pos hA (pow_pos (GeometricUniversality.gramM_pos hq0.le hq1) 3), ?_⟩
  simpa only [orderB_eq_closed_form, lambertL_eq_lambert hq0 hq1] using hmain

end ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base_exists
