import Mathlib
import ErdosProblems.Erdos1049.ActualPositiveMeasureR16
import ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisationAnalytic
import ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality

/-!
# Erdős #1049: the size of `V_N^*` at a fixed base

`long1049:thm:sharp-fixed-base` (core.tex, subsection "The size of `V_N^*` at a fixed base").
Fix `0 < q < 1`, `P = (q;q)_∞`, `L = ∑_{r ≥ 1} q^r/(1 - q^r)` (`lambertL`),
`c_k = (k+1)^2 (k+2)/2` (`cK`), `C_N = (N!)^2 (N+1)!/2^N = ∏_{k<N} c_k` (`leadC`, `prod_cK`),
`B_N = ∑_{j<N} j^2` (`orderB`), `γ_k = [w^k] G_q(w)` and `a_k = P^4 γ_k`. Then
`𝓐(q) = e^{-8 γ_E L} ∏_{k ≥ 0} (a_k/c_k) e^{8L/(k+1)}` (`sharpA`) converges to a positive value,
and with `K(q) = 𝓐(q) 𝓜(q)^3` (`sharpK`), `V_N^*(q) ∼ K(q) C_N q^{B_N} P^{2N} N^{-8L}`,
equivalently `log V_N^*(q) = B_N log q + log C_N + 2N log P - 8L log N + log K(q) + o(1)`.
The main theorem is `sharp_fixed_base`.

## Route

The paper obtains `a_k/c_k = 1 - 8L/(k+1) + O((k+1)^{-2})` from the two leading Taylor
coefficients of `(1-w)^4 G_q(w)` at `w = 1`. The Lean proof reaches the same expansion from the
factorisation `γ_k = (q;q)_k b^{(2)}_k b^{(3)}_k` of `RogersFactorisationAnalytic.lean`, where
`b^{(r)}` is the `r`-fold convolution of `e_n = 1/(q;q)_n`:
* `hasSum_tau`: `τ_n = P^{-1} - e_n` is exponentially small and `∑_n τ_n = L/P`; the value comes
  from the `q`-difference equations of `T(x) = ∑ x^m/(q;q)_m` and `U(x) = ∑ m x^m/(q;q)_m`
  (`T_rec`, `U_rec`, `hasSum_lambert`);
* `b2_expand`, `b3_expand`: `P^2 b^{(2)}_k = (k+1) - 2L + ε_k` and
  `P^3 b^{(3)}_k = (k+1)(k+2)/2 - 3L(k+1) + R_k`, with `0 ≤ ε_k ≤ E (k+1) q^k` and `|R_k|`
  bounded (`eps2_le`, `abs_rem3_le`);
* `summable_ell`: hence `log(a_k/c_k) + 8L/(k+1)` is summable.
`geometric_universality` applies to `a_k` through the Rogers proposition (`weight_pos`,
`tendsto_weight_ratio`, `weight_ratio_le` with `C = P^{-6}`, `κ = 3`), and Euler's constant enters
through `Real.tendsto_harmonic_sub_log`.
-/

noncomputable section

namespace ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase

open Filter Finset
open scoped Topology BigOperators
open ErdosProblems.Erdos1049.PaperR10 (qPochhammerFinite qPochhammerInfinity)
open ErdosProblems.Erdos1049.PaperR12 (actualGeneratingFunction actualMoment)
open ErdosProblems.Erdos1049.PaperR16 (actualMomentHankel)
open ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation (cK realGamma realB)
open ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality
  (gramM geomMoment geomHankelDet geometric_universality)

/-! ### The sequences `e_n = 1/(q;q)_n`, `δ_m`, `τ_n = P^{-1} - e_n` -/

section Tau

variable {q : ℝ}

/-- `e_n = 1/(q;q)_n`. -/
def einv (q : ℝ) (n : ℕ) : ℝ := (qPochhammerFinite q q n)⁻¹

/-- `δ_m = q^m/(q;q)_m`, the increment `e_m - e_{m-1}`. -/
def delta (q : ℝ) (m : ℕ) : ℝ := einv q m * q ^ m

/-- `P^{-1} = 1/(q;q)_∞`. -/
def Pinv (q : ℝ) : ℝ := (qPochhammerInfinity q q)⁻¹

/-- `τ_n = P^{-1} - e_n`. -/
def tau (q : ℝ) (n : ℕ) : ℝ := Pinv q - einv q n

/-- `L = F(1/q) = ∑_{r ≥ 1} q^r/(1 - q^r)`. -/
def lambertL (q : ℝ) : ℝ := ∑' r : ℕ, q ^ (r + 1) / (1 - q ^ (r + 1))

lemma qPoch_pos (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : 0 < qPochhammerFinite q q n :=
  PaperR10.qPochhammerFinite_pos hq0.le hq1 hq0.le hq1.le n

lemma P_pos (q : ℝ) : 0 < qPochhammerInfinity q q := PaperR10.qPochhammerInfinity_pos q q

lemma Pinv_pos (q : ℝ) : 0 < Pinv q := inv_pos.mpr (P_pos q)

lemma einv_pos (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : 0 < einv q n :=
  inv_pos.mpr (qPoch_pos hq0 hq1 n)

lemma one_le_einv (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : 1 ≤ einv q n :=
  (one_le_inv₀ (qPoch_pos hq0 hq1 n)).mpr
    (PaperR10.qPochhammerFinite_nonneg_le_one hq0.le hq1.le hq0.le hq1.le n).2

lemma einv_le (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : einv q n ≤ Pinv q :=
  inv_anti₀ (P_pos q) (PaperR10.qPochhammerInfinity_le_finite hq0.le hq1 hq0.le hq1 n)

lemma einv_zero (q : ℝ) : einv q 0 = 1 := by simp [einv]

lemma einv_succ_mul (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) :
    einv q (m + 1) * (1 - q ^ (m + 1)) = einv q m := by
  unfold einv
  rw [PaperR10.qPochhammerFinite_succ, ← pow_succ']
  have h1 := qPoch_pos hq0 hq1 m
  have h2 : 0 < 1 - q ^ (m + 1) := by
    have : q ^ (m + 1) < 1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero m)
    linarith
  field_simp

lemma einv_succ (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    einv q (n + 1) = einv q n + delta q (n + 1) := by
  rw [delta, ← einv_succ_mul hq0 hq1 n]
  ring

lemma einv_eq_sum (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    einv q n = ∑ m ∈ range (n + 1), delta q m := by
  induction n with
  | zero => simp [delta, einv_zero]
  | succ n ih => rw [sum_range_succ, ← ih, einv_succ hq0 hq1]

lemma delta_nonneg (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) : 0 ≤ delta q m :=
  mul_nonneg (einv_pos hq0 hq1 m).le (pow_nonneg hq0.le m)

lemma delta_le (hq0 : 0 < q) (hq1 : q < 1) (m : ℕ) : delta q m ≤ Pinv q * q ^ m :=
  mul_le_mul_of_nonneg_right (einv_le hq0 hq1 m) (pow_nonneg hq0.le m)

lemma tendsto_einv (hq0 : 0 < q) (hq1 : q < 1) : Tendsto (einv q) atTop (𝓝 (Pinv q)) :=
  (PaperR10.tendsto_qPochhammerFinite hq0.le hq1 hq0.le hq1).inv₀ (P_pos q).ne'

lemma hasSum_delta (hq0 : 0 < q) (hq1 : q < 1) : HasSum (delta q) (Pinv q) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (delta_nonneg hq0 hq1), ← tendsto_add_atTop_iff_nat 1]
  exact (tendsto_einv hq0 hq1).congr fun n => einv_eq_sum hq0 hq1 n

lemma hasSum_tau_tail (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    HasSum (fun m => delta q (m + (n + 1))) (tau q n) := by
  have h := (hasSum_nat_add_iff' (n + 1)).mpr (hasSum_delta hq0 hq1)
  rw [← einv_eq_sum hq0 hq1] at h
  exact h

lemma tau_nonneg (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : 0 ≤ tau q n :=
  (hasSum_tau_tail hq0 hq1 n).nonneg fun m => delta_nonneg hq0 hq1 _

/-- `β = P^{-1} q/(1-q)`, so that `τ_n ≤ β q^n`. -/
def betaT (q : ℝ) : ℝ := Pinv q * q / (1 - q)

lemma betaT_nonneg (hq0 : 0 < q) (hq1 : q < 1) : 0 ≤ betaT q := by
  unfold betaT
  have := Pinv_pos q
  have : 0 < 1 - q := by linarith
  positivity

lemma tau_le (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : tau q n ≤ betaT q * q ^ n := by
  have h1 := hasSum_tau_tail hq0 hq1 n
  have h2 : HasSum (fun m => Pinv q * q ^ (n + 1) * q ^ m) (Pinv q * q ^ (n + 1) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
  have hle : ∀ m, delta q (m + (n + 1)) ≤ Pinv q * q ^ (n + 1) * q ^ m := by
    intro m
    calc delta q (m + (n + 1)) ≤ Pinv q * q ^ (m + (n + 1)) := delta_le hq0 hq1 _
      _ = Pinv q * q ^ (n + 1) * q ^ m := by rw [pow_add]; ring
  have h1q : 1 - q ≠ 0 := by linarith
  calc tau q n ≤ Pinv q * q ^ (n + 1) * (1 - q)⁻¹ := hasSum_le hle h1 h2
    _ = betaT q * q ^ n := by
      unfold betaT
      field_simp
      ring

lemma tau_succ (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    tau q n = tau q (n + 1) + delta q (n + 1) := by
  unfold tau
  rw [einv_succ hq0 hq1]
  ring

lemma P_mul_einv (q : ℝ) (n : ℕ) :
    qPochhammerInfinity q q * einv q n = 1 - qPochhammerInfinity q q * tau q n := by
  unfold tau Pinv
  have := P_pos q
  field_simp
  ring

/-! ### The Lambert value `L`, through the generating functions `T` and `U` -/

/-- `T(x) = ∑ e_m x^m`. -/
def Tq (q x : ℝ) : ℝ := ∑' m : ℕ, einv q m * x ^ m

/-- `U(x) = ∑ m e_m x^m`. -/
def Uq (q x : ℝ) : ℝ := ∑' m : ℕ, (m : ℝ) * einv q m * x ^ m

lemma summable_T (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun m : ℕ => einv q m * x ^ m) :=
  Summable.of_nonneg_of_le (fun m => mul_nonneg (einv_pos hq0 hq1 m).le (pow_nonneg hx0 m))
    (fun m => mul_le_mul_of_nonneg_right (einv_le hq0 hq1 m) (pow_nonneg hx0 m))
    ((summable_geometric_of_lt_one hx0 hx1).mul_left (Pinv q))

lemma summable_U (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable (fun m : ℕ => (m : ℝ) * einv q m * x ^ m) := by
  have hg : Summable (fun m : ℕ => (m : ℝ) ^ 1 * x ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one 1
      (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (hg.mul_left (Pinv q))
  · have := einv_pos hq0 hq1 m
    positivity
  · rw [pow_one]
    have h1 := einv_le hq0 hq1 m
    have h2 : 0 ≤ (m : ℝ) * x ^ m := by positivity
    calc (m : ℝ) * einv q m * x ^ m = einv q m * ((m : ℝ) * x ^ m) := by ring
      _ ≤ Pinv q * ((m : ℝ) * x ^ m) := mul_le_mul_of_nonneg_right h1 h2

lemma T_rec (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Tq q (q * x) = (1 - x) * Tq q x := by
  have hqx0 : 0 ≤ q * x := mul_nonneg hq0.le hx0
  have hqx1 : q * x < 1 := by nlinarith
  have h1 : HasSum (fun m : ℕ => einv q m * x ^ m) (Tq q x) :=
    (summable_T hq0 hq1 hx0 hx1).hasSum
  have h2 : HasSum (fun m : ℕ => einv q m * (q * x) ^ m) (Tq q (q * x)) :=
    (summable_T hq0 hq1 hqx0 hqx1).hasSum
  have h3 : HasSum (fun m : ℕ => einv q m * x ^ m * (1 - q ^ m)) (Tq q x - Tq q (q * x)) := by
    convert h1.sub h2 using 1
    funext m
    rw [mul_pow]
    ring
  have h4 : HasSum (fun m : ℕ => einv q m * x ^ m * (1 - q ^ m)) (x * Tq q x) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [range_one, sum_singleton, pow_zero, sub_self, mul_zero, sub_zero]
    convert h1.mul_left x using 1
    funext m
    have e := einv_succ_mul hq0 hq1 m
    calc einv q (m + 1) * x ^ (m + 1) * (1 - q ^ (m + 1))
        = (einv q (m + 1) * (1 - q ^ (m + 1))) * x ^ (m + 1) := by ring
      _ = x * (einv q m * x ^ m) := by rw [e, pow_succ]; ring
  have := h3.unique h4
  linarith

lemma U_rec (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Uq q (q * x) = (1 - x) * Uq q x - x * Tq q x := by
  have hqx0 : 0 ≤ q * x := mul_nonneg hq0.le hx0
  have hqx1 : q * x < 1 := by nlinarith
  have hT : HasSum (fun m : ℕ => einv q m * x ^ m) (Tq q x) :=
    (summable_T hq0 hq1 hx0 hx1).hasSum
  have h1 : HasSum (fun m : ℕ => (m : ℝ) * einv q m * x ^ m) (Uq q x) :=
    (summable_U hq0 hq1 hx0 hx1).hasSum
  have h2 : HasSum (fun m : ℕ => (m : ℝ) * einv q m * (q * x) ^ m) (Uq q (q * x)) :=
    (summable_U hq0 hq1 hqx0 hqx1).hasSum
  have h3 : HasSum (fun m : ℕ => (m : ℝ) * einv q m * x ^ m * (1 - q ^ m))
      (Uq q x - Uq q (q * x)) := by
    convert h1.sub h2 using 1
    funext m
    rw [mul_pow]
    ring
  have h4 : HasSum (fun m : ℕ => (m : ℝ) * einv q m * x ^ m * (1 - q ^ m))
      (x * (Uq q x + Tq q x)) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [range_one, sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
    convert (h1.add hT).mul_left x using 1
    funext m
    have e := einv_succ_mul hq0 hq1 m
    calc ((m + 1 : ℕ) : ℝ) * einv q (m + 1) * x ^ (m + 1) * (1 - q ^ (m + 1))
        = ((m : ℝ) + 1) * (einv q (m + 1) * (1 - q ^ (m + 1))) * x ^ (m + 1) := by
          push_cast
          ring
      _ = x * ((m : ℝ) * einv q m * x ^ m + einv q m * x ^ m) := by rw [e, pow_succ]; ring
  have := h3.unique h4
  linarith

lemma one_le_T (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    1 ≤ Tq q x := by
  have hs := summable_T hq0 hq1 hx0 hx1
  have := hs.le_tsum 0 (fun m _ => mul_nonneg (einv_pos hq0 hq1 m).le (pow_nonneg hx0 m))
  calc (1 : ℝ) = einv q 0 * x ^ 0 := by rw [einv_zero, pow_zero, mul_one]
    _ ≤ Tq q x := this

lemma U_nonneg (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) (hx0 : 0 ≤ x) : 0 ≤ Uq q x :=
  tsum_nonneg fun m => by
    have := einv_pos hq0 hq1 m
    positivity

lemma UT_step (hq0 : 0 < q) (hq1 : q < 1) (j : ℕ) :
    Uq q (q ^ (j + 1 + 1)) / Tq q (q ^ (j + 1 + 1)) =
      Uq q (q ^ (j + 1)) / Tq q (q ^ (j + 1)) - q ^ (j + 1) / (1 - q ^ (j + 1)) := by
  have hx0 : 0 ≤ q ^ (j + 1) := pow_nonneg hq0.le _
  have hx1 : q ^ (j + 1) < 1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero j)
  rw [pow_succ' q (j + 1), T_rec hq0 hq1 hx0 hx1, U_rec hq0 hq1 hx0 hx1]
  have hT := one_le_T hq0 hq1 hx0 hx1
  have h1x : 0 < 1 - q ^ (j + 1) := by linarith
  have hTne : Tq q (q ^ (j + 1)) ≠ 0 := by linarith
  field_simp

lemma UT_telescope (hq0 : 0 < q) (hq1 : q < 1) (J : ℕ) :
    Uq q (q ^ (J + 1)) / Tq q (q ^ (J + 1)) =
      Uq q q / Tq q q - ∑ j ∈ range J, q ^ (j + 1) / (1 - q ^ (j + 1)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [UT_step hq0 hq1 J, ih, sum_range_succ]
    ring

lemma U_le (hq0 : 0 < q) (hq1 : q < 1) (J : ℕ) : Uq q (q ^ (J + 1)) ≤ q ^ J * Uq q q := by
  have hx0 : 0 ≤ q ^ (J + 1) := pow_nonneg hq0.le _
  have hx1 : q ^ (J + 1) < 1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero J)
  have hs1 := summable_U hq0 hq1 hx0 hx1
  have hs2 := summable_U hq0 hq1 hq0.le hq1
  unfold Uq
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun m => ?_) hs1 (hs2.mul_left _)
  rcases Nat.eq_zero_or_pos m with h | hm
  · subst h
    simp
  · have hpow : (q ^ (J + 1)) ^ m ≤ q ^ J * q ^ m := by
      rw [← pow_mul, ← pow_add]
      exact pow_le_pow_of_le_one hq0.le hq1.le (by nlinarith)
    have h0 : 0 ≤ (m : ℝ) * einv q m := by
      have := einv_pos hq0 hq1 m
      positivity
    calc (m : ℝ) * einv q m * (q ^ (J + 1)) ^ m ≤ (m : ℝ) * einv q m * (q ^ J * q ^ m) :=
          mul_le_mul_of_nonneg_left hpow h0
      _ = q ^ J * ((m : ℝ) * einv q m * q ^ m) := by ring

lemma hasSum_lambert (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun j : ℕ => q ^ (j + 1) / (1 - q ^ (j + 1))) (Uq q q / Tq q q) := by
  have h0 : ∀ j : ℕ, 0 ≤ q ^ (j + 1) / (1 - q ^ (j + 1)) := fun j => by
    have : q ^ (j + 1) < 1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero j)
    exact div_nonneg (pow_nonneg hq0.le _) (by linarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg h0]
  have hlim : Tendsto (fun J : ℕ => Uq q (q ^ (J + 1)) / Tq q (q ^ (J + 1))) atTop (𝓝 0) := by
    have hup : Tendsto (fun J : ℕ => q ^ J * Uq q q) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).mul_const (Uq q q)
    refine squeeze_zero (fun J => ?_) (fun J => ?_) hup
    · have hx0 : 0 ≤ q ^ (J + 1) := pow_nonneg hq0.le _
      have hx1 : q ^ (J + 1) < 1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero J)
      exact div_nonneg (U_nonneg hq0 hq1 _ hx0) (by linarith [one_le_T hq0 hq1 hx0 hx1])
    · have hx0 : 0 ≤ q ^ (J + 1) := pow_nonneg hq0.le _
      have hx1 : q ^ (J + 1) < 1 := pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero J)
      have hT := one_le_T hq0 hq1 hx0 hx1
      calc Uq q (q ^ (J + 1)) / Tq q (q ^ (J + 1)) ≤ Uq q (q ^ (J + 1)) :=
            div_le_self (U_nonneg hq0 hq1 _ hx0) hT
        _ ≤ q ^ J * Uq q q := U_le hq0 hq1 J
  have := (tendsto_const_nhds (x := Uq q q / Tq q q)).sub hlim
  rw [sub_zero] at this
  refine this.congr fun J => ?_
  rw [UT_telescope hq0 hq1 J]
  ring

lemma T_q_eq (hq0 : 0 < q) (hq1 : q < 1) : Tq q q = Pinv q :=
  (hasSum_delta hq0 hq1).tsum_eq

lemma lambertL_eq (hq0 : 0 < q) (hq1 : q < 1) : lambertL q = Uq q q / Tq q q :=
  (hasSum_lambert hq0 hq1).tsum_eq

lemma lambertL_nonneg (hq0 : 0 < q) (hq1 : q < 1) : 0 ≤ lambertL q := by
  rw [lambertL_eq hq0 hq1]
  exact div_nonneg (U_nonneg hq0 hq1 q hq0.le) (by linarith [one_le_T hq0 hq1 hq0.le hq1])

lemma U_q_eq (hq0 : 0 < q) (hq1 : q < 1) : Uq q q = lambertL q * Pinv q := by
  rw [lambertL_eq hq0 hq1, T_q_eq hq0 hq1]
  have := Pinv_pos q
  field_simp

lemma sum_tau_abel (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    ∑ n ∈ range N, tau q n = N * tau q N + ∑ m ∈ range (N + 1), (m : ℝ) * delta q m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun m => (m : ℝ) * delta q m) (N + 1),
      tau_succ hq0 hq1 N]
    push_cast
    ring

/-- `∑_n τ_n = L/P`. -/
lemma hasSum_tau (hq0 : 0 < q) (hq1 : q < 1) : HasSum (tau q) (lambertL q * Pinv q) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (tau_nonneg hq0 hq1)]
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) * tau q N) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ => betaT q * ((N : ℝ) * q ^ N)) atTop (𝓝 0) := by
      simpa using (tendsto_self_mul_const_pow_of_lt_one hq0.le hq1).const_mul (betaT q)
    refine squeeze_zero (fun N => ?_) (fun N => ?_) hb
    · have := tau_nonneg hq0 hq1 N
      positivity
    · calc (N : ℝ) * tau q N ≤ (N : ℝ) * (betaT q * q ^ N) :=
            mul_le_mul_of_nonneg_left (tau_le hq0 hq1 N) (Nat.cast_nonneg _)
        _ = betaT q * ((N : ℝ) * q ^ N) := by ring
  have h2 : Tendsto (fun N : ℕ => ∑ m ∈ range (N + 1), (m : ℝ) * delta q m) atTop
      (𝓝 (lambertL q * Pinv q)) := by
    rw [← U_q_eq hq0 hq1]
    have hs : HasSum (fun m : ℕ => (m : ℝ) * delta q m) (Uq q q) := by
      have := (summable_U hq0 hq1 hq0.le hq1).hasSum
      convert this using 1
      funext m
      unfold delta
      ring
    exact (tendsto_add_atTop_iff_nat 1).mpr hs.tendsto_sum_nat
  have := h1.add h2
  rw [zero_add] at this
  exact this.congr fun N => (sum_tau_abel hq0 hq1 N).symm

/-- `∑_{i > k} τ_i`. -/
def tauTail (q : ℝ) (k : ℕ) : ℝ := ∑' m : ℕ, tau q (m + (k + 1))

lemma sum_tau_add_tail (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    ∑ i ∈ range (k + 1), tau q i + tauTail q k = lambertL q * Pinv q := by
  rw [tauTail, (hasSum_tau hq0 hq1).summable.sum_add_tsum_nat_add (k + 1),
    (hasSum_tau hq0 hq1).tsum_eq]

lemma tauTail_nonneg (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) : 0 ≤ tauTail q k :=
  tsum_nonneg fun m => tau_nonneg hq0 hq1 _

lemma tauTail_le (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    tauTail q k ≤ betaT q / (1 - q) * q ^ k := by
  have hs : Summable (fun m => tau q (m + (k + 1))) :=
    (summable_nat_add_iff (k + 1)).mpr (hasSum_tau hq0 hq1).summable
  have hg : HasSum (fun m : ℕ => betaT q * q ^ (k + 1) * q ^ m) (betaT q * q ^ (k + 1) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0.le hq1).mul_left _
  have hle : ∀ m, tau q (m + (k + 1)) ≤ betaT q * q ^ (k + 1) * q ^ m := by
    intro m
    calc tau q (m + (k + 1)) ≤ betaT q * q ^ (m + (k + 1)) := tau_le hq0 hq1 _
      _ = betaT q * q ^ (k + 1) * q ^ m := by rw [pow_add]; ring
  have h1q : 0 < 1 - q := by linarith
  have hb := betaT_nonneg hq0 hq1
  calc tauTail q k ≤ betaT q * q ^ (k + 1) * (1 - q)⁻¹ := hasSum_le hle hs.hasSum hg
    _ ≤ betaT q / (1 - q) * q ^ k := by
      rw [pow_succ]
      have hqk : 0 ≤ q ^ k := pow_nonneg hq0.le k
      have : betaT q * (q ^ k * q) * (1 - q)⁻¹ = betaT q / (1 - q) * q ^ k * q := by
        field_simp
      rw [this]
      have : 0 ≤ betaT q / (1 - q) * q ^ k := by positivity
      nlinarith

lemma sum_tau_le (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    ∑ i ∈ range (k + 1), tau q i ≤ lambertL q * Pinv q := by
  have := sum_tau_add_tail hq0 hq1 k
  have := tauTail_nonneg hq0 hq1 k
  linarith

end Tau

/-! ### Polynomial times geometric bounds -/

section PolyGeo

variable {q : ℝ}

lemma summable_one_add_pow_mul_geometric (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    Summable (fun k : ℕ => (1 + (k : ℝ)) ^ n * q ^ k) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one n
    (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1 : ‖q‖ < 1)
  have h1 := ((summable_nat_add_iff 1).mpr h).mul_left q⁻¹
  refine h1.congr fun k => ?_
  push_cast
  field_simp
  ring

/-- `Cₙ = ∑ (1+k)^n q^k`, a bound for every term. -/
def polyC (q : ℝ) (n : ℕ) : ℝ := ∑' k : ℕ, (1 + (k : ℝ)) ^ n * q ^ k

lemma le_polyC (hq0 : 0 < q) (hq1 : q < 1) (n k : ℕ) :
    (1 + (k : ℝ)) ^ n * q ^ k ≤ polyC q n :=
  (summable_one_add_pow_mul_geometric hq0 hq1 n).le_tsum k fun j _ => by positivity

lemma polyC_nonneg (hq0 : 0 < q) (n : ℕ) : 0 ≤ polyC q n :=
  tsum_nonneg fun k => by positivity

end PolyGeo

/-! ### The second-order expansions of `b^{(2)}_k` and `b^{(3)}_k` -/

section Expansions

variable {q : ℝ}

/-- `ε_k = P^2 b^{(2)}_k - (k+1) + 2L`, written through `τ`. -/
def eps2 (q : ℝ) (k : ℕ) : ℝ :=
  2 * qPochhammerInfinity q q * tauTail q k +
    qPochhammerInfinity q q ^ 2 * ∑ i ∈ range (k + 1), tau q i * tau q (k - i)

lemma eps2_nonneg (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) : 0 ≤ eps2 q k := by
  unfold eps2
  have := P_pos q
  have := tauTail_nonneg hq0 hq1 k
  have : 0 ≤ ∑ i ∈ range (k + 1), tau q i * tau q (k - i) :=
    sum_nonneg fun i _ => mul_nonneg (tau_nonneg hq0 hq1 _) (tau_nonneg hq0 hq1 _)
  positivity

/-- The constant in `ε_k ≤ E (k+1) q^k`. -/
def epsE (q : ℝ) : ℝ :=
  2 * qPochhammerInfinity q q * (betaT q / (1 - q)) + qPochhammerInfinity q q ^ 2 * betaT q ^ 2

lemma eps2_le (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    eps2 q k ≤ epsE q * (((k : ℝ) + 1) * q ^ k) := by
  unfold eps2 epsE
  have hP := P_pos q
  have hb := betaT_nonneg hq0 hq1
  have h1q : 0 < 1 - q := by linarith
  have hqk : 0 ≤ q ^ k := pow_nonneg hq0.le k
  have ht := tauTail_le hq0 hq1 k
  have hxi : ∑ i ∈ range (k + 1), tau q i * tau q (k - i) ≤ ((k : ℝ) + 1) * (betaT q ^ 2 * q ^ k) := by
    calc ∑ i ∈ range (k + 1), tau q i * tau q (k - i)
        ≤ ∑ i ∈ range (k + 1), betaT q ^ 2 * q ^ k := by
          refine sum_le_sum fun i hi => ?_
          have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
          calc tau q i * tau q (k - i) ≤ (betaT q * q ^ i) * (betaT q * q ^ (k - i)) :=
                mul_le_mul (tau_le hq0 hq1 i) (tau_le hq0 hq1 (k - i)) (tau_nonneg hq0 hq1 _)
                  (by positivity)
            _ = betaT q ^ 2 * q ^ k := by
                rw [show q ^ k = q ^ i * q ^ (k - i) by rw [← pow_add]; congr 1; omega]
                ring
      _ = ((k : ℝ) + 1) * (betaT q ^ 2 * q ^ k) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          ring
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hb1 : 0 ≤ betaT q / (1 - q) := div_nonneg hb h1q.le
  calc 2 * qPochhammerInfinity q q * tauTail q k +
        qPochhammerInfinity q q ^ 2 * ∑ i ∈ range (k + 1), tau q i * tau q (k - i)
      ≤ 2 * qPochhammerInfinity q q * (betaT q / (1 - q) * q ^ k) +
          qPochhammerInfinity q q ^ 2 * (((k : ℝ) + 1) * (betaT q ^ 2 * q ^ k)) := by
        gcongr
    _ ≤ 2 * qPochhammerInfinity q q * (betaT q / (1 - q) * (((k : ℝ) + 1) * q ^ k)) +
          qPochhammerInfinity q q ^ 2 * (((k : ℝ) + 1) * (betaT q ^ 2 * q ^ k)) := by
        gcongr
        nlinarith
    _ = (2 * qPochhammerInfinity q q * (betaT q / (1 - q)) +
          qPochhammerInfinity q q ^ 2 * betaT q ^ 2) * (((k : ℝ) + 1) * q ^ k) := by ring

lemma epsE_nonneg (hq0 : 0 < q) (hq1 : q < 1) : 0 ≤ epsE q := by
  unfold epsE
  have := P_pos q
  have := betaT_nonneg hq0 hq1
  have : 0 < 1 - q := by linarith
  positivity

/-- **Expansion of `b^{(2)}`**: `P^2 b^{(2)}_k = (k+1) - 2L + ε_k`. -/
lemma b2_expand (hq0 : 0 < q) (hq1 : q < 1) (b2 : ℕ → ℝ)
    (hb2 : ∀ k, b2 k = ∑ i ∈ range (k + 1), einv q i * einv q (k - i)) (k : ℕ) :
    qPochhammerInfinity q q ^ 2 * b2 k = ((k : ℝ) + 1) - 2 * lambertL q + eps2 q k := by
  have hP := P_pos q
  have hterm : ∀ i ∈ range (k + 1), qPochhammerInfinity q q ^ 2 * (einv q i * einv q (k - i)) =
      1 - qPochhammerInfinity q q * tau q i - qPochhammerInfinity q q * tau q (k - i) +
        qPochhammerInfinity q q ^ 2 * (tau q i * tau q (k - i)) := by
    intro i _
    have h1 := P_mul_einv q i
    have h2 := P_mul_einv q (k - i)
    calc qPochhammerInfinity q q ^ 2 * (einv q i * einv q (k - i))
        = (qPochhammerInfinity q q * einv q i) * (qPochhammerInfinity q q * einv q (k - i)) := by
          ring
      _ = _ := by rw [h1, h2]; ring
  have hrefl : ∑ i ∈ range (k + 1), tau q (k - i) = ∑ i ∈ range (k + 1), tau q i := by
    have := sum_range_reflect (tau q) (k + 1)
    simpa using this
  have hsplit := sum_tau_add_tail hq0 hq1 k
  rw [hb2, mul_sum, sum_congr rfl hterm, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    sum_const, card_range, nsmul_eq_mul, mul_one, ← mul_sum, ← mul_sum, ← mul_sum, hrefl]
  unfold eps2
  have hSig : ∑ i ∈ range (k + 1), tau q i = lambertL q * Pinv q - tauTail q k := by linarith
  rw [hSig]
  unfold Pinv
  field_simp
  push_cast
  ring

lemma sum_range_cast_id (k : ℕ) : ∑ j ∈ range (k + 1), (j : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

lemma sum_range_cast_sub (k : ℕ) :
    ∑ x ∈ range (k + 1), ((k - x : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  have h := sum_range_reflect (fun j : ℕ => (j : ℝ)) (k + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h, sum_range_cast_id]

/-- The remainder in the expansion of `b^{(3)}`. -/
def rem3 (q : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ range (k + 1), eps2 q n + ((k : ℝ) + 1) * qPochhammerInfinity q q * tauTail q k +
    qPochhammerInfinity q q * ∑ i ∈ range (k + 1), tau q i * ((i : ℝ) + 2 * lambertL q) -
    qPochhammerInfinity q q * ∑ i ∈ range (k + 1), tau q i * eps2 q (k - i)

/-- **Expansion of `b^{(3)}`**: `P^3 b^{(3)}_k = (k+1)(k+2)/2 - 3L(k+1) + R_k`. -/
lemma b3_expand (hq0 : 0 < q) (hq1 : q < 1) (b2 b3 : ℕ → ℝ)
    (hb2 : ∀ k, b2 k = ∑ i ∈ range (k + 1), einv q i * einv q (k - i))
    (hb3 : ∀ k, b3 k = ∑ i ∈ range (k + 1), einv q i * b2 (k - i)) (k : ℕ) :
    qPochhammerInfinity q q ^ 3 * b3 k =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 - 3 * lambertL q * ((k : ℝ) + 1) + rem3 q k := by
  have hP := P_pos q
  set P := qPochhammerInfinity q q with hPdef
  set L := lambertL q with hLdef
  have hterm : ∀ i ∈ range (k + 1), P ^ 3 * (einv q i * b2 (k - i)) =
      ((((k - i : ℕ) : ℝ) + 1) + (eps2 q (k - i) - 2 * L)) - (P * ((k : ℝ) + 1)) * tau q i +
        P * (tau q i * ((i : ℝ) + 2 * L)) - P * (tau q i * eps2 q (k - i)) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have h1 := P_mul_einv q i
    have h2 := b2_expand hq0 hq1 b2 hb2 (k - i)
    have hc : ((k - i : ℕ) : ℝ) = (k : ℝ) - (i : ℝ) := Nat.cast_sub hik
    calc P ^ 3 * (einv q i * b2 (k - i)) = (P * einv q i) * (P ^ 2 * b2 (k - i)) := by ring
      _ = _ := by
        rw [h1, h2, hc]
        ring
  have hrefl : ∑ i ∈ range (k + 1), eps2 q (k - i) = ∑ i ∈ range (k + 1), eps2 q i := by
    have := sum_range_reflect (eps2 q) (k + 1)
    simpa using this
  have hsplit := sum_tau_add_tail hq0 hq1 k
  have hSig : ∑ i ∈ range (k + 1), tau q i = L * Pinv q - tauTail q k := by
    rw [hLdef]
    linarith
  rw [hb3, mul_sum, sum_congr rfl hterm]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  rw [sum_range_cast_sub, hrefl, hSig]
  unfold rem3
  rw [← hLdef, ← hPdef]
  unfold Pinv
  rw [← hPdef]
  field_simp
  push_cast
  ring

/-- A two-sided bound for the remainder of `b^{(3)}`. -/
def remK (q : ℝ) : ℝ :=
  epsE q * polyC q 1 + qPochhammerInfinity q q * (betaT q / (1 - q)) * polyC q 1 +
    qPochhammerInfinity q q * (betaT q * (1 + 2 * lambertL q) * polyC q 1) +
    epsE q * polyC q 1 * lambertL q

lemma abs_rem3_le (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) : |rem3 q k| ≤ remK q := by
  have hP := P_pos q
  have hb := betaT_nonneg hq0 hq1
  have hE := epsE_nonneg hq0 hq1
  have hL := lambertL_nonneg hq0 hq1
  have hC1 := polyC_nonneg hq0 1
  have h1q : 0 < 1 - q := by linarith
  have hepsC : ∀ n, eps2 q n ≤ epsE q * polyC q 1 := by
    intro n
    have h := le_polyC hq0 hq1 1 n
    rw [pow_one] at h
    calc eps2 q n ≤ epsE q * (((n : ℝ) + 1) * q ^ n) := eps2_le hq0 hq1 n
      _ ≤ epsE q * polyC q 1 := by
        apply mul_le_mul_of_nonneg_left _ hE
        linarith
  -- the four pieces
  have hA0 : 0 ≤ ∑ n ∈ range (k + 1), eps2 q n := sum_nonneg fun n _ => eps2_nonneg hq0 hq1 n
  have hA1 : ∑ n ∈ range (k + 1), eps2 q n ≤ epsE q * polyC q 1 := by
    calc ∑ n ∈ range (k + 1), eps2 q n ≤ ∑ n ∈ range (k + 1), epsE q * (((n : ℝ) + 1) * q ^ n) :=
          sum_le_sum fun n _ => eps2_le hq0 hq1 n
      _ = epsE q * ∑ n ∈ range (k + 1), (1 + (n : ℝ)) ^ 1 * q ^ n := by
          rw [mul_sum]
          refine sum_congr rfl fun n _ => by ring
      _ ≤ epsE q * polyC q 1 := by
          apply mul_le_mul_of_nonneg_left _ hE
          exact (summable_one_add_pow_mul_geometric hq0 hq1 1).sum_le_tsum _
            fun n _ => by positivity
  have hB0 : 0 ≤ ((k : ℝ) + 1) * qPochhammerInfinity q q * tauTail q k := by
    have := tauTail_nonneg hq0 hq1 k
    positivity
  have hB1 : ((k : ℝ) + 1) * qPochhammerInfinity q q * tauTail q k ≤
      qPochhammerInfinity q q * (betaT q / (1 - q)) * polyC q 1 := by
    have h := le_polyC hq0 hq1 1 k
    rw [pow_one] at h
    have ht := tauTail_le hq0 hq1 k
    have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    have hb1 : 0 ≤ betaT q / (1 - q) := div_nonneg hb h1q.le
    calc ((k : ℝ) + 1) * qPochhammerInfinity q q * tauTail q k
        ≤ ((k : ℝ) + 1) * qPochhammerInfinity q q * (betaT q / (1 - q) * q ^ k) := by
          gcongr
      _ = qPochhammerInfinity q q * (betaT q / (1 - q)) * ((1 + (k : ℝ)) * q ^ k) := by ring
      _ ≤ qPochhammerInfinity q q * (betaT q / (1 - q)) * polyC q 1 := by
          gcongr
  have hC0 : 0 ≤ qPochhammerInfinity q q * ∑ i ∈ range (k + 1), tau q i * ((i : ℝ) + 2 * lambertL q) := by
    have : 0 ≤ ∑ i ∈ range (k + 1), tau q i * ((i : ℝ) + 2 * lambertL q) :=
      sum_nonneg fun i _ => mul_nonneg (tau_nonneg hq0 hq1 i) (by positivity)
    positivity
  have hC1' : qPochhammerInfinity q q * ∑ i ∈ range (k + 1), tau q i * ((i : ℝ) + 2 * lambertL q) ≤
      qPochhammerInfinity q q * (betaT q * (1 + 2 * lambertL q) * polyC q 1) := by
    apply mul_le_mul_of_nonneg_left _ hP.le
    calc ∑ i ∈ range (k + 1), tau q i * ((i : ℝ) + 2 * lambertL q)
        ≤ ∑ i ∈ range (k + 1), betaT q * (1 + 2 * lambertL q) * ((1 + (i : ℝ)) ^ 1 * q ^ i) := by
          refine sum_le_sum fun i _ => ?_
          have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
          have hqi : 0 ≤ q ^ i := pow_nonneg hq0.le i
          calc tau q i * ((i : ℝ) + 2 * lambertL q) ≤ (betaT q * q ^ i) * ((i : ℝ) + 2 * lambertL q) :=
                mul_le_mul_of_nonneg_right (tau_le hq0 hq1 i) (by positivity)
            _ ≤ (betaT q * q ^ i) * ((1 + 2 * lambertL q) * (1 + (i : ℝ))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                nlinarith
            _ = betaT q * (1 + 2 * lambertL q) * ((1 + (i : ℝ)) ^ 1 * q ^ i) := by ring
      _ = betaT q * (1 + 2 * lambertL q) * ∑ i ∈ range (k + 1), (1 + (i : ℝ)) ^ 1 * q ^ i := by
          rw [mul_sum]
      _ ≤ betaT q * (1 + 2 * lambertL q) * polyC q 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (summable_one_add_pow_mul_geometric hq0 hq1 1).sum_le_tsum _
            fun n _ => by positivity
  have hD0 : 0 ≤ qPochhammerInfinity q q * ∑ i ∈ range (k + 1), tau q i * eps2 q (k - i) := by
    have : 0 ≤ ∑ i ∈ range (k + 1), tau q i * eps2 q (k - i) :=
      sum_nonneg fun i _ => mul_nonneg (tau_nonneg hq0 hq1 i) (eps2_nonneg hq0 hq1 _)
    positivity
  have hD1 : qPochhammerInfinity q q * ∑ i ∈ range (k + 1), tau q i * eps2 q (k - i) ≤
      epsE q * polyC q 1 * lambertL q := by
    have hsum := sum_tau_le hq0 hq1 k
    calc qPochhammerInfinity q q * ∑ i ∈ range (k + 1), tau q i * eps2 q (k - i)
        ≤ qPochhammerInfinity q q * ∑ i ∈ range (k + 1), tau q i * (epsE q * polyC q 1) := by
          apply mul_le_mul_of_nonneg_left _ hP.le
          exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hepsC _) (tau_nonneg hq0 hq1 i)
      _ = qPochhammerInfinity q q * (∑ i ∈ range (k + 1), tau q i) * (epsE q * polyC q 1) := by
          rw [← sum_mul]
          ring
      _ ≤ qPochhammerInfinity q q * (lambertL q * Pinv q) * (epsE q * polyC q 1) := by
          have : 0 ≤ epsE q * polyC q 1 := mul_nonneg hE hC1
          gcongr
      _ = epsE q * polyC q 1 * lambertL q := by
          unfold Pinv
          field_simp
  unfold rem3 remK
  rw [abs_le]
  constructor <;> linarith

end Expansions

/-! ### Summability of the logarithmic defects -/

section LogDefect

variable {q : ℝ}

lemma abs_log_one_add_sub_le {t : ℝ} (ht : |t| ≤ 1 / 2) : |Real.log (1 + t) - t| ≤ 2 * t ^ 2 := by
  have h1 : |-t| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [range_one, sum_singleton, zero_add, pow_one, Nat.cast_zero, div_one,
    sub_neg_eq_add, abs_neg] at h
  have hden : (1 : ℝ) / 2 ≤ 1 - |t| := by linarith
  have h2 : |t| ^ 2 / (1 - |t|) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ (by linarith), sq_abs]
    nlinarith [sq_nonneg t]
  calc |Real.log (1 + t) - t| = |-t + Real.log (1 + t)| := by ring_nf
    _ ≤ |t| ^ 2 / (1 - |t|) := h
    _ ≤ 2 * t ^ 2 := h2

lemma summable_inv_sq_succ : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using h

/-- If `|t_k| ≤ A/(k+1)` and `|t_k - s_k| ≤ B/(k+1)^2`, then `log(1+t_k) - s_k` is summable. -/
lemma summable_log_defect {t s : ℕ → ℝ} {A B : ℝ}
    (ht : ∀ k, |t k| ≤ A / ((k : ℝ) + 1)) (hts : ∀ k, |t k - s k| ≤ B / ((k : ℝ) + 1) ^ 2) :
    Summable (fun k => Real.log (1 + t k) - s k) := by
  have hA : Tendsto (fun k : ℕ => A / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul A
    rw [mul_zero] at this
    exact this.congr fun k => mul_one_div A _
  have hev : ∀ᶠ k : ℕ in atTop, A / ((k : ℝ) + 1) ≤ 1 / 2 :=
    (hA.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine Summable.of_norm_bounded_eventually (g := fun k => (2 * A ^ 2 + B) * (1 / ((k : ℝ) + 1) ^ 2))
    (summable_inv_sq_succ.mul_left _) ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with k hk
  have htk : |t k| ≤ 1 / 2 := (ht k).trans hk
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlog := abs_log_one_add_sub_le htk
  have htsq : t k ^ 2 ≤ A ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    have h0 : |t k| ^ 2 ≤ (A / ((k : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (ht k) 2
    rw [sq_abs, div_pow] at h0
    exact h0
  rw [Real.norm_eq_abs]
  calc |Real.log (1 + t k) - s k| = |(Real.log (1 + t k) - t k) + (t k - s k)| := by ring_nf
    _ ≤ |Real.log (1 + t k) - t k| + |t k - s k| := abs_add_le _ _
    _ ≤ 2 * (A ^ 2 / ((k : ℝ) + 1) ^ 2) + B / ((k : ℝ) + 1) ^ 2 := by
        have := hts k
        nlinarith
    _ = (2 * A ^ 2 + B) * (1 / ((k : ℝ) + 1) ^ 2) := by
        field_simp

end LogDefect

/-! ### The defect `ℓ_k = log(a_k/c_k) + 8L/(k+1)` is summable -/

section Ell

variable {q : ℝ}

/-- `c_k = (k+1)^2 (k+2)/2`. -/
def cSeq (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ 2 * ((k : ℝ) + 2) / 2

lemma cSeq_pos (k : ℕ) : 0 < cSeq k := by
  unfold cSeq
  positivity

lemma b2_pos (hq0 : 0 < q) (hq1 : q < 1) {b2 : ℕ → ℝ}
    (hb2 : ∀ k, b2 k = ∑ i ∈ range (k + 1), einv q i * einv q (k - i)) (k : ℕ) : 0 < b2 k := by
  rw [hb2]
  exact sum_pos (fun i _ => mul_pos (einv_pos hq0 hq1 _) (einv_pos hq0 hq1 _))
    ⟨0, by simp⟩

lemma b3_pos (hq0 : 0 < q) (hq1 : q < 1) {b2 b3 : ℕ → ℝ}
    (hb2 : ∀ k, b2 k = ∑ i ∈ range (k + 1), einv q i * einv q (k - i))
    (hb3 : ∀ k, b3 k = ∑ i ∈ range (k + 1), einv q i * b2 (k - i)) (k : ℕ) : 0 < b3 k := by
  rw [hb3]
  exact sum_pos (fun i _ => mul_pos (einv_pos hq0 hq1 _) (b2_pos hq0 hq1 hb2 _))
    ⟨0, by simp⟩

/-- **The second-order expansion**: with `a_k = P^4 (q;q)_k b^{(2)}_k b^{(3)}_k`, the defect
`log(a_k/c_k) + 8L/(k+1)` is summable. -/
lemma summable_ell (hq0 : 0 < q) (hq1 : q < 1) {b2 b3 : ℕ → ℝ}
    (hb2 : ∀ k, b2 k = ∑ i ∈ range (k + 1), einv q i * einv q (k - i))
    (hb3 : ∀ k, b3 k = ∑ i ∈ range (k + 1), einv q i * b2 (k - i)) :
    Summable (fun k : ℕ => Real.log (qPochhammerInfinity q q ^ 4 *
      (qPochhammerFinite q q k * b2 k * b3 k) / cSeq k) + 8 * lambertL q / ((k : ℝ) + 1)) := by
  have hP := P_pos q
  have hL := lambertL_nonneg hq0 hq1
  have hE := epsE_nonneg hq0 hq1
  have hK : 0 ≤ remK q := (abs_nonneg _).trans (abs_rem3_le hq0 hq1 0)
  have hepsC1 : ∀ k : ℕ, eps2 q k ≤ epsE q * polyC q 1 := by
    intro k
    have h := le_polyC hq0 hq1 1 k
    rw [pow_one] at h
    calc eps2 q k ≤ epsE q * (((k : ℝ) + 1) * q ^ k) := eps2_le hq0 hq1 k
      _ ≤ epsE q * polyC q 1 := mul_le_mul_of_nonneg_left (by linarith) hE
  have hqk : ∀ k : ℕ, q ^ k ≤ polyC q 2 / ((k : ℝ) + 1) ^ 2 := by
    intro k
    have h := le_polyC hq0 hq1 2 k
    rw [le_div_iff₀ (by positivity)]
    calc q ^ k * ((k : ℝ) + 1) ^ 2 = (1 + (k : ℝ)) ^ 2 * q ^ k := by ring
      _ ≤ polyC q 2 := h
  -- the factor `Z_k = (q;q)_k/P`
  have hZ : Summable (fun k : ℕ => Real.log (qPochhammerFinite q q k / qPochhammerInfinity q q)) := by
    refine Summable.of_norm_bounded (hasSum_tau hq0 hq1).summable fun k => ?_
    have hQ := qPoch_pos hq0 hq1 k
    have hQ1 : qPochhammerFinite q q k ≤ 1 :=
      (PaperR10.qPochhammerFinite_nonneg_le_one hq0.le hq1.le hq0.le hq1.le k).2
    have hPQ : qPochhammerInfinity q q ≤ qPochhammerFinite q q k :=
      PaperR10.qPochhammerInfinity_le_finite hq0.le hq1 hq0.le hq1 k
    have hZ1 : 1 ≤ qPochhammerFinite q q k / qPochhammerInfinity q q := (one_le_div hP).mpr hPQ
    have hlog0 : 0 ≤ Real.log (qPochhammerFinite q q k / qPochhammerInfinity q q) :=
      Real.log_nonneg hZ1
    have hlogle := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hZ1)
    rw [Real.norm_eq_abs, abs_of_nonneg hlog0]
    refine hlogle.trans ?_
    have ht0 := tau_nonneg hq0 hq1 k
    unfold tau Pinv einv at ht0 ⊢
    have e : qPochhammerFinite q q k / qPochhammerInfinity q q - 1 =
        qPochhammerFinite q q k * ((qPochhammerInfinity q q)⁻¹ - (qPochhammerFinite q q k)⁻¹) := by
      field_simp
    rw [e]
    calc qPochhammerFinite q q k * ((qPochhammerInfinity q q)⁻¹ - (qPochhammerFinite q q k)⁻¹)
        ≤ 1 * ((qPochhammerInfinity q q)⁻¹ - (qPochhammerFinite q q k)⁻¹) :=
          mul_le_mul_of_nonneg_right hQ1 ht0
      _ = (qPochhammerInfinity q q)⁻¹ - (qPochhammerFinite q q k)⁻¹ := one_mul _
  -- the factor `X_k = P^2 b^{(2)}_k/(k+1)`
  have hX : Summable (fun k : ℕ => Real.log (1 + (qPochhammerInfinity q q ^ 2 * b2 k /
      ((k : ℝ) + 1) - 1)) - (-(2 * lambertL q / ((k : ℝ) + 1)))) := by
    refine summable_log_defect (A := 2 * lambertL q + epsE q * polyC q 1)
      (B := epsE q * polyC q 2) (fun k => ?_) (fun k => ?_)
    · have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h := b2_expand hq0 hq1 b2 hb2 k
      have e : qPochhammerInfinity q q ^ 2 * b2 k / ((k : ℝ) + 1) - 1 =
          (eps2 q k - 2 * lambertL q) / ((k : ℝ) + 1) := by
        rw [h]
        field_simp
        ring
      rw [e, abs_div, abs_of_pos hk]
      apply div_le_div_of_nonneg_right _ hk.le
      rw [abs_le]
      constructor <;> linarith [eps2_nonneg hq0 hq1 k, hepsC1 k]
    · have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have h := b2_expand hq0 hq1 b2 hb2 k
      have e : qPochhammerInfinity q q ^ 2 * b2 k / ((k : ℝ) + 1) - 1 -
          (-(2 * lambertL q / ((k : ℝ) + 1))) = eps2 q k / ((k : ℝ) + 1) := by
        rw [h]
        field_simp
        ring
      rw [e, abs_of_nonneg (div_nonneg (eps2_nonneg hq0 hq1 k) hk.le)]
      calc eps2 q k / ((k : ℝ) + 1) ≤ epsE q * (((k : ℝ) + 1) * q ^ k) / ((k : ℝ) + 1) :=
            div_le_div_of_nonneg_right (eps2_le hq0 hq1 k) hk.le
        _ = epsE q * q ^ k := by field_simp
        _ ≤ epsE q * (polyC q 2 / ((k : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left (hqk k) hE
        _ = epsE q * polyC q 2 / ((k : ℝ) + 1) ^ 2 := by ring
  -- the factor `Y_k = 2 P^3 b^{(3)}_k/((k+1)(k+2))`
  have hY : Summable (fun k : ℕ => Real.log (1 + (2 * (qPochhammerInfinity q q ^ 3 * b3 k) /
      (((k : ℝ) + 1) * ((k : ℝ) + 2)) - 1)) - (-(6 * lambertL q / ((k : ℝ) + 1)))) := by
    refine summable_log_defect (A := 6 * lambertL q + 2 * remK q)
      (B := 6 * lambertL q + 2 * remK q) (fun k => ?_) (fun k => ?_)
    · have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have h := b3_expand hq0 hq1 b2 b3 hb2 hb3 k
      have hR := abs_rem3_le hq0 hq1 k
      have e : 2 * (qPochhammerInfinity q q ^ 3 * b3 k) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) - 1 =
          (2 * rem3 q k - 6 * lambertL q * ((k : ℝ) + 1)) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        rw [h]
        field_simp
        ring
      have habs : |2 * rem3 q k - 6 * lambertL q * ((k : ℝ) + 1)| ≤
          2 * remK q + 6 * lambertL q * ((k : ℝ) + 1) := by
        rw [abs_le] at hR
        rw [abs_le]
        constructor <;> nlinarith [mul_nonneg hL hk1.le]
      rw [e, abs_div, abs_of_pos (mul_pos hk1 hk2), div_le_div_iff₀ (mul_pos hk1 hk2) hk1]
      have hnum := mul_le_mul_of_nonneg_right habs hk1.le
      nlinarith [mul_nonneg hL hk1.le, mul_nonneg hK (mul_nonneg hk1.le hk1.le),
        mul_nonneg hK hk1.le]
    · have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      have h := b3_expand hq0 hq1 b2 b3 hb2 hb3 k
      have hR := abs_rem3_le hq0 hq1 k
      have e : 2 * (qPochhammerInfinity q q ^ 3 * b3 k) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) - 1 -
          (-(6 * lambertL q / ((k : ℝ) + 1))) =
          (6 * lambertL q + 2 * rem3 q k) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
        rw [h]
        field_simp
        ring
      have habs : |6 * lambertL q + 2 * rem3 q k| ≤ 6 * lambertL q + 2 * remK q := by
        rw [abs_le] at hR
        rw [abs_le]
        constructor <;> linarith
      rw [e, abs_div, abs_of_pos (mul_pos hk1 hk2), div_le_div_iff₀ (mul_pos hk1 hk2) (pow_pos hk1 2)]
      have h6 : 0 ≤ 6 * lambertL q + 2 * remK q := by positivity
      have hsq : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by nlinarith
      calc |6 * lambertL q + 2 * rem3 q k| * ((k : ℝ) + 1) ^ 2
          ≤ (6 * lambertL q + 2 * remK q) * ((k : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_right habs (by positivity)
        _ ≤ (6 * lambertL q + 2 * remK q) * (((k : ℝ) + 1) * ((k : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left hsq h6
  have hsplit : ∀ k : ℕ, Real.log (qPochhammerInfinity q q ^ 4 *
      (qPochhammerFinite q q k * b2 k * b3 k) / cSeq k) + 8 * lambertL q / ((k : ℝ) + 1) =
      Real.log (qPochhammerFinite q q k / qPochhammerInfinity q q) +
      (Real.log (1 + (qPochhammerInfinity q q ^ 2 * b2 k / ((k : ℝ) + 1) - 1)) -
        (-(2 * lambertL q / ((k : ℝ) + 1)))) +
      (Real.log (1 + (2 * (qPochhammerInfinity q q ^ 3 * b3 k) /
        (((k : ℝ) + 1) * ((k : ℝ) + 2)) - 1)) - (-(6 * lambertL q / ((k : ℝ) + 1)))) := by
    intro k
    have hQ := qPoch_pos hq0 hq1 k
    have hb2k := b2_pos hq0 hq1 hb2 k
    have hb3k := b3_pos hq0 hq1 hb2 hb3 k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hfac : qPochhammerInfinity q q ^ 4 * (qPochhammerFinite q q k * b2 k * b3 k) / cSeq k =
        (qPochhammerFinite q q k / qPochhammerInfinity q q) *
          (qPochhammerInfinity q q ^ 2 * b2 k / ((k : ℝ) + 1)) *
          (2 * (qPochhammerInfinity q q ^ 3 * b3 k) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
      unfold cSeq
      field_simp
    have e1 : 1 + (qPochhammerInfinity q q ^ 2 * b2 k / ((k : ℝ) + 1) - 1) =
        qPochhammerInfinity q q ^ 2 * b2 k / ((k : ℝ) + 1) := by ring
    have e2 : 1 + (2 * (qPochhammerInfinity q q ^ 3 * b3 k) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) - 1) =
        2 * (qPochhammerInfinity q q ^ 3 * b3 k) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by ring
    rw [hfac, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), e1, e2]
    field_simp
    ring
  exact ((hZ.add hX).add hY).congr fun k => (hsplit k).symm

end Ell

/-- `C_N = (N!)^2 (N+1)!/2^N`. -/
def leadC (N : ℕ) : ℝ := ((N.factorial : ℝ) ^ 2 * ((N + 1).factorial : ℝ)) / 2 ^ N

/-- `B_N = ∑_{j<N} j^2`. -/
def orderB (N : ℕ) : ℕ := ∑ j ∈ range N, j ^ 2

/-- The factor `(a_k/c_k) e^{8L/(k+1)}` of `𝓐(q)`, where `a_k = P^4 γ_k`. -/
def sharpFactor (q : ℝ) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  qPochhammerInfinity q q ^ 4 * γ k / cK k * Real.exp (8 * lambertL q / ((k : ℝ) + 1))

/-- `𝓐(q) = e^{-8 γ_E L} ∏_{k ≥ 0} (a_k/c_k) e^{8L/(k+1)}`. -/
def sharpA (q : ℝ) (γ : ℕ → ℝ) : ℝ :=
  Real.exp (-8 * Real.eulerMascheroniConstant * lambertL q) * ∏' k : ℕ, sharpFactor q γ k

/-- `K(q) = 𝓐(q) 𝓜(q)^3`. -/
def sharpK (q : ℝ) (γ : ℕ → ℝ) : ℝ := sharpA q γ * gramM q ^ 3

lemma leadC_pos (N : ℕ) : 0 < leadC N := by
  unfold leadC
  have h1 : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h2 : (0 : ℝ) < (N + 1).factorial := by exact_mod_cast Nat.factorial_pos (N + 1)
  positivity

/-- `C_N = ∏_{k<N} c_k`. -/
lemma prod_cK (N : ℕ) : ∏ k ∈ range N, cK k = leadC N := by
  induction N with
  | zero => simp [leadC]
  | succ N ih =>
    rw [prod_range_succ, ih]
    unfold leadC cK
    rw [Nat.factorial_succ (N + 1), Nat.factorial_succ N]
    push_cast
    field_simp
    ring

lemma harmonic_eq_sum (N : ℕ) : (harmonic N : ℝ) = ∑ k ∈ range N, 1 / ((k : ℝ) + 1) := by
  simp [harmonic, one_div]

/-- `long1049:thm:sharp-fixed-base` (the size of `V_N^*` at a fixed base).

Let `0 < q < 1` and let `γ_k = [w^k] G_q(w)`, i.e. `∑_k γ_k w^k = G_q(w)` on `0 ≤ w < 1`, with
`G_q` the tree's `actualGeneratingFunction q`; put `a_k = P^4 γ_k`. With `L = lambertL q`,
`c_k = cK k`, `C_N = leadC N`, `B_N = orderB N` and
`V_N^*(q) = det (v^*_{i+j}(q))_{0 ≤ i,j < N}` (`actualMomentHankel`):
* the product `∏_{k ≥ 0} (a_k/c_k) e^{8L/(k+1)}` converges (`HasProd`), and
  `𝓐(q) = e^{-8 γ_E L} ∏_{k ≥ 0} (a_k/c_k) e^{8L/(k+1)}` (`sharpA`) is positive;
* with `K(q) = 𝓐(q) 𝓜(q)^3` (`sharpK`), `V_N^*(q) ∼ K(q) C_N q^{B_N} P^{2N} N^{-8L}`:
  the ratio tends to `1`;
* equivalently
  `log V_N^*(q) = B_N log q + log C_N + 2N log P - 8L log N + log K(q) + o(1)`. -/
theorem sharp_fixed_base {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (γ : ℕ → ℝ)
    (hγ : ∀ w : ℝ, 0 ≤ w → w < 1 →
      HasSum (fun k => γ k * w ^ k) (actualGeneratingFunction q w)) :
    HasProd (sharpFactor q γ) (∏' k : ℕ, sharpFactor q γ k) ∧
    0 < sharpA q γ ∧
    Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
        (sharpK q γ * leadC N * q ^ orderB N * qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * lambertL q))) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => Real.log (actualMomentHankel q N).det -
        ((orderB N : ℝ) * Real.log q + Real.log (leadC N) +
          2 * (N : ℝ) * Real.log (qPochhammerInfinity q q) - 8 * lambertL q * Real.log N +
          Real.log (sharpK q γ))) atTop (𝓝 0) := by
  have hγeq : γ = realGamma q := RogersFactorisation.eq_of_hasSum_on_unit_interval hγ
    (fun w hw0 hw1 => RogersFactorisation.hasSum_realGamma hq0 hq1 hw0 hw1)
  subst hγeq
  have hP := P_pos q
  have hL := lambertL_nonneg hq0 hq1
  have hM := GeometricUniversality.gramM_pos hq0.le hq1
  -- the weights
  have ha : ∀ k, 0 < qPochhammerInfinity q q ^ 4 * realGamma q k := fun k =>
    RogersFactorisation.weight_pos hq0 hq1 k
  have hb2 : ∀ k, realB q 2 k = ∑ i ∈ range (k + 1), einv q i * einv q (k - i) := fun k =>
    RogersFactorisation.realB_two k
  have hb3 : ∀ k, realB q 3 k = ∑ i ∈ range (k + 1), einv q i * realB q 2 (k - i) := fun k =>
    RogersFactorisation.realB_three k
  have hℓ := summable_ell hq0 hq1 hb2 hb3
  set ℓ : ℕ → ℝ := fun k => Real.log (qPochhammerInfinity q q ^ 4 *
      (qPochhammerFinite q q k * realB q 2 k * realB q 3 k) / cSeq k) +
      8 * lambertL q / ((k : ℝ) + 1) with hℓdef
  have hratio : ∀ k, qPochhammerInfinity q q ^ 4 *
      (qPochhammerFinite q q k * realB q 2 k * realB q 3 k) / cSeq k =
        qPochhammerInfinity q q ^ 4 * realGamma q k / cK k := by
    intro k
    rw [RogersFactorisation.realGamma_eq hq0 hq1]
    rfl
  have hratio_pos : ∀ k, 0 < qPochhammerInfinity q q ^ 4 * realGamma q k / cK k := fun k =>
    div_pos (ha k) (RogersFactorisation.cK_pos k)
  have hfac : ∀ k, sharpFactor q (realGamma q) k = Real.exp (ℓ k) := by
    intro k
    simp only [hℓdef]
    rw [Real.exp_add, hratio, Real.exp_log (hratio_pos k)]
    rfl
  -- clauses 1 and 2
  have hSum : HasSum ℓ (∑' k, ℓ k) := hℓ.hasSum
  have hprod : HasProd (sharpFactor q (realGamma q)) (Real.exp (∑' k, ℓ k)) := by
    refine Real.hasProd_of_hasSum_log (fun k => ?_) ?_
    · rw [hfac]
      exact Real.exp_pos _
    · convert hSum using 1
      funext k
      rw [hfac, Real.log_exp]
  have htprod : ∏' k : ℕ, sharpFactor q (realGamma q) k = Real.exp (∑' k, ℓ k) := hprod.tprod_eq
  have hApos : 0 < sharpA q (realGamma q) := by
    unfold sharpA
    rw [htprod]
    positivity
  refine ⟨htprod ▸ hprod, hApos, ?_⟩
  -- Theorem 1 applied to `a_k = P^4 γ_k`
  have hlim : ∀ h : ℕ, Tendsto (fun k => qPochhammerInfinity q q ^ 4 * realGamma q (k + h) /
      (qPochhammerInfinity q q ^ 4 * realGamma q k)) atTop (𝓝 1) := fun h =>
    RogersFactorisation.tendsto_weight_ratio hq0 hq1 h
  have hbd : ∀ k h : ℕ, qPochhammerInfinity q q ^ 4 * realGamma q (k + h) /
      (qPochhammerInfinity q q ^ 4 * realGamma q k) ≤
        ((qPochhammerInfinity q q)⁻¹) ^ 6 * (1 + (h : ℝ)) ^ (3 : ℝ) := by
    intro k h
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact RogersFactorisation.weight_ratio_le hq0 hq1 k h
  have hT1 := (geometric_universality hq0 hq1 (a := fun k => qPochhammerInfinity q q ^ 4 *
    realGamma q k) ha hlim hbd).2.2.2
  -- `V_N^*` is the Hankel determinant of the moments of these weights
  have hmom : ∀ m, actualMoment q m =
      geomMoment q (fun k => qPochhammerInfinity q q ^ 4 * realGamma q k) m := by
    intro m
    rw [PaperR12.actual_moment_generating_identity hq0 hq1 m]
    have h := RogersFactorisation.hasSum_realGamma hq0 hq1 (w := q ^ (m + 1))
      (pow_nonneg hq0.le _) (pow_lt_one₀ hq0.le hq1 (Nat.succ_ne_zero m))
    unfold geomMoment
    rw [← h.tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [← pow_mul]
    ring
  have hV : ∀ N, (actualMomentHankel q N).det =
      geomHankelDet q (fun k => qPochhammerInfinity q q ^ 4 * realGamma q k) N := by
    intro N
    unfold geomHankelDet
    congr 1
    ext i j
    simp only [PaperR16.actualMomentHankel, Matrix.of_apply]
    exact hmom _
  -- the product of the weights
  have hak : ∀ k, qPochhammerInfinity q q ^ 4 * realGamma q k =
      cK k * Real.exp (ℓ k - 8 * lambertL q * (1 / ((k : ℝ) + 1))) := by
    intro k
    have e : ℓ k - 8 * lambertL q * (1 / ((k : ℝ) + 1)) =
        Real.log (qPochhammerInfinity q q ^ 4 * realGamma q k / cK k) := by
      simp only [hℓdef]
      rw [hratio, mul_one_div]
      ring
    rw [e, Real.exp_log (hratio_pos k)]
    have := RogersFactorisation.cK_pos k
    field_simp
  have hprod_a : ∀ N : ℕ, ∏ k ∈ range N, qPochhammerInfinity q q ^ 4 * realGamma q k =
      leadC N * Real.exp (∑ k ∈ range N, ℓ k - 8 * lambertL q * (harmonic N : ℝ)) := by
    intro N
    rw [harmonic_eq_sum, mul_sum, ← sum_sub_distrib, Real.exp_sum, ← prod_cK N,
      ← prod_mul_distrib]
    exact prod_congr rfl fun k _ => hak k
  -- the ratio of the product to its claimed asymptotic
  set S := ∑' k, ℓ k with hSdef
  have hexp : Tendsto (fun N : ℕ => Real.exp (∑ k ∈ range N, ℓ k - S -
      8 * lambertL q * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant)))
      atTop (𝓝 1) := by
    have h1 := hSum.tendsto_sum_nat
    have h2 := Real.tendsto_harmonic_sub_log
    have h3 := (h1.sub_const S).sub ((h2.sub_const Real.eulerMascheroniConstant).const_mul
      (8 * lambertL q))
    rw [sub_self, sub_self, mul_zero, sub_zero] at h3
    have h4 := (Real.continuous_exp.tendsto 0).comp h3
    rw [Real.exp_zero] at h4
    exact h4
  have hprodratio : ∀ N : ℕ, 1 ≤ N →
      (∏ k ∈ range N, qPochhammerInfinity q q ^ 4 * realGamma q k) /
        (sharpA q (realGamma q) * leadC N * (N : ℝ) ^ (-8 * lambertL q)) =
      Real.exp (∑ k ∈ range N, ℓ k - S -
        8 * lambertL q * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant)) := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hC := leadC_pos N
    rw [hprod_a N, Real.rpow_def_of_pos hNpos]
    unfold sharpA
    rw [htprod, div_eq_iff (by positivity)]
    rw [show ∑ k ∈ range N, ℓ k - 8 * lambertL q * (harmonic N : ℝ) =
        (∑ k ∈ range N, ℓ k - S -
          8 * lambertL q * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant)) +
        (-8 * Real.eulerMascheroniConstant * lambertL q) + S +
        Real.log N * (-8 * lambertL q) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
    ring
  have hT2 : Tendsto (fun N : ℕ => (∏ k ∈ range N, qPochhammerInfinity q q ^ 4 * realGamma q k) /
      (sharpA q (realGamma q) * leadC N * (N : ℝ) ^ (-8 * lambertL q))) atTop (𝓝 1) := by
    refine hexp.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hprodratio N hN).symm
  -- clause 3
  have hmain : Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
      (sharpK q (realGamma q) * leadC N * q ^ orderB N * qPochhammerInfinity q q ^ (2 * N) *
        (N : ℝ) ^ (-8 * lambertL q))) atTop (𝓝 1) := by
    have h := hT1.mul hT2
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hC := leadC_pos N
    have hpa : 0 < ∏ k ∈ range N, qPochhammerInfinity q q ^ 4 * realGamma q k :=
      prod_pos fun k _ => ha k
    have hqB : 0 < q ^ orderB N := pow_pos hq0 _
    have hrp : 0 < (N : ℝ) ^ (-8 * lambertL q) := Real.rpow_pos_of_pos hNpos _
    rw [hV N]
    unfold sharpK orderB
    field_simp
  refine ⟨hmain, ?_⟩
  -- clause 4: the logarithmic form
  have hlog := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto).comp hmain
  rw [Real.log_one] at hlog
  refine hlog.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hC := leadC_pos N
  have hVpos := PaperR16.actualMomentHankel_det_pos hq0 hq1 N
  have hK : 0 < sharpK q (realGamma q) := by
    unfold sharpK
    positivity
  have hqB : 0 < q ^ orderB N := pow_pos hq0 _
  have hP2 : 0 < qPochhammerInfinity q q ^ (2 * N) := pow_pos hP _
  have hrp : 0 < (N : ℝ) ^ (-8 * lambertL q) := Real.rpow_pos_of_pos hNpos _
  simp only [Function.comp_apply]
  rw [Real.log_div hVpos.ne' (by positivity), Real.log_mul (by positivity) hrp.ne',
    Real.log_mul (by positivity) hP2.ne', Real.log_mul (by positivity) hqB.ne',
    Real.log_mul hK.ne' hC.ne', Real.log_rpow hNpos, Real.log_pow, Real.log_pow]
  push_cast
  ring

end ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase

#print axioms ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base
