import ErdosProblems.Erdos68.ChannelIntegralCongruence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-!
# End-to-end candidate for the two displayed sharp asymptotic constants

Long-record labels res:lcm-growth and res:radius-constant.

`LowerLimitAtLeast f c` is the epsilon/eventual formulation of liminf f >= c:
for every a<c, eventually a<f(n). It is deliberately used instead of a
real-valued `Filter.liminf`, whose default value is not an extended-real
infinity when the sequence diverges to +infinity. This representation places
no unproved upper-boundedness hypothesis on the lcm sequence.

The proof starts from the supplied finite product and Stirling inequalities.
It proves the optimising Nat.sqrt limit, the moving logarithm limit, and the
binomial normalisation, rather than assuming their asymptotic conclusions.

STATUS: uncompiled proof candidates. These are the largest API/elaboration
risks in the return. There are no admitted analytic facts or proof placeholders.
-/
namespace ErdosProblems.Erdos68.PaperComplete

open Filter
open scoped Topology BigOperators

/-- Standard extended-real lower-limit assertion, stated without boundedness
side conditions or a choice of infinity representation. -/
def LowerLimitAtLeast (f : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ a : ℝ, a < c → ∀ᶠ n : ℕ in atTop, a < f n

noncomputable def blockLogLower (N k : ℕ) : ℝ :=
  (k : ℝ) *
    (((N + 1 - k : ℕ) : ℝ) * Real.log ((N + 1 - k : ℕ) : ℝ) -
      (N + 1 - k : ℕ) - Real.log 2) -
    ((k + 1).choose 3 : ℝ) * Real.log (N : ℝ)

lemma blockLogLower_le_log_lcm {N k : ℕ} (hk : k < N) :
    blockLogLower N k ≤ Real.log (_root_.Erdos68.channelLCM N : ℝ) := by
  have hn : 2 ≤ N + 1 - k := by omega
  have hN : 0 < N := by omega
  have hL : (0 : ℝ) < _root_.Erdos68.channelLCM N := by
    exact_mod_cast _root_.Erdos68.channelLCM_pos N
  have hgap : (0 : ℝ) < ((N + 1 - k).factorial - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt (Nat.one_lt_factorial.mpr hn)
  have hnat := _root_.Erdos68.factorialGapSegment_base_pow_le_channelLCM_mul_pow_choose hk
  have hr : (((N + 1 - k).factorial - 1 : ℕ) : ℝ) ^ k ≤
      (_root_.Erdos68.channelLCM N : ℝ) * (N : ℝ) ^ ((k + 1).choose 3) := by
    exact_mod_cast hnat
  have hl := Real.log_le_log (pow_pos hgap _) hr
  rw [Real.log_pow, Real.log_mul hL.ne' (pow_ne_zero _ (by exact_mod_cast hN.ne')),
    Real.log_pow] at hl
  have hs := _root_.Erdos68.log_factorial_sub_one_lower_bound hn
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ k)
  unfold blockLogLower
  linarith

lemma blockLogLower_lt_radius {N k M R : ℕ} (hk : k < N)
    (hM : 0 < M) (hdiv : _root_.Erdos68.channelLCM N ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    blockLogLower N k < ((R + 1 : ℕ) : ℝ) * Real.log ((R + 1 : ℕ) : ℝ) := by
  have h := _root_.Erdos68.factorialGapSegment_stirling_radius_constraint hk hM hdiv hsmall
  unfold blockLogLower
  push_cast at h ⊢
  linarith

lemma inv_nat_tendsto_zero :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

lemma inv_sqrt_nat_tendsto_zero :
    Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

lemma inv_log_nat_tendsto_zero :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

noncomputable def optimalWindow (N : ℕ) : ℕ := Nat.sqrt (2 * N)
noncomputable def blockStart (N : ℕ) : ℕ := N + 1 - optimalWindow N

lemma optimalWindow_lt {N : ℕ} (hN : 3 ≤ N) : optimalWindow N < N :=
  _root_.Erdos68.radiusOptimizationWindow_lt hN

lemma optimal_window_sandwich {N : ℕ} (hN : 0 < N) :
    Real.sqrt 2 - (Real.sqrt (N : ℝ))⁻¹ ≤
        (optimalWindow N : ℝ) / Real.sqrt (N : ℝ) ∧
    (optimalWindow N : ℝ) / Real.sqrt (N : ℝ) ≤ Real.sqrt 2 := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hs2 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hk0 : (0 : ℝ) ≤ optimalWindow N := by positivity
  have hlo : (optimalWindow N : ℝ) ^ 2 ≤ 2 * (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le' (2 * N)
  have hhi : 2 * (N : ℝ) < ((optimalWindow N : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (2 * N)
  have hsprod : (Real.sqrt 2 * Real.sqrt (N : ℝ)) ^ 2 = 2 * (N : ℝ) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  have hkn : (optimalWindow N : ℝ) ≤ Real.sqrt 2 * Real.sqrt (N : ℝ) := by
    nlinarith [mul_nonneg hs2 hs.le]
  have hnk : Real.sqrt 2 * Real.sqrt (N : ℝ) < (optimalWindow N : ℝ) + 1 := by
    nlinarith [mul_nonneg hs2 hs.le]
  constructor
  · apply (le_div_iff₀ hs).mpr
    calc
      (Real.sqrt 2 - (Real.sqrt (N : ℝ))⁻¹) * Real.sqrt (N : ℝ)
          = Real.sqrt 2 * Real.sqrt (N : ℝ) - 1 := by
            field_simp [hs.ne']
            all_goals ring
      _ ≤ optimalWindow N := by linarith
  · exact (div_le_iff₀ hs).mpr hkn

lemma optimal_window_ratio_tendsto :
    Tendsto (fun N : ℕ => (optimalWindow N : ℝ) / Real.sqrt (N : ℝ))
      atTop (𝓝 (Real.sqrt 2)) := by
  have hlo : Tendsto (fun N : ℕ => Real.sqrt 2 - (Real.sqrt (N : ℝ))⁻¹)
      atTop (𝓝 (Real.sqrt 2)) := by
    simpa using tendsto_const_nhds.sub inv_sqrt_nat_tendsto_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (optimal_window_sandwich (by omega)).1
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (optimal_window_sandwich (by omega)).2

lemma sqrt_division_identity {x s a : ℝ} (hsq : s ^ 2 = x) :
    a / x = (a / s) * s⁻¹ := by
  rw [← hsq]
  simp only [pow_two, div_eq_mul_inv, mul_inv_rev, mul_assoc]

lemma optimal_window_div_nat_tendsto_zero :
    Tendsto (fun N : ℕ => (optimalWindow N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  have h := optimal_window_ratio_tendsto.mul inv_sqrt_nat_tendsto_zero
  have heq : (fun N : ℕ => (optimalWindow N : ℝ) / (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ => ((optimalWindow N : ℝ) / Real.sqrt (N : ℝ)) *
        (Real.sqrt (N : ℝ))⁻¹) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hs : Real.sqrt (N : ℝ) ≠ 0 :=
      (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))).ne'
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
    exact sqrt_division_identity hsquare
  have h0 : Tendsto (fun N : ℕ => ((optimalWindow N : ℝ) / Real.sqrt (N : ℝ)) *
      (Real.sqrt (N : ℝ))⁻¹) atTop (𝓝 0) := by simpa using h
  exact h0.congr' heq.symm

lemma block_start_ratio_tendsto :
    Tendsto (fun N : ℕ => (blockStart N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => 1 + (N : ℝ)⁻¹ - (optimalWindow N : ℝ) / N)
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add inv_nat_tendsto_zero).sub
      optimal_window_div_nat_tendsto_zero
  apply h.congr'
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hk := optimalWindow_lt hN
  have hcast : (blockStart N : ℝ) = N + 1 - (optimalWindow N : ℝ) := by
    simp only [blockStart, Nat.cast_sub (by omega : optimalWindow N ≤ N + 1), Nat.cast_add,
      Nat.cast_one]
  have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [hcast]
  field_simp [hne]
  all_goals ring

lemma moving_log_ratio_tendsto :
    Tendsto (fun N : ℕ => Real.log (blockStart N : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((blockStart N : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    simpa using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      block_start_ratio_tendsto
  have h : Tendsto (fun N : ℕ => 1 +
      Real.log ((blockStart N : ℝ) / N) * (Real.log (N : ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hlog.mul inv_log_nat_tendsto_zero)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hstart : 2 ≤ blockStart N := by
    have hk := optimalWindow_lt hN
    dsimp [blockStart]
    omega
  have hb : (blockStart N : ℝ) ≠ 0 := by exact_mod_cast (show blockStart N ≠ 0 by omega)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hln : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  rw [Real.log_div hb hn]
  field_simp [hln]
  ring

lemma choose_three_cast (k : ℕ) :
    ((k + 1).choose 3 : ℝ) = ((k : ℝ) ^ 3 - k) / 6 := by
  cases k with
  | zero => norm_num
  | succ k =>
    have h := Nat.descFactorial_eq_factorial_mul_choose (k + 2) 3
    norm_num [Nat.descFactorial, Nat.factorial] at h
    have hr := congrArg (fun z : ℕ => (z : ℝ)) h
    push_cast at hr ⊢
    nlinarith

lemma cubic_normalisation {x s a : ℝ} (hs : s ≠ 0) (hsq : s ^ 2 = x) :
    ((a ^ 3 - a) / 6) / (x * s) = ((a / s) ^ 3 - (a / s) / x) / 6 := by
  rw [← hsq]
  field_simp [hs]
  all_goals ring

lemma collision_ratio_tendsto :
    Tendsto (fun N : ℕ => ((optimalWindow N + 1).choose 3 : ℝ) /
      ((N : ℝ) * Real.sqrt (N : ℝ))) atTop (𝓝 ((Real.sqrt 2) ^ 3 / 6)) := by
  have h := ((optimal_window_ratio_tendsto.pow 3).sub
    (optimal_window_ratio_tendsto.mul inv_nat_tendsto_zero)).div_const 6
  have h0 : Tendsto (fun N : ℕ => (((optimalWindow N : ℝ) / Real.sqrt (N : ℝ)) ^ 3 -
      ((optimalWindow N : ℝ) / Real.sqrt (N : ℝ)) * (N : ℝ)⁻¹) / 6)
      atTop (𝓝 ((Real.sqrt 2) ^ 3 / 6)) := by simpa using h
  apply h0.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))).ne'
  rw [choose_three_cast, cubic_normalisation hs (Real.sq_sqrt (by positivity))]
  simp only [div_eq_mul_inv]

noncomputable def optimisedLogLower (N : ℕ) : ℝ :=
  blockLogLower N (optimalWindow N) /
    ((N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ))

lemma optimised_lower_tendsto :
    Tendsto optimisedLogLower atTop (𝓝 (2 * Real.sqrt 2 / 3)) := by
  have hmain := (optimal_window_ratio_tendsto.mul block_start_ratio_tendsto).mul
    moving_log_ratio_tendsto
  have hlinear := (optimal_window_ratio_tendsto.mul block_start_ratio_tendsto).mul
    inv_log_nat_tendsto_zero
  have hconstant := ((optimal_window_ratio_tendsto.mul inv_nat_tendsto_zero).mul
    inv_log_nat_tendsto_zero).mul_const (Real.log 2)
  have h := ((hmain.sub hlinear).sub hconstant).sub collision_ratio_tendsto
  have hlim : Real.sqrt 2 - Real.sqrt 2 ^ 3 / 6 = 2 * Real.sqrt 2 / 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    calc
      Real.sqrt 2 - Real.sqrt 2 ^ 3 / 6
          = Real.sqrt 2 - (Real.sqrt 2 ^ 2 * Real.sqrt 2) / 6 := by ring
      _ = 2 * Real.sqrt 2 / 3 := by rw [hs]; ring
  have h' : Tendsto
      (fun N : ℕ =>
        ((optimalWindow N : ℝ) / Real.sqrt (N : ℝ)) * ((blockStart N : ℝ) / N) *
          (Real.log (blockStart N : ℝ) / Real.log (N : ℝ)) -
        ((optimalWindow N : ℝ) / Real.sqrt (N : ℝ)) * ((blockStart N : ℝ) / N) *
          (Real.log (N : ℝ))⁻¹ -
        (((optimalWindow N : ℝ) / Real.sqrt (N : ℝ)) * (N : ℝ)⁻¹ *
          (Real.log (N : ℝ))⁻¹) * Real.log 2 -
        ((optimalWindow N + 1).choose 3 : ℝ) / ((N : ℝ) * Real.sqrt (N : ℝ)))
      atTop (𝓝 (2 * Real.sqrt 2 / 3)) := by
    simpa only [mul_one, mul_zero, zero_mul, sub_zero, hlim] using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))).ne'
  have hl : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  dsimp [optimisedLogLower, blockLogLower, blockStart]
  field_simp [hn, hs, hl]
  all_goals ring

/-- Whole res:lcm-growth, in the epsilon/eventual (extended liminf) form.
N*sqrt N is the positive-real N^(3/2), with no integer exponent coercion. -/
theorem common_denominator_growth :
    LowerLimitAtLeast
      (fun N : ℕ => Real.log (_root_.Erdos68.channelLCM N : ℝ) /
        ((N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ)))
      (2 * Real.sqrt 2 / 3) := by
  intro a ha
  have hnear := optimised_lower_tendsto.eventually (Ioi_mem_nhds ha)
  filter_upwards [hnear, eventually_ge_atTop 3] with N haN hN
  have hden : 0 < (N : ℝ) * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hs := Real.sqrt_pos.mpr hn
    have hl := Real.log_pos (by exact_mod_cast (show 1 < N by omega) : (1 : ℝ) < N)
    positivity
  have hb := blockLogLower_le_log_lcm (optimalWindow_lt hN)
  exact haN.trans_le (div_le_div_of_nonneg_right hb hden.le)

end ErdosProblems.Erdos68.PaperComplete
