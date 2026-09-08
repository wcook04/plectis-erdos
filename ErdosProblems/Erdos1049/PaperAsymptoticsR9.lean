import ErdosProblems.Erdos1049.PaperRankTwoCapR7
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Quadratic asymptotic transfer, revision of the round-8 return.
UNCOMPILED. This file contains proof text, not a kernel receipt.

The asymptotic hypotheses below are estimates, not assumptions of the conclusions.
In particular `cross_product_limits` proves both successor products. The integer
contradiction is the desk's repaired PaperRankTwoCapR7 theorem, reused unchanged.

Pinned API: Mathlib 5e932f97dd25535344f80f9dd8da3aab83df0fe6.
Filter/metric API: Order/Filter/AtTopBot/Basic.lean and
Topology/MetricSpace/Pseudo/Defs.lean. Exponential/log API:
Analysis/SpecialFunctions/Exp.lean and Log/Basic.lean. Elementary ordered-field
algebra is handled by ring, linarith and explicitly supplied polynomial facts.
-/
namespace ErdosProblems.Erdos1049.PaperR9
open Filter Asymptotics
open scoped Topology

/-- The scale is a real square, avoiding truncated natural subtraction. -/
def sqScale (n : ℕ) : ℝ := (n : ℝ) ^ 2

/-- Upper quadratic rate, with an arbitrary additive epsilon in the rate. -/
def QuadUpper (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n ≤ (a + ε) * sqScale n

/-- Upper quadratic exponential rate, allowing zeros of f. -/
def QuadExpUpper (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    |f n| ≤ Real.exp ((a + ε) * sqScale n)

/-- Exact two-sided logarithmic asymptotic; nonvanishing is supplied separately. -/
def QuadLogRate (f : ℕ → ℝ) (a : ℝ) : Prop :=
  (fun n => Real.log |f n| - a * sqScale n) =o[atTop] sqScale

lemma sqScale_nonneg (n : ℕ) : 0 ≤ sqScale n := sq_nonneg _

/-- API: Analysis/Asymptotics/Defs.lean, `IsLittleO.def`. -/
lemma littleO_bound (f : ℕ → ℝ) (hf : f =o[atTop] sqScale)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, |f n| ≤ ε * sqScale n := by
  have hb := hf.def hε
  filter_upwards [hb] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sqScale_nonneg n)] using hn

lemma QuadUpper.mono {f : ℕ → ℝ} {a b : ℝ}
    (hf : QuadUpper f a) (hab : a ≤ b) : QuadUpper f b := by
  intro ε hε
  filter_upwards [hf ε hε] with n hn
  exact hn.trans (mul_le_mul_of_nonneg_right (add_le_add_left hab ε)
    (sqScale_nonneg n))

lemma QuadUpper.add {f g : ℕ → ℝ} {a b : ℝ}
    (hf : QuadUpper f a) (hg : QuadUpper g b) :
    QuadUpper (fun n => f n + g n) (a + b) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε)] with n hn hm
  calc
    f n + g n ≤ (a + ε / 2) * sqScale n + (b + ε / 2) * sqScale n :=
      add_le_add hn hm
    _ = (a + b + ε) * sqScale n := by ring

lemma QuadUpper.const_mul {f : ℕ → ℝ} {a c : ℝ}
    (hf : QuadUpper f a) (hc : 0 ≤ c) :
    QuadUpper (fun n => c * f n) (c * a) := by
  intro ε hε
  have hcp : 0 < c + 1 := by linarith
  have he : 0 < ε / (c + 1) := div_pos hε hcp
  have hcancel : (ε / (c + 1)) * (c + 1) = ε :=
    div_mul_cancel₀ ε hcp.ne'
  filter_upwards [hf (ε / (c + 1)) he] with n hn
  have hrate : c * (a + ε / (c + 1)) ≤ c * a + ε := by
    nlinarith [he.le]
  calc
    c * f n ≤ c * ((a + ε / (c + 1)) * sqScale n) :=
      mul_le_mul_of_nonneg_left hn hc
    _ = (c * (a + ε / (c + 1))) * sqScale n := by ring
    _ ≤ (c * a + ε) * sqScale n :=
      mul_le_mul_of_nonneg_right hrate (sqScale_nonneg n)

lemma QuadLogRate.upper {f : ℕ → ℝ} {a : ℝ} (hf : QuadLogRate f a) :
    QuadUpper (fun n => Real.log |f n|) a := by
  intro ε hε
  filter_upwards [littleO_bound _ hf ε hε] with n hn
  have h := (le_abs_self (Real.log |f n| - a * sqScale n)).trans hn
  linarith

lemma QuadLogRate.exp_lower {f : ℕ → ℝ} {a : ℝ}
    (hf : QuadLogRate f a) (hne : ∀ᶠ n in atTop, f n ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, Real.exp ((a - ε) * sqScale n) ≤ |f n| := by
  filter_upwards [littleO_bound _ hf ε hε, hne] with n hn hz
  have hlo := (abs_le.mp hn).1
  have he : (a - ε) * sqScale n ≤ Real.log |f n| := by linarith
  calc
    Real.exp ((a - ε) * sqScale n) ≤ Real.exp (Real.log |f n|) :=
      Real.exp_le_exp.mpr he
    _ = |f n| := Real.exp_log (abs_pos.mpr hz)

lemma expUpper_of_logUpper {f : ℕ → ℝ} {a : ℝ}
    (hf : QuadUpper (fun n => Real.log |f n|) a) : QuadExpUpper f a := by
  intro ε hε
  filter_upwards [hf ε hε] with n hn
  exact (Real.le_exp_log |f n|).trans (Real.exp_le_exp.mpr hn)

lemma QuadLogRate.exp_upper {f : ℕ → ℝ} {a : ℝ}
    (hf : QuadLogRate f a) : QuadExpUpper f a :=
  expUpper_of_logUpper hf.upper

lemma QuadExpUpper.mul {f g : ℕ → ℝ} {a b : ℝ}
    (hf : QuadExpUpper f a) (hg : QuadExpUpper g b) :
    QuadExpUpper (fun n => f n * g n) (a + b) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (half_pos hε), hg (ε / 2) (half_pos hε)] with n hn hm
  rw [abs_mul]
  calc
    |f n| * |g n| ≤ Real.exp ((a + ε / 2) * sqScale n) *
        Real.exp ((b + ε / 2) * sqScale n) :=
      mul_le_mul hn hm (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((a + b + ε) * sqScale n) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- A linear error in the exponent is absorbed by any positive quadratic margin. -/
lemma eventually_linear_le_square (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, C * (2 * (n : ℝ) + 1) ≤ ε * sqScale n := by
  -- API: Algebra/Order/Archimedean/Basic.lean, `exists_nat_gt`.
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (3 * C / ε))
  apply eventually_atTop.2
  refine ⟨N, ?_⟩
  intro n hn
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans (hN.le.trans hnn)
  have hnc : 3 * C / ε ≤ (n : ℝ) :=
    (le_max_right _ _).trans (hN.le.trans hnn)
  have hmul : 3 * C ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hnc
  have hnn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hprod := mul_le_mul_of_nonneg_right hmul hnn0
  have hlin : C * (2 * (n : ℝ) + 1) ≤ 3 * C * n := by
    nlinarith
  dsimp [sqScale]
  nlinarith

/-- Metric epsilon proof, rather than an unverified name for an exp/power limit. -/
lemma tendsto_zero_of_exp_bound (f : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hf : ∀ᶠ n in atTop, |f n| ≤ Real.exp (-c * sqScale n)) :
    Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hf
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (-Real.log ε / c))
  refine ⟨max N M, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : M ≤ n := (le_max_right _ _).trans hn
  have hm : (M : ℝ) ≤ n := by exact_mod_cast hnM
  have hn1 : (1 : ℝ) ≤ n := (le_max_left _ _).trans (hM.le.trans hm)
  have hnlog : -Real.log ε / c < (n : ℝ) :=
    (le_max_right _ _).trans_lt (hM.trans_le hm)
  have hp : -Real.log ε < (n : ℝ) * c := (div_lt_iff₀ hc).mp hnlog
  have hsq : (n : ℝ) ≤ sqScale n := by
    dsimp [sqScale]
    nlinarith
  have hcscale := mul_le_mul_of_nonneg_left hsq hc.le
  have hexp : -c * sqScale n < Real.log ε := by nlinarith
  have hsmall : |f n| < ε := calc
    |f n| ≤ Real.exp (-c * sqScale n) := hN n hnN
    _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr hexp
    _ = ε := Real.exp_log hε
  simpa only [Real.dist_eq, sub_zero] using hsmall

lemma QuadExpUpper.tendsto_zero {f : ℕ → ℝ} {a : ℝ}
    (hf : QuadExpUpper f a) (ha : a < 0) : Tendsto f atTop (𝓝 0) := by
  have hc : 0 < -a / 2 := by linarith
  apply tendsto_zero_of_exp_bound f (-a / 2) hc
  filter_upwards [hf (-a / 2) hc] with n hn
  have he : a + -a / 2 = -(-a / 2) := by ring
  simpa only [he] using hn

/-- Complete successor bookkeeping: both products, not just A_n L_n. -/
theorem cross_product_limits (A L : ℕ → ℝ) (α β : ℝ)
    (hα : 0 ≤ α) (hgap : α < β)
    (hA : QuadExpUpper A α) (hL : QuadExpUpper L (-β)) :
    Tendsto L atTop (𝓝 0) ∧
    Tendsto (fun n => A n * L (n + 1)) atTop (𝓝 0) ∧
    Tendsto (fun n => A (n + 1) * L n) atTop (𝓝 0) := by
  let ε : ℝ := (β - α) / 8
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hid : 8 * ε = β - α := by dsimp [ε]; ring
  have hβ : 0 < β := hα.trans_lt hgap
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hA ε hε).and (hL ε hε))
  have hC : 0 ≤ α + ε := add_nonneg hα hε.le
  have hlin := eventually_linear_le_square (α + ε) ε hC hε
  have hleft : ∀ᶠ n in atTop,
      |A n * L (n + 1)| ≤ Real.exp (-ε * sqScale n) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : N ≤ n + 1 := hn.trans (Nat.le_succ n)
    rw [abs_mul]
    have hs : sqScale n ≤ sqScale (n + 1) := by
      dsimp [sqScale]
      push_cast
      nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hex : (α + ε) * sqScale n + (-β + ε) * sqScale (n + 1) ≤
        -ε * sqScale n := by
      have hc : -β + ε ≤ 0 := by linarith
      have hh : (-β + ε) * sqScale (n + 1) ≤ (-β + ε) * sqScale n :=
        mul_le_mul_of_nonpos_left hs hc
      have hscale := congrArg (fun t : ℝ => t * sqScale n) hid
      have hpos := mul_nonneg hε.le (sqScale_nonneg n)
      nlinarith [sqScale_nonneg n]
    calc
      |A n| * |L (n + 1)| ≤ Real.exp ((α + ε) * sqScale n) *
          Real.exp ((-β + ε) * sqScale (n + 1)) :=
        mul_le_mul (hN n hn).1 (hN (n + 1) hn').2
          (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (-ε * sqScale n) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr hex
  have hright : ∀ᶠ n in atTop,
      |A (n + 1) * L n| ≤ Real.exp (-ε * sqScale n) := by
    filter_upwards [eventually_ge_atTop N, hlin] with n hn hl
    have hn' : N ≤ n + 1 := hn.trans (Nat.le_succ n)
    have hsq : sqScale (n + 1) = sqScale n + 2 * (n : ℝ) + 1 := by
      dsimp [sqScale]
      push_cast
      ring
    have hex : (α + ε) * sqScale (n + 1) + (-β + ε) * sqScale n ≤
        -ε * sqScale n := by
      rw [hsq]
      have hscale := congrArg (fun t : ℝ => t * sqScale n) hid
      have hpos := mul_nonneg hε.le (sqScale_nonneg n)
      nlinarith [sqScale_nonneg n]
    rw [abs_mul]
    calc
      |A (n + 1)| * |L n| ≤ Real.exp ((α + ε) * sqScale (n + 1)) *
          Real.exp ((-β + ε) * sqScale n) :=
        mul_le_mul (hN (n + 1) hn').1 (hN n hn).2
          (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (-ε * sqScale n) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr hex
  exact ⟨hL.tendsto_zero (by linarith),
    tendsto_zero_of_exp_bound _ ε hε hleft,
    tendsto_zero_of_exp_bound _ ε hε hright⟩

/-- No new irrationality assumption is used in this analytic-to-integer transfer. -/
theorem rate_le_height_rate (A B : ℕ → ℤ) (ξ α β : ℝ)
    (hα : 0 ≤ α)
    (hne : ∀ᶠ n in atTop, (A n : ℝ) * ξ - B n ≠ 0)
    (hA : QuadExpUpper (fun n => (A n : ℝ)) α)
    (hL : QuadLogRate (fun n => (A n : ℝ) * ξ - B n) (-β)) :
    β ≤ α := by
  by_contra hn
  have hab : α < β := lt_of_not_ge hn
  obtain ⟨hz, hl, hr⟩ := cross_product_limits _ _ α β hα hab hA hL.exp_upper
  exact PaperR7.no_small_forms_of_cross_product_limits A B ξ hne hz hl hr

end ErdosProblems.Erdos1049.PaperR9
