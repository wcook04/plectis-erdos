import ErdosProblems.Erdos1049.G02WeightedBlocksR16
import Mathlib

/-! Quadratic-rate transport lemmas and strict-rate dominance for the source.
The V step follows from strict separation of the U and remainder rates. -/
namespace ErdosProblems.Erdos1049.PaperR16
open Filter Asymptotics
open PaperR9
open scoped Topology
set_option maxHeartbeats 2000000

lemma QuadRateR16.congr_eventually {f g : ℕ → ℝ} {a : ℝ}
    (hf : QuadRateR16 f a) (he : ∀ᶠ n in atTop, f n = g n) :
    QuadRateR16 g a := by
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [littleO_bound _ hf ε hε, he] with n hn heq
  simpa only [← heq, Real.norm_eq_abs, abs_of_nonneg (sqScale_nonneg n)] using hn

lemma QuadRateR16.add {f g : ℕ → ℝ} {a b : ℝ}
    (hf : QuadRateR16 f a) (hg : QuadRateR16 g b) :
    QuadRateR16 (fun n => f n + g n) (a+b) := by
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [littleO_bound _ hf (ε/2) (half_pos hε),
    littleO_bound _ hg (ε/2) (half_pos hε)] with n hn hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sqScale_nonneg n)]
  have he : f n + g n - (a+b)*sqScale n =
      (f n-a*sqScale n)+(g n-b*sqScale n) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

lemma QuadRateR16.const_mul {f : ℕ → ℝ} {a : ℝ}
    (hf : QuadRateR16 f a) (c : ℝ) :
    QuadRateR16 (fun n => c*f n) (c*a) := by
  apply IsLittleO.of_bound
  intro ε hε
  have hc : 0 < |c|+1 := by positivity
  filter_upwards [littleO_bound _ hf (ε/(|c|+1)) (div_pos hε hc)] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sqScale_nonneg n)]
  have he : c*f n-(c*a)*sqScale n = c*(f n-a*sqScale n) := by ring
  rw [he, abs_mul]
  have hb := mul_le_mul_of_nonneg_left hn (abs_nonneg c)
  have hεeq : (|c|+1)*(ε/(|c|+1)) = ε := by field_simp [hc.ne']
  have hratio : |c| * (ε/(|c|+1)) ≤ ε := by
    have ht := mul_le_mul_of_nonneg_right (show |c| ≤ |c|+1 by linarith)
      (div_nonneg hε.le hc.le)
    linarith
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hratio (sqScale_nonneg n)])

lemma QuadRateR16.sub {f g : ℕ → ℝ} {a b : ℝ}
    (hf : QuadRateR16 f a) (hg : QuadRateR16 g b) :
    QuadRateR16 (fun n => f n-g n) (a-b) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hf.add (hg.const_mul (-1))

lemma QuadRateR16.upper {f : ℕ → ℝ} {a : ℝ} (hf : QuadRateR16 f a) :
    QuadUpper f a := by
  intro ε hε
  filter_upwards [littleO_bound _ hf ε hε] with n hn
  have h := (le_abs_self (f n-a*sqScale n)).trans hn
  linarith

lemma rate_of_eventual_linear_errorR16 (f : ℕ → ℝ) (a C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᶠ n in atTop, |f n-a*sqScale n| ≤ C*(2*(n : ℝ)+1)) :
    QuadRateR16 f a := by
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [h, eventually_linear_le_square C ε hC hε] with n hn hm
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sqScale_nonneg n)] using hn.trans hm

lemma bounded_rate_zeroR16 (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ᶠ n in atTop, |f n| ≤ C) : QuadRateR16 f 0 := by
  apply rate_of_eventual_linear_errorR16 f 0 C hC
  filter_upwards [h] with n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  simpa only [zero_mul, sub_zero] using hn.trans (by nlinarith)

lemma quadLogRate_congrR16 {f g : ℕ → ℝ} {a : ℝ}
    (hf : QuadLogRate f a) (he : ∀ᶠ n in atTop, f n=g n) : QuadLogRate g a := by
  apply QuadRateR16.congr_eventually hf
  filter_upwards [he] with n hn
  rw [hn]

lemma quadLogRate_mulR16 {f g : ℕ → ℝ} {a b : ℝ}
    (hf : QuadLogRate f a) (hg : QuadLogRate g b)
    (hfn : ∀ᶠ n in atTop, f n ≠ 0) (hgn : ∀ᶠ n in atTop, g n ≠ 0) :
    QuadLogRate (fun n => f n*g n) (a+b) := by
  apply QuadRateR16.congr_eventually (QuadRateR16.add hf hg)
  filter_upwards [hfn, hgn] with n hn hm
  rw [abs_mul, Real.log_mul (abs_ne_zero.mpr hn) (abs_ne_zero.mpr hm)]

lemma quadLogRate_divR16 {f g : ℕ → ℝ} {a b : ℝ}
    (hf : QuadLogRate f a) (hg : QuadLogRate g b)
    (hfn : ∀ᶠ n in atTop, f n ≠ 0) (hgn : ∀ᶠ n in atTop, g n ≠ 0) :
    QuadLogRate (fun n => f n/g n) (a-b) := by
  apply QuadRateR16.congr_eventually (QuadRateR16.sub hf hg)
  filter_upwards [hfn, hgn] with n hn hm
  rw [abs_div, Real.log_div (abs_ne_zero.mpr hn) (abs_ne_zero.mpr hm)]

lemma quadLogRate_powerR16 (m : ℕ → ℕ) (a p : ℝ) (hp : 0 < p)
    (hm : QuadRateR16 (fun n => (m n : ℝ)) a) :
    QuadLogRate (fun n => p^m n) (a*Real.log p) := by
  have h := hm.const_mul (Real.log p)
  rw [mul_comm (Real.log p) a] at h
  apply QuadRateR16.congr_eventually h
  exact Eventually.of_forall (fun n => by
    rw [abs_of_pos (pow_pos hp _), Real.log_pow]
    ring)

/-- Strict rate separation justifies the V step; no cancellation premise is omitted. -/
theorem quadLogRate_dominant_differenceR16 (f g : ℕ → ℝ) (a b c : ℝ)
    (hc : 0 < c) (hgap : b < a)
    (hf : QuadLogRate f a) (hg : QuadLogRate g b)
    (hfn : ∀ᶠ n in atTop, f n ≠ 0) (hgn : ∀ᶠ n in atTop, g n ≠ 0) :
    QuadLogRate (fun n => c*f n-g n) a ∧
      (∀ᶠ n in atTop, c*f n-g n ≠ 0) := by
  have hquot := quadLogRate_divR16 hg hf hgn hfn
  have ht : Tendsto (fun n => g n/f n) atTop (𝓝 0) :=
    hquot.exp_upper.tendsto_zero (sub_neg.mpr hgap)
  have hsmall : ∀ᶠ n in atTop, |g n/f n| < c/2 := by
    simpa only [Real.dist_eq, sub_zero] using
      (Metric.tendsto_nhds.mp ht) (c/2) (half_pos hc)
  let r : ℕ → ℝ := fun n => c-g n/f n
  have hrange : ∀ᶠ n in atTop, c/2 < r n ∧ r n < 3*c/2 := by
    filter_upwards [hsmall] with n hn
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hn
    dsimp [r]
    constructor <;> linarith
  have hrpos : ∀ᶠ n in atTop, 0 < r n := by
    filter_upwards [hrange] with n hn
    linarith [hn.1]
  have hrbound : ∀ᶠ n in atTop, |Real.log (|r n|)| ≤
      |Real.log (c/2)| + |Real.log (3*c/2)| := by
    filter_upwards [hrange, hrpos] with n hn hp
    rw [abs_of_pos hp]
    have hlo := Real.log_le_log (half_pos hc) hn.1.le
    have hhi := Real.log_le_log hp hn.2.le
    rw [abs_le]
    constructor
    · have hl := neg_abs_le (Real.log (c/2))
      have hu := abs_nonneg (Real.log (3*c/2))
      linarith
    · have hl := le_abs_self (Real.log (3*c/2))
      have hu := abs_nonneg (Real.log (c/2))
      linarith
  have hr : QuadLogRate r 0 := bounded_rate_zeroR16 _ _ (by positivity) hrbound
  have hrne : ∀ᶠ n in atTop, r n ≠ 0 := hrpos.mono (fun n hn => hn.ne')
  have hprod := quadLogRate_mulR16 hf hr hfn hrne
  have he : ∀ᶠ n in atTop, f n*r n = c*f n-g n := by
    filter_upwards [hfn] with n hn
    dsimp [r]
    field_simp [hn]
    <;> ring
  constructor
  · simpa only [add_zero] using quadLogRate_congrR16 hprod he
  · filter_upwards [hfn, hrne, he] with n hn hm heq
    rw [← heq]
    exact mul_ne_zero hn hm

end ErdosProblems.Erdos1049.PaperR16
