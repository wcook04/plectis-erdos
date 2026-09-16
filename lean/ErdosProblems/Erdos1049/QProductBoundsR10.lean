import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-!
# Positive q-products and q-binomial ratio coefficients

The infinite product is constructed from an absolutely
convergent logarithmic series, and is proved to be the limit of its finite
products. Its positivity is therefore not an assumed supplier.
-/
namespace ErdosProblems.Erdos1049.PaperR10
open Filter
open scoped BigOperators Topology

/-- A comparison test proved using finite partial sums, avoiding a conditional
use of the totalised `tsum` operation. -/
theorem summable_nonneg_dominated {f g : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hfg : ∀ k, f k ≤ g k) (hg : Summable g) : Summable f := by
  apply summable_of_sum_le hf
  intro s
  exact (Finset.sum_le_sum (fun k _ => hfg k)).trans
    (hg.sum_le_tsum s (fun k _ => (hf k).trans (hfg k)))

/-- Uniform logarithmic bound on a compact subinterval of [0,1). -/
theorem abs_log_one_sub_le {u a : ℝ}
    (hu : 0 ≤ u) (hua : u ≤ a) (ha : a < 1) :
    |Real.log (1 - u)| ≤ u / (1 - a) := by
  have hau : u < 1 := hua.trans_lt ha
  have hd : 0 < 1 - u := sub_pos.mpr hau
  have hda : 0 < 1 - a := sub_pos.mpr ha
  have hlog : Real.log (1 - u) ≤ 0 := by
    have hh := Real.log_le_log hd (by linarith : 1 - u ≤ 1)
    simpa using hh
  have hl := Real.one_sub_inv_le_log_of_pos hd
  have hid : 1 - (1 - u)⁻¹ = -(u / (1 - u)) := by
    field_simp [hd.ne']
    <;> ring
  rw [hid] at hl
  have hdiv : u / (1 - u) ≤ u / (1 - a) :=
    div_le_div_of_nonneg_left hu hda (by linarith)
  rw [abs_of_nonpos hlog]
  linarith

noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)

@[simp] theorem qPochhammerFinite_zero (a q : ℝ) : qPochhammerFinite a q 0 = 1 := by
  simp [qPochhammerFinite]

theorem qPochhammerFinite_succ (a q : ℝ) (n : ℕ) :
    qPochhammerFinite a q (n + 1) = qPochhammerFinite a q n * (1 - a * q ^ n) := by
  simp [qPochhammerFinite, Finset.prod_range_succ]

theorem qPochhammerFinite_nonneg_le_one {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    0 ≤ qPochhammerFinite a q n ∧ qPochhammerFinite a q n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hpow : 0 ≤ q ^ n := pow_nonneg hq0 n
    have hpow1 : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1
    have hmul : 0 ≤ a * q ^ n := mul_nonneg ha0 hpow
    have hmul1 : a * q ^ n ≤ 1 := by
      calc
        a * q ^ n ≤ a * 1 := mul_le_mul_of_nonneg_left hpow1 ha0
        _ ≤ 1 := by simpa using ha1
    rw [qPochhammerFinite_succ]
    constructor
    · exact mul_nonneg hn.1 (by linarith)
    · calc
        _ ≤ 1 * (1 - a * q ^ n) :=
          mul_le_mul_of_nonneg_right hn.2 (by linarith)
        _ ≤ 1 := by nlinarith

theorem qPochhammerFinite_pos {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    0 < qPochhammerFinite a q n := by
  unfold qPochhammerFinite
  apply Finset.prod_pos
  intro k hk
  have hp : q ^ k ≤ 1 := pow_le_one₀ hq0 hq1
  have : a * q ^ k ≤ a := by simpa using mul_le_mul_of_nonneg_left hp ha0
  linarith

/-- Explicit summability of the majorant for logarithms of q-product factors. -/
lemma hasSum_qPochhammer_log_majorant {a q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => a * q ^ k / (1 - a))
      (a / ((1 - a) * (1 - q))) := by
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (a / (1 - a))
  convert h using 1 <;> simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Absolute logarithmic convergence proves that no limiting product vanishes. -/
theorem summable_log_qPochhammer {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun k : ℕ => Real.log (1 - a * q ^ k)) := by
  apply Summable.of_abs
  apply summable_nonneg_dominated (fun _ => abs_nonneg _)
  · intro k
    apply abs_log_one_sub_le (mul_nonneg ha0 (pow_nonneg hq0 k))
    · simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1.le) ha0
    · exact ha1
  · exact (hasSum_qPochhammer_log_majorant (a := a) hq0 hq1).summable

noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))

/-- Positivity is subsequently paired with the finite-product limit theorem. -/
theorem qPochhammerInfinity_pos (a q : ℝ) : 0 < qPochhammerInfinity a q :=
  Real.exp_pos _

lemma exp_sum_log_qPochhammer {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (n : ℕ) :
    Real.exp (∑ k ∈ Finset.range n, Real.log (1 - a * q ^ k)) =
      qPochhammerFinite a q n := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hfactor : 0 < 1 - a * q ^ n := by
      have hp : a * q ^ n ≤ a := by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) ha0
      linarith
    rw [Finset.sum_range_succ, Real.exp_add, hn, Real.exp_log hfactor,
      qPochhammerFinite_succ]

theorem tendsto_qPochhammerFinite {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (qPochhammerFinite a q) atTop (𝓝 (qPochhammerInfinity a q)) := by
  have h := (summable_log_qPochhammer ha0 ha1 hq0 hq1).hasSum.tendsto_sum_nat
  have he := (Real.continuous_exp.tendsto _).comp h
  change Tendsto (fun n : ℕ => Real.exp
    (∑ k ∈ Finset.range n, Real.log (1 - a * q ^ k))) atTop
    (𝓝 (qPochhammerInfinity a q)) at he
  simpa only [exp_sum_log_qPochhammer ha0 ha1 hq0 hq1.le] using he

/-- The infinite product is a uniform lower bound for every prefix. -/
theorem qPochhammerInfinity_le_finite {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    qPochhammerInfinity a q ≤ qPochhammerFinite a q n := by
  have hs := summable_log_qPochhammer ha0 ha1 hq0 hq1
  have hn : ∀ k : ℕ, Real.log (1 - a * q ^ k) ≤ 0 := by
    intro k
    have hf : 0 < 1 - a * q ^ k := by
      have : a * q ^ k ≤ a := by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1.le) ha0
      linarith
    have hh := Real.log_le_log hf
      (by nlinarith [mul_nonneg ha0 (pow_nonneg hq0 k)] : 1 - a * q ^ k ≤ 1)
    simpa using hh
  have hb := hs.neg.sum_le_tsum (Finset.range n) (fun k _ => neg_nonneg.mpr (hn k))
  simp only [Finset.sum_neg_distrib, tsum_neg] at hb
  have hlogs : (∑' k : ℕ, Real.log (1 - a * q ^ k)) ≤
      ∑ k ∈ Finset.range n, Real.log (1 - a * q ^ k) := by linarith
  calc
    qPochhammerInfinity a q ≤
        Real.exp (∑ k ∈ Finset.range n, Real.log (1 - a * q ^ k)) :=
      Real.exp_le_exp.mpr hlogs
    _ = _ := exp_sum_log_qPochhammer ha0 ha1 hq0 hq1.le n

/-- An explicit positive lower bound, with no asymptotic product convention. -/
theorem qPochhammerInfinity_lower {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Real.exp (-a / ((1 - a) * (1 - q))) ≤ qPochhammerInfinity a q := by
  have hs := summable_log_qPochhammer ha0 ha1 hq0 hq1
  have hg := hasSum_qPochhammer_log_majorant (a := a) hq0 hq1
  have hb : (∑' k : ℕ, -Real.log (1 - a * q ^ k)) ≤
      ∑' k : ℕ, a * q ^ k / (1 - a) := by
    apply Summable.tsum_le_tsum _ hs.neg hg.summable
    intro k
    have hc := abs_log_one_sub_le
      (mul_nonneg ha0 (pow_nonneg hq0 k))
      (by simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1.le) ha0) ha1
    exact (neg_le_abs _).trans hc
  rw [tsum_neg, hg.tsum_eq] at hb
  apply Real.exp_le_exp.mpr
  change -a / ((1 - a) * (1 - q)) ≤ ∑' k : ℕ, Real.log (1 - a * q ^ k)
  calc
    _ = -(a / ((1 - a) * (1 - q))) := by ring
    _ ≤ -(-(∑' k : ℕ, Real.log (1 - a * q ^ k))) := neg_le_neg hb
    _ = _ := neg_neg _

/-- Elementary antitonicity in the exponent, with the endpoint q=0 allowed. -/
theorem qpow_antitone {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {i j : ℕ} (hij : i ≤ j) : q ^ j ≤ q ^ i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [pow_add]
  simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) (pow_nonneg hq0 i)

/-- Every finite product beginning at a positive exponent is bounded below by P. -/
theorem shifted_qPochhammer_bounds {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (s n : ℕ) (hs : 1 ≤ s) :
    qPochhammerInfinity q q ≤ qPochhammerFinite (q ^ s) q n ∧
      qPochhammerFinite (q ^ s) q n ≤ 1 := by
  have hqs : q ^ s ≤ q := by simpa using qpow_antitone hq0.le hq1.le hs
  constructor
  · apply (qPochhammerInfinity_le_finite hq0.le hq1 hq0.le hq1 n).trans
    unfold qPochhammerFinite
    apply Finset.prod_le_prod
    · intro k hk
      have h : q * q ^ k ≤ q := by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hq0.le hq1.le) hq0.le
      linarith
    · intro k hk
      have h := mul_le_mul_of_nonneg_right hqs (pow_nonneg hq0.le k)
      linarith
  · exact (qPochhammerFinite_nonneg_le_one (pow_nonneg hq0.le s)
      (hqs.trans hq1.le) hq0.le hq1.le n).2

/-- Coefficients of (a w;q)_infinity/(w;q)_infinity, defined by the coefficient
recurrence rather than by invoking a q-binomial identity without a proof. -/
noncomputable def qBinomialRatioCoeff (a q : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => qBinomialRatioCoeff a q k * (1 - a * q ^ k) / (1 - q ^ (k + 1))

theorem qBinomialRatioCoeff_nonneg {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    0 ≤ qBinomialRatioCoeff a q k := by
  induction k with
  | zero => simp [qBinomialRatioCoeff]
  | succ k hk =>
    have hnum : 0 ≤ 1 - a * q ^ k := by
      have hpow : q ^ k ≤ 1 := pow_le_one₀ hq0 hq1.le
      have hp := mul_le_mul_of_nonneg_left hpow ha0
      nlinarith
    have hden : 0 < 1 - q ^ (k + 1) := by
      have hp : q ^ (k + 1) ≤ q := by
        simpa using qpow_antitone hq0 hq1.le (by omega : 1 ≤ k + 1)
      linarith
    exact div_nonneg (mul_nonneg hk hnum) hden.le

theorem qBinomialRatioCoeff_eq_ratio {a q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    qBinomialRatioCoeff a q k = qPochhammerFinite a q k / qPochhammerFinite q q k := by
  induction k with
  | zero => simp [qBinomialRatioCoeff]
  | succ k hk =>
    rw [qBinomialRatioCoeff, hk, qPochhammerFinite_succ,
      qPochhammerFinite_succ]
    have he : q * q ^ k = q ^ (k + 1) := by rw [pow_succ]; ring
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- The a=1 endpoint is important: all positive-degree coefficients vanish. -/
@[simp] theorem qBinomialRatioCoeff_one_succ (q : ℝ) (k : ℕ) :
    qBinomialRatioCoeff 1 q (k + 1) = 0 := by
  induction k with
  | zero => simp [qBinomialRatioCoeff]
  | succ k hk =>
      rw [qBinomialRatioCoeff, hk]
      simp

/-- The lower comparison used at a=sqrt(q), with a strict endpoint. -/
theorem qBinomialRatioCoeff_lower {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    qPochhammerInfinity a q ≤ qBinomialRatioCoeff a q k := by
  rw [qBinomialRatioCoeff_eq_ratio hq0 hq1]
  have hd := qPochhammerFinite_pos hq0 hq1 hq0 hq1.le k
  apply (le_div_iff₀ hd).mpr
  have hD := (qPochhammerFinite_nonneg_le_one hq0 hq1.le hq0 hq1.le k).2
  calc
    _ ≤ qPochhammerInfinity a q * 1 :=
      mul_le_mul_of_nonneg_left hD (qPochhammerInfinity_pos a q).le
    _ = qPochhammerInfinity a q := by ring
    _ ≤ _ := qPochhammerInfinity_le_finite ha0 ha1 hq0 hq1 k

/-- Uniform upper coefficient bound, including the a=1 endpoint. -/
theorem qBinomialRatioCoeff_upper {a q : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    qBinomialRatioCoeff a q k ≤ (qPochhammerInfinity q q)⁻¹ := by
  rw [qBinomialRatioCoeff_eq_ratio hq0 hq1]
  have hd := qPochhammerFinite_pos hq0 hq1 hq0 hq1.le k
  have hnum := (qPochhammerFinite_nonneg_le_one ha0 ha1 hq0 hq1.le k).2
  calc
    _ ≤ 1 / qPochhammerFinite q q k := div_le_div_of_nonneg_right hnum hd.le
    _ ≤ 1 / qPochhammerInfinity q q :=
      one_div_le_one_div_of_le (qPochhammerInfinity_pos q q)
        (qPochhammerInfinity_le_finite hq0 hq1 hq0 hq1 k)
    _ = _ := one_div _

end ErdosProblems.Erdos1049.PaperR10
