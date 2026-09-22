import ErdosProblems.Erdos1049.QProductBoundsR10
import Mathlib

/-!
# Positive coefficient series: convergence, recurrence, and finite convolutions

New candidate. All elaboration, kernel checks, and axiom audits UNRUN.
No source-moment identity or coefficient-positivity supplier is a premise of
any source-specific theorem in the downstream files. The abstract lemmas in
this file prove reusable statements about explicitly given real sequences.
-/

namespace ErdosProblems.Erdos1049.PaperR16
open PaperR10 Filter
open scoped BigOperators Topology

noncomputable def coeffEval (c : ℕ → ℝ) (w : ℝ) : ℝ :=
  ∑' n : ℕ, c n * w ^ n

noncomputable def coeffConv (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ ij ∈ Finset.antidiagonal n, a ij.1 * b ij.2

noncomputable def coeffScale (a : ℕ → ℝ) (r : ℝ) (n : ℕ) : ℝ :=
  a n * r ^ n

lemma coeffScale_nonneg {a : ℕ → ℝ} {r : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ coeffScale a r n := mul_nonneg (ha n) (pow_nonneg hr n)

lemma summable_coeffEval_of_bounded {c : ℕ → ℝ} {C w : ℝ}
    (hc0 : ∀ n, 0 ≤ c n) (hcC : ∀ n, c n ≤ C)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    Summable (fun n : ℕ => c n * w ^ n) := by
  apply summable_nonneg_dominated
    (fun n => mul_nonneg (hc0 n) (pow_nonneg hw0 n))
    (fun n => mul_le_mul_of_nonneg_right (hcC n) (pow_nonneg hw0 n))
  exact (hasSum_geometric_of_lt_one hw0 hw1).summable.mul_left C

lemma coeffEval_nonneg {c : ℕ → ℝ} {w : ℝ}
    (hc : ∀ n, 0 ≤ c n) (hw : 0 ≤ w) : 0 ≤ coeffEval c w := by
  exact tsum_nonneg (fun n => mul_nonneg (hc n) (pow_nonneg hw n))

@[simp] lemma coeffEval_zero (c : ℕ → ℝ) : coeffEval c 0 = c 0 := by
  unfold coeffEval
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp

@[simp] lemma coeffEval_scale (c : ℕ → ℝ) (a w : ℝ) :
    coeffEval (coeffScale c a) w = coeffEval c (a * w) := by
  unfold coeffEval coeffScale
  apply tsum_congr
  intro n
  simp [mul_pow, mul_assoc]

/-- A quantitative approach to the constant coefficient; this supplies the
boundary condition in the q-binomial functional-equation argument. -/
lemma coeffEval_bounds {c : ℕ → ℝ} {C w : ℝ}
    (hc0 : ∀ n, 0 ≤ c n) (hcC : ∀ n, c n ≤ C) (hcz : c 0 = 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    1 ≤ coeffEval c w ∧ coeffEval c w ≤ 1 + C * w / (1 - w) := by
  have hs := summable_coeffEval_of_bounded hc0 hcC hw0 hw1
  have ht : Summable (fun n : ℕ => c (n + 1) * w ^ (n + 1)) :=
    (summable_nat_add_iff 1).2 hs
  have hg := (hasSum_geometric_of_lt_one hw0 hw1).mul_left (C * w)
  have he : coeffEval c w = 1 + ∑' n : ℕ, c (n + 1) * w ^ (n + 1) := by
    simpa [coeffEval, hcz] using hs.tsum_eq_zero_add
  have hb : (∑' n : ℕ, c (n + 1) * w ^ (n + 1)) ≤ C * w / (1 - w) := by
    calc
      _ ≤ ∑' n : ℕ, (C * w) * w ^ n := by
        apply Summable.tsum_le_tsum _ ht hg.summable
        intro n
        calc
          c (n + 1) * w ^ (n + 1) ≤ C * w ^ (n + 1) :=
            mul_le_mul_of_nonneg_right (hcC (n + 1)) (pow_nonneg hw0 _)
          _ = (C * w) * w ^ n := by rw [pow_succ]; ring
      _ = C * w / (1 - w) := by rw [hg.tsum_eq]; ring
  rw [he]
  constructor
  · exact le_add_of_nonneg_right
      (tsum_nonneg (fun n => mul_nonneg (hc0 _) (pow_nonneg hw0 _)))
  · linarith

/-- A bounded coefficient series with constant term one tends to one at the
geometrically shrinking arguments used in the product iteration. -/
lemma coeffEval_tendsto_geometric {c : ℕ → ℝ} {C q w : ℝ}
    (hc0 : ∀ n, 0 ≤ c n) (hcC : ∀ n, c n ≤ C) (hcz : c 0 = 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Tendsto (fun n : ℕ => coeffEval c (q ^ (n + 1) * w)) atTop (𝓝 1) := by
  have hz0 (n : ℕ) : 0 ≤ q ^ (n + 1) * w :=
    mul_nonneg (pow_nonneg hq0 _) hw0
  have hz1 (n : ℕ) : q ^ (n + 1) * w < 1 := by
    have hp : q ^ (n + 1) ≤ q := by
      simpa using qpow_antitone hq0 hq1.le (by omega : 1 ≤ n + 1)
    calc
      q ^ (n + 1) * w ≤ q ^ (n + 1) * 1 :=
        mul_le_mul_of_nonneg_left hw1 (pow_nonneg hq0 _)
      _ ≤ q := by simpa using hp
      _ < 1 := hq1
  have hz : Tendsto (fun n : ℕ => q ^ (n + 1) * w) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (q * w)
    simpa [pow_succ, mul_assoc] using h
  have hu : Tendsto (fun n : ℕ =>
      1 + C * (q ^ (n + 1) * w) / (1 - q ^ (n + 1) * w)) atTop (𝓝 1) := by
    have hnum : Tendsto (fun n : ℕ => C * (q ^ (n + 1) * w)) atTop (𝓝 0) := by
      simpa using hz.const_mul C
    have hden : Tendsto (fun n : ℕ => 1 - q ^ (n + 1) * w) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hz :
        Tendsto (fun n : ℕ => 1 - q ^ (n + 1) * w) atTop (𝓝 (1 - 0)))
    simpa using (hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)).const_add 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => (coeffEval_bounds hc0 hcC hcz (hz0 n) (hz1 n)).1)
    (fun n => (coeffEval_bounds hc0 hcC hcz (hz0 n) (hz1 n)).2)

set_option maxHeartbeats 1600000 in
/-- One recurrence lemma serves both q-binomial ratios and Euler's positive
product. All series used in subtracting and shifting have HasSum witnesses. -/
lemma coeffEval_functional_equation {c : ℕ → ℝ} {q w u v : ℝ}
    (hw : Summable (fun n : ℕ => c n * w ^ n))
    (hqw : Summable (fun n : ℕ => c n * (q * w) ^ n))
    (hrec : ∀ n : ℕ,
      c (n + 1) * (1 - q ^ (n + 1)) = c n * (u + v * q ^ n)) :
    (1 - u * w) * coeffEval c w = (1 + v * w) * coeffEval c (q * w) := by
  have ht : HasSum
      (fun n : ℕ => c (n + 1) * w ^ (n + 1) -
        c (n + 1) * (q * w) ^ (n + 1))
      (w * (u * coeffEval c w + v * coeffEval c (q * w))) := by
    have h := ((hw.hasSum.mul_left u).add (hqw.hasSum.mul_left v)).mul_left w
    refine h.congr_fun (fun n => ?_)
    calc
      c (n + 1) * w ^ (n + 1) - c (n + 1) * (q * w) ^ (n + 1) =
          (c (n + 1) * (1 - q ^ (n + 1))) * w ^ (n + 1) := by
            rw [mul_pow]
            ring
      _ = (c n * (u + v * q ^ n)) * w ^ (n + 1) := by rw [hrec n]
      _ = w * (u * (c n * w ^ n) + v * (c n * (q * w) ^ n)) := by
            rw [mul_pow, pow_succ]
            ring
  have ha : HasSum
      (fun n : ℕ => c n * w ^ n - c n * (q * w) ^ n)
      (w * (u * coeffEval c w + v * coeffEval c (q * w))) := by
    let f : ℕ → ℝ := fun n => c n * w ^ n - c n * (q * w) ^ n
    have ht' : HasSum (fun n => f (n + 1))
        (w * (u * coeffEval c w + v * coeffEval c (q * w))) := by
      simpa only [f] using ht
    simpa only [f, pow_zero, mul_one, sub_self, zero_add] using ht'.zero_add
  have he := (hw.hasSum.sub hqw.hasSum).unique ha
  simp only [pow_zero, mul_one, sub_self, zero_add] at he
  change coeffEval c w - coeffEval c (q * w) = _ at he
  linear_combination he

lemma coeffConv_nonneg {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (n : ℕ) :
    0 ≤ coeffConv a b n := by
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (ha ij.1) (hb ij.2))

@[simp] lemma coeffConv_zero (a b : ℕ → ℝ) : coeffConv a b 0 = a 0 * b 0 := by
  simp [coeffConv]

lemma coeffConv_mono {a b c d : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hd : ∀ n, 0 ≤ d n)
    (hac : ∀ n, a n ≤ c n) (hbd : ∀ n, b n ≤ d n) (n : ℕ) :
    coeffConv a b n ≤ coeffConv c d n := by
  apply Finset.sum_le_sum
  intro ij hij
  calc
    a ij.1 * b ij.2 ≤ a ij.1 * d ij.2 :=
      mul_le_mul_of_nonneg_left (hbd ij.2) (ha ij.1)
    _ ≤ c ij.1 * d ij.2 :=
      mul_le_mul_of_nonneg_right (hac ij.1) (hd ij.2)

/-- The monotonicity form used downstream has all factors nonnegative. -/
lemma coeffConv_le_coeffConv {a b c d : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hac : ∀ n, a n ≤ c n) (hbd : ∀ n, b n ≤ d n) (n : ℕ) :
    coeffConv a b n ≤ coeffConv c d n := by
  apply Finset.sum_le_sum
  intro ij hij
  exact mul_le_mul (hac ij.1) (hbd ij.2) (hb ij.2) ((ha ij.1).trans (hac ij.1))

/-- Summability of a nonnegative product family via the normed-ring product
summability theorem. -/
lemma summable_product_nonneg {ι κ : Type*} {f : ι → ℝ} {g : κ → ℝ}
    (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ j, 0 ≤ g j)
    (hf : Summable f) (hg : Summable g) :
    Summable (fun p : ι × κ => f p.1 * g p.2) := by
  exact hf.mul_of_nonneg hg hf0 hg0

lemma coeffConv_weight (a b : ℕ → ℝ) (w : ℝ) (n : ℕ) :
    coeffConv a b n * w ^ n =
      coeffConv (fun k => a k * w ^ k) (fun k => b k * w ^ k) n := by
  unfold coeffConv
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [← he, pow_add]
  ring

set_option maxHeartbeats 800000 in
lemma coeffConv_hasSum {a b : ℕ → ℝ} {w : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n) (hw0 : 0 ≤ w)
    (ha : Summable (fun n => a n * w ^ n))
    (hb : Summable (fun n => b n * w ^ n)) :
    HasSum (fun n => coeffConv a b n * w ^ n)
      (coeffEval a w * coeffEval b w) := by
  have hp : Summable (fun p : ℕ × ℕ =>
      (a p.1 * w ^ p.1) * (b p.2 * w ^ p.2)) :=
    summable_product_nonneg
      (fun n => mul_nonneg (ha0 n) (pow_nonneg hw0 n))
      (fun n => mul_nonneg (hb0 n) (pow_nonneg hw0 n)) ha hb
  let f : ℕ → ℝ := fun n => a n * w ^ n
  let g : ℕ → ℝ := fun n => b n * w ^ n
  have hs : Summable (fun n : ℕ => ∑ ij ∈ Finset.antidiagonal n,
      f ij.1 * g ij.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul (A := ℕ) (f := f) (g := g) hp
  have he : (∑' n, f n) * (∑' n, g n) =
      ∑' n, ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 :=
    Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      (A := ℕ) (f := f) (g := g) ha hb hp
  have hsum : HasSum (fun n : ℕ => ∑ ij ∈ Finset.antidiagonal n,
      f ij.1 * g ij.2) ((∑' n, f n) * (∑' n, g n)) :=
    he.symm ▸ hs.hasSum
  apply hsum.congr_fun
  intro n
  exact coeffConv_weight a b w n

lemma coeffEval_conv {a b : ℕ → ℝ} {w : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n) (hw0 : 0 ≤ w)
    (ha : Summable (fun n => a n * w ^ n))
    (hb : Summable (fun n => b n * w ^ n)) :
    coeffEval (coeffConv a b) w = coeffEval a w * coeffEval b w :=
  (coeffConv_hasSum ha0 hb0 hw0 ha hb).tsum_eq

/-- The regular-factor convolution estimate used in the cubic comparison. -/
lemma coeffConv_le_mass_mul {a d : ℕ → ℝ} {M : ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hd0 : ∀ n, 0 ≤ d n) (hd : Monotone d)
    (ha : Summable a) (hM : (∑' n, a n) ≤ M) (n : ℕ) :
    coeffConv a d n ≤ M * d n := by
  rw [coeffConv,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * d j)]
  calc
    (∑ i ∈ Finset.range (n + 1), a i * d (n - i)) ≤
        ∑ i ∈ Finset.range (n + 1), a i * d n := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hd (Nat.sub_le n i)) (ha0 i)
    _ = (∑ i ∈ Finset.range (n + 1), a i) * d n := by rw [Finset.sum_mul]
    _ ≤ M * d n := mul_le_mul_of_nonneg_right
      ((ha.sum_le_tsum _ (fun i _ => ha0 i)).trans hM) (hd0 n)

/-- Keeping the degree-zero contribution of one factor is a genuine lower
bound because every discarded convolution term is nonnegative. -/
lemma left_le_coeffConv {a b : ℕ → ℝ}
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n) (hbz : b 0 = 1) (n : ℕ) :
    a n ≤ coeffConv a b n := by
  have hm : (n, 0) ∈ Finset.antidiagonal n := by simp
  have h := Finset.single_le_sum
    (fun ij (_ : ij ∈ Finset.antidiagonal n) => mul_nonneg (ha0 ij.1) (hb0 ij.2)) hm
  simpa only [hbz, mul_one] using h

end ErdosProblems.Erdos1049.PaperR16
