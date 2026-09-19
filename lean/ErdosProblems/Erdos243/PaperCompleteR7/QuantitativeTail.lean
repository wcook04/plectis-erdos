import ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The quantitative canonical-tail lemma

Uncompiled candidates for the whole long-record `res:tailratio`.
The O(1/a_n) conclusion has an explicit eventual constant 16.  The growth
bound is first proved as an exact binary-power inequality, and then
converted to the exponential notation of the paper.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter

/-- Quantitative tail comparison under the stated quadratic growth.
This is stronger than merely proving the scaled tail ratio tends to one. -/
theorem quantitative_reciprocal_tail_ratio
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hs : Summable (fun n ↦ 1 / (a n : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ n, N ≤ n →
      |(a n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) /
          realTail (fun k ↦ 1 / (a k : ℝ)) n -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| ≤ 16 / (a n : ℝ) := by
  let t : ℕ → ℝ := fun n ↦ 1 / (a n : ℝ)
  let b : ℕ → ℝ := fun n ↦ (a n : ℝ) * realTail t n
  have hap : ∀ n, (0 : ℝ) < (a n : ℝ) := fun n ↦ by exact_mod_cast hpos n
  have htp : ∀ n, 0 < t n := fun n ↦ one_div_pos.mpr (hap n)
  have hq : Tendsto (fun n ↦ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))
      atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using hgrowth.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  obtain ⟨Nq, hNq⟩ := Metric.tendsto_atTop.mp hq 1 (by norm_num)
  have hqb : ∀ n, Nq ≤ n → (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) ≤ 2 := by
    intro n hn
    have hh := hNq n hn
    rw [Real.dist_eq] at hh
    have := (abs_lt.mp hh).2
    linarith
  have hr := reciprocal_successive_ratio_tendsto_zero a ha hpos hgrowth
  obtain ⟨Nr, hNr⟩ := Metric.tendsto_atTop.mp hr (1 / 2) (by norm_num)
  have hstep : ∀ n, Nr ≤ n → t (n + 1) ≤ (1 / 2) * t n := by
    intro n hn
    have hp : 0 ≤ t (n + 1) / t n := div_nonneg (htp _).le (htp _).le
    have hlt : t (n + 1) / t n < 1 / 2 := by
      have h := hNr n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤
          1 / (a (n + 1) : ℝ) / (1 / (a n : ℝ)))] at h
      exact h
    exact (div_le_iff₀ (htp n)).mp hlt.le
  have htail : ∀ n, Nr ≤ n → realTail t n ≤ 2 / (a n : ℝ) := by
    intro n hn
    have hh := realTail_geometric_bound t hs (fun j ↦ (htp j).le)
      (1 / 2) (by norm_num) (by norm_num) Nr n hn hstep
    rw [show (1 - (1 / 2 : ℝ))⁻¹ = 2 by norm_num] at hh
    calc realTail t n ≤ 2 * t n := hh
      _ = 2 / (a n : ℝ) := by dsimp only [t]; ring
  have hb1 : ∀ n, 1 ≤ b n := by
    intro n
    have hlead := realTail_leading_term t hs (fun j ↦ (htp j).le) n
    have hh := mul_le_mul_of_nonneg_left hlead (hap n).le
    have hcancel : (a n : ℝ) * t n = 1 := by
      dsimp [t]
      field_simp [(hap n).ne']
    simpa only [hcancel] using hh
  let N := max Nq Nr
  have hberr : ∀ n, N ≤ n → b n - 1 ≤ 4 / (a n : ℝ) := by
    intro n hn
    have hid : b n - 1 = (a n : ℝ) * realTail t (n + 1) := by
      dsimp [b]
      rw [realTail_step t hs n]
      dsimp [t]
      field_simp [(hap n).ne']
      <;> ring
    rw [hid]
    have ht := htail (n + 1) (by dsimp [N] at hn; omega)
    calc
      (a n : ℝ) * realTail t (n + 1) ≤ (a n : ℝ) * (2 / (a (n + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (hap n).le
      _ = (2 * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ))) / (a n : ℝ) := by
        field_simp [(hap n).ne', (hap (n + 1)).ne']
        <;> ring
      _ ≤ 4 / (a n : ℝ) := by
        apply (div_le_div_iff₀ (hap n) (hap n)).mpr
        have hh := hqb n (by dsimp [N] at hn; omega)
        nlinarith [mul_nonneg (hap n).le (show 0 ≤ 2 -
          (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) by linarith)]
  refine ⟨N, fun n hn ↦ ?_⟩
  have hbpos : 0 < b n := lt_of_lt_of_le (by norm_num) (hb1 n)
  have hqnonneg : 0 ≤ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) :=
    div_nonneg (sq_nonneg _) (hap _).le
  have hqdiv : (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) / b n ≤ 2 := by
    apply (div_le_iff₀ hbpos).mpr
    have hqq := hqb n (by dsimp [N] at hn; omega)
    have hb := hb1 n
    nlinarith
  have hnexterr : b (n + 1) - 1 ≤ 4 / (a n : ℝ) := by
    have hh := hberr (n + 1) (by omega)
    apply hh.trans
    apply (div_le_div_iff₀ (hap (n + 1)) (hap n)).mpr
    have hmono : (a n : ℝ) ≤ (a (n + 1) : ℝ) := by
      exact_mod_cast (ha (Nat.lt_succ_self n)).le
    linarith
  have hdiff : |b (n + 1) - b n| ≤ 8 / (a n : ℝ) := by
    have h0 := hb1 n
    have h1 := hb1 (n + 1)
    have he := hberr n hn
    have hnz : 0 ≤ 4 / (a n : ℝ) := div_nonneg (by norm_num) (hap n).le
    have hrel : (8 : ℝ) / (a n : ℝ) = 2 * (4 / (a n : ℝ)) := by ring
    rw [abs_le]
    constructor <;> linarith
  have hid : (a n : ℝ) * realTail t (n + 1) / realTail t n -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) =
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) / b n) * (b (n + 1) - b n) := by
    have hx : realTail t n ≠ 0 := (realTail_pos t hs htp n).ne'
    dsimp [b]
    field_simp [(hap n).ne', (hap (n + 1)).ne', hx]
    <;> ring
  rw [hid, abs_mul, abs_of_nonneg (div_nonneg hqnonneg hbpos.le)]
  calc
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) / b n) * |b (n + 1) - b n|
        ≤ 2 * (8 / (a n : ℝ)) :=
      mul_le_mul hqdiv hdiff (abs_nonneg _) (by norm_num)
    _ = 16 / (a n : ℝ) := by ring

/-- Explicit double-exponential lower bound with no asymptotic premise
other than the original ratio limit. -/
theorem quadratic_growth_binary_lower_bound
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ k : ℕ, 2 * (2 : ℝ) ^ ((2 : ℕ) ^ k) ≤ (a (N + k) : ℝ) := by
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hgrowth (1 / 2) (by norm_num)
  have hstep : ∀ n, N0 ≤ n → (a n : ℝ) ^ 2 ≤ 2 * (a (n + 1) : ℝ) := by
    intro n hn
    have hh := hN0 n hn
    rw [Real.dist_eq] at hh
    have hlo := (abs_lt.mp hh).1
    have hap : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast hpos n
    have hratio : (1 / 2 : ℝ) ≤ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2 := by linarith
    have hmul := (le_div_iff₀ (pow_pos hap 2)).mp hratio
    linarith
  have hnat : ∀ n, n < a n := by
    intro n
    induction n with
    | zero => exact hpos 0
    | succ n ih =>
        have hh : a n < a (n + 1) := ha (Nat.lt_succ_self n)
        omega
  let N := max N0 3
  refine ⟨N, fun k ↦ ?_⟩
  induction k with
  | zero =>
      have h4 : 4 ≤ a N := by have hh := hnat N; dsimp [N] at *; omega
      norm_num only [pow_zero, pow_one, Nat.add_zero]
      exact_mod_cast h4
  | succ k ih =>
      have hg := hstep (N + k) (by dsimp [N]; omega)
      have hp : 0 ≤ 2 * (2 : ℝ) ^ ((2 : ℕ) ^ k) := by positivity
      have hsq := mul_self_le_mul_self hp ih
      have heq : (2 : ℝ) ^ ((2 : ℕ) ^ (k + 1)) =
          ((2 : ℝ) ^ ((2 : ℕ) ^ k)) ^ 2 := by
        rw [pow_succ, pow_mul]
      rw [heq]
      have hi : N + (k + 1) = N + k + 1 := by omega
      rw [hi]
      nlinarith

/-- The exponential form printed in `res:tailratio`. -/
theorem quadratic_growth_exponential_lower_bound
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ c : ℝ, 0 < c ∧ ∃ N, ∀ n, N ≤ n →
      Real.exp (c * (2 : ℝ) ^ n) ≤ (a n : ℝ) := by
  obtain ⟨N, hN⟩ := quadratic_growth_binary_lower_bound a ha hpos hgrowth
  let c : ℝ := Real.log 2 / (2 : ℝ) ^ N
  have hc : 0 < c := div_pos (Real.log_pos (by norm_num)) (by positivity)
  refine ⟨c, hc, N, fun n hn ↦ ?_⟩
  let k := n - N
  have hnk : N + k = n := Nat.add_sub_of_le hn
  have hexp : Real.exp ((2 : ℝ) ^ k * Real.log 2) =
      (2 : ℝ) ^ ((2 : ℕ) ^ k) := by
    have hh := Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2) ((2 : ℕ) ^ k))
    rw [Real.log_pow] at hh
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh
  have hexponent : c * (2 : ℝ) ^ n = (2 : ℝ) ^ k * Real.log 2 := by
    rw [← hnk, pow_add]
    dsimp [c]
    field_simp
    <;> ring
  rw [hexponent, hexp]
  have hb := hN k
  rw [hnk] at hb
  have hp : 0 ≤ (2 : ℝ) ^ ((2 : ℕ) ^ k) := by positivity
  linarith

/-- Both conclusions of the displayed canonical-tail lemma.  The
asymptotic error is stated by its stronger explicit eventual constant;
1+gamma is exactly a_n^2/a_(n+1). -/
theorem canonical_tail_ratio_quantitative
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    let C := canonicalNaturalNumerator a p q
    (∃ N, ∀ n, N ≤ n →
      |(C (n + 1) : ℝ) / (C n : ℝ) -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| ≤ 16 / (a n : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N, ∀ n, N ≤ n →
      Real.exp (c * (2 : ℝ) ^ n) ≤ (a n : ℝ)) := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  obtain ⟨hcpos, hdpos, hc, hd, hrep⟩ := canonical_integer_tail a hpos p q hq hs
  refine ⟨?_, quadratic_growth_exponential_lower_bound a ha hpos hgrowth⟩
  obtain ⟨N, hN⟩ := quantitative_reciprocal_tail_ratio a ha hpos hs.summable hgrowth
  refine ⟨N, fun n hn ↦ ?_⟩
  have heq : (C (n + 1) : ℝ) / (C n : ℝ) =
      (a n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) /
        realTail (fun k ↦ 1 / (a k : ℝ)) n := by
    rw [hrep (n + 1), hrep n, hd n, Nat.cast_mul]
    have hdne : ((canonicalDenominator a q n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (hdpos n).ne'
    have hx : realTail (fun k ↦ 1 / (a k : ℝ)) n ≠ 0 :=
      (realTail_pos _ hs.summable (fun k ↦ one_div_pos.mpr
        (by exact_mod_cast hpos k)) n).ne'
    field_simp [hdne, hx]
    <;> ring
  rw [heq]
  exact hN n hn

end ErdosProblems.Erdos243.PaperCompleteR7
