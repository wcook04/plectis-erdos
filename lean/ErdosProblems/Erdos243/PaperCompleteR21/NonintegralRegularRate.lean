-- SPDX-FileCopyrightText: 2026 Will Cook
-- SPDX-License-Identifier: Apache-2.0

import ErdosProblems.Erdos243.PaperCompleteR21.RegularRateExtraction
import ErdosProblems.Erdos243.PaperCompleteR7.QuantitativeTail

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21

open Filter
open ErdosProblems.Erdos243.PaperCompleteR7

private theorem regular_rate_gives_quadratic_growth
    (a : ℕ → ℕ) (l : ℝ) (hl : 1 < l)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ l *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + l / (n : ℝ))))
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1) := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ l) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ l)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hbase
  have herr : Tendsto (fun n : ℕ =>
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + l / (n : ℝ)))
      atTop (nhds 0) := by
    have hprod := hrate.mul hinv
    simp only [mul_zero] at hprod
    apply hprod.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hpow : (n : ℝ) ^ l ≠ 0 :=
      (Real.rpow_pos_of_pos (by exact_mod_cast hn) l).ne'
    field_simp [hpow]
  have hinvN : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hmodel : Tendsto (fun n : ℕ => 1 + l / (n : ℝ))
      atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := l)).mul hinvN)
  have hq : Tendsto (fun n : ℕ => (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))
      atTop (nhds 1) := by
    convert herr.add hmodel using 1 <;> ring
  simpa only [inv_div, inv_one] using hq.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

private theorem rpow_over_denominator_tendsto_zero
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n) (l : ℝ)
    (hl : 0 ≤ l)
    (hgrowth : Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ l / (a n : ℝ)) atTop (nhds 0) := by
  let u : ℕ → ℝ := fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ l / (a n : ℝ)
  have hu : ∀ n, 0 < u n := by
    intro n
    exact div_pos (Real.rpow_pos_of_pos (by positivity) _)
      (by exact_mod_cast hpos n)
  have hnlarge : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (shift_tendsto_atTop 1)
  have hninv := tendsto_inv_atTop_zero.comp hnlarge
  have hlinear : Tendsto
      (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    have hh : Tendsto (fun n : ℕ => 1 + ((n + 1 : ℕ) : ℝ)⁻¹)
        atTop (nhds 1) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).add hninv
    apply hh.congr'
    filter_upwards [] with n
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hn]
    ring
  have hrecip := reciprocal_successive_ratio_tendsto_zero a ha hpos hgrowth
  have hratio : Tendsto (fun n : ℕ => u (n + 1) / u n) atTop (nhds 0) := by
    have hrpow : Tendsto
        (fun n : ℕ => (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) ^ l)
        atTop (nhds 1) := by
      simpa using hlinear.rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
    have hz := hrpow.mul hrecip
    simp only [one_mul] at hz
    apply hz.congr'
    filter_upwards [] with n
    have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hp : ((n + 1 : ℕ) : ℝ) ^ l ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) l).ne'
    dsimp [u]
    rw [Real.div_rpow (by positivity) (by positivity) l]
    field_simp [h0, h1, hn, hp]
  have huSummable : Summable u := by
    apply summable_of_ratio_test_tendsto_lt_one (by norm_num : (0 : ℝ) < 1)
    · exact Filter.Eventually.of_forall fun n => (hu n).ne'
    · apply hratio.congr'
      exact Filter.Eventually.of_forall fun n => by
        simp only [Real.norm_eq_abs, abs_of_pos (hu (n + 1)), abs_of_pos (hu n)]
  have hu0 := huSummable.tendsto_atTop_zero
  apply squeeze_zero
    (fun n : ℕ => div_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)) _ hu0
  intro n
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_succ n) hl

private theorem summable_reciprocal_of_quadratic_growth
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    Summable (fun n : ℕ => 1 / (a n : ℝ)) := by
  have hr := reciprocal_successive_ratio_tendsto_zero a ha hpos hgrowth
  apply summable_of_ratio_test_tendsto_lt_one (by norm_num : (0 : ℝ) < 1)
  · exact Filter.Eventually.of_forall fun n => by
      have han : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
      simp [han]
  · apply hr.congr'
    exact Filter.Eventually.of_forall fun n => by
      have hn : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast hpos n
      have hn1 : (0 : ℝ) < (a (n + 1) : ℝ) := by exact_mod_cast hpos (n + 1)
      simp only [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn),
        abs_of_pos (one_div_pos.mpr hn1)]

private theorem canonical_numerator_rate_error
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q) (l : ℝ) (hl : 1 < l)
    (hs : HasSum (fun n : ℕ => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ l *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + l / (n : ℝ))))
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ l * rateError l
      (fun j => (canonicalNaturalNumerator a p q j : ℝ)) n)
      atTop (nhds 0) := by
  let C := canonicalNaturalNumerator a p q
  have hgrowth := regular_rate_gives_quadratic_growth a l hl hrate
  obtain ⟨N, hN⟩ :=
    (canonical_tail_ratio_quantitative a ha hpos p q hq hs hgrowth).1
  have hpoly := rpow_over_denominator_tendsto_zero a ha hpos l (by linarith) hgrowth
  have hupper : Tendsto (fun n : ℕ =>
      16 * ((n : ℝ) ^ l / (a n : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hpoly.const_mul 16
  have htail : Tendsto (fun n : ℕ => (n : ℝ) ^ l *
      ((C (n + 1) : ℝ) / (C n : ℝ) -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero'
      (g := fun n : ℕ => 16 * ((n : ℝ) ^ l / (a n : ℝ)))
    · filter_upwards [] with n
      exact abs_nonneg _
    · filter_upwards [eventually_ge_atTop N] with n hn
      simp only [Function.comp_apply]
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      have hh := mul_le_mul_of_nonneg_left (hN n hn)
        (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) l)
      calc
        (n : ℝ) ^ l *
            |(C (n + 1) : ℝ) / (C n : ℝ) -
              (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)|
            ≤ (n : ℝ) ^ l * (16 / (a n : ℝ)) := hh
        _ = 16 * ((n : ℝ) ^ l / (a n : ℝ)) := by ring
    · exact hupper
  have hsum := htail.add hrate
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [] with n
  simp only [rateError, C]
  ring

/-- A nonintegral regular-rate coefficient above one excludes a rational
reciprocal sum for a zero-indexed positive strictly increasing sequence.
The asymptotic is evaluated at the original index; a one-based finite-prefix
bridge is a separate statement. -/
private theorem nonintegral_regular_rate_irrational_of_hasSum
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (l : ℝ) (hl : 1 < l) (hnonint : ∀ d : ℕ, l ≠ (d : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ l *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + l / (n : ℝ))))
      atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv) :
    Irrational Sv := by
  rintro ⟨q, hq⟩
  have hS' : HasSum (fun n : ℕ => 1 / (a n : ℝ)) ((q.num : ℝ) / (q.den : ℝ)) := by
    rw [show ((q.num : ℝ) / (q.den : ℝ)) = (q : ℝ) from (Rat.cast_def q).symm, hq]
    exact hS
  have hCpos := (canonical_integer_tail a hpos q.num q.den q.pos hS').1
  have hpos' : ∀ n, 0 < ((canonicalNaturalNumerator a q.num q.den n : ℤ)) := by
    intro n
    exact_mod_cast hCpos n
  have hCrate := canonical_numerator_rate_error a ha hpos q.num q.den q.pos l hl hS' hrate
  obtain ⟨d, _, hld, _⟩ := regular_rate_extraction hl
    (fun n => (canonicalNaturalNumerator a q.num q.den n : ℤ)) hpos'
    (by simpa only [Int.cast_natCast] using hCrate)
  exact hnonint d hld

/-- Irrationality of the reciprocal sum at every nonintegral regular rate
`l > 1`, under the sharp `o(n⁻ˡ)` ratio remainder. The summability of the
reciprocal sequence is derived from the rate and strict increase. -/
theorem nonintegral_regular_rate_irrational
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (l : ℝ) (hl : 1 < l) (hnonint : ∀ d : ℕ, l ≠ (d : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ l *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + l / (n : ℝ))))
      atTop (nhds 0)) :
    Irrational (∑' n : ℕ, 1 / (a n : ℝ)) := by
  have hgrowth := regular_rate_gives_quadratic_growth a l hl hrate
  have hs := summable_reciprocal_of_quadratic_growth a ha hpos hgrowth
  exact nonintegral_regular_rate_irrational_of_hasSum a ha hpos l hl hnonint
    hrate _ hs.hasSum

#print axioms nonintegral_regular_rate_irrational

end ErdosProblems.Erdos243.PaperCompleteR21
