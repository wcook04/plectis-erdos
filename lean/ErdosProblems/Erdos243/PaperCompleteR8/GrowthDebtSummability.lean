import ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect
import ErdosProblems.Erdos243.PaperCompleteR8.CanonicalWeightedRecords
import ErdosProblems.Erdos243.PaperCompleteR7.QuantitativeTail
import Mathlib.Analysis.SpecificLimits.Normed

/-! Summable majorant needed for the paper weighted-growth-defect transport.
This strengthens the existing zero-limit result using the same exact ratio
identity; it does not assert that the record-growth budget is finite. -/
namespace ErdosProblems.Erdos243.PaperCompleteR8
open Filter Classical PaperCompleteR7
open scoped Topology

theorem summable_prefix_over_square
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    Summable (fun n ↦ (prefixProduct a n : ℝ) / (a n : ℝ) ^ 2) := by
  let u : ℕ → ℝ := fun n ↦ (prefixProduct a n : ℝ) / (a n : ℝ) ^ 2
  have hu : ∀ n, 0 < u n := by
    intro n
    exact div_pos (by exact_mod_cast prefixProduct_pos a hpos n)
      (pow_pos (by exact_mod_cast hpos n) 2)
  have hinv : Tendsto (fun n ↦ (a n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (strictMono_nat_cast_tendsto_atTop a ha hpos)
  have hq : Tendsto (fun n ↦ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))
      atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using hgrowth.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hlim := (hq.pow 2).mul hinv
  have hlim' : Tendsto (fun n ↦
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) ^ 2 * (a n : ℝ)⁻¹)
      atTop (nhds 0) := by simpa only [one_pow, one_mul] using hlim
  apply summable_of_ratio_test_tendsto_lt_one (by norm_num : (0 : ℝ) < 1)
    (Eventually.of_forall (fun n => (hu n).ne'))
  apply hlim'.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
    have hP : (prefixProduct a n : ℝ) ≠ 0 :=
      by exact_mod_cast (prefixProduct_pos a hpos n).ne'
    simp only [Real.norm_eq_abs, abs_of_pos (hu n), abs_of_pos (hu (n + 1))]
    dsimp [u]
    rw [prefixProduct_succ, Nat.cast_mul]
    field_simp [h0, h1, hP]
    <;> ring


section Canonical
variable (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
  (p : ℤ) (q : ℕ) (hq : 0 < q)
  (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
  (hg : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ)^2) atTop (nhds 1))

include ha hpos hq hs hg

/-- The actual canonical numerator over its denominator is summable. -/
theorem summable_canonical_numerator_over_digit :
    Summable (fun n => (canonicalNaturalNumerator a p q n : ℝ) / (a n : ℝ)) := by
  obtain ⟨hCp, hDp, hC, hD, hrep⟩ := canonical_integer_tail a hpos p q hq hs
  have hsmall := reciprocal_successive_ratio_tendsto_zero a ha hpos hg
  have hrel : Tendsto (fun n => (a n : ℝ) *
      realTail (fun k => 1 / (a k : ℝ)) n) atTop (nhds 1) := by
    have hh := realTail_div_term_tendsto_one _ hs.summable
      (fun n => one_div_pos.mpr (by exact_mod_cast hpos n)) hsmall
    simpa only [one_div, div_inv_eq_mul, mul_comm] using hh
  have hmajor := (summable_prefix_over_square a ha hpos hg).mul_left (2 * (q : ℝ))
  apply hmajor.of_norm_bounded_eventually_nat
  filter_upwards [hrel.eventually_le_const (by norm_num : (1 : ℝ) < 2)] with n hn
  have haR : (0 : ℝ) < a n := by exact_mod_cast hpos n
  have hP : (0 : ℝ) ≤ q * (prefixProduct a n : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) haR.le)]
  rw [hrep n, canonicalDenominator, Nat.cast_mul]
  have hh := mul_le_mul_of_nonneg_left hn hP
  apply (div_le_iff₀ haR).mpr
  have hid : 2 * (q : ℝ) * ((prefixProduct a n : ℝ) / (a n : ℝ)^2) * a n =
      2 * ((q : ℝ) * prefixProduct a n) / a n := by field_simp <;> ring
  rw [hid]
  apply (le_div_iff₀ haR).mpr
  nlinarith

/-- Quantitative growth-defect dictionary on the actual LCM orbit.
The constant16 suffices for summability; no sharper constant is needed. -/
theorem canonical_lcm_growth_error_bound :
    let o := canonicalLcmOrbit a ha hpos p q hq hs hg
    ∀ᶠ n in atTop,
      |(o.U n : ℝ) * ((a n : ℝ)^2 / a (n+1) - 1) + (o.V n : ℝ)| ≤
        16 * (o.U n : ℝ) / a n := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let o := canonicalLcmOrbit a ha hpos p q hq hs hg
  obtain ⟨hCp, hDp, hC, hD, hrep⟩ := canonical_integer_tail a hpos p q hq hs
  have hscale : ∀ n, D n = digitProductScale q a n :=
    fun n => (productScale_eq_canonicalDenominator q a n).symm
  obtain ⟨N, hN⟩ := quantitative_reciprocal_tail_ratio a ha hpos hs.summable hg
  filter_upwards [eventually_ge_atTop N] with n hn
  let T := realTail (fun k => 1 / (a k : ℝ))
  have hT : 0 < T n := realTail_pos _ hs.summable
    (fun k => one_div_pos.mpr (by exact_mod_cast hpos k)) n
  have hDr : (0 : ℝ) < D n := by exact_mod_cast hDp n
  have hCr : (0 : ℝ) < C n := by exact_mod_cast hCp n
  have hM : (0 : ℝ) < cumulativeOverlapDebt q a n := by
    exact_mod_cast cumulativeOverlapDebt_pos hq hpos n
  have hU : (cumulativeOverlapDebt q a n : ℝ) * (o.U n : ℝ) = (C n : ℝ) := by
    exact_mod_cast lcmLiftedNumerator_spec q a C D hscale hC n
  have hV : (cumulativeOverlapDebt q a n : ℝ) * (o.V n : ℝ) =
      (D n : ℝ) - ((a n : ℝ)-1) * C n := by
    have hh := lcmLiftedDigit_mul_overlapDebt q a C D hscale hC n
    change (cumulativeOverlapDebt q a n : ℤ) * o.V n =
      (D n : ℤ) - ((a n : ℤ)-1) * C n at hh
    exact_mod_cast hh
  have hrepR : (C n : ℝ) = D n * T n := hrep n
  have hstep := realTail_step (fun k => 1 / (a k : ℝ)) hs.summable n
  change T n = 1 / (a n : ℝ) + T (n+1) at hstep
  have haR : (0 : ℝ) < a n := by exact_mod_cast hpos n
  have hid : (o.U n : ℝ) * ((a n : ℝ)^2 / a (n+1)-1) + o.V n =
      (o.U n : ℝ) * ((a n : ℝ)^2 / a (n+1) - (a n : ℝ)*T (n+1)/T n) := by
    have hmul : (a n : ℝ) * T n = 1 + (a n : ℝ)*T (n+1) := by
      rw [hstep]
      field_simp
    apply (mul_left_cancel₀ hM.ne')
    rw [mul_add, ← mul_assoc, hU, hV, ← mul_assoc, hU]
    have hratio : (a n : ℝ) * T (n+1) / T n = (a n : ℝ) - 1 / T n := by
      field_simp [hT.ne']
      linarith [hmul]
    rw [hratio, hrepR]
    have hnxt : (a (n+1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n+1)).ne'
    field_simp [hT.ne', hnxt]
    <;> ring
  rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hb := hN n hn
  change |(a n : ℝ)*T (n+1)/T n - (a n : ℝ)^2/a (n+1)| ≤ 16/(a n : ℝ) at hb
  rw [abs_sub_comm] at hb
  have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (o.U n) : (0 : ℝ) ≤ o.U n)
  convert hh using 1 <;> ring

end Canonical

lemma real_natAbs_negative_part (z : ℤ) : (z.toNat : ℝ) = max (z : ℝ) 0 := by
  by_cases hz : 0 ≤ z
  · have hr : (0 : ℝ) ≤ z := by exact_mod_cast hz
    rw [max_eq_left hr]
    exact_mod_cast Int.toNat_of_nonneg hz
  · have hz' : z ≤ 0 := le_of_lt (lt_of_not_ge hz)
    have hr : (z : ℝ) ≤ 0 := by exact_mod_cast hz'
    simp [Int.toNat_eq_zero.mpr hz', max_eq_right hr]

/-- The actual weighted growth budget, indexed only by strict LCM records. -/
noncomputable def growthRecordWeight (a U : ℕ → ℕ) (B : ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  if Record U n then
    max ((U n : ℝ) * ((a n : ℝ)^2 / a (n+1) - 1) - B) 0 * f (U n)
  else 0

section GrowthTransport
variable (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
  (p : ℤ) (q : ℕ) (hq : 0 < q)
  (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
  (hg : Tendsto (fun n => (a (n+1) : ℝ) / (a n : ℝ)^2) atTop (nhds 1))

/-- The weighted debt comparison is summable under the original hypotheses. -/
theorem summable_growth_record_difference (B : ℕ) (f : ℝ → ℝ)
    (hf : AntitoneOn f (Set.Ici 1)) (hfpos : ∀ x, 1 ≤ x → 0 ≤ f x) :
    let o := canonicalLcmOrbit a ha hpos p q hq hs hg
    Summable (fun n => growthRecordWeight a o.U B f n -
      (if Record o.U n then ((-o.V n - B).toNat : ℝ) * f (o.U n) else 0)) := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let o := canonicalLcmOrbit a ha hpos p q hq hs hg
  obtain ⟨hCp, _, hC, _, _⟩ := canonical_integer_tail a hpos p q hq hs
  have hscale : ∀ n, D n = digitProductScale q a n :=
    fun n => (productScale_eq_canonicalDenominator q a n).symm
  have hUC : ∀ n, (o.U n : ℝ) ≤ C n := by
    intro n
    have hh := lcmLiftedNumerator_spec q a C D hscale hC n
    have hM := cumulativeOverlapDebt_pos hq hpos n
    have hh' : o.U n ≤ C n := by
      change cumulativeOverlapDebt q a n * o.U n = C n at hh
      nlinarith
    exact_mod_cast hh'
  have hsum := (summable_canonical_numerator_over_digit a ha hpos p q hq hs hg).mul_left
    (16 * f 1)
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [canonical_lcm_growth_error_bound a ha hpos p q hq hs hg] with n hn
  have hU1 : (1 : ℝ) ≤ o.U n := by exact_mod_cast o.Upos n
  have hfu := hfpos _ hU1
  have hf1 := hfpos 1 (le_refl 1)
  have hfle : f (o.U n) ≤ f 1 := hf (by simp) hU1 hU1
  have haR : (0 : ℝ) < a n := by exact_mod_cast hpos n
  change |growthRecordWeight a o.U B f n -
    (if Record o.U n then ((-o.V n - B).toNat : ℝ) * f (o.U n) else 0)| ≤ _
  unfold growthRecordWeight
  split_ifs with hr
  · rw [real_natAbs_negative_part]
    push_cast
    rw [← sub_mul, abs_mul, abs_of_nonneg hfu]
    have hm := abs_max_sub_max_le_abs
      ((o.U n : ℝ) * ((a n : ℝ)^2 / a (n+1)-1)-B) (-(o.V n : ℝ)-B) 0
    have hm' : |max ((o.U n : ℝ)*((a n : ℝ)^2/a (n+1)-1)-B) 0 -
      max (-(o.V n : ℝ)-B) 0| ≤
      |(o.U n : ℝ)*((a n : ℝ)^2/a (n+1)-1)+(o.V n : ℝ)| := by
      convert hm using 1 <;> congr 1 <;> ring
    calc
      _ ≤ (16 * (o.U n : ℝ) / a n) * f (o.U n) :=
        mul_le_mul_of_nonneg_right (hm'.trans hn) hfu
      _ ≤ (16 * (C n : ℝ) / a n) * f 1 := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hUC n) (by norm_num)) haR.le
        · exact hfle
        · exact hfu
        · positivity
      _ = (16 * f 1) * ((C n : ℝ) / a n) := by ring
  · simp only [sub_self, abs_zero]
    positivity

/-- The paper's weighted growth-defect equivalence, with no extra growth debt premise. -/
theorem canonical_weighted_growth_record
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hfpos : ∀ x, 1 ≤ x → 0 ≤ f x) (hdiv : DivergentIntegral f) :
    let o := canonicalLcmOrbit a ha hpos p q hq hs hg
    (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = sylvesterNext (a n : ℤ)) ↔
      ∃ B : ℕ, Summable (growthRecordWeight a o.U B f) := by
  let o := canonicalLcmOrbit a ha hpos p q hq hs hg
  have hc := canonical_weighted_record a ha hpos p q hq hs hg f hf hfpos hdiv
  change (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = sylvesterNext (a n : ℤ)) ↔ _ at hc
  rw [hc]
  apply exists_congr
  intro B
  have hd := summable_growth_record_difference a ha hpos p q hq hs hg B f hf hfpos
  constructor
  · intro h
    simpa only [sub_add_cancel] using hd.add h
  · intro h
    simpa only [sub_sub_cancel] using h.sub hd

/-- Literal factored summand in equation `eq:weightedgrowth`. -/
theorem canonical_weighted_growth_record_factored
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hfpos : ∀ x, 1 ≤ x → 0 ≤ f x) (hdiv : DivergentIntegral f) :
    let o := canonicalLcmOrbit a ha hpos p q hq hs hg
    (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = sylvesterNext (a n : ℤ)) ↔
      ∃ B : ℕ, Summable (fun n => if Record o.U n then
        (o.U n : ℝ) * f (o.U n) *
          max ((a n : ℝ)^2 / a (n+1) - 1 - B / (o.U n : ℝ)) 0 else 0) := by
  let o := canonicalLcmOrbit a ha hpos p q hq hs hg
  have heq : ∀ B : ℕ, growthRecordWeight a o.U B f =
      fun n => if Record o.U n then (o.U n : ℝ) * f (o.U n) *
        max ((a n : ℝ)^2 / a (n+1) - 1 - B / (o.U n : ℝ)) 0 else 0 := by
    intro B
    funext n
    unfold growthRecordWeight
    split_ifs
    · have hU : (0 : ℝ) < o.U n := by exact_mod_cast o.Upos n
      have hm := mul_max_of_nonneg
        ((a n : ℝ)^2 / a (n+1) - 1 - B / (o.U n : ℝ)) 0 hU.le
      have hid : (o.U n : ℝ) *
          ((a n : ℝ)^2 / a (n+1) - 1 - B / (o.U n : ℝ)) =
          (o.U n : ℝ) * ((a n : ℝ)^2 / a (n+1) - 1) - B := by
        rw [mul_sub, mul_div_cancel₀ _ hU.ne']
      rw [hid, mul_zero] at hm
      rw [← hm]
      ring
    · rfl
  have hh := canonical_weighted_growth_record a ha hpos p q hq hs hg f hf hfpos hdiv
  apply hh.trans
  apply exists_congr
  intro B
  change Summable (growthRecordWeight a o.U B f) ↔ _
  rw [heq B]

end GrowthTransport

end ErdosProblems.Erdos243.PaperCompleteR8
