import ErdosProblems.Erdos243.PaperCompleteR11.CanonicalRecords
import ErdosProblems.Erdos243.PaperCompleteR7.QuantitativeTail
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The canonical weighted growth-defect criterion


This module supplies the previously missing `weightedgrowth` endpoint, not
merely a comparison conditional on a growth-budget supplier.  The error
budget is proved from the actual canonical reciprocal tail by the ratio
test: `(Cₙ₊₁/aₙ₊₁)/(Cₙ/aₙ) → 0`.  No subexponential estimate for C and no
unproved summability hypothesis are used.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Filter PaperCompleteR7 PaperCompleteR9
open scoped BigOperators Topology

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Positive-part truncation is nonexpansive, including both zero cases. -/
theorem positivePart_lipschitz (x y : ℝ) :
    |max x 0 - max y 0| ≤ |x - y| := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · simp only [max_eq_left hx, max_eq_left hy, le_refl]
  · rw [max_eq_left hx, max_eq_right hy, sub_zero, abs_of_nonneg hx,
      abs_of_nonneg (by linarith : 0 ≤ x - y)]
    linarith
  · rw [max_eq_right hx, max_eq_left hy, zero_sub, abs_neg, abs_of_nonneg hy,
      abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · simp only [max_eq_right hx, max_eq_right hy, sub_self, abs_zero, abs_nonneg]

/-- The paper's `U f(U) (γ-B/U)₊` is exactly a scaled positive part. -/
theorem scaled_positivePart (u w γ B : ℝ) (hu : 0 < u) :
    u * w * max (γ - B / u) 0 = max (u * γ - B) 0 * w := by
  have hu0 := hu.ne'
  have hid : u * (γ - B / u) = u * γ - B := by
    field_simp [hu0]
    <;> ring
  by_cases h : 0 ≤ γ - B / u
  · have hz : 0 ≤ u * γ - B := by rw [← hid]; exact mul_nonneg hu.le h
    rw [max_eq_left h, max_eq_left hz, ← hid]
    ring
  · have h' : γ - B / u ≤ 0 := le_of_not_ge h
    have hz : u * γ - B ≤ 0 := by rw [← hid]; exact mul_nonpos_of_nonneg_of_nonpos hu.le h'
    rw [max_eq_right h', max_eq_right hz]
    ring

/-- A pointwise comparison of the exact two printed summands. -/
theorem growth_charge_discrepancy
    (u v γ B w ε : ℝ) (hu : 0 < u) (hw : 0 ≤ w)
    (herror : |γ + v / u| ≤ ε) :
    |u * w * max (γ - B / u) 0 - max (-v - B) 0 * w| ≤ ε * u * w := by
  rw [scaled_positivePart u w γ B hu, ← sub_mul, abs_mul, abs_of_nonneg hw]
  have hscale : |(u * γ - B) - (-v - B)| = u * |γ + v / u| := by
    calc
      |(u * γ - B) - (-v - B)| = |u * (γ + v / u)| := by
        congr 1
        field_simp [hu.ne']
        <;> ring
      _ = u * |γ + v / u| := by rw [abs_mul, abs_of_pos hu]
  calc
    |max (u * γ - B) 0 - max (-v - B) 0| * w ≤
        |(u * γ - B) - (-v - B)| * w :=
      mul_le_mul_of_nonneg_right (positivePart_lipschitz _ _) hw
    _ = (u * |γ + v / u|) * w := by rw [hscale]
    _ ≤ (u * ε) * w :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left herror hu.le) hw
    _ = ε * u * w := by ring

/-- Masked sum on precisely the global strict record indices. -/
noncomputable def paperGrowthCharge (a U : ℕ → ℕ) (B : ℕ)
    (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  if IsStrictRecord U n then
    (U n : ℝ) * f (U n : ℝ) *
      max ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 - (B : ℝ) / (U n : ℝ)) 0
  else 0

theorem paperGrowthCharge_nonneg (a U : ℕ → ℕ) (B : ℕ) (f : ℝ → ℝ)
    (hU : ∀ n, 0 < U n) (hf : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (n : ℕ) :
    0 ≤ paperGrowthCharge a U B f n := by
  have hw : 0 ≤ f (U n : ℝ) := hf _ (by exact_mod_cast (Nat.succ_le_of_lt (hU n)))
  unfold paperGrowthCharge
  split_ifs <;> positivity

theorem paperRecordCharge_nonneg (U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ)
    (f : ℝ → ℝ) (hU : ∀ n, 0 < U n)
    (hf : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (n : ℕ) :
    0 ≤ paperRecordCharge U V B f n := by
  have hw : 0 ≤ f (U n : ℝ) := hf _ (by exact_mod_cast (Nat.succ_le_of_lt (hU n)))
  unfold paperRecordCharge
  split_ifs <;> positivity

/-- The real-tail quotient is the canonical integer-numerator quotient. -/
theorem canonical_numerator_ratio_eq
    (a : ℕ → ℕ) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    (canonicalNaturalNumerator a p q (n + 1) : ℝ) /
        (canonicalNaturalNumerator a p q n : ℝ) =
      (a n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) /
        realTail (fun k ↦ 1 / (a k : ℝ)) n := by
  obtain ⟨hC, hD, _hnum, hden, hrep⟩ := canonical_integer_tail a hapos p q hq hs
  have hd0 : (canonicalDenominator a q n : ℝ) ≠ 0 := by exact_mod_cast (hD n).ne'
  have ht0 : realTail (fun k ↦ 1 / (a k : ℝ)) n ≠ 0 :=
    (realTail_pos _ hs.summable
      (fun k ↦ one_div_pos.mpr (by exact_mod_cast hapos k)) n).ne'
  rw [hrep (n + 1), hrep n, hden n, Nat.cast_mul]
  field_simp [hd0, ht0]
  <;> ring

/-- A complete supplier for the comparison-error series.  It is obtained
from the actual rational sum, not assumed as a growth-debt hypothesis. -/
theorem canonical_numerator_div_digit_summable
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    Summable (fun n ↦ (canonicalNaturalNumerator a p q n : ℝ) / (a n : ℝ)) := by
  let C := canonicalNaturalNumerator a p q
  have hCpos : ∀ n, 0 < C n := (canonical_integer_tail a hapos p q hq hs).1
  have haposR : ∀ n, (0 : ℝ) < (a n : ℝ) := fun n ↦ by exact_mod_cast hapos n
  have hCposR : ∀ n, (0 : ℝ) < (C n : ℝ) := fun n ↦ by exact_mod_cast hCpos n
  have hCr : Tendsto (fun n ↦ (C (n + 1) : ℝ) / (C n : ℝ)) atTop (𝓝 1) := by
    have h := scaled_reciprocal_tail_ratio_tendsto_one a ha hapos hs.summable hgrowth
    apply h.congr'
    exact Eventually.of_forall fun n ↦ (canonical_numerator_ratio_eq a hapos p q hq hs n).symm
  have har : Tendsto (fun n ↦ (a n : ℝ) / (a (n + 1) : ℝ)) atTop (𝓝 0) := by
    have h := reciprocal_successive_ratio_tendsto_zero a ha hapos hgrowth
    apply h.congr'
    exact Eventually.of_forall fun n ↦ by
      field_simp [(haposR n).ne', (haposR (n + 1)).ne']
  have hratio : Tendsto
      (fun n ↦ ‖(C (n + 1) : ℝ) / (a (n + 1) : ℝ)‖ /
        ‖(C n : ℝ) / (a n : ℝ)‖) atTop (𝓝 0) := by
    have h : Tendsto
        (fun n ↦ ((C (n + 1) : ℝ) / (C n : ℝ)) *
          ((a n : ℝ) / (a (n + 1) : ℝ))) atTop (𝓝 0) := by
      simpa only [mul_zero] using hCr.mul har
    apply h.congr'
    exact Eventually.of_forall fun n ↦ by
      simp only [Real.norm_eq_abs,
        abs_of_pos (div_pos (hCposR (n + 1)) (haposR (n + 1))),
        abs_of_pos (div_pos (hCposR n) (haposR n))]
      field_simp [(hCposR n).ne', (haposR n).ne', (haposR (n + 1)).ne']
      <;> ring
  exact summable_of_ratio_test_tendsto_lt_one (by norm_num : (0 : ℝ) < 1)
    (Eventually.of_forall fun n ↦ (div_pos (hCposR n) (haposR n)).ne') hratio

/-- The exact product/LCM scale identities, including the domination U ≤ C. -/
theorem canonical_lcm_scale_data
    (a : ℕ → ℕ) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let U := canonicalLcmNumerator a p q
    let V := canonicalLcmDigit a p q
    let M := cumulativeOverlapDebt q a
    (∀ n, M n * U n = C n) ∧
    (∀ n, (M n : ℤ) * V n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) ∧
    (∀ n, U n ≤ C n) := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let U := canonicalLcmNumerator a p q
  let V := canonicalLcmDigit a p q
  let M := cumulativeOverlapDebt q a
  obtain ⟨_hC, _hD, hnum, _hden, _hrep⟩ := canonical_integer_tail a hapos p q hq hs
  have hDscale : ∀ n, D n = digitProductScale q a n :=
    fun n ↦ (productScale_eq_canonicalDenominator q a n).symm
  have hu : ∀ n, M n * U n = C n := lcmLiftedNumerator_spec q a C D hDscale hnum
  have hv : ∀ n, (M n : ℤ) * V n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ) :=
    lcmLiftedDigit_mul_overlapDebt q a C D hDscale hnum
  refine ⟨hu, hv, ?_⟩
  intro n
  have hM : 1 ≤ M n := Nat.succ_le_of_lt (cumulativeOverlapDebt_pos hq hapos n)
  calc
    U n = 1 * U n := (one_mul _).symm
    _ ≤ M n * U n := Nat.mul_le_mul_right (U n) hM
    _ = C n := hu n

/-- Quantitative comparison with constant 16 in the canonical LCM
coordinates.  This is valid at all sufficiently late indices, not only
fresh steps or record indices. -/
theorem canonical_growth_error_bound
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      |(a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 +
        (canonicalLcmDigit a p q n : ℝ) / (canonicalLcmNumerator a p q n : ℝ)|
        ≤ 16 / (a n : ℝ) := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let U := canonicalLcmNumerator a p q
  let V := canonicalLcmDigit a p q
  let M := cumulativeOverlapDebt q a
  obtain ⟨hC, _hD, hnum, _hden, _hrep⟩ := canonical_integer_tail a hapos p q hq hs
  obtain ⟨hMU, hMV, _hUC⟩ := canonical_lcm_scale_data a hapos p q hq hs
  have hU : ∀ n, 0 < U n := (canonical_lcm_data a ha hapos p q hq hs hgrowth).1
  obtain ⟨N, hN⟩ := quantitative_reciprocal_tail_ratio a ha hapos hs.summable hgrowth
  refine ⟨N, fun n hn ↦ ?_⟩
  have hM0 : (M n : ℝ) ≠ 0 := by exact_mod_cast (cumulativeOverlapDebt_pos hq hapos n).ne'
  have hU0 : (U n : ℝ) ≠ 0 := by exact_mod_cast (hU n).ne'
  have hu : (M n : ℝ) * (U n : ℝ) = (C n : ℝ) := by exact_mod_cast hMU n
  have hv : (M n : ℝ) * (V n : ℝ) =
      (centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ) : ℝ) := by exact_mod_cast hMV n
  have hnext : (C (n + 1) : ℝ) = (C n : ℝ) -
      (centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ) : ℝ) := by
    have hnR : (C (n + 1) : ℝ) + (D n : ℝ) = (a n : ℝ) * (C n : ℝ) := by
      exact_mod_cast hnum n
    unfold centeredState
    push_cast
    nlinarith
  have hratio : (C (n + 1) : ℝ) / (C n : ℝ) = 1 - (V n : ℝ) / (U n : ℝ) := by
    rw [hnext, ← hu, ← hv]
    field_simp [hM0, hU0]
    <;> ring
  have hqbound := hN n hn
  rw [← canonical_numerator_ratio_eq a hapos p q hq hs n] at hqbound
  change |(C (n + 1) : ℝ) / (C n : ℝ) -
    (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| ≤ _ at hqbound
  rw [hratio] at hqbound
  calc
    |(a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 + (V n : ℝ) / (U n : ℝ)| =
      |-(1 - (V n : ℝ) / (U n : ℝ) - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))| := by
        congr 1
        ring
    _ = |1 - (V n : ℝ) / (U n : ℝ) - (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| := abs_neg _
    _ ≤ 16 / (a n : ℝ) := hqbound

/-- Eventual absolutely summable error preserves summability of the two
nonnegative series.  The finite prefix is treated explicitly. -/
theorem summable_iff_of_nonnegative_discrepancy
    (F G e : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) (hG : ∀ n, 0 ≤ G n)
    (he : ∀ n, 0 ≤ e n) (hse : Summable e)
    (hbound : ∃ N : ℕ, ∀ n, N ≤ n → |F n - G n| ≤ e n) :
    Summable F ↔ Summable G := by
  obtain ⟨N, hN⟩ := hbound
  constructor
  · intro hs
    apply summable_of_nonneg_of_eventual_le G (fun n ↦ F n + e n) hG
      (fun n ↦ add_nonneg (hF n) (he n)) (hs.add hse)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hh := (abs_le.mp (hN n hn)).1
    linarith
  · intro hs
    apply summable_of_nonneg_of_eventual_le F (fun n ↦ G n + e n) hF
      (fun n ↦ add_nonneg (hG n) (he n)) (hs.add hse)
    refine ⟨N, fun n hn ↦ ?_⟩
    have hh := (abs_le.mp (hN n hn)).2
    linarith

/-- Exact weighted-growth / weighted-record equivalence for each baseline.
The entire summable majorant is manufactured inside this theorem. -/
theorem canonical_weighted_growth_iff_record
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1))
    (B : ℕ) (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) :
    Summable (paperGrowthCharge a (canonicalLcmNumerator a p q) B f) ↔
      Summable (paperRecordCharge (canonicalLcmNumerator a p q)
        (canonicalLcmDigit a p q) B f) := by
  let C := canonicalNaturalNumerator a p q
  let U := canonicalLcmNumerator a p q
  let V := canonicalLcmDigit a p q
  let e : ℕ → ℝ := fun n ↦ (16 * f 1) * ((C n : ℝ) / (a n : ℝ))
  have hU := (canonical_lcm_data a ha hapos p q hq hs hgrowth).1
  have hUC := (canonical_lcm_scale_data a hapos p q hq hs).2.2
  have hf1 : 0 ≤ f 1 := hpos 1 le_rfl
  have he : ∀ n, 0 ≤ e n := fun n ↦ by dsimp [e]; positivity
  have hse : Summable e :=
    (canonical_numerator_div_digit_summable a ha hapos p q hq hs hgrowth).mul_left (16 * f 1)
  apply summable_iff_of_nonnegative_discrepancy _ _ e
    (paperGrowthCharge_nonneg a U B f hU hpos)
    (paperRecordCharge_nonneg U V B f hU hpos) he hse
  obtain ⟨N, hN⟩ := canonical_growth_error_bound a ha hapos p q hq hs hgrowth
  refine ⟨N, fun n hn ↦ ?_⟩
  have hu : (0 : ℝ) < (U n : ℝ) := by exact_mod_cast hU n
  have hu1 : (1 : ℝ) ≤ (U n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (hU n))
  have hw : 0 ≤ f (U n : ℝ) := hpos _ hu1
  have hw1 : f (U n : ℝ) ≤ f 1 := hf (by simp) hu1 hu1
  have huc : (U n : ℝ) ≤ (C n : ℝ) := by exact_mod_cast hUC n
  have haR : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast hapos n
  have hmax : ((max (-V n - (B : ℤ)) 0 : ℤ) : ℝ) =
      max (-(V n : ℝ) - (B : ℝ)) 0 := by push_cast; rfl
  by_cases hr : IsStrictRecord U n
  · simp only [paperGrowthCharge, paperRecordCharge, if_pos hr, hmax]
    calc
      _ ≤ (16 / (a n : ℝ)) * (U n : ℝ) * f (U n : ℝ) :=
        growth_charge_discrepancy (U n : ℝ) (V n : ℝ)
          ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) (B : ℝ)
          (f (U n : ℝ)) (16 / (a n : ℝ)) hu hw (hN n hn)
      _ ≤ (16 / (a n : ℝ)) * (C n : ℝ) * f 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left huc (by positivity)
        · exact hw1
        · exact hw
        · positivity
      _ = e n := by dsimp [e]; ring
  · simp only [paperGrowthCharge, paperRecordCharge, if_neg hr, sub_self, abs_zero]
    exact he n

/-- **The exact canonical weighted-growth paper endpoint.**
No extra convergence, growth-budget, record supply or state-realisation
hypothesis is introduced.  An initial digit equal to one is allowed. -/
theorem canonical_weighted_growth_excess
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : IntegralUnbounded f) :
    (∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1) ↔
      ∃ B : ℕ, Summable (paperGrowthCharge a (canonicalLcmNumerator a p q) B f) := by
  rw [canonical_weighted_record_excess a ha hapos p q hq hs hgrowth f hf hpos hdiv]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, (canonical_weighted_growth_iff_record a ha hapos p q hq hs hgrowth B f hf hpos).2 hB⟩
  · rintro ⟨B, hB⟩
    exact ⟨B, (canonical_weighted_growth_iff_record a ha hapos p q hq hs hgrowth B f hf hpos).1 hB⟩

end ErdosProblems.Erdos243.PaperCompleteR11
