import ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect
import ErdosProblems.Erdos243.PaperCompleteR7.QuantitativeTail
import ErdosProblems.Erdos243.IntegerRoundingBarrier

/-!
# The original-variable strict 1/n threshold

Uncompiled end-to-end candidate for long-record `res:onethreshold`.
The strict limsup bound is expressed by its equivalent eventual bound
c<1.  An integer linear barrier supplies a bounded negative error, after
the quantitative canonical-tail estimate absorbs the exponentially small
error.  No unpublished record-amplified equivalence is used.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter

/-- Quadratic growth makes n/a_n tend to zero; the proof only needs the
already-derived successive reciprocal ratio. -/
theorem linear_over_denominator_tendsto_zero
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / (a n : ℝ)) atTop (nhds 0) := by
  let u : ℕ → ℝ := fun n ↦ ((n + 1 : ℕ) : ℝ) / (a n : ℝ)
  have hu : ∀ n, 0 < u n := by
    intro n
    apply div_pos
    · exact_mod_cast Nat.succ_pos n
    · exact_mod_cast hpos n
  have hnlarge : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (shift_tendsto_atTop 1)
  have hninv := tendsto_inv_atTop_zero.comp hnlarge
  have hfac : Tendsto (fun n : ℕ ↦ ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    have hh : Tendsto (fun n : ℕ ↦ 1 + ((n + 1 : ℕ) : ℝ)⁻¹)
        atTop (nhds 1) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hninv
    apply hh.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      <;> ring
  have hr := reciprocal_successive_ratio_tendsto_zero a ha hpos hgrowth
  have hprod := hfac.mul hr
  have hlim : Tendsto u atTop (nhds 0) := by
    apply positive_sequence_zero_of_ratio_zero u hu
    have hz : Tendsto (fun n ↦
        (((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) *
          ((1 / (a (n + 1) : ℝ)) / (1 / (a n : ℝ)))) atTop (nhds 0) := by
      simpa only [mul_zero] using hprod
    apply hz.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
      have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      dsimp [u]
      field_simp [h0, h1, hn]
      <;> push_cast <;> ring
  apply squeeze_zero (fun n ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hlim
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.le_succ n

/-- The exact linear barrier and its bounded-rise consequence.  Natural
integrality is retained throughout this assembly. -/
theorem linear_barrier_bounded_rises
    (C : ℕ → ℕ) (N : ℕ) (hN : 0 < N)
    (hstep : ∀ n, N ≤ n → n * C (n + 1) ≤ (n + 1) * C n) :
    ∃ B : ℕ, ∀ n, N ≤ n → C (n + 1) ≤ C n + B := by
  refine ⟨C N, ?_⟩
  apply step_rise_le_of_barrier C (fun _ ↦ 0) (C N) N hN
  · intro k hk; exact le_rfl
  · intro k hk; exact le_rfl
  · intro k hk
    have hh := hstep k hk
    have hr : (k : ℝ) * (C (k + 1) : ℝ) ≤
        ((k : ℝ) + 1) * (C k : ℝ) := by exact_mod_cast hh
    simpa only [add_zero] using hr
  · norm_num
  · exact Nat.le_mul_of_pos_right (C N) hN

/-- Full strict 1/n threshold.  The fixed eventual c<1 bound is precisely
the strict upper-limsup hypothesis of the paper, not a pointwise sign or
bounded-error hypothesis imposed on the canonical state. -/
theorem original_coordinate_one_threshold
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hthreshold : ∃ c : ℝ, c < 1 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) * max ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) 0 ≤ c) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  obtain ⟨hcpos, hdpos, hc, hd, hrep, hvanish, _⟩ :=
    canonical_integer_tail_normalized a ha hpos p q hq hs hgrowth
  obtain ⟨c, hc1, N0, hN0⟩ := hthreshold
  obtain ⟨N1, hN1⟩ := (canonical_tail_ratio_quantitative a ha hpos p q hq hs hgrowth).1
  have hnsmall := (linear_over_denominator_tendsto_zero a ha hpos hgrowth).const_mul 16
  have hz : Tendsto (fun n : ℕ ↦ (16 : ℝ) * ((n : ℝ) / (a n : ℝ)))
      atTop (nhds 0) := by simpa only [mul_zero] using hnsmall
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hz (1 - c) (by linarith)
  let N := max 1 (max N0 (max N1 N2))
  have hNpos : 0 < N := by dsimp [N]; omega
  have hlinear : ∀ n, N ≤ n → n * C (n + 1) ≤ (n + 1) * C n := by
    intro n hn
    have hne : N1 ≤ n := by dsimp [N] at hn; omega
    have he := hN1 n hne
    have heupper := (abs_le.mp he).2
    have hγ := hN0 n (by dsimp [N] at hn; omega)
    have hnγ : (n : ℝ) * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) ≤ c := by
      exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg n)).trans hγ
    have hsmall := hN2 n (by dsimp [N] at hn; omega)
    rw [Real.dist_eq, sub_zero] at hsmall
    have hsmall' := (abs_lt.mp hsmall).2
    have heprod := mul_le_mul_of_nonneg_left heupper (Nat.cast_nonneg n)
    have hratio : (n : ℝ) * ((C (n + 1) : ℝ) / (C n : ℝ)) ≤ (n : ℝ) + 1 := by
      have hid : (n : ℝ) * (16 / (a n : ℝ)) = 16 * ((n : ℝ) / (a n : ℝ)) := by ring
      nlinarith [heprod, hnγ, hsmall', hid]
    have hC : (0 : ℝ) < (C n : ℝ) := by exact_mod_cast hcpos n
    have hmul : (n : ℝ) * (C (n + 1) : ℝ) ≤ ((n : ℝ) + 1) * (C n : ℝ) := by
      apply (div_le_iff₀ hC).mp
      simpa only [mul_div_assoc] using hratio
    exact_mod_cast hmul
  obtain ⟨B, hB⟩ := linear_barrier_bounded_rises C N hNpos hlinear
  have hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n := by
    refine ⟨N, B, fun n hn ↦ ?_⟩
    have he := natTail_eq_sub_centeredState a C D E hc (fun _ ↦ rfl) n
    have hb := hB n hn
    omega
  have haevent : ∃ N, ∀ n, N ≤ n → 1 < a n := by
    refine ⟨1, fun n hn ↦ ?_⟩
    have hh := ha (show 0 < n by omega)
    have hp := hpos 0
    omega
  simpa only [sylvesterNext] using bounded_negative_endpoint_eventual_multiplier
    a C D E haevent hcpos hc hd (fun _ ↦ rfl) hbound hvanish

end ErdosProblems.Erdos243.PaperCompleteR7
