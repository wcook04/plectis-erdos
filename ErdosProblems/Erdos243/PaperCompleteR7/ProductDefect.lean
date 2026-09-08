import ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState

/-!
# The original-coordinate bounded-product-defect corollary

Uncompiled candidates.  This module supplies the analytic error dictionary
rather than assuming bounded centred error.  Finite upper limsup is stated
as eventual boundedness above by a real constant; the finite initial
segment is irrelevant.  Rationality is given by p/q and HasSum.

The proof avoids assuming a pre-existing double-exponential estimate:
P_n/a_n^2 tends to zero by its successive-ratio identity.  This suffices
for the exact two-term error dictionary.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators

noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)

/-- A positive sequence with successive ratio zero tends to zero.
The shift and the geometric majorant are proved explicitly. -/
theorem positive_sequence_zero_of_ratio_zero
    (u : ℕ → ℝ) (hu : ∀ n, 0 < u n)
    (hratio : Tendsto (fun n ↦ u (n + 1) / u n) atTop (nhds 0)) :
    Tendsto u atTop (nhds 0) := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hratio (1 / 2) (by norm_num)
  have hstep : ∀ n, N ≤ n → u (n + 1) ≤ (1 / 2) * u n := by
    intro n hn
    have hnonneg : 0 ≤ u (n + 1) / u n := div_nonneg (hu _).le (hu _).le
    have hh : u (n + 1) / u n < 1 / 2 := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hN n hn
    exact (div_le_iff₀ (hu n)).mp hh.le
  have hbound : ∀ k : ℕ, u (k + N) ≤ (1 / 2 : ℝ) ^ k * u N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          u (k + 1 + N) = u (k + N + 1) := by congr 1 <;> omega
          _ ≤ (1 / 2) * u (k + N) := hstep _ (by omega)
          _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ k * u N) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (k + 1) * u N := by rw [pow_succ]; ring
  have hgeom : Tendsto (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k * u N) atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (u N)
  have hshift : Tendsto (fun k : ℕ ↦ u (k + N)) atTop (nhds 0) :=
    squeeze_zero (fun k ↦ (hu (k + N)).le) hbound hgeom
  exact (Filter.tendsto_add_atTop_iff_nat N).mp hshift

/-- The scale needed for the bounded-defect transfer.  No polynomial or
exponential rate is assumed for the product. -/
theorem prefix_over_square_tendsto_zero
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    Tendsto (fun n ↦ (prefixProduct a n : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 0) := by
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
  apply positive_sequence_zero_of_ratio_zero u hu
  apply hlim'.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
    have hP : (prefixProduct a n : ℝ) ≠ 0 :=
      by exact_mod_cast (prefixProduct_pos a hpos n).ne'
    dsimp [u]
    rw [prefixProduct_succ, Nat.cast_mul]
    field_simp [h0, h1, hP]
    <;> ring

/-- Exact two-term algebra behind E_n + q Q_n, before limiting. -/
theorem two_term_defect_identity
    (a aNext P q x x2 : ℝ) (ha : a ≠ 0) (haNext : aNext ≠ 0)
    (hx : x = 1 / a + 1 / aNext + x2) :
    q * P - (a - 1) * (q * P * x) + q * (P / a * (a ^ 2 / aNext - 1)) =
      q * (P / aNext - P * (a - 1) * x2) := by
  rw [hx]
  field_simp [ha, haNext]
  <;> ring

/-- Complete error dictionary for the actual canonical integer state.
Unlike the sharper printed O(1/a_n) statement, this conclusion suffices
for the product-prefactor bounded-defect corollary. -/
theorem canonical_error_plus_productDefect_tendsto_zero
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hqpos : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    Tendsto (fun n ↦ (E n : ℝ) + (q : ℝ) * productDefect a n)
      atTop (nhds 0) := by
  let t : ℕ → ℝ := fun n ↦ 1 / (a n : ℝ)
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  obtain ⟨hcpos, hdpos, hc, hd, hrep⟩ := canonical_integer_tail a hpos p q hqpos hs
  have hinv : Tendsto (fun n ↦ (a n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (strictMono_nat_cast_tendsto_atTop a ha hpos)
  have hq : Tendsto (fun n ↦ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))
      atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using hgrowth.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hqnext := hq.comp (shift_tendsto_atTop 1)
  have hscale := prefix_over_square_tendsto_zero a ha hpos hgrowth
  have hsmall := reciprocal_successive_ratio_tendsto_zero a ha hpos hgrowth
  have hfirst : Tendsto (fun n ↦ (prefixProduct a n : ℝ) / (a (n + 1) : ℝ))
      atTop (nhds 0) := by
    have hz := hscale.mul hq
    have hz' : Tendsto (fun n ↦
        ((prefixProduct a n : ℝ) / (a n : ℝ) ^ 2) *
          ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ))) atTop (nhds 0) := by
      simpa only [zero_mul] using hz
    apply hz'.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
      have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
      field_simp [h0, h1]
      <;> ring
  have hprod : Tendsto (fun n ↦
      (prefixProduct a n : ℝ) * (a n : ℝ) / (a (n + 2) : ℝ))
      atTop (nhds 0) := by
    have hz := ((hscale.mul hq).mul hqnext).mul hsmall
    have hz' : Tendsto (fun n ↦
        (((prefixProduct a n : ℝ) / (a n : ℝ) ^ 2) *
          ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ))) *
          ((a (n + 1) : ℝ) ^ 2 / (a (n + 2) : ℝ)) *
          ((1 / (a (n + 1) : ℝ)) / (1 / (a n : ℝ))))
        atTop (nhds 0) := by
      simpa only [zero_mul, Function.comp_apply, Nat.add_assoc] using hz
    apply hz'.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
      have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
      have h2 : (a (n + 2) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 2)).ne'
      field_simp [h0, h1, h2]
      <;> ring
  have hrel : Tendsto (fun n ↦ (a n : ℝ) * realTail t n) atTop (nhds 1) := by
    have hh := realTail_div_term_tendsto_one t hs.summable
      (fun n ↦ one_div_pos.mpr (by exact_mod_cast hpos n)) hsmall
    simpa only [t, one_div, div_inv_eq_mul, mul_comm] using hh
  have hsecond : Tendsto (fun n ↦
      (prefixProduct a n : ℝ) * ((a n : ℝ) - 1) * realTail t (n + 2))
      atTop (nhds 0) := by
    have hfactor : Tendsto (fun n ↦ 1 - (a n : ℝ)⁻¹) atTop (nhds 1) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
    have hz := (hprod.mul hfactor).mul (hrel.comp (shift_tendsto_atTop 2))
    have hz' : Tendsto (fun n ↦
        ((prefixProduct a n : ℝ) * (a n : ℝ) / (a (n + 2) : ℝ)) *
          (1 - (a n : ℝ)⁻¹) * ((a (n + 2) : ℝ) * realTail t (n + 2)))
        atTop (nhds 0) := by
      simpa only [zero_mul, Function.comp_apply] using hz
    apply hz'.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
      have h2 : (a (n + 2) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 2)).ne'
      field_simp [h0, h2]
      <;> ring
  have hdict : ∀ n, (E n : ℝ) + (q : ℝ) * productDefect a n =
      (q : ℝ) * ((prefixProduct a n : ℝ) / (a (n + 1) : ℝ) -
        (prefixProduct a n : ℝ) * ((a n : ℝ) - 1) * realTail t (n + 2)) := by
    intro n
    have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
    have htail : realTail t n = 1 / (a n : ℝ) + 1 / (a (n + 1) : ℝ) +
        realTail t (n + 2) := by
      rw [realTail_step t hs.summable n, realTail_step t hs.summable (n + 1)]
      simp only [t, Nat.add_assoc]
      ring
    have hecast : (E n : ℝ) = (D n : ℝ) - ((a n : ℝ) - 1) * (C n : ℝ) := by
      simp [E, centeredState]
    rw [hecast, hrep n]
    simp only [D, canonicalDenominator, Nat.cast_mul]
    exact two_term_defect_identity (a n : ℝ) (a (n + 1) : ℝ)
      (prefixProduct a n : ℝ) (q : ℝ) (realTail t n) (realTail t (n + 2))
      h0 h1 htail
  have hz := (tendsto_const_nhds (x := (q : ℝ))).mul (hfirst.sub hsecond)
  have hz' : Tendsto (fun n ↦ (q : ℝ) *
      ((prefixProduct a n : ℝ) / (a (n + 1) : ℝ) -
       (prefixProduct a n : ℝ) * ((a n : ℝ) - 1) * realTail t (n + 2)))
      atTop (nhds 0) := by simpa only [sub_self, mul_zero] using hz
  apply hz'.congr'
  exact Filter.Eventually.of_forall fun n ↦ (hdict n).symm

/-- Short note `res:originalbounded`, with the rational value represented
by p/q and the finite upper limsup represented by eventual boundedness.
This is an end-to-end source candidate: the integer state, analytic
hypotheses and bounded negative error are all derived, not assumed. -/
theorem original_coordinate_bounded_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hupper : ∃ M : ℝ, ∃ N, ∀ n, N ≤ n → productDefect a n ≤ M) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  obtain ⟨hcpos, hdpos, hc, hd, hrep, hv, _⟩ :=
    canonical_integer_tail_normalized a ha hpos p q hq hs hgrowth
  have herror := canonical_error_plus_productDefect_tendsto_zero a ha hpos p q hq hs hgrowth
  obtain ⟨M, Nq, hNq⟩ := hupper
  obtain ⟨Ne, hNe⟩ := Metric.tendsto_atTop.mp herror 1 (by norm_num)
  obtain ⟨B, hB⟩ := exists_nat_gt (1 + (q : ℝ) * M)
  have hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n := by
    refine ⟨max Nq Ne, B, fun n hn ↦ ?_⟩
    have habs : |(E n : ℝ) + (q : ℝ) * productDefect a n| < 1 := by
      simpa only [Real.dist_eq, sub_zero] using
        hNe n ((Nat.le_max_right Nq Ne).trans hn)
    have hlow := (abs_lt.mp habs).1
    have hproduct : (q : ℝ) * productDefect a n ≤ (q : ℝ) * M :=
      mul_le_mul_of_nonneg_left (hNq n ((Nat.le_max_left Nq Ne).trans hn))
        (by positivity)
    have hb : -(B : ℝ) ≤ (E n : ℝ) := by linarith
    exact_mod_cast hb
  have hlarge : ∃ N, ∀ n, N ≤ n → 1 < a n := by
    refine ⟨1, fun n hn ↦ ?_⟩
    have h01 := ha (by omega : (0 : ℕ) < 1)
    have h0 := hpos 0
    have h1n := ha.monotone hn
    omega
  simpa only [sylvesterNext] using bounded_negative_endpoint_eventual_multiplier
    a C D E hlarge hcpos hc hd (fun _ ↦ rfl) hbound hv

end ErdosProblems.Erdos243.PaperCompleteR7
