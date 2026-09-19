import ErdosProblems.Erdos243.PaperCompleteR11.IntegralWeights
import ErdosProblems.Erdos243.PaperCompleteR7.LcmDefect

/-!
# Canonical reciprocal-series weighted records

This module supplies the real-series construction and the converse
from eventual Sylvester recursion. It allows the original first multiplier
to be one. A record series is written as a masked series on ℕ, rather than
as an unordered series on a separate record-index subtype.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Filter PaperCompleteR7 PaperCompleteR9
open scoped BigOperators Topology

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def canonicalLcmNumerator (a : ℕ → ℕ) (p : ℤ) (q : ℕ) : ℕ → ℕ :=
  lcmLiftedNumerator q a (canonicalNaturalNumerator a p q)

noncomputable def canonicalLcmDigit (a : ℕ → ℕ) (p : ℤ) (q : ℕ) : ℕ → ℤ :=
  lcmLiftedDigit q a (canonicalNaturalNumerator a p q)

/-- The paper's raw record term, with the real weight evaluated at U itself. -/
noncomputable def paperRecordCharge (U : ℕ → ℕ) (V : ℕ → ℤ)
    (B : ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  if IsStrictRecord U n then
    ((max (-V n - (B : ℤ)) 0 : ℤ) : ℝ) * f (U n : ℝ)
  else 0

/-- Strict increase and positivity include the initial-one case. -/
theorem strictMono_eventually_ge_two (a : ℕ → ℕ)
    (ha : StrictMono a) (hp : ∀ n, 0 < a n) :
    ∃ N : ℕ, ∀ n, N ≤ n → 2 ≤ a n := by
  refine ⟨1, ?_⟩
  intro n hn
  have h0 := hp 0
  have hh := ha (show 0 < n by omega)
  omega

/-- Construction from the actual rational reciprocal series. In particular,
U=L*x is proved, not imposed as an additional state hypothesis. -/
theorem canonical_lcm_data
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    let U := canonicalLcmNumerator a p q
    let V := canonicalLcmDigit a p q
    (∀ n, 0 < U n) ∧
    (∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) = (U n : ℤ) - V n) ∧
    (∀ n, V n = (cumulativeDigitLcm q a n : ℤ) - ((a n : ℤ) - 1) * U n) ∧
    (∀ n, (U n : ℝ) = (cumulativeDigitLcm q a n : ℝ) *
      realTail (fun k ↦ 1 / (a k : ℝ)) n) ∧
    (∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * (V n).natAbs < U n) := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  let M := cumulativeOverlapDebt q a
  let U := canonicalLcmNumerator a p q
  let V := canonicalLcmDigit a p q
  obtain ⟨hcpos, _hdpos, hc, _hd, hrep, hvanish, _⟩ :=
    canonical_integer_tail_normalized a ha hapos p q hq hs hgrowth
  have hdscale : ∀ n, D n = digitProductScale q a n :=
    fun n ↦ (productScale_eq_canonicalDenominator q a n).symm
  have hMpos : ∀ n, 0 < M n := cumulativeOverlapDebt_pos hq hapos
  have hUeq : ∀ n, M n * U n = C n :=
    lcmLiftedNumerator_spec q a C D hdscale hc
  have hVeq : ∀ n, (M n : ℤ) * V n = E n :=
    lcmLiftedDigit_mul_overlapDebt q a C D hdscale hc
  have hUpos : ∀ n, 0 < U n := by
    intro n
    have hh := hUeq n
    by_contra hnot
    have hz : U n = 0 := by omega
    rw [hz, mul_zero] at hh
    exact (hcpos n).ne' hh.symm
  refine ⟨hUpos, lcmLifted_step C D hq hapos hdscale hc, (fun _ ↦ rfl), ?_, ?_⟩
  · intro n
    have hMu : (M n : ℝ) * (U n : ℝ) = (C n : ℝ) := by exact_mod_cast hUeq n
    have hML : (M n : ℝ) * (cumulativeDigitLcm q a n : ℝ) = (D n : ℝ) := by
      have hh := cumulativeOverlapDebt_mul_lcm_eq_productScale q a n
      rw [← hdscale n] at hh
      exact_mod_cast hh
    have hm0 : (M n : ℝ) ≠ 0 := by exact_mod_cast (hMpos n).ne'
    apply mul_left_cancel₀ hm0
    rw [hMu, ← mul_assoc, hML, hrep n]
  · intro K
    obtain ⟨N, hN⟩ := hvanish K
    refine ⟨N, ?_⟩
    intro n hn
    have hh : K * Int.natAbs ((M n : ℤ) * V n) < M n * U n := by
      rw [hVeq n, hUeq n]
      exact hN n hn
    rw [Int.natAbs_mul, Int.natAbs_natCast] at hh
    have hh' : M n * (K * Int.natAbs (V n)) < M n * U n := by nlinarith [hh]
    exact (Nat.mul_lt_mul_left (hMpos n)).mp hh'

/-- Exact equality of the implementation charge and the printed charge. -/
theorem rawCharge_eq_paperRecordCharge
    (U rho : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ) (f : ℝ → ℝ)
    (hU : ∀ n, 0 < U n)
    (hstep : ∀ n, (rho n : ℤ) * U (n + 1) = (U n : ℤ) - V n) :
    rawCharge U rho B (natWeight f) = paperRecordCharge U V B f := by
  funext n
  rw [rawCharge_eq_error U rho V B (natWeight f) n (hstep n)]
  simp only [paperRecordCharge, natWeight_eq_at_positive f (hU n)]

/-- The finite telescoping identity used for the converse. -/
theorem sylvester_reciprocal_step (x y : ℝ)
    (hx : 1 < x) (hy : y = x ^ 2 - x + 1) :
    1 / x = 1 / (x - 1) - 1 / (y - 1) := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x - 1 ≠ 0 := by linarith
  have hyd : y - 1 = x * (x - 1) := by rw [hy]; ring
  rw [hyd]
  field_simp [hx0, hx1]

/-- The vanishing telescoping endpoint requires no growth estimate beyond
strict increase of the positive natural denominators. -/
theorem reciprocal_pred_tendsto_zero
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n) (N : ℕ) :
    Tendsto (fun k : ℕ ↦ 1 / ((a (N + k) : ℝ) - 1)) atTop (𝓝 0) := by
  have hlinear : ∀ n, n < a n := by
    intro n
    induction n with
    | zero => exact hpos 0
    | succ n ih =>
        have hh : a n < a (n + 1) := ha (Nat.lt_succ_self n)
        omega
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (1 + 1 / ε)
  refine ⟨K, ?_⟩
  intro k hk
  have hkr : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have har : ((N + k : ℕ) : ℝ) < (a (N + k) : ℝ) := by exact_mod_cast hlinear (N + k)
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have heinv : 0 < (1 : ℝ) / ε := one_div_pos.mpr hε
  have hden : 1 / ε < (a (N + k) : ℝ) - 1 := by push_cast at har; linarith
  have hdenpos : 0 < (a (N + k) : ℝ) - 1 := heinv.trans hden
  have hmul : 1 < ((a (N + k) : ℝ) - 1) * ε := (div_lt_iff₀ hε).mp hden
  have hsmall : 1 / ((a (N + k) : ℝ) - 1) < ε :=
    (div_lt_iff₀ hdenpos).2 (by nlinarith [hmul])
  simpa only [Real.dist_eq, sub_zero, abs_of_pos (one_div_pos.mpr hdenpos)] using hsmall

/-- The actual reciprocal tail on a Sylvester tail. The sum is already
known to converge, so uniqueness of limits identifies its value. -/
theorem realTail_eq_of_eventual_sylvester
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hs : Summable (fun n ↦ 1 / (a n : ℝ)))
    (N : ℕ) (hN : ∀ n, N ≤ n → 2 ≤ a n)
    (hrec : ∀ n, N ≤ n → (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1) :
    ∀ n, N ≤ n → realTail (fun k ↦ 1 / (a k : ℝ)) n = 1 / ((a n : ℝ) - 1) := by
  intro n hn
  have htelescope : ∀ K : ℕ, (∑ k ∈ Finset.range K, 1 / (a (n + k) : ℝ)) =
      1 / ((a n : ℝ) - 1) - 1 / ((a (n + K) : ℝ) - 1) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ, ih]
        have hlow : (1 : ℝ) < (a (n + K) : ℝ) := by
          have hh := hN (n + K) (by omega)
          exact_mod_cast (show 1 < a (n + K) by omega)
        have hrecR : (a (n + K + 1) : ℝ) = (a (n + K) : ℝ) ^ 2 - (a (n + K) : ℝ) + 1 := by
          exact_mod_cast hrec (n + K) (by omega)
        rw [sylvester_reciprocal_step _ _ hlow hrecR]
        simp only [Nat.add_assoc]
        ring
  have hs0 : Summable (fun k : ℕ ↦ 1 / (a (n + k) : ℝ)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff n).2 hs
  have hlim : Tendsto (fun K : ℕ ↦ ∑ k ∈ Finset.range K, 1 / (a (n + k) : ℝ))
      atTop (𝓝 (1 / ((a n : ℝ) - 1))) := by
    simp_rw [htelescope]
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := 1 / ((a n : ℝ) - 1))).sub
        (reciprocal_pred_tendsto_zero a ha hpos n)
  have heq := tendsto_nhds_unique hs0.tendsto_sum_tsum_nat hlim
  simpa only [realTail, Nat.add_comm] using heq

/-- A finite prefix followed by a nonincreasing natural orbit is bounded. -/
theorem bounded_of_eventually_nonincreasing (U : ℕ → ℕ)
    (hdec : ∃ N, ∀ n, N ≤ n → U (n + 1) ≤ U n) :
    ∃ H : ℕ, ∀ n, U n ≤ H := by
  obtain ⟨N, hN⟩ := hdec
  refine ⟨runningMax U N, ?_⟩
  intro n
  induction n with
  | zero => exact le_runningMax U (Nat.zero_le N)
  | succ n ih =>
      by_cases hn : N ≤ n
      · exact (hN n hn).trans ih
      · exact le_runningMax U (by omega)

/-- Exact short-paper weighted-record equivalence, stated with the canonical
LCM numerator constructed above and the printed raw error weight. The
baseline is existential; all previous state theorems work for every fixed B. -/
theorem canonical_weighted_record_excess
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : IntegralUnbounded f) :
    (∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1) ↔
      ∃ B : ℕ, Summable (paperRecordCharge (canonicalLcmNumerator a p q)
        (canonicalLcmDigit a p q) B f) := by
  let U := canonicalLcmNumerator a p q
  let V := canonicalLcmDigit a p q
  obtain ⟨hU, hstep, herror, hrep, hvanish⟩ :=
    canonical_lcm_data a ha hapos p q hq hs hgrowth
  have ha2 := strictMono_eventually_ge_two a ha hapos
  have harith : ∀ n, (lcmOverlap q a n : ℤ) * U (n + 1) =
      (a n : ℤ) * U n - (1 : ℤ) * (cumulativeDigitLcm q a n : ℤ) := by
    intro n
    have hh := hstep n
    rw [herror n] at hh
    nlinarith
  constructor
  · rintro ⟨Nr, hNr⟩
    obtain ⟨Na, hNa⟩ := strictMono_eventually_ge_two a ha hapos
    let N := max Nr Na
    have htail := realTail_eq_of_eventual_sylvester a ha hapos hs.summable N
      (fun n hn ↦ hNa n (by dsimp [N] at hn; omega))
      (fun n hn ↦ hNr n (by dsimp [N] at hn; omega))
    have hzero : ∀ n, N ≤ n → V n = 0 := by
      intro n hn
      have hr := hrep n
      rw [htail n hn] at hr
      have hane : (a n : ℝ) - 1 ≠ 0 := by
        have hh : (2 : ℝ) ≤ (a n : ℝ) := by
          exact_mod_cast hNa n (by dsimp [N] at hn; omega)
        linarith
      have hm : ((a n : ℝ) - 1) * (U n : ℝ) = (cumulativeDigitLcm q a n : ℝ) := by
        rw [hr]
        field_simp [hane]
      have he : (V n : ℝ) = 0 := by
        have hh : (V n : ℝ) = (cumulativeDigitLcm q a n : ℝ) -
            ((a n : ℝ) - 1) * (U n : ℝ) := by exact_mod_cast herror n
        rw [hh, hm, sub_self]
      exact_mod_cast he
    have hb : ∃ H : ℕ, ∀ n, U n ≤ H := by
      apply bounded_of_eventually_nonincreasing U
      refine ⟨N, ?_⟩
      intro n hn
      have hh := hstep n
      have hz := hzero n hn
      change canonicalLcmDigit a p q n = 0 at hz
      rw [hz, sub_zero] at hh
      have hrho : (1 : ℤ) ≤ (lcmOverlap q a n : ℤ) := by
        exact_mod_cast (Nat.succ_le_of_lt (lcmOverlap_pos hq hapos n))
      have hnonneg : (0 : ℤ) ≤ (U (n + 1) : ℤ) := by positivity
      have hle : (U (n + 1) : ℤ) ≤ (U n : ℤ) := by nlinarith
      exact_mod_cast hle
    refine ⟨0, ?_⟩
    have hbraw := (bounded_iff_summable_raw q a U (fun _ ↦ 1) 0 hq ha2 harith
      (natWeight f) (natWeight_antitone f hf) (natWeight_nonneg f hpos)
      (natWeight_divergesOnProgressions f hf hpos hdiv)).mp hb
    rw [rawCharge_eq_paperRecordCharge U (lcmOverlap q a) V 0 f hU hstep] at hbraw
    exact hbraw
  · rintro ⟨B, hB⟩
    have hbraw : Summable (rawCharge U (lcmOverlap q a) B (natWeight f)) := by
      rw [rawCharge_eq_paperRecordCharge U (lcmOverlap q a) V B f hU hstep]
      exact hB
    obtain ⟨N, hN⟩ := weighted_recurrence_of_summable_raw_integral
      q a U (fun _ ↦ 1) V B hq ha2 hU hstep
      (fun n ↦ by simpa only [one_mul] using herror n)
      f hf hpos hdiv hbraw hvanish
    refine ⟨N, ?_⟩
    intro n hn
    have hh := hN n hn
    simp only [one_mul] at hh
    nlinarith

end ErdosProblems.Erdos243.PaperCompleteR11
