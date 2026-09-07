import ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect
import ErdosProblems.Erdos243.PaperCompleteR7.LcmStationarity

/-!
# Original-coordinate LCM-prefactor corollary

Uncompiled end-to-end candidate for short-note `res:lcmbounded`.
The rational denominator q is NOT assumed to divide the prefix LCM.
The proof constructs the lifted integer state, derives its small-error
hypothesis, supplies its one-sided bound from the printed LCM-weighted
expression, and invokes the global CRT argument, not a supply hypothesis.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter

noncomputable def lcmDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (cumulativeDigitLcm 1 a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)

theorem productScale_eq_canonicalDenominator (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    digitProductScale q a n = canonicalDenominator a q n := by
  induction n with
  | zero => simp [digitProductScale, canonicalDenominator, prefixProduct]
  | succ n ih =>
      simp only [digitProductScale, ih, canonicalDenominator, prefixProduct_succ]
      ring

/-- Retaining the rational denominator changes the prefix LCM by at most
its original factor q; no eventual q-divisibility assertion is used. -/
theorem lcm_seed_le_mul_prefix (q : ℕ) (a : ℕ → ℕ)
    (hq : 0 < q) (ha : ∀ n, 0 < a n) (n : ℕ) :
    cumulativeDigitLcm q a n ≤ q * cumulativeDigitLcm 1 a n := by
  have hid : ∀ k, cumulativeDigitLcm q a k = Nat.lcm q (cumulativeDigitLcm 1 a k) := by
    intro k
    induction k with
    | zero => simp [cumulativeDigitLcm]
    | succ k ih => simp only [cumulativeDigitLcm, ih, Nat.lcm_assoc]
  rw [hid n]
  have hd : Nat.lcm q (cumulativeDigitLcm 1 a n) ∣ q * cumulativeDigitLcm 1 a n := by
    apply Nat.lcm_dvd
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  exact Nat.le_of_dvd (Nat.mul_pos hq (cumulativeDigitLcm_pos (by norm_num) ha n)) hd

/-- Full short-note LCM-weighted bounded-defect implication, with finite
upper limsup encoded as an eventual real upper bound. -/
theorem original_coordinate_lcm_bounded_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hupper : ∃ M : ℝ, ∃ N, ∀ n, N ≤ n → lcmDefect a n ≤ M) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  let M := cumulativeOverlapDebt q a
  let L := cumulativeDigitLcm q a
  let U := lcmLiftedNumerator q a C
  let V := lcmLiftedDigit q a C
  obtain ⟨hcpos, hdpos, hc, hd, hrep, hvanish, _⟩ :=
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
  have hVsmall : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (V n) < U n := by
    intro K
    obtain ⟨N, hN⟩ := hvanish K
    refine ⟨N, fun n hn ↦ ?_⟩
    have hh : K * Int.natAbs ((M n : ℤ) * V n) < M n * U n := by
      rw [hVeq n, hUeq n]
      exact hN n hn
    rw [Int.natAbs_mul, Int.natAbs_natCast] at hh
    have hh' : M n * (K * Int.natAbs (V n)) < M n * U n := by
      nlinarith [hh]
    exact (Nat.mul_lt_mul_left (hMpos n)).mp hh'
  have herr := canonical_error_plus_productDefect_tendsto_zero a ha hapos p q hq hs hgrowth
  obtain ⟨Ne, hNe⟩ := Metric.tendsto_atTop.mp herr 1 (by norm_num)
  obtain ⟨H, Nu, hH⟩ := hupper
  let Z : ℕ → ℝ := fun n ↦ (L n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)
  have hap : ∀ n, (0 : ℝ) < (a n : ℝ) := fun n ↦ by exact_mod_cast hapos n
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hZbound : ∀ n, Nu ≤ n → Z n ≤ (q : ℝ) * max H 0 := by
    intro n hn
    have hLbound : (L n : ℝ) ≤ (q : ℝ) * (cumulativeDigitLcm 1 a n : ℝ) := by
      exact_mod_cast lcm_seed_le_mul_prefix q a hq hapos n
    let γ := (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1
    by_cases hγ : 0 ≤ γ
    · have hscale := div_le_div_of_nonneg_right hLbound (hap n).le
      have hmul := mul_le_mul_of_nonneg_right hscale hγ
      have htoQ : Z n ≤ (q : ℝ) * lcmDefect a n := by
        dsimp [Z, lcmDefect, γ] at *
        convert hmul using 1 <;> ring
      calc
        Z n ≤ (q : ℝ) * lcmDefect a n := htoQ
        _ ≤ (q : ℝ) * H := mul_le_mul_of_nonneg_left (hH n hn) hqr.le
        _ ≤ (q : ℝ) * max H 0 := mul_le_mul_of_nonneg_left (le_max_left H 0) hqr.le
    · have hγle : γ ≤ 0 := by linarith
      have hz : Z n ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (Nat.cast_nonneg _) (hap n).le) hγle
      exact hz.trans (mul_nonneg hqr.le (le_max_right H 0))
  have hdict : ∀ n, (M n : ℝ) * ((V n : ℝ) + Z n) =
      (E n : ℝ) + (q : ℝ) * productDefect a n := by
    intro n
    have hMV : (M n : ℝ) * (V n : ℝ) = (E n : ℝ) := by exact_mod_cast hVeq n
    have hML : (M n : ℝ) * (L n : ℝ) =
        (q : ℝ) * (prefixProduct a n : ℝ) := by
      have hh := cumulativeOverlapDebt_mul_lcm_eq_productScale q a n
      rw [productScale_eq_canonicalDenominator] at hh
      exact_mod_cast hh
    rw [mul_add, hMV]
    dsimp [Z, productDefect]
    congr 1
    calc
      (M n : ℝ) * ((L n : ℝ) / (a n : ℝ) *
          ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)) =
          ((M n : ℝ) * (L n : ℝ)) / (a n : ℝ) *
            ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) := by ring
      _ = _ := by rw [hML]; ring
  obtain ⟨B, hB⟩ := exists_nat_gt ((q : ℝ) * max H 0 + 1)
  have hVbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ V n := by
    refine ⟨max Ne Nu, B, fun n hn ↦ ?_⟩
    have he := hNe n (by omega)
    rw [Real.dist_eq, sub_zero] at he
    have helo := (abs_lt.mp he).1
    have hMone : (1 : ℝ) ≤ (M n : ℝ) := by exact_mod_cast hMpos n
    have hz := hZbound n (by omega)
    have hlower : -(1 : ℝ) ≤ (V n : ℝ) + Z n := by
      by_contra hnot
      have hneg : (V n : ℝ) + Z n < -1 := by linarith
      have hprod : 0 ≤ ((M n : ℝ) - 1) * (-((V n : ℝ) + Z n)) :=
        mul_nonneg (by linarith) (by linarith)
      have hid := hdict n
      nlinarith
    have hVreal : -(B : ℝ) ≤ (V n : ℝ) := by linarith
    exact_mod_cast hVreal
  have hUbound := bounded_lcm_height q a U V hq ha hapos hUpos
    (lcmLifted_step C D hq hapos hdscale hc)
    (fun _ ↦ rfl) hVbound
  obtain ⟨Nv, hNv⟩ := zero_digit_of_bounded_height U V hUbound hVsmall
  have hEzero : ∃ N, ∀ n, N ≤ n → E n = 0 := by
    refine ⟨Nv, fun n hn ↦ ?_⟩
    have hh := hVeq n
    rw [hNv n hn, mul_zero] at hh
    exact hh.symm
  simpa only [sylvesterNext] using
    natural_sylvester_of_eventual_zero a C D E hcpos hc hd (fun _ ↦ rfl) hEzero

end ErdosProblems.Erdos243.PaperCompleteR7
