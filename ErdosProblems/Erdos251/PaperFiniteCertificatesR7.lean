import ErdosProblems.Erdos251.PaperTailBoundsR7
import ErdosProblems.Erdos251.KernelDenominatorFloor

/-!
# Exact finite certificates appearing in the long record

New proof source, not compiled in the return environment. All numerical
claims below use exact arithmetic. No numerical approximation to an
infinite tail is used: the Farey bracket is proved from the supplied
kernel-verifiable certificate and its unconditional tail bound.
-/

open scoped BigOperators
open Finset

namespace ErdosProblems.Erdos251.PaperR7

/-- The supplied certificate proves a real enclosure, not only a denominator
floor. This form is useful for the small-pair example in the long record. -/
theorem prime_series_between_of_certCheck
    (c u v u' v' X : ℕ) (hc : 9 ≤ c)
    (h : certCheck c u v u' v' X = true) :
    (u : ℝ) / v < (∑' n, primeDyadicTerm n) ∧
    (∑' n, primeDyadicTerm n) < (u' : ℝ) / v' := by
  simp only [certCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_iff] at h
  obtain ⟨⟨⟨⟨⟨hcount, hv⟩, hv'⟩, _hdet⟩, hlo⟩, hhi⟩ := h
  rw [primeSumLoop_fst] at hcount
  have hsnd := primeSumLoop_snd c X (by rw [hcount])
  rw [hcount] at hsnd
  set lo := (primeSumLoop c X).2
  have hprefix : ∑ i ∈ range c, primeDyadicTerm i = (lo : ℝ) / 2 ^ c := by
    rw [sum_primeDyadicTerm_eq_div c c le_rfl, hsnd]
  obtain ⟨hb1, hb2⟩ := tsum_primeDyadicTerm_bracket c hc
  rw [hprefix] at hb1 hb2
  have h2c : (0 : ℝ) < 2 ^ c := by positivity
  have h2c1 : (0 : ℝ) < 2 ^ (c + 1) := by positivity
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hv'R : (0 : ℝ) < v' := by exact_mod_cast hv'
  have hloR : (u : ℝ) / v < (lo : ℝ) / 2 ^ c := by
    rw [div_lt_div_iff₀ hvR h2c]
    exact_mod_cast hlo
  have hhiR : ((2 * lo + 5000 * (c + 1) ^ 4 : ℕ) : ℝ) / 2 ^ (c + 1)
      < (u' : ℝ) / v' := by
    rw [div_lt_div_iff₀ h2c1 hv'R]
    exact_mod_cast hhi
  have hsum : (lo : ℝ) / 2 ^ c + 5000 * (c + 1) ^ 4 / 2 ^ (c + 1)
      = ((2 * lo + 5000 * (c + 1) ^ 4 : ℕ) : ℝ) / 2 ^ (c + 1) := by
    push_cast
    rw [pow_succ]
    field_simp
    ring
  exact ⟨lt_of_lt_of_le hloR hb1, lt_of_le_of_lt hb2 (by rw [hsum]; exact hhiR)⟩

/-- A deliberately coarse exact enclosure sufficient for the printed local
example. The large certificate is reused rather than re-sieving here. -/
theorem coarse_prime_series_enclosure :
    (367 : ℝ) / 100 < (∑' n, primeDyadicTerm n) ∧
    (∑' n, primeDyadicTerm n) < (368 : ℝ) / 100 := by
  obtain ⟨hlo, hhi⟩ := prime_series_between_of_certCheck
    certC certU certV certU' certV' certX (by decide) cert_10000
  have hleft : (367 : ℝ) / 100 < (certU : ℝ) / certV := by
    norm_num [certU, certV]
  have hright : (certU' : ℝ) / certV' < (368 : ℝ) / 100 := by
    norm_num [certU', certV']
  exact ⟨lt_trans hleft hlo, lt_trans hhi hright⟩

private theorem prime0_eq_seven : prime0 3 = 7 := by
  have hc : Nat.count Nat.Prime 7 = 3 := by decide +kernel
  have hp : Nat.Prime 7 := by norm_num
  simpa [prime0, hc] using Nat.nth_count hp

private theorem prime0_eq_eleven : prime0 4 = 11 := by
  have hc : Nat.count Nat.Prime 11 = 4 := by decide +kernel
  have hp : Nat.Prime 11 := by norm_num
  simpa [prime0, hc] using Nat.nth_count hp

private theorem prime0_eq_thirteen : prime0 5 = 13 := by
  have hc : Nat.count Nat.Prime 13 = 5 := by decide +kernel
  have hp : Nat.Prime 13 := by norm_num
  simpa [prime0, hc] using Nat.nth_count hp

private theorem prime0_eq_five : prime0 2 = 5 := by
  have hc : Nat.count Nat.Prime 5 = 2 := by decide +kernel
  have hp : Nat.Prime 5 := by norm_num
  simpa [prime0, hc] using Nat.nth_count hp

theorem first_needed_prime_gaps :
    primeGap0 2 = 2 ∧ primeGap0 3 = 4 ∧ primeGap0 4 = 2 := by
  norm_num [primeGap0, prime0_eq_five, prime0_eq_seven,
    prime0_eq_eleven, prime0_eq_thirteen]

/-- Exact values of the two shifts as affine expressions in the actual gap
sum. These are equalities of convergent infinite tails. -/
theorem adjacent_pair_affine_values :
    realTailShift realPrimeGapTail 1 2 =
      8 * (∑' n, primeGapDyadicTerm n) - 14 ∧
    realTailShift realPrimeGapTail 1 3 =
      16 * (∑' n, primeGapDyadicTerm n) - 26 := by
  obtain ⟨hg2, hg3, hg4⟩ := first_needed_prime_gaps
  have h0 := realPrimeGapTail_zero
  have h1 := realPrimeGapTail_recurrence 0
  have h2 := realPrimeGapTail_recurrence 1
  have h3 := realPrimeGapTail_recurrence 2
  have h4 := realPrimeGapTail_recurrence 3
  norm_num [primeGap0_one, hg2, hg3, hg4] at h1 h2 h3 h4
  constructor <;> simp only [realTailShift] <;> norm_num <;> linarith

/-- `res:finite-smallpair`: both adjacent actual infinite-tail shifts are
strictly between -1 and 1 and individually nonintegral, while the digits
are unequal. This is a finite instance, not a cofinal supply. -/
theorem finite_small_pair :
    (-1 < realTailShift realPrimeGapTail 1 2 ∧
      realTailShift realPrimeGapTail 1 2 < 1) ∧
    (-1 < realTailShift realPrimeGapTail 1 3 ∧
      realTailShift realPrimeGapTail 1 3 < 1) ∧
    ¬ RealIntegral (realTailShift realPrimeGapTail 1 2) ∧
    ¬ RealIntegral (realTailShift realPrimeGapTail 1 3) ∧
    primeGap0 4 = 2 ∧ primeGap0 3 = 4 := by
  obtain ⟨hslo, hshi⟩ := coarse_prime_series_enclosure
  rw [tsum_primeDyadicTerm_eq_two_add_primeGap_unconditional] at hslo hshi
  obtain ⟨hD2, hD3⟩ := adjacent_pair_affine_values
  obtain ⟨_hg2, hg3, hg4⟩ := first_needed_prime_gaps
  have ha : -1 < realTailShift realPrimeGapTail 1 2 := by linarith
  have hb : realTailShift realPrimeGapTail 1 2 < 0 := by linarith
  have hc : 0 < realTailShift realPrimeGapTail 1 3 := by linarith
  have hd : realTailShift realPrimeGapTail 1 3 < 1 := by linarith
  refine ⟨⟨ha, by linarith⟩, ⟨by linarith, hd⟩, ?_, ?_, hg4, hg3⟩
  · intro hint
    have hz := realIntegral_eq_zero_of_small hint ha (by linarith)
    linarith
  · intro hint
    have hz := realIntegral_eq_zero_of_small hint (by linarith) hd
    linarith

set_option exponentiation.threshold 1024 in
/-- The strict decimal comparison printed beside the binary floor. -/
theorem denominator_floor_decimal : (10 ^ 177 : ℕ) < 2 ^ 589 := by
  decide +kernel

/-- `res:denominatorfloor`, including the strict decimal lower bound, for
both displayed normalisations Pi and G. No reduced-fraction premise is needed. -/
theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ((∑' n, primeDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) ∧
    ((∑' n, primeGapDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) := by
  constructor
  · intro h
    have hf := kernel_denominator_floor a b hb h
    exact ⟨hf, lt_of_lt_of_le denominator_floor_decimal hf⟩
  · intro h
    have hf := kernel_denominator_floor_primeGap a b hb h
    exact ⟨hf, lt_of_lt_of_le denominator_floor_decimal hf⟩

end ErdosProblems.Erdos251.PaperR7
