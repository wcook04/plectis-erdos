import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Erdős #1049: endpoint arithmetic for the Heine--Zudilin cone

This module isolates the source-independent arithmetic behind the returned
scalar-cone obstruction at the rational base `3 / 2`.  It does not construct
the Zudilin coefficient polynomials or import their analytic asymptotics.

The key finite observation is that homogeneous evaluation at `(3,2)` sees the
bottom polynomial endpoint modulo `3` and the top endpoint modulo `2`.
Consequently a unit at either endpoint prevents a common local factor.  The
endpoint-jet definitions record the exact additive congruence problem left
after scalar and multiplicative deformations have been exhausted.
-/

namespace ErdosProblems.Erdos1049

open Polynomial

/-- Twice the normalising exponent used in the finite Heine--Zudilin
coefficient calculation.  Doubling removes every parity and integer-division
side condition from the algebraic certificate. -/
def zudilinNormExpTwice (a0 a1 a2 b : ℤ) : ℤ :=
  a1 * (a1 - 1) + 2 * a0 * a1 + 2 * (b - a2) * (a2 - a1)

/-- The explicit monomial exponent in the `k`-th partial-fraction
coefficient. -/
def zudilinPartialFractionExpTwice (a1 a2 b k : ℤ) : ℤ :=
  a1 * (a1 - 1) -
    (b - a2) * (b - a2 - 1) +
    (b - k) * (b - k - 1)

/-- The bottom exponent of the normalised `U` summand indexed by `k`. -/
def zudilinBottomExpTwice (a0 a1 a2 b k : ℤ) : ℤ :=
  zudilinPartialFractionExpTwice a1 a2 b k + 2 * a0 * k -
    zudilinNormExpTwice a0 a1 a2 b

/-- The degree of the raw `U` summand indexed by `k`, before the common
normalisation and cyclotomic factor. -/
def zudilinRawDegreeTwice (a0 a1 a2 b k : ℤ) : ℤ :=
  2 * a0 * k + zudilinPartialFractionExpTwice a1 a2 b k +
    2 * (a1 - 1) * (k - a1) + 2 * (b - k - 1) * (k - a2)

/-- At the bottom endpoint, the normalised exponent is exactly
`(a₂-a₁)(a₀+a₂-b)`. -/
theorem zudilinBottomExpTwice_at_a2 (a0 a1 a2 b : ℤ) :
    zudilinBottomExpTwice a0 a1 a2 b a2 =
      2 * (a2 - a1) * (a0 + a2 - b) := by
  simp [zudilinBottomExpTwice, zudilinPartialFractionExpTwice,
    zudilinNormExpTwice]
  ring

/-- Exact first difference of consecutive normalised bottom exponents. -/
theorem zudilinBottomExpTwice_succ_sub (a0 a1 a2 b k : ℤ) :
    zudilinBottomExpTwice a0 a1 a2 b (k + 1) -
        zudilinBottomExpTwice a0 a1 a2 b k =
      2 * (a0 - b + k + 1) := by
  simp [zudilinBottomExpTwice, zudilinPartialFractionExpTwice,
    zudilinNormExpTwice]
  ring

/-- Inside the source cone, bottom exponents strictly increase from `a₂`
onward. -/
theorem zudilinBottomExpTwice_strict_step
    {a0 a1 a2 b k : ℤ}
    (hcone : b ≤ a0 + a2) (hk : a2 ≤ k) :
    zudilinBottomExpTwice a0 a1 a2 b k <
      zudilinBottomExpTwice a0 a1 a2 b (k + 1) := by
  have hdiff := zudilinBottomExpTwice_succ_sub a0 a1 a2 b k
  linarith

/-- Exact first difference of consecutive raw degrees. -/
theorem zudilinRawDegreeTwice_succ_sub (a0 a1 a2 b k : ℤ) :
    zudilinRawDegreeTwice a0 a1 a2 b (k + 1) -
        zudilinRawDegreeTwice a0 a1 a2 b k =
      2 * (a0 + a1 + a2 - k - 2) := by
  simp [zudilinRawDegreeTwice, zudilinPartialFractionExpTwice]
  ring

/-- Inside the source cone, raw summand degrees strictly increase through
the last allowed index `b-1`. -/
theorem zudilinRawDegreeTwice_strict_step
    {a0 a1 a2 b k : ℤ}
    (ha1 : 0 < a1) (hcone : b ≤ a0 + a2) (hk : k ≤ b - 2) :
    zudilinRawDegreeTwice a0 a1 a2 b k <
      zudilinRawDegreeTwice a0 a1 a2 b (k + 1) := by
  have hdiff := zudilinRawDegreeTwice_succ_sub a0 a1 a2 b k
  linarith

/-- Integer homogeneous evaluation of an integral polynomial at `(3,2)`,
using the declared ambient width `W`. -/
def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)

/-- The bottom `3`-adic endpoint jet of depth `R`. -/
def bottomJet3 (R W : ℕ) (P : Polynomial ℤ) : ZMod (3 ^ R) :=
  homEvalThreeTwo W P

/-- The top `2`-adic endpoint jet of depth `S`. -/
def topJet2 (S W : ℕ) (P : Polynomial ℤ) : ZMod (2 ^ S) :=
  homEvalThreeTwo W P

/-- The four simultaneous endpoint congruences for a coefficient pair:
bottom and top jets in both channels. -/
abbrev FourJetSignature (R S : ℕ) :=
  (ZMod (3 ^ R) × ZMod (3 ^ R)) ×
    (ZMod (2 ^ S) × ZMod (2 ^ S))

/-- Four-jet signature of one integral coefficient pair. -/
def fourJetSignature (R S W : ℕ) (U V : Polynomial ℤ) :
    FourJetSignature R S :=
  ((bottomJet3 R W U, bottomJet3 R W V),
    (topJet2 S W U, topJet2 S W V))

/-- Sum of the four-jet signatures selected by a binary coefficient vector. -/
def selectedFourJetSum {n : ℕ} (R S W : ℕ)
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (ε : Fin n → Bool) : FourJetSignature R S :=
  ∑ i, if ε i then
    fourJetSignature R S W (forms i).1 (forms i).2
  else 0

/-- Once the binary selector space is larger than the four-jet target, two
distinct subsets have the same simultaneous endpoint signature.  Subtracting
their indicator vectors gives a nonzero coefficient vector in
`{-1,0,1}` whose four endpoint jets cancel.  This theorem supplies kernel
existence only; it does not prove that the resulting analytic remainder is
nonzero or that its height beats the local gain. -/
theorem exists_distinct_binary_selectors_same_fourJet
    {n R S W : ℕ}
    (forms : Fin n → Polynomial ℤ × Polynomial ℤ)
    (hcard : Fintype.card (FourJetSignature R S) < 2 ^ n) :
    ∃ ε η : Fin n → Bool, ε ≠ η ∧
      selectedFourJetSum R S W forms ε =
        selectedFourJetSum R S W forms η := by
  have hlt :
      Fintype.card (FourJetSignature R S) <
        Fintype.card (Fin n → Bool) := by
    simpa using hcard
  exact Fintype.exists_ne_map_eq_of_card_lt
    (selectedFourJetSum R S W forms) hlt

/-- Vanishing of the bottom jet is exactly divisibility of the homogeneous
evaluation by the requested power of `3`. -/
theorem bottomJet3_eq_zero_iff_dvd (R W : ℕ) (P : Polynomial ℤ) :
    bottomJet3 R W P = 0 ↔ ((3 ^ R : ℕ) : ℤ) ∣ homEvalThreeTwo W P := by
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

/-- Vanishing of the top jet is exactly divisibility of the homogeneous
evaluation by the requested power of `2`. -/
theorem topJet2_eq_zero_iff_dvd (S W : ℕ) (P : Polynomial ℤ) :
    topJet2 S W P = 0 ↔ ((2 ^ S : ℕ) : ℤ) ∣ homEvalThreeTwo W P := by
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _

/-- Modulo `3`, homogeneous evaluation retains only the constant
coefficient. -/
theorem homEvalThreeTwo_mod_three (W : ℕ) (P : Polynomial ℤ) :
    (homEvalThreeTwo W P : ZMod 3) = (P.coeff 0 : ZMod 3) * 2 ^ W := by
  simp only [homEvalThreeTwo, Int.cast_sum, Int.cast_mul, Int.cast_pow]
  rw [Finset.sum_eq_single 0]
  · norm_num
  · intro i hi hi0
    have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    have hthree : (3 : ZMod 3) ^ i = 0 := by
      rw [show (3 : ZMod 3) = 0 by decide, zero_pow hipos.ne']
    simp [hthree]
  · simp

/-- Modulo `2`, homogeneous evaluation retains only the coefficient at the
declared top width. -/
theorem homEvalThreeTwo_mod_two (W : ℕ) (P : Polynomial ℤ) :
    (homEvalThreeTwo W P : ZMod 2) = (P.coeff W : ZMod 2) * 3 ^ W := by
  simp only [homEvalThreeTwo, Int.cast_sum, Int.cast_mul, Int.cast_pow]
  rw [Finset.sum_eq_single W]
  · norm_num
  · intro i hi hiW
    have hi_le : i ≤ W := by
      have hi_lt : i < W + 1 := Finset.mem_range.mp hi
      omega
    have hi_lt : i < W := lt_of_le_of_ne hi_le hiW
    have hsub : 0 < W - i := Nat.sub_pos_of_lt hi_lt
    have htwo : (2 : ZMod 2) ^ (W - i) = 0 := by
      rw [show (2 : ZMod 2) = 0 by decide, zero_pow hsub.ne']
    simp [htwo]
  · simp

/-- A unit constant coefficient prevents any factor `3` in the homogeneous
specialisation. -/
theorem three_not_dvd_homEvalThreeTwo_of_const_unit
    (W : ℕ) (P : Polynomial ℤ)
    (hunit : P.coeff 0 = 1 ∨ P.coeff 0 = -1) :
    ¬ (3 : ℤ) ∣ homEvalThreeTwo W P := by
  intro hdvd
  have hzero : (homEvalThreeTwo W P : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
  rw [homEvalThreeTwo_mod_three] at hzero
  have hpow : (2 : ZMod 3) ^ W ≠ 0 :=
    pow_ne_zero _ (by decide)
  rcases hunit with h | h
  · rw [h] at hzero
    exact hpow (by simpa using hzero)
  · rw [h] at hzero
    exact hpow (by simpa using hzero)

/-- A unit coefficient at the declared top width prevents any factor `2` in
the homogeneous specialisation. -/
theorem two_not_dvd_homEvalThreeTwo_of_top_unit
    (W : ℕ) (P : Polynomial ℤ)
    (hunit : P.coeff W = 1 ∨ P.coeff W = -1) :
    ¬ (2 : ℤ) ∣ homEvalThreeTwo W P := by
  intro hdvd
  have hzero : (homEvalThreeTwo W P : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdvd
  rw [homEvalThreeTwo_mod_two] at hzero
  have hpow : (3 : ZMod 2) ^ W ≠ 0 :=
    pow_ne_zero _ (by decide)
  rcases hunit with h | h
  · rw [h] at hzero
    exact hpow (by simpa using hzero)
  · rw [h] at hzero
    exact hpow (by simpa using hzero)

/-- If one channel has a unit top coefficient, the two coefficient channels
cannot have a common factor `2` after homogeneous specialisation. -/
theorem not_two_dvd_both_homEval_of_left_top_unit
    (W : ℕ) (U V : Polynomial ℤ)
    (hunit : U.coeff W = 1 ∨ U.coeff W = -1) :
    ¬ ((2 : ℤ) ∣ homEvalThreeTwo W U ∧
      (2 : ℤ) ∣ homEvalThreeTwo W V) := by
  intro h
  exact two_not_dvd_homEvalThreeTwo_of_top_unit W U hunit h.1

/-- If one channel has a unit constant coefficient, the two coefficient
channels cannot have a common factor `3` after homogeneous specialisation. -/
theorem not_three_dvd_both_homEval_of_right_const_unit
    (W : ℕ) (U V : Polynomial ℤ)
    (hunit : V.coeff 0 = 1 ∨ V.coeff 0 = -1) :
    ¬ ((3 : ℤ) ∣ homEvalThreeTwo W U ∧
      (3 : ℤ) ∣ homEvalThreeTwo W V) := by
  intro h
  exact three_not_dvd_homEvalThreeTwo_of_const_unit W V hunit h.2

/-- The only analytic input needed from an irrationality-exponent argument:
if an irrational number has exponent at least `2` and a source construction
bounds that exponent by `C₁ / C₀`, then `2 C₀ ≤ C₁`. -/
theorem twice_le_of_irrationalityExponent_bounds
    {μ C0 C1 : ℝ} (hC0 : 0 < C0)
    (hlower : 2 ≤ μ) (hupper : μ ≤ C1 / C0) :
    2 * C0 ≤ C1 := by
  apply (le_div_iff₀ hC0).mp
  exact hlower.trans hupper

/-- The parameter inequality forced by an integer-base
irrationality-exponent estimate makes the rational-base `3/2`
product-formula margin strictly negative.  The theorem deliberately consumes
the source-backed inequality as a hypothesis rather than importing the
analytic construction. -/
theorem three_two_scalar_margin_neg
    {C0 C1 : ℝ} (hC1 : 0 < C1)
    (hsource : C0 ≤ 0 ∨ 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 < 0 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases hsource with hC0 | htwice
  · have hnonpos : C0 * Real.log 3 ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg hC0 (Real.log_nonneg (by norm_num))
    nlinarith
  · by_cases hC0 : C0 ≤ 0
    · have hnonpos : C0 * Real.log 3 ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg hC0 (Real.log_nonneg (by norm_num))
      nlinarith
    · have hC0pos : 0 < C0 := lt_of_not_ge hC0
      have hlog : Real.log 3 < 2 * Real.log 2 := by
        calc
          Real.log 3 < Real.log 4 :=
            Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
          _ = Real.log (2 ^ 2) := by norm_num
          _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
      nlinarith

end ErdosProblems.Erdos1049
