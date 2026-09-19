import ErdosProblems.Erdos269.PaperR7RationalBridge
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find

/-!
# Exact reduced denominators for the paper tail states

This module formalises the exact-denominator calculation in the short and long
papers.  The rational representative below is proved to cast to the literal
real tail state, so its `Rat.den` is the paper's positive reduced denominator.
-/

namespace ErdosProblems.Erdos269.PaperR13

open scoped BigOperators
open PaperR7

/-- The rational representative of the paper state `X_a`, written from the
value `N / D` and the finite rational prefix below scale `a`. -/
def rationalTailState (N : ℤ) (D a : ℕ) : ℚ :=
  (heightNormalizer235 a : ℚ) *
    ((N : ℚ) / (D : ℚ) - 1 - dyadicSmoothWindowMassQ235 1 (a - 1))

/-- At positive scale the half-height definition is literally the normalizer
used in `trueNormalizedState`. -/
theorem trueNormalizedState_eq_heightNormalizer_mul (a : ℕ) (ha : 1 ≤ a) :
    trueNormalizedState a =
      (heightNormalizer235 a : ℝ) * dyadicShellTsumTailR235 a := by
  unfold trueNormalizedState dyadicNormalizedTailStateR235
  have h2 : (threePrimeHeight 2 3 5 (2 ^ a) : ℝ) =
      2 * (heightNormalizer235 a : ℝ) := by
    exact_mod_cast (two_mul_heightNormalizer235 a ha).symm
  rw [h2]
  ring

/-- The rational representative is the literal real tail state under the
paper's rational-value hypothesis. -/
theorem rationalTailState_cast {N : ℤ} {D a : ℕ} (hD : 0 < D) (ha : 1 ≤ a)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ((rationalTailState N D a : ℚ) : ℝ) = trueNormalizedState a := by
  have haeq : 1 + (a - 1) = a := by omega
  have hsplit := dyadicShellTsumTailR235_eq_range_add 1 (a - 1)
  rw [haeq] at hsplit
  have hpref :
      (∑ i ∈ Finset.range (a - 1), dyadicShellMassR235 (1 + i)) =
        ((dyadicSmoothWindowMassQ235 1 (a - 1) : ℚ) : ℝ) := by
    simp [dyadicSmoothWindowMassQ235, dyadicShellMassR235]
  have htailOne := tail_one_of_paperSeries_eq_rat hD hval
  have htail : dyadicShellTsumTailR235 a =
      (N : ℝ) / (D : ℝ) - 1 -
        ((dyadicSmoothWindowMassQ235 1 (a - 1) : ℚ) : ℝ) := by
    rw [hpref, htailOne] at hsplit
    have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have hquot :
        (((N - (D : ℤ) : ℤ) : ℤ) : ℝ) / (D : ℝ) =
          (N : ℝ) / (D : ℝ) - 1 := by
      push_cast
      field_simp [hDR]
    rw [hquot] at hsplit
    linarith
  rw [trueNormalizedState_eq_heightNormalizer_mul a ha, htail]
  simp only [rationalTailState, Rat.cast_mul, Rat.cast_natCast, Rat.cast_sub,
    Rat.cast_intCast, Rat.cast_div, Rat.cast_one]

/-- Multiplying a reduced rational numerator by a natural number cancels
exactly the gcd with the denominator. -/
theorem den_nat_mul_int_div_nat {h M : ℕ} {N : ℤ} (hM : 0 < M)
    (hcop : Nat.Coprime N.natAbs M) :
    (((h : ℚ) * (N : ℚ) / (M : ℚ)).den) = M / Nat.gcd M h := by
  have hMZ : (M : ℤ) ≠ 0 := by exact_mod_cast hM.ne'
  have heq : (h : ℚ) * (N : ℚ) / (M : ℚ) =
      Rat.divInt ((h : ℤ) * N) (M : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    rfl
  rw [heq, Rat.den_mk, if_neg hMZ, Int.gcd_def]
  simp only [Int.natAbs_natCast, Int.natAbs_mul]
  rw [hcop.gcd_mul_right_cancel h, Nat.gcd_comm]

/-- The half-height normalizer has no prime factors outside `2,3,5`. -/
theorem heightNormalizer235_dvd_thirty_pow (a : ℕ) (ha : 1 ≤ a) :
    heightNormalizer235 a ∣ 30 ^ a := by
  have h2 : Nat.log 2 (2 ^ a) = a := Nat.log_pow (by norm_num) a
  have h3 : Nat.log 3 (2 ^ a) ≤ a := by
    have h := Nat.log_mono_right (b := 3)
      (Nat.pow_le_pow_left (by norm_num : 2 ≤ 3) a)
    simpa [Nat.log_pow (by norm_num : 1 < (3 : ℕ))] using h
  have h5 : Nat.log 5 (2 ^ a) ≤ a := by
    have h := Nat.log_mono_right (b := 5)
      (Nat.pow_le_pow_left (by norm_num : 2 ≤ 5) a)
    simpa [Nat.log_pow (by norm_num : 1 < (5 : ℕ))] using h
  have hH : threePrimeHeight 2 3 5 (2 ^ a) ∣ 30 ^ a := by
    unfold threePrimeHeight
    rw [h2]
    have hm := monomial235_dvd (le_refl a) h3 h5
    have h30 : 30 ^ a = 2 ^ a * 3 ^ a * 5 ^ a := by
      rw [show (30 : ℕ) = 2 * 3 * 5 by norm_num, mul_pow, mul_pow]
    rw [h30]
    exact hm
  have hh : heightNormalizer235 a ∣ threePrimeHeight 2 3 5 (2 ^ a) := by
    refine ⟨2, ?_⟩
    simpa [mul_comm] using (two_mul_heightNormalizer235 a ha).symm
  exact hh.trans hH

/-- A rough denominator coprime to `30` is coprime to every paper
half-height normalizer. -/
theorem coprime_heightNormalizer235 {B a : ℕ} (hB : Nat.Coprime B 30)
    (ha : 1 ≤ a) : Nat.Coprime B (heightNormalizer235 a) := by
  exact Nat.Coprime.of_dvd_right (heightNormalizer235_dvd_thirty_pow a ha)
    (hB.pow_right a)

/-- At a positive scale, the half-height removes exactly one factor of two
from the boundary height. -/
theorem heightNormalizer235_eq_monomial (a : ℕ) (ha : 1 ≤ a) :
    heightNormalizer235 a =
      2 ^ (a - 1) * 3 ^ Nat.log 3 (2 ^ a) * 5 ^ Nat.log 5 (2 ^ a) := by
  apply Nat.mul_left_cancel (n := 2) (by norm_num)
  rw [two_mul_heightNormalizer235 a ha]
  unfold threePrimeHeight
  rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))]
  have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
    calc
      2 ^ a = 2 ^ ((a - 1) + 1) := by congr 1 <;> omega
      _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ring
  rw [hpow]
  ring

/-- Divisibility between two `2,3,5` monomials is exactly the three
coordinatewise exponent inequalities. -/
theorem monomial235_dvd_iff {u v w r s t : ℕ} :
    2 ^ u * 3 ^ v * 5 ^ w ∣ 2 ^ r * 3 ^ s * 5 ^ t ↔
      u ≤ r ∧ v ≤ s ∧ w ≤ t := by
  have hp2 : Nat.Prime 2 := by norm_num
  have hp3 : Nat.Prime 3 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  constructor
  · intro hdvd
    rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity)] at hdvd
    have h2 := hdvd 2
    have h3 := hdvd 3
    have h5 := hdvd 5
    norm_num [Nat.factorization_mul, hp2.factorization_pow,
      hp3.factorization_pow, hp5.factorization_pow] at h2 h3 h5
    exact ⟨h2, h3, h5⟩
  · rintro ⟨hu, hv, hw⟩
    exact monomial235_dvd hu hv hw

/-- The paper's smooth denominator divides the normalizer precisely at the
three integer-power thresholds. -/
theorem smoothPart_dvd_heightNormalizer235_iff {u v w a : ℕ} (ha : 1 ≤ a) :
    2 ^ u * 3 ^ v * 5 ^ w ∣ heightNormalizer235 a ↔
      2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a := by
  rw [heightNormalizer235_eq_monomial a ha, monomial235_dvd_iff]
  rw [Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))]
  rw [Nat.le_log_iff_pow_le (by norm_num : 1 < (3 : ℕ)) (by positivity)]
  rw [Nat.le_log_iff_pow_le (by norm_num : 1 < (5 : ℕ)) (by positivity)]
  omega

/-- The integer-power condition defining the paper's first clearing index. -/
def ClearingCondition (u v w a : ℕ) : Prop :=
  1 ≤ a ∧ 2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a

/-- The conjunction form is exactly the maximum inequality displayed in the
papers. -/
theorem clearingCondition_iff_max {u v w a : ℕ} :
    ClearingCondition u v w a ↔
      1 ≤ a ∧ max (2 ^ (u + 1)) (max (3 ^ v) (5 ^ w)) ≤ 2 ^ a := by
  simp only [ClearingCondition, max_le_iff]

theorem clearingCondition_mono {u v w a b : ℕ} (hab : a ≤ b)
    (ha : ClearingCondition u v w a) : ClearingCondition u v w b := by
  rcases ha with ⟨ha1, h2, h3, h5⟩
  have hp : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
  exact ⟨ha1.trans hab, h2.trans hp, h3.trans hp, h5.trans hp⟩

/-- The paper's elementary bound `a_D = u+1+2v+3w` satisfies all three
integer-power thresholds. -/
theorem clearingCondition_sufficient (u v w : ℕ) :
    ClearingCondition u v w (u + 1 + 2 * v + 3 * w) := by
  let aD := u + 1 + 2 * v + 3 * w
  have h2 : 2 ^ (u + 1) ≤ 2 ^ aD :=
    Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega)
  have h3four : 3 ^ v ≤ 4 ^ v := Nat.pow_le_pow_left (by norm_num) v
  have h4two : 4 ^ v = 2 ^ (2 * v) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h3 : 3 ^ v ≤ 2 ^ aD := by
    rw [h4two] at h3four
    exact h3four.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega))
  have h5eight : 5 ^ w ≤ 8 ^ w := Nat.pow_le_pow_left (by norm_num) w
  have h8two : 8 ^ w = 2 ^ (3 * w) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  have h5 : 5 ^ w ≤ 2 ^ aD := by
    rw [h8two] at h5eight
    exact h5eight.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega))
  exact ⟨by omega, h2, h3, h5⟩

/-- The first positive scale satisfying the three integer-power comparisons. -/
noncomputable def firstClearingIndex (u v w : ℕ) : ℕ := by
  classical
  exact Nat.find ⟨u + 1 + 2 * v + 3 * w, clearingCondition_sufficient u v w⟩

theorem firstClearingIndex_spec (u v w : ℕ) :
    ClearingCondition u v w (firstClearingIndex u v w) := by
  classical
  exact Nat.find_spec ⟨u + 1 + 2 * v + 3 * w, clearingCondition_sufficient u v w⟩

theorem firstClearingIndex_minimal {u v w a : ℕ} (ha : ClearingCondition u v w a) :
    firstClearingIndex u v w ≤ a := by
  classical
  exact Nat.find_min' ⟨u + 1 + 2 * v + 3 * w, clearingCondition_sufficient u v w⟩ ha

theorem firstClearingIndex_le_sufficient (u v w : ℕ) :
    firstClearingIndex u v w ≤ u + 1 + 2 * v + 3 * w :=
  firstClearingIndex_minimal (clearingCondition_sufficient u v w)

/-- Because the three comparisons persist with the scale, their first valid
index characterises every later valid index. -/
theorem clearingCondition_iff_firstClearingIndex_le {u v w a : ℕ} :
    ClearingCondition u v w a ↔ firstClearingIndex u v w ≤ a := by
  constructor
  · exact firstClearingIndex_minimal
  · intro h
    exact clearingCondition_mono h (firstClearingIndex_spec u v w)

/-- Exact denominator of the unscaled rational representative. -/
theorem rationalTailState_den {N : ℤ} {D a : ℕ} (hD : 0 < D)
    (hcop : Nat.Coprime N.natAbs D) (ha : 1 ≤ a) :
    (rationalTailState N D a).den = D / Nat.gcd D (heightNormalizer235 a) := by
  obtain ⟨z, hz⟩ := heightNormalizer235_mul_windowMass_eq_int 1 (a - 1)
  have haeq : 1 + (a - 1) = a := by omega
  rw [haeq] at hz
  have heq : rationalTailState N D a =
      (heightNormalizer235 a : ℚ) * (N : ℚ) / (D : ℚ) -
        (heightNormalizer235 a : ℤ) - (z : ℤ) := by
    rw [rationalTailState, mul_sub, mul_sub, hz]
    push_cast
    ring
  rw [heq, Rat.sub_intCast_den, Rat.sub_intCast_den]
  exact den_nat_mul_int_div_nat hD hcop

/-- Exact denominator formulas from the long paper.  The first equality is for
`X_a`; the second is for the reduced state `B X_a`. -/
theorem exact_denominators {N : ℤ} {M B a : ℕ}
    (hM : 0 < M) (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (M * B)) (ha : 1 ≤ a) :
    (rationalTailState N (M * B) a).den =
        M * B / Nat.gcd M (heightNormalizer235 a) ∧
      ((B : ℚ) * rationalTailState N (M * B) a).den =
        M / Nat.gcd M (heightNormalizer235 a) := by
  have hD : 0 < M * B := Nat.mul_pos hM hB
  have hBh : Nat.Coprime B (heightNormalizer235 a) :=
    coprime_heightNormalizer235 hB30 ha
  have hgcd : Nat.gcd (M * B) (heightNormalizer235 a) =
      Nat.gcd M (heightNormalizer235 a) := by
    exact hBh.gcd_mul_right_cancel M
  constructor
  · rw [rationalTailState_den hD hcop ha, hgcd]
  · obtain ⟨z, hz⟩ := heightNormalizer235_mul_windowMass_eq_int 1 (a - 1)
    have haeq : 1 + (a - 1) = a := by omega
    rw [haeq] at hz
    have hMne : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have hBne : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
    have heq : (B : ℚ) * rationalTailState N (M * B) a =
        (heightNormalizer235 a : ℚ) * (N : ℚ) / (M : ℚ) -
          ((B * heightNormalizer235 a : ℕ) : ℤ) - ((B * z : ℕ) : ℤ) := by
      rw [rationalTailState, mul_sub, mul_sub, hz]
      push_cast
      field_simp [hMne, hBne]
    have hcopM : Nat.Coprime N.natAbs M :=
      Nat.Coprime.of_dvd_right (dvd_mul_right M B) hcop
    rw [heq, Rat.sub_intCast_den, Rat.sub_intCast_den]
    exact den_nat_mul_int_div_nat hM hcopM

/-- The scaled state is integral exactly when the smooth denominator divides
its half-height normalizer. -/
theorem scaled_state_den_eq_one_iff {N : ℤ} {M B a : ℕ}
    (hM : 0 < M) (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (M * B)) (ha : 1 ≤ a) :
    ((B : ℚ) * rationalTailState N (M * B) a).den = 1 ↔
      M ∣ heightNormalizer235 a := by
  rw [(exact_denominators hM hB hB30 hcop ha).2]
  constructor
  · intro h
    have hgcdDvd : Nat.gcd M (heightNormalizer235 a) ∣ M :=
      Nat.gcd_dvd_left _ _
    have hgcd : Nat.gcd M (heightNormalizer235 a) = M :=
      Nat.eq_of_dvd_of_div_eq_one hgcdDvd h
    exact Nat.gcd_eq_left_iff_dvd.mp hgcd
  · intro h
    rw [Nat.gcd_eq_left h, Nat.div_self hM]

/-- Literal first-clearing statement from the short paper and the long-paper
proposition.  The reduced state has denominator one exactly from the first
integer-power threshold onward. -/
theorem scaled_state_den_eq_one_iff_firstClearingIndex_le
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a) :
    ((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den = 1 ↔
      firstClearingIndex u v w ≤ a := by
  rw [scaled_state_den_eq_one_iff (by positivity) hB hB30 hcop ha]
  rw [smoothPart_dvd_heightNormalizer235_iff ha]
  rw [← clearingCondition_iff_firstClearingIndex_le]
  simp only [ClearingCondition, ha, true_and]

/-- Equivalent integer-valued form of the first-clearing statement. -/
theorem scaled_state_is_integer_iff_firstClearingIndex_le
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a) :
    (∃ z : ℤ,
      (B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a = (z : ℚ)) ↔
      firstClearingIndex u v w ≤ a := by
  let q : ℚ := (B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a
  have hden : q.den = 1 ↔ firstClearingIndex u v w ≤ a := by
    simpa [q] using
      (scaled_state_den_eq_one_iff_firstClearingIndex_le hB hB30 hcop ha)
  change (∃ z : ℤ, q = (z : ℚ)) ↔ firstClearingIndex u v w ≤ a
  constructor
  · rintro ⟨z, hz⟩
    rw [hz] at hden
    exact hden.mp (Rat.den_intCast z)
  · intro h
    have hq : q.den = 1 := hden.mpr h
    exact ⟨q.num, ((Rat.den_eq_one_iff q).mp hq).symm⟩

/-- Combined literal bridge for the paper proposition: under its rational-value
and lowest-terms hypotheses, the rational representative is the real tail
state, has both displayed reduced denominators, and clears precisely from the
minimal integer-power index onward. -/
theorem exact_denominators_and_minimal_clearing
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a)
    (hval : paperSeries235 =
      (N : ℝ) / ((2 ^ u * 3 ^ v * 5 ^ w * B : ℕ) : ℝ)) :
    ((rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a : ℚ) : ℝ) =
        trueNormalizedState a ∧
      (rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w * B) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      ((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      (((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den = 1 ↔
        firstClearingIndex u v w ≤ a) := by
  have hcast := rationalTailState_cast (N := N)
    (D := 2 ^ u * 3 ^ v * 5 ^ w * B) (a := a) (by positivity) ha hval
  have hdens := exact_denominators (N := N)
    (M := 2 ^ u * 3 ^ v * 5 ^ w) (B := B) (a := a)
    (by positivity) hB hB30 hcop ha
  exact ⟨hcast, hdens.1, hdens.2,
    scaled_state_den_eq_one_iff_firstClearingIndex_le hB hB30 hcop ha⟩

end ErdosProblems.Erdos269.PaperR13
