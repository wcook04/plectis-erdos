import Erdos249257.BooleanMobiusLocalRepair

/-!
# Exact upper-half fill from a skipped Boolean Mersenne core

Suppose a Boolean support `D ⊆ {2, …, c - 1}` is still below one half,
but its deficit is smaller than the next Mersenne weight at rank `c`.  At the
usual odd endpoint `2c - 1`, the rank-`c` quotient is the top binary coin and
can obstruct the direct suffix fill.  One row earlier, at `M = 2c - 2`, the
same deficit is strictly below the complete upper-half window.  Hence it has
an exact Boolean binary realization of width `c - 1`.

This is an unconditional finite-row producer.  It does not assert that the
skipped ranks are cofinal; that is the remaining local-to-global supply issue.
-/

namespace Erdos249257

open scoped BigOperators

/-- At row `2c - 2`, the integral quotient of the rank-`c` Mersenne weight is
the largest power strictly below the upper-half window. -/
theorem localMersenneQuotient_two_mul_sub_two_self
    {c : ℕ} (hc : 4 ≤ c) :
    localMersenneQuotient (2 * c - 2) c = 2 ^ (c - 2) := by
  let P := 2 ^ (c - 2)
  let q := 2 ^ c - 1
  have hqpos : 0 < q := by
    dsimp [q]
    exact Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by omega))
  have hpow : 2 ^ (2 * c - 2) = P * 2 ^ c := by
    dsimp [P]
    rw [show 2 * c - 2 = (c - 2) + c by omega, pow_add]
  have hdecomp : 2 ^ (2 * c - 2) = P * q + P := by
    rw [hpow]
    dsimp [q]
    have hone : 1 ≤ 2 ^ c := Nat.one_le_pow _ _ (by norm_num)
    calc
      P * 2 ^ c = P * ((2 ^ c - 1) + 1) := by
        rw [Nat.sub_add_cancel hone]
      _ = P * (2 ^ c - 1) + P := by ring
  have hPltq : P < q := by
    dsimp [P, q]
    have hmono : 2 ^ (c - 2) ≤ 2 ^ (c - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsplit : 2 ^ c = 2 ^ (c - 1) * 2 := by
      calc
        2 ^ c = 2 ^ ((c - 1) + 1) := by congr 1 <;> omega
        _ = 2 ^ (c - 1) * 2 := by rw [pow_succ]
    have htwo : 2 ≤ 2 ^ (c - 1) := by
      simpa using
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ c - 1))
    omega
  unfold localMersenneQuotient
  change 2 ^ (2 * c - 2) / q = P
  apply Nat.div_eq_of_lt_le
  · rw [hdecomp]
    exact Nat.le_add_right _ _
  · rw [hdecomp]
    calc
      P * q + P < P * q + q := Nat.add_lt_add_left hPltq _
      _ = (P + 1) * q := by ring

/-- Every local Mersenne residue is below one.  This local copy keeps the
skipped-core producer independent of the later global-repair consumer. -/
theorem localMersenneFraction_lt_one_skippedCore
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneFraction M d < 1 := by
  unfold localMersenneFraction
  have hrlt : M % d < d := Nat.mod_lt _ (by omega)
  have hrle : M % d ≤ d - 1 := by omega
  have hpowle : 2 ^ (M % d) ≤ 2 ^ (d - 1) :=
    Nat.pow_le_pow_right (by norm_num) hrle
  have hsplit : 2 ^ d = 2 ^ (d - 1) * 2 := by
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (d - 1) * 2 := by rw [pow_succ]
  have hhalf : 2 ≤ 2 ^ (d - 1) := by
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ d - 1))
  have hltNat : 2 ^ (M % d) < 2 ^ d - 1 := by omega
  rw [div_lt_one]
  · exact_mod_cast hltNat
  · exact_mod_cast (Nat.sub_pos_of_lt
      (one_lt_pow₀ (by omega) (by omega) : 1 < 2 ^ d))

/-- The residue mass of a Boolean core is at most its cardinality. -/
theorem localFractionMass_le_card_skippedCore
    {D : Finset ℕ} {M : ℕ} (hD : ∀ d ∈ D, 2 ≤ d) :
    localFractionMass D M ≤ (D.card : ℚ) := by
  unfold localFractionMass
  calc
    (∑ d ∈ D, localMersenneFraction M d)
        ≤ ∑ _d ∈ D, (1 : ℚ) := by
          exact Finset.sum_le_sum fun d hd ↦
            (localMersenneFraction_lt_one_skippedCore (M := M)
              (hD d hd)).le
    _ = (D.card : ℚ) := by simp

/-- A support contained in the integer interval `[2,c)` has at most `c-2`
elements. -/
theorem card_le_sub_two_of_mem_lt
    {D : Finset ℕ} {c : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c) :
    D.card ≤ c - 2 := by
  have hsubset : D ⊆ Finset.Ico 2 c := by
    intro d hd
    exact Finset.mem_Ico.mpr (hD d hd)
  calc
    D.card ≤ (Finset.Ico 2 c).card := Finset.card_le_card hsubset
    _ = c - 2 := by simp

/-- **Skipped-core upper-half capacity.**  If `D ⊆ [2,c)` lies below one
half and the missing mass is smaller than the rank-`c` Mersenne weight, then
the exact binary suffix at row `2c-2` fits strictly in `c-1` bits.

The proof is the finite identity

`A = 2^M (1/2 - value(D)) + fractionalMass(D,M) - 1`

with `M=2c-2`.  The first term is below `2^(c-2)+1`, while the fractional
mass is at most `|D| ≤ c-2 ≤ 2^(c-2)`. -/
theorem localBinarySuffix_two_mul_sub_two_lt_upperHalfCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 1) := by
  let M := 2 * c - 2
  let T := 2 ^ (M - 1)
  let P := 2 ^ (c - 2)
  let Q := localPrefixQuotient D M
  let F := localFractionMass D M
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hDtwo : ∀ d ∈ D, 2 ≤ d := fun d hd ↦ (hD d hd).1
  have hscale :
      (2 : ℚ) ^ M * localMersennePrefixValue D = (Q : ℚ) + F := by
    simpa [Q, F] using
      (scaled_localMersennePrefixValue (D := D) (M := M) hDtwo)
  have hhalfScale : (2 : ℚ) ^ M * (1 / 2 : ℚ) = (T : ℚ) := by
    dsimp [T]
    calc
      (2 : ℚ) ^ M * (1 / 2 : ℚ) =
          2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by congr 2 <;> omega
      _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
      _ = ((2 ^ (M - 1) : ℕ) : ℚ) := by norm_num
  have hFnonneg : 0 ≤ F := by
    dsimp [F, localFractionMass]
    exact Finset.sum_nonneg fun d hd ↦
      (localMersenneFraction_pos (M := M) (hDtwo d hd)).le
  have hFcard : F ≤ (D.card : ℚ) := by
    simpa [F] using
      (localFractionMass_le_card_skippedCore (D := D) (M := M) hDtwo)
  have hscaledBelow : (Q : ℚ) + F < (T : ℚ) := by
    have h := mul_lt_mul_of_pos_left hbelow
      (pow_pos (by norm_num : (0 : ℚ) < 2) M)
    rw [hscale, hhalfScale] at h
    exact h
  have hQltCast : (Q : ℚ) < (T : ℚ) := by linarith
  have hQlt : Q < T := by exact_mod_cast hQltCast
  have hQle : Q ≤ T := hQlt.le
  have honeSub : 1 ≤ T - Q := by omega
  have hAcast :
      ((localBinarySuffix D 1 M : ℕ) : ℚ) =
        (T : ℚ) - (Q : ℚ) - 1 := by
    unfold localBinarySuffix
    change (((T - Q - 1 : ℕ) : ℚ)) = _
    rw [Nat.cast_sub honeSub, Nat.cast_sub hQle]
    norm_num
  have hdeficit :
      (2 : ℚ) ^ M * ((1 / 2 : ℚ) - localMersennePrefixValue D) =
        (T : ℚ) - (Q : ℚ) - F := by
    rw [mul_sub, hhalfScale, hscale]
    ring
  have hquot : localMersenneQuotient M c = P := by
    simpa [M, P] using localMersenneQuotient_two_mul_sub_two_self hc
  have hfraclt : localMersenneFraction M c < 1 :=
    localMersenneFraction_lt_one_skippedCore (M := M) (by omega)
  have hweightDecomp :=
    scaled_mersenneWeightRat_eq_quotient_add_fraction (M := M) (d := c)
      (by omega : 2 ≤ c)
  have hscaledWeight :
      (2 : ℚ) ^ M * mersenneWeightRat c < (P : ℚ) + 1 := by
    calc
      (2 : ℚ) ^ M * mersenneWeightRat c =
          (P : ℚ) + localMersenneFraction M c := by
            simpa [hquot] using hweightDecomp
      _ < (P : ℚ) + 1 := by linarith
  have hscaledSkip :
      (2 : ℚ) ^ M * ((1 / 2 : ℚ) - localMersennePrefixValue D) <
        (P : ℚ) + 1 := by
    have h := mul_lt_mul_of_pos_left hskip
      (pow_pos (by norm_num : (0 : ℚ) < 2) M)
    exact h.trans hscaledWeight
  have hAeq :
      ((localBinarySuffix D 1 M : ℕ) : ℚ) =
        (2 : ℚ) ^ M *
            ((1 / 2 : ℚ) - localMersennePrefixValue D) + F - 1 := by
    rw [hAcast, hdeficit]
    ring
  have hAlt :
      ((localBinarySuffix D 1 M : ℕ) : ℚ) <
        (P : ℚ) + (D.card : ℚ) := by
    rw [hAeq]
    linarith
  have hcard : D.card ≤ c - 2 := card_le_sub_two_of_mem_lt hD
  have hcpow : c - 2 ≤ P := by
    have h := nat_le_two_pow_pred (c - 1)
    dsimp [P]
    rw [show c - 1 - 1 = c - 2 by omega] at h
    omega
  have hcardP : D.card ≤ P := hcard.trans hcpow
  have hAltTwo :
      ((localBinarySuffix D 1 M : ℕ) : ℚ) < 2 * (P : ℚ) := by
    have hcardPCast : (D.card : ℚ) ≤ (P : ℚ) := by exact_mod_cast hcardP
    linarith
  have hnat : localBinarySuffix D 1 M < 2 * P := by exact_mod_cast hAltTwo
  have hcap : 2 ^ (c - 1) = 2 * P := by
    dsimp [P]
    rw [show c - 1 = (c - 2) + 1 by omega, pow_succ]
    ring
  simpa [M, hcap] using hnat

/-- The skipped-core suffix therefore has an exact Boolean word of the whole
upper-half width. -/
theorem exists_upperHalfBooleanWord_of_skippedCore
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    ∃ y : List ℕ,
      y.length = c - 1 ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      Nat.ofDigits 2 y = localBinarySuffix D 1 (2 * c - 2) := by
  exact exists_boolean_word_of_lt_two_pow
    (localBinarySuffix_two_mul_sub_two_lt_upperHalfCapacity
      hc hD hbelow hskip)

end Erdos249257
