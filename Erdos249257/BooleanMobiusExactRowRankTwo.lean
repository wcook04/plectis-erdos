import Erdos249257.BooleanMobiusSkipRow

/-!
# Rank two is forced in every nontrivial exact Boolean--Möbius row

The quotient target at endpoint `n` is already too large to be assembled
from ranks strictly above two.  Indeed, a finite support omitting rank two is
bounded by the complete real Mersenne tail after rank two, which is strictly
smaller than the rank-two weight `1/3`.  On the other hand, the exact quotient
identity at any endpoint `n ≥ 3` forces the scaled support value to be at least
`2^(n-1)-1`, and that target is at least `2^n/3`.

This removes the rank-two side condition from exact-row extension arguments.
-/

namespace Erdos249257

open scoped BigOperators

/-- Any exact local Mersenne quotient row at endpoint `n ≥ 3` contains rank
two.  The proof compares a support omitting rank two with the complete tail
after rank two, then contradicts the exact quotient target after scaling. -/
theorem two_mem_of_exact_localMersenneQuotient
    {D : Finset ℕ} {n : ℕ}
    (hn : 3 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    2 ∈ D := by
  classical
  by_contra htwo
  have hone : 1 ∉ D := by
    intro hone
    have := (hD 1 hone).1
    omega
  have honeSet : 1 ∉ (↑D : Set ℕ) := by simpa using hone
  have htwoSet : 2 ∉ (↑D : Set ℕ) := by simpa using htwo
  have hvalueSuffix :
      positiveMersenneSupportValue (↑D : Set ℕ) =
        positiveMersenneSupportSuffix (↑D : Set ℕ) 2 := by
    simpa [Finset.sum_range_succ, honeSet, htwoSet] using
      (positiveMersenneSupportValue_eq_prefix_add_suffix
        (↑D : Set ℕ) 2)
  have hvalueUpper :
      positiveMersenneSupportValue (↑D : Set ℕ) < (1 / 3 : ℝ) := by
    rw [hvalueSuffix]
    calc
      positiveMersenneSupportSuffix (↑D : Set ℕ) 2
          ≤ mersenneTail 2 :=
        positiveMersenneSupportSuffix_le_tail (↑D : Set ℕ) 2
      _ < mersenneWeight 2 := mersenneTail_lt_weight (by omega)
      _ = (1 / 3 : ℝ) := by norm_num [mersenneWeight]
  have hvalueCast :
      positiveMersenneSupportValue (↑D : Set ℕ) =
        (((localMersennePrefixValue D : ℚ)) : ℝ) := by
    calc
      positiveMersenneSupportValue (↑D : Set ℕ) =
          ((finiteErdosSum D 2 : ℚ) : ℝ) :=
        positiveMersenneSupportValue_eq_cast_finiteErdosSum D
      _ = (((localMersennePrefixValue D : ℚ)) : ℝ) := by
        rw [localMersennePrefixValue_eq_finiteErdosSum]
  have hvalueUpper' :
      (((localMersennePrefixValue D : ℚ)) : ℝ) < (1 / 3 : ℝ) := by
    rw [← hvalueCast]
    exact hvalueUpper
  have hDtwo : ∀ d ∈ D, 2 ≤ d := fun d hd ↦ (hD d hd).1
  have hscaled :=
    scaled_localMersennePrefixValue (D := D) (M := n) hDtwo
  have hfractionNonneg : 0 ≤ localFractionMass D n := by
    unfold localFractionMass
    exact Finset.sum_nonneg fun d hd ↦
      (localMersenneFraction_pos (M := n) (hDtwo d hd)).le
  have hquotLeRat :
      (localPrefixQuotient D n : ℚ) ≤
        (2 : ℚ) ^ n * localMersennePrefixValue D := by
    rw [hscaled]
    exact le_add_of_nonneg_right hfractionNonneg
  have hquotLeReal :
      ((localPrefixQuotient D n : ℕ) : ℝ) ≤
        (2 : ℝ) ^ n * (((localMersennePrefixValue D : ℚ)) : ℝ) := by
    exact_mod_cast hquotLeRat
  have hscaledUpper :
      (2 : ℝ) ^ n * (((localMersennePrefixValue D : ℚ)) : ℝ) <
        (2 : ℝ) ^ n * (1 / 3 : ℝ) :=
    mul_lt_mul_of_pos_left hvalueUpper' (by positivity)
  have hthreeQuotLt :
      3 * ((localPrefixQuotient D n : ℕ) : ℝ) < (2 : ℝ) ^ n := by
    nlinarith
  have hfour : 4 ≤ 2 ^ (n - 1) := by
    simpa using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 2 ≤ n - 1))
  have hpowSplit : 2 ^ n = 2 ^ (n - 1) * 2 := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1 <;> omega
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
  have htargetNat :
      2 ^ n ≤ 3 * (2 ^ (n - 1) - 1) := by
    rw [hpowSplit]
    omega
  have htargetReal :
      (2 : ℝ) ^ n ≤
        3 * (((2 ^ (n - 1) - 1 : ℕ) : ℝ)) := by
    exact_mod_cast htargetNat
  rw [hquot] at hthreeQuotLt
  nlinarith

/-- Witness form: an exact-row proposition at endpoint `n ≥ 3` admits a
witness support in which rank two is explicitly present. -/
theorem exactLocalMersenneHalfRow_exists_support_with_two
    {n : ℕ} (hn : 3 ≤ n)
    (hrow : ExactLocalMersenneHalfRow n) :
    ∃ D : Finset ℕ,
      2 ∈ D ∧
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1) - 1 := by
  obtain ⟨D, hD, hquot⟩ := hrow
  exact ⟨D, two_mem_of_exact_localMersenneQuotient hn hD hquot, hD, hquot⟩

end Erdos249257
