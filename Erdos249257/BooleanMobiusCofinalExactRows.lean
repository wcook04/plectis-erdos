import Erdos249257.BooleanMobiusGlobalRepair

/-!
# Cofinal exact Boolean--Möbius rows

This module isolates a weaker consumer than a coherent global repair
trajectory.  It needs only exact finite quotient rows at arbitrarily large
endpoints.  The supports at different endpoints need not agree at any
coordinate.

For an exact row `D` at endpoint `n`, the quotient identity

`localPrefixQuotient D n = 2^(n-1) - 1`

and the fractional-part estimate from `BooleanMobiusGlobalRepair` give

`|localMersennePrefixValue D - 1/2| <= (n+1)/2^n`.

Thus any cofinal supply of exact rows produces achievement-set points tending
to `1/2`.  Closedness then gives exact membership.  This separates the
finite Boolean producer from every coherence or frozen-diagonal requirement.
-/

namespace Erdos249257

open Filter Set

/-! ## Producer socket -/

/-- An exact finite Boolean quotient row at endpoint `n`. -/
def ExactLocalMersenneHalfRow (n : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1) - 1

/-- Exact Boolean quotient rows occur at arbitrarily large endpoints.  No
compatibility is imposed between the witnesses at different endpoints. -/
def CofinalExactLocalMersenneHalfRows : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ExactLocalMersenneHalfRow n

/-! ## Finite row values -/

/-- The real Mersenne value carried by a finite exact-row support. -/
noncomputable def exactLocalMersenneRowValue (D : Finset ℕ) : ℝ :=
  ((localMersennePrefixValue D : ℚ) : ℝ)

theorem exactLocalMersenneRowValue_mem_mersenneAchievementSet
    {D : Finset ℕ} (hD : ∀ d ∈ D, 2 ≤ d) :
    exactLocalMersenneRowValue D ∈ mersenneAchievementSet := by
  refine ⟨(↑D : Set ℕ), ?_, ?_⟩
  · intro hzero
    have := hD 0 hzero
    omega
  · rw [positiveMersenneSupportValue_eq_cast_finiteErdosSum]
    simp [exactLocalMersenneRowValue,
      localMersennePrefixValue_eq_finiteErdosSum]

theorem abs_exactLocalMersenneRowValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    |exactLocalMersenneRowValue D - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  exact abs_localMersennePrefixValue_sub_half_le hn hD hquot

/-! ## Cofinal closed-set consumer -/

/-- **Cofinal exact-row consumer.**  Arbitrarily large exact finite quotient
rows force `1/2` into the closed Mersenne achievement set.  The selected rows
may be mutually incompatible; only their endpoint lengths tend to infinity. -/
theorem half_mem_mersenneAchievementSet_of_cofinalExactLocalRows
    (hcofinal : CofinalExactLocalMersenneHalfRows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  unfold CofinalExactLocalMersenneHalfRows at hcofinal
  have hsupply : ∀ N : ℕ, ∃ n : ℕ,
      max N 2 ≤ n ∧ ExactLocalMersenneHalfRow n := fun N ↦
    hcofinal (max N 2)
  choose n hn hrow using hsupply
  simp only [ExactLocalMersenneHalfRow] at hrow
  choose D hD hquot using hrow
  let y : ℕ → ℝ := fun N ↦ exactLocalMersenneRowValue (D N)
  have hn2 : ∀ N : ℕ, 2 ≤ n N := by
    intro N
    exact (le_max_right N 2).trans (hn N)
  have hntop : Tendsto n atTop atTop := by
    exact tendsto_atTop_mono
      (fun N ↦ (le_max_left N 2).trans (hn N)) tendsto_id
  have hbound : ∀ N : ℕ,
      |y N - (1 : ℝ) / 2| ≤
        ((n N + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n N) := by
    intro N
    exact abs_exactLocalMersenneRowValue_sub_half_le
      (hn2 N) (hD N) (hquot N)
  have hy : Tendsto y atTop (nhds ((1 : ℝ) / 2)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have habs : Tendsto (fun N : ℕ ↦ |y N - (1 : ℝ) / 2|)
        atTop (nhds 0) := by
      apply squeeze_zero'
      · exact Filter.Eventually.of_forall fun N ↦ abs_nonneg _
      · exact Filter.Eventually.of_forall hbound
      · exact tendsto_nat_succ_div_two_pow_zero.comp hntop
    simpa [Real.norm_eq_abs] using habs
  exact isClosed_mersenneAchievementSet.mem_of_tendsto hy
    (Filter.Eventually.of_forall fun N ↦
      exactLocalMersenneRowValue_mem_mersenneAchievementSet
        (fun d hd ↦ (hD N d hd).1))

end Erdos249257
