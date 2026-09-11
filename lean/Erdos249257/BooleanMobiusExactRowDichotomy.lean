import Erdos249257.BooleanMobiusExactRowCrossing
import Erdos249257.BooleanMobiusExactRowDoubling
import Erdos249257.BooleanMobiusExactRowRankTwo

/-!
# Sign dichotomy for exact Boolean--Möbius rows

This module combines the independent exact-row producers.  A row below one
half admits a literal doubling-window extension, while a row above one half
can be recycled through its first crossing.  The result is a transition
dichotomy, not a cofinality assertion: the crossing branch need not increase
the endpoint.
-/

namespace Erdos249257

/-- Every exact row of endpoint at least six has one of the two available
finite continuations.  If the witness's finite value is below one half, the
literal upper-window construction gives an exact row at `2n-1`.  If it is
above one half, the first crossing gives a recycled exact row at `2c-2` for
some `4 ≤ c ≤ n`.

The second endpoint is intentionally not claimed to exceed `n`; a separate
progress input is still required before this transition can yield cofinal
exact rows. -/
theorem exactLocalMersenneHalfRow_double_or_recycle
    {n : ℕ} (hn : 6 ≤ n)
    (hrow : ExactLocalMersenneHalfRow n) :
    ExactLocalMersenneHalfRow (2 * n - 1) ∨
      ∃ c : ℕ,
        4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2) := by
  obtain ⟨D, htwo, hD, hquot⟩ :=
    exactLocalMersenneHalfRow_exists_support_with_two (by omega) hrow
  have hzero : 0 ∉ D := by
    intro hzero
    have := (hD 0 hzero).1
    omega
  have hne : localMersennePrefixValue D ≠ (1 / 2 : ℚ) := by
    intro heq
    have hodd := finiteErdosSum_den_odd D hzero
    rw [← localMersennePrefixValue_eq_finiteErdosSum, heq] at hodd
    obtain ⟨k, hk⟩ := hodd
    norm_num at hk
    omega
  rcases lt_or_gt_of_ne hne with hbelow | habove
  · exact Or.inl
      (exactLocalMersenneHalfRow_two_mul_sub_one_of_exact_below
        hn hD htwo hquot hbelow)
  · exact Or.inr (exists_skippedCoreExactRow_of_value_above hD habove)

/-! ## Why the transition still needs a progress input -/

/-- A one-point predicate satisfying the same endpoint transition shape as
`exactLocalMersenneHalfRow_double_or_recycle`.  It is the smallest explicit
falsifier for any attempt to infer cofinal exact rows from that dichotomy
alone: at endpoint six the recycling arm may return to endpoint six through
`c = 4` forever. -/
def boundedDoubleOrRecycleModel (n : ℕ) : Prop := n = 6

theorem boundedDoubleOrRecycleModel_seed :
    boundedDoubleOrRecycleModel 6 := by
  rfl

theorem boundedDoubleOrRecycleModel_transition
    {n : ℕ} (hn : 6 ≤ n)
    (hmodel : boundedDoubleOrRecycleModel n) :
    boundedDoubleOrRecycleModel (2 * n - 1) ∨
      ∃ c : ℕ,
        4 ≤ c ∧ c ≤ n ∧ boundedDoubleOrRecycleModel (2 * c - 2) := by
  unfold boundedDoubleOrRecycleModel at hmodel ⊢
  subst n
  exact Or.inr ⟨4, by omega, by omega, by omega⟩

/-- The bounded transition model is not cofinal.  Consequently the transition
shape proved above, even together with an endpoint-six seed, cannot by itself
feed `half_mem_mersenneAchievementSet_of_cofinalExactLocalRows`.  A future
consumer must supply strict endpoint progress or cofinality by an independent
arithmetic argument. -/
theorem boundedDoubleOrRecycleModel_not_cofinal :
    ¬ ∀ N : ℕ, ∃ n : ℕ,
      N ≤ n ∧ boundedDoubleOrRecycleModel n := by
  intro hcofinal
  obtain ⟨n, hn, hmodel⟩ := hcofinal 7
  unfold boundedDoubleOrRecycleModel at hmodel
  omega

/-- **Finite-to-cofinal no-go.**  There exists a seeded, bounded endpoint
predicate satisfying the exact double-or-recycle transition schema.  This
packages the route falsifier in the same logical shape used by the exact-row
development. -/
theorem exists_seeded_bounded_double_or_recycle_model :
    ∃ P : ℕ → Prop,
      P 6 ∧
      (∀ n : ℕ, 6 ≤ n → P n →
        P (2 * n - 1) ∨
          ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ P (2 * c - 2)) ∧
      ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n := by
  exact ⟨boundedDoubleOrRecycleModel,
    boundedDoubleOrRecycleModel_seed,
    fun _n hn hmodel ↦
      boundedDoubleOrRecycleModel_transition hn hmodel,
    boundedDoubleOrRecycleModel_not_cofinal⟩

#print axioms exactLocalMersenneHalfRow_double_or_recycle
#print axioms boundedDoubleOrRecycleModel_transition
#print axioms boundedDoubleOrRecycleModel_not_cofinal
#print axioms exists_seeded_bounded_double_or_recycle_model

end Erdos249257
