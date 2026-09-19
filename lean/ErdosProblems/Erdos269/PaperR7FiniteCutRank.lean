import ErdosProblems.Erdos269.FiniteCutRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Paper-complete campaign, round 7: the complete finite cut-rank formula

Target: short-note `res:finite-cut-rank`.  This file generalises the supplied
rational interval-difference engine to an arbitrary field, proves independence
except for the two extreme columns, removes exactly that redundancy, and states
the result using `Matrix.rank`. Repetitions and permutations of columns are
handled by a column-range equality, not an extra independence assumption.

Validation: authored against Lean 4.29.1 / the packet's Mathlib pin; NOT compiled
in this return. No admitted statements or additional axioms are introduced.
-/

namespace ErdosProblems.Erdos269.PaperR7

open scoped BigOperators
open Module Submodule

variable {F : Type*} [Field F]

/-- A cut at `k`, with `m` rows. -/
def cutVector (c : F) (m k : ℕ) : Fin m → F :=
  fun i => if (i : ℕ) < k then 1 else c

/-- Compatibility with the already supplied rational cut columns. -/
theorem cutVector_rat (c : ℚ) (m k : ℕ) :
    cutVector c m k = ErdosProblems.Erdos269.cutCol (m := m) c k := rfl

/-- The discrete derivative detects exactly the interior cut at that row. -/
theorem cutVector_adjacent (c : F) {m j : ℕ} (hj : 0 < j) (hjm : j < m)
    (k : ℕ) :
    cutVector c m k ⟨j - 1, by omega⟩ - cutVector c m k ⟨j, hjm⟩ =
      if k = j then 1 - c else 0 := by
  unfold cutVector
  by_cases hkj : k = j
  · subst k
    simp [show j - 1 < j by omega]
  · by_cases hk : j < k
    · simp [hk, show j - 1 < k by omega, hkj]
    · simp [hk, show ¬ j - 1 < k by omega, hkj]

/-- An arbitrary linear relation has zero coefficient at every interior cut. -/
theorem cut_relation_interior (c : F) (hc : c ≠ 1) {m : ℕ}
    (E : Finset ℕ) (g : E → F)
    (hg : (∑ k : E, g k • cutVector c m k) = 0)
    (j : E) (hj : 0 < (j : ℕ)) (hjm : (j : ℕ) < m) : g j = 0 := by
  classical
  have hleft := congrFun hg (⟨(j : ℕ) - 1, by omega⟩ : Fin m)
  have hright := congrFun hg (⟨(j : ℕ), hjm⟩ : Fin m)
  have hdiff :
      (∑ k : E, g k *
        (cutVector c m k ⟨(j : ℕ) - 1, by omega⟩ -
         cutVector c m k ⟨(j : ℕ), hjm⟩)) = 0 := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hleft hright
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hleft, hright, sub_self]
  have hterm : ∀ k : E,
      g k *
        (cutVector c m k ⟨(j : ℕ) - 1, by omega⟩ -
         cutVector c m k ⟨(j : ℕ), hjm⟩) =
          if k = j then g j * (1 - c) else 0 := by
    intro k
    rw [cutVector_adjacent c hj hjm]
    by_cases hkj : k = j
    · subst k
      simp
    · have hval : (k : ℕ) ≠ (j : ℕ) := fun h => hkj (Subtype.ext h)
      simp [hkj, hval]
  simp_rw [hterm] at hdiff
  have hprod : g j * (1 - c) = 0 := by simpa using hdiff
  exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr (Ne.symm hc))

/-- Apart from the pair of extreme cuts, every set of cut columns is independent. -/
theorem cutVectors_linearIndependent (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    {m : ℕ} (hm : 0 < m) (E : Finset ℕ)
    (hbound : ∀ k ∈ E, k ≤ m) (hext : ¬ (0 ∈ E ∧ m ∈ E)) :
    LinearIndependent F (fun k : E => cutVector c m k) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have hinterior : ∀ k : E, 0 < (k : ℕ) → (k : ℕ) < m → g k = 0 :=
    fun k hk hkm => cut_relation_interior c hc1 E g hg k hk hkm
  by_cases hj0 : (j : ℕ) = 0
  · have h0 : 0 ∈ E := hj0 ▸ j.property
    have hnotm : m ∉ E := fun h => hext ⟨h0, h⟩
    have hother : ∀ k : E, k ≠ j → g k = 0 := by
      intro k hkj
      have hk0 : (k : ℕ) ≠ 0 := by
        intro h
        exact hkj (Subtype.ext (h.trans hj0.symm))
      have hkm : (k : ℕ) ≠ m := fun h => hnotm (h ▸ k.property)
      exact hinterior k (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne (hbound k k.property) hkm)
    have hrow := congrFun hg (⟨0, hm⟩ : Fin m)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hrow
    have hs : (∑ k : E, g k * cutVector c m k ⟨0, hm⟩) =
        g j * cutVector c m j ⟨0, hm⟩ := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [hother k hkj, zero_mul]
      · simp
    rw [hs] at hrow
    have hp : g j * c = 0 := by simpa [cutVector, hj0] using hrow
    exact (mul_eq_zero.mp hp).resolve_right hc0
  · by_cases hjm : (j : ℕ) = m
    · have hmE : m ∈ E := hjm ▸ j.property
      have hnot0 : 0 ∉ E := fun h => hext ⟨h, hmE⟩
      have hother : ∀ k : E, k ≠ j → g k = 0 := by
        intro k hkj
        have hk0 : (k : ℕ) ≠ 0 := fun h => hnot0 (h ▸ k.property)
        have hkm : (k : ℕ) ≠ m := by
          intro h
          exact hkj (Subtype.ext (h.trans hjm.symm))
        exact hinterior k (Nat.pos_of_ne_zero hk0)
          (lt_of_le_of_ne (hbound k k.property) hkm)
      have hrow := congrFun hg (⟨0, hm⟩ : Fin m)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hrow
      have hs : (∑ k : E, g k * cutVector c m k ⟨0, hm⟩) =
          g j * cutVector c m j ⟨0, hm⟩ := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          rw [hother k hkj, zero_mul]
        · simp
      rw [hs] at hrow
      simpa [cutVector, hjm, hm] using hrow
    · exact hinterior j (Nat.pos_of_ne_zero hj0)
        (lt_of_le_of_ne (hbound j j.property) hjm)

/-- Column-space description, independent of column ordering or repetitions. -/
noncomputable def cutSpan (c : F) (m : ℕ) (E : Finset ℕ) :
    Submodule F (Fin m → F) :=
  Submodule.span F (Set.range (fun k : E => cutVector c m k))

/-- If both extremes occur, erasing cut zero does not alter the span. -/
theorem cutSpan_erase_zero (c : F) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hmE : m ∈ E) :
    cutSpan c m E = cutSpan c m (E.erase 0) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    by_cases hk0 : (k : ℕ) = 0
    · have hmerase : m ∈ E.erase 0 := Finset.mem_erase.mpr ⟨Nat.ne_of_gt hm, hmE⟩
      have hmem : cutVector c m m ∈ cutSpan c m (E.erase 0) :=
        Submodule.subset_span ⟨⟨m, hmerase⟩, rfl⟩
      have heq : cutVector c m (k : ℕ) = c • cutVector c m m := by
        ext i
        simp [cutVector, hk0, i.isLt]
      show cutVector c m (k : ℕ) ∈ (cutSpan c m (E.erase 0) : Set (Fin m → F))
      rw [SetLike.mem_coe, heq]
      exact Submodule.smul_mem _ _ hmem
    · exact Submodule.subset_span ⟨⟨k, Finset.mem_erase.mpr ⟨hk0, k.property⟩⟩, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨k, Finset.mem_of_mem_erase k.property⟩, rfl⟩

/-- Complete field-general formula, including the single extreme-column defect. -/
theorem finrank_cutSpan (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    {m : ℕ} (hm : 0 < m) (E : Finset ℕ)
    (hbound : ∀ k ∈ E, k ≤ m) :
    Module.finrank F (cutSpan c m E) =
      E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0 := by
  classical
  by_cases hext : 0 ∈ E ∧ m ∈ E
  · rw [if_pos hext, cutSpan_erase_zero c hm E hext.2]
    have hb : ∀ k ∈ E.erase 0, k ≤ m :=
      fun k hk => hbound k (Finset.mem_of_mem_erase hk)
    have hi := cutVectors_linearIndependent c hc0 hc1 hm (E.erase 0) hb (by simp)
    change Module.finrank F
      (Submodule.span F (Set.range (fun k : E.erase 0 => cutVector c m k))) = _
    rw [finrank_span_eq_card hi, Fintype.card_coe, Finset.card_erase_of_mem hext.1]
  · rw [if_neg hext, Nat.sub_zero]
    exact (finrank_span_eq_card
      (cutVectors_linearIndependent c hc0 hc1 hm E hbound hext)).trans
        (Fintype.card_coe E)

/-- Literal `Matrix.rank` version of short-note `res:finite-cut-rank`.
The range equality says exactly that `E` is the set of cuts present. -/
theorem rank_cutMatrix {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutVector c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0 := by
  rw [Matrix.rank_eq_finrank_span_cols, hcols]
  exact finrank_cutSpan c hc0 hc1 hm E hbound

end ErdosProblems.Erdos269.PaperR7
