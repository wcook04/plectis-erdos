import Mathlib

/-!
# Finite block coupling for the sparse-rationalisation proposition

NEW uncompiled proof source. These estimates discharge the finite
combinatorial/statistical part of `res:sparserationalisation`; they do NOT
construct the sparse support or prove its analytic density bounds. The
coverage file therefore keeps the displayed proposition incomplete.
-/

open scoped BigOperators
open Finset

namespace ErdosProblems.Erdos251.PaperR7

noncomputable section

/-- Starting indices whose length-m block meets the finite changed set. -/
def affectedStarts (I S : Finset ℕ) (m : ℕ) : Finset ℕ := by
  classical
  exact I.filter (fun N => ∃ i ∈ range m, N + i ∈ S)

theorem affectedStarts_subset (I S : Finset ℕ) (m : ℕ) :
    affectedStarts I S m ⊆ I := Finset.filter_subset _ _

/-- Each changed coordinate affects at most m starting positions. There is
no probabilistic independence or assumption about prime gaps here. -/
theorem affectedStarts_card_le (I S : Finset ℕ) (m : ℕ) :
    (affectedStarts I S m).card ≤ m * S.card := by
  classical
  have hsub : affectedStarts I S m ⊆
      (range m).biUnion (fun i => S.image (fun k => k - i)) := by
    intro N hN
    obtain ⟨_hNI, i, him, his⟩ := mem_filter.mp hN
    apply mem_biUnion.mpr
    refine ⟨i, him, mem_image.mpr ⟨N + i, his, ?_⟩⟩
    omega
  calc
    (affectedStarts I S m).card ≤
        ((range m).biUnion (fun i => S.image (fun k => k - i))).card := card_le_card hsub
    _ ≤ ∑ i ∈ range m, (S.image (fun k => k - i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ range m, S.card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
    _ = m * S.card := by simp

/-- An arbitrary bounded statistic of unnormalised blocks changes only at
affected starts. Tests may depend on the index N as well as the block. -/
theorem block_test_sum_difference_le {α : Type*}
    (a b : ℕ → α) (I S : Finset ℕ) (m : ℕ)
    (hS : ∀ N ∈ I, ∀ i : Fin m, a (N + i.val) ≠ b (N + i.val) → N + i.val ∈ S)
    (Φ : ℕ → (Fin m → α) → ℝ)
    (ha : ∀ N ∈ I, |Φ N (fun i => a (N + i.val))| ≤ 1)
    (hb : ∀ N ∈ I, |Φ N (fun i => b (N + i.val))| ≤ 1) :
    |(∑ N ∈ I, Φ N (fun i => a (N + i.val))) -
      (∑ N ∈ I, Φ N (fun i => b (N + i.val)))| ≤
      2 * (m : ℝ) * S.card := by
  classical
  let B := affectedStarts I S m
  have hBsub : B ⊆ I := affectedStarts_subset I S m
  have hpoint : ∀ N ∈ I,
      |Φ N (fun i => a (N + i.val)) - Φ N (fun i => b (N + i.val))| ≤
        if N ∈ B then (2 : ℝ) else 0 := by
    intro N hN
    by_cases hNB : N ∈ B
    · rw [if_pos hNB]
      have htri : |Φ N (fun i => a (N + i.val)) - Φ N (fun i => b (N + i.val))| ≤
          |Φ N (fun i => a (N + i.val))| + |Φ N (fun i => b (N + i.val))| := by
        simpa using abs_sub_le (Φ N (fun i => a (N + i.val))) 0
          (Φ N (fun i => b (N + i.val)))
      linarith [ha N hN, hb N hN]
    · rw [if_neg hNB]
      have heq : (fun i : Fin m => a (N + i.val)) = (fun i => b (N + i.val)) := by
        funext i
        by_contra hne
        apply hNB
        exact mem_filter.mpr ⟨hN, i.val, mem_range.mpr i.isLt, hS N hN i hne⟩
      rw [heq, sub_self, abs_zero]
  have hfilter : I.filter (fun N => N ∈ B) = B := by
    ext N
    simp only [mem_filter]
    exact ⟨And.right, fun h => ⟨hBsub h, h⟩⟩
  have hcount : (B.card : ℝ) ≤ (m : ℝ) * S.card := by
    exact_mod_cast affectedStarts_card_le I S m
  calc
    _ = |∑ N ∈ I, (Φ N (fun i => a (N + i.val)) -
        Φ N (fun i => b (N + i.val)))| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ N ∈ I, |Φ N (fun i => a (N + i.val)) -
        Φ N (fun i => b (N + i.val))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ N ∈ I, if N ∈ B then (2 : ℝ) else 0 := Finset.sum_le_sum hpoint
    _ = 2 * B.card := by
      rw [← Finset.sum_filter, hfilter]
      simp [mul_comm]
    _ ≤ _ := by linarith

/-- Event counts with classical membership made explicit in the definition. -/
def eventStarts {α : Type*} (a : ℕ → α) (I : Finset ℕ) (m : ℕ)
    (event : Set (Fin m → α)) : Finset ℕ := by
  classical
  exact I.filter (fun N => (fun i : Fin m => a (N + i.val)) ∈ event)

/-- Cardinality discrepancy for every subset of the block alphabet. This
is the direct finite total-variation estimate, with no normalisation or
algebraic-degree restriction on the event. -/
theorem block_event_count_difference_le {α : Type*}
    (a b : ℕ → α) (I S : Finset ℕ) (m : ℕ)
    (hS : ∀ N ∈ I, ∀ i : Fin m, a (N + i.val) ≠ b (N + i.val) → N + i.val ∈ S)
    (event : Set (Fin m → α)) :
    |((eventStarts a I m event).card : ℤ) - (eventStarts b I m event).card| ≤
      (m * S.card : ℕ) := by
  classical
  let A := eventStarts a I m event
  let B := eventStarts b I m event
  let D := affectedStarts I S m
  have hdiff : A \ B ⊆ D := by
    intro N hN
    obtain ⟨hNA, hNB⟩ := mem_sdiff.mp hN
    obtain ⟨hNI, hAE⟩ := mem_filter.mp hNA
    by_contra hND
    have heq : (fun i : Fin m => a (N + i.val)) = (fun i => b (N + i.val)) := by
      funext i
      by_contra hne
      exact hND (mem_filter.mpr ⟨hNI, i.val, mem_range.mpr i.isLt, hS N hNI i hne⟩)
    apply hNB
    exact mem_filter.mpr ⟨hNI, by rw [← heq]; exact hAE⟩
  have hdiff' : B \ A ⊆ D := by
    intro N hN
    obtain ⟨hNB, hNA⟩ := mem_sdiff.mp hN
    obtain ⟨hNI, hBE⟩ := mem_filter.mp hNB
    by_contra hND
    have heq : (fun i : Fin m => a (N + i.val)) = (fun i => b (N + i.val)) := by
      funext i
      by_contra hne
      exact hND (mem_filter.mpr ⟨hNI, i.val, mem_range.mpr i.isLt, hS N hNI i hne⟩)
    apply hNA
    exact mem_filter.mpr ⟨hNI, by rw [heq]; exact hBE⟩
  have hA : A.card ≤ B.card + D.card := by
    have hs : A ⊆ B ∪ D := by
      intro N hnA
      by_cases hnB : N ∈ B
      · exact Finset.mem_union.mpr (Or.inl hnB)
      · exact Finset.mem_union.mpr (Or.inr (hdiff (mem_sdiff.mpr ⟨hnA, hnB⟩)))
    exact (card_le_card hs).trans (Finset.card_union_le _ _)
  have hB : B.card ≤ A.card + D.card := by
    have hs : B ⊆ A ∪ D := by
      intro N hnB
      by_cases hnA : N ∈ A
      · exact Finset.mem_union.mpr (Or.inl hnA)
      · exact Finset.mem_union.mpr (Or.inr (hdiff' (mem_sdiff.mpr ⟨hnB, hnA⟩)))
    exact (card_le_card hs).trans (Finset.card_union_le _ _)
  have hD : D.card ≤ m * S.card := affectedStarts_card_le I S m
  change |(A.card : ℤ) - B.card| ≤ (m * S.card : ℕ)
  rw [abs_le]
  constructor <;> omega

end
end ErdosProblems.Erdos251.PaperR7
