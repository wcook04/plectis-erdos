import ErdosProblems.Erdos251.NonconcentrationCoreR11

noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperCompleteR20
open PaperR11.Nonconcentration

theorem zeroDensity_union {S T : Set ℕ} (hS : ZeroDensity S) (hT : ZeroDensity T) :
    ZeroDensity (S ∪ T) := by
  classical
  intro ε hε
  obtain ⟨NS, hs⟩ := hS (ε/2) (by positivity)
  obtain ⟨NT, ht⟩ := hT (ε/2) (by positivity)
  refine ⟨max NS NT, fun N hN => ?_⟩
  have hc : ((range N).filter (fun n => n ∈ S ∪ T)).card ≤
      ((range N).filter (fun n => n ∈ S)).card +
      ((range N).filter (fun n => n ∈ T)).card := by
    rw [show (range N).filter (fun n => n ∈ S ∪ T) =
      (range N).filter (fun n => n ∈ S) ∪ (range N).filter (fun n => n ∈ T) by
        ext n; simp; tauto]
    exact card_union_le _ _
  have hcR : (((range N).filter (fun n => n ∈ S ∪ T)).card : ℝ) ≤
      ((range N).filter (fun n => n ∈ S)).card +
      ((range N).filter (fun n => n ∈ T)).card := by exact_mod_cast hc
  have hsum := add_lt_add
    (hs N (le_trans (le_max_left _ _) hN))
    (ht N (le_trans (le_max_right _ _) hN))
  have hend : (ε/2)*(N : ℝ) + (ε/2)*N = ε*N := by ring
  rw [hend] at hsum
  simpa only [Set.mem_union] using hcR.trans_lt hsum

theorem zeroDensity_backward_shift {S : Set ℕ} (hS : ZeroDensity S) (i : ℕ) :
    ZeroDensity {n | n+i ∈ S} := by
  classical
  intro ε hε
  obtain ⟨N₀, hs⟩ := hS (ε/2) (by positivity)
  refine ⟨max N₀ i, fun N hN => ?_⟩
  have hNi : i ≤ N := le_trans (le_max_right _ _) hN
  have hc : ((range N).filter (fun n => n+i ∈ S)).card ≤
      ((range (N+i)).filter (fun n => n ∈ S)).card := by
    apply card_le_card_of_injOn (fun n => n+i)
    · intro n hn
      obtain ⟨hn, hs⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.add_lt_add_right (mem_range.mp hn) i), hs⟩
    · intro a ha b hb he; exact Nat.add_right_cancel he
  have hcR : (((range N).filter (fun n => n+i ∈ S)).card : ℝ) ≤
      ((range (N+i)).filter (fun n => n ∈ S)).card := by exact_mod_cast hc
  have hh := hs (N+i) (by have := le_trans (le_max_left N₀ i) hN; omega)
  have hNiR : (i : ℝ) ≤ N := by exact_mod_cast hNi
  push_cast at hh
  change (((range N).filter (fun n => n+i ∈ S)).card : ℝ) < ε*N
  nlinarith

theorem zeroDensity_affected_blocks {S : Set ℕ} (hS : ZeroDensity S) (m : ℕ) :
    ZeroDensity {n | ∃ i < m, n+i ∈ S} := by
  classical
  induction m with
  | zero =>
    intro ε hε
    refine ⟨1, fun N hN => ?_⟩
    simp only [Nat.not_lt_zero, false_and, exists_false, Set.mem_setOf_eq,
      filter_false, card_empty, Nat.cast_zero]
    exact mul_pos hε (by exact_mod_cast hN)
  | succ m ih =>
    have he : {n | ∃ i < m+1, n+i ∈ S} = {n | ∃ i < m, n+i ∈ S} ∪ {n | n+m ∈ S} := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · rintro ⟨i, hi, hs⟩
        by_cases him : i < m
        · exact Or.inl ⟨i, him, hs⟩
        · have : i=m := by omega
          subst i; exact Or.inr hs
      · rintro (⟨i, hi, hs⟩ | hs)
        · exact ⟨i, by omega, hs⟩
        · exact ⟨m, by omega, hs⟩
    rw [he]
    exact zeroDensity_union ih (zeroDensity_backward_shift hS m)

theorem sparse_nonconcentration (a b : ℕ → ℤ) (S : Set ℕ)
    (hS : ZeroDensity S) (hab : ∀ n, n ∉ S → a n = b n)
    (ha : FixedBlockNonconcentration a) : FixedBlockNonconcentration b := by
  intro m hm F hF
  apply zeroDensity_mono (t :=
    {n | MvPolynomial.eval (fun i : Fin m => a (n+i.val)) F = 0} ∪
      {n | ∃ i < m, n+i ∈ S})
  · intro n hn
    by_cases hc : ∃ i < m, n+i ∈ S
    · exact Or.inr hc
    · left
      have he : (fun i : Fin m => a (n+i.val)) = (fun i : Fin m => b (n+i.val)) := by
        funext i
        exact hab _ (fun hi => hc ⟨i.val, i.isLt, hi⟩)
      change MvPolynomial.eval (fun i : Fin m => a (n+i.val)) F = 0
      rw [he]; exact hn
  · exact zeroDensity_union (ha m hm F hF) (zeroDensity_affected_blocks hS m)

end ErdosProblems.Erdos251.PaperCompleteR20
#print axioms ErdosProblems.Erdos251.PaperCompleteR20.sparse_nonconcentration
