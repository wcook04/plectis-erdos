import ErdosProblems.Erdos251.SparsePaperR11

noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperCompleteR20
open PaperR11.GrowingBlocks

theorem bounded_test_finite_coupling {α : Type*} (a b : ℕ → α)
    (X m : ℕ) (S : Finset ℕ)
    (hS : ∀ N ∈ Ico X (2*X), ∀ i : Fin m,
      a (N+i.val) ≠ b (N+i.val) → N+i.val ∈ S)
    (B : ℝ) (hB : 0 ≤ B) (Φ : ℕ → (Fin m → α) → ℝ)
    (ha : ∀ N ∈ Ico X (2*X), |Φ N (fun i => a (N+i.val))| ≤ B)
    (hb : ∀ N ∈ Ico X (2*X), |Φ N (fun i => b (N+i.val))| ≤ B) :
    |testMean a X m Φ - testMean b X m Φ| ≤ 2*B*(m : ℝ)*S.card/X := by
  classical
  by_cases hz : B = 0
  · subst B
    have hza : ∑ N ∈ Ico X (2*X), Φ N (fun i => a (N+i.val)) = 0 :=
      sum_eq_zero (fun N hN => (by have := abs_le.mp (ha N hN); linarith))
    have hzb : ∑ N ∈ Ico X (2*X), Φ N (fun i => b (N+i.val)) = 0 :=
      sum_eq_zero (fun N hN => (by have := abs_le.mp (hb N hN); linarith))
    simp [testMean, hza, hzb]
  · have hp : 0 < B := lt_of_le_of_ne hB (Ne.symm hz)
    let ψ : ℕ → (Fin m → α) → ℝ := fun N u => Φ N u / B
    have ha' : ∀ N ∈ Ico X (2*X), |ψ N (fun i => a (N+i.val))| ≤ 1 := by
      intro N hN
      dsimp [ψ]
      rw [abs_div, abs_of_pos hp]
      exact (div_le_one hp).mpr (ha N hN)
    have hb' : ∀ N ∈ Ico X (2*X), |ψ N (fun i => b (N+i.val))| ≤ 1 := by
      intro N hN
      dsimp [ψ]
      rw [abs_div, abs_of_pos hp]
      exact (div_le_one hp).mpr (hb N hN)
    have h := testMean_le_finite_support a b X m S hS ψ ha' hb'
    have he : testMean a X m ψ - testMean b X m ψ =
        (testMean a X m Φ - testMean b X m Φ)/B := by
      unfold testMean ψ
      simp only [← sum_div]
      ring
    rw [he, abs_div, abs_of_pos hp] at h
    have hh := (div_le_iff₀ hp).mp h
    convert hh using 1 <;> ring

end ErdosProblems.Erdos251.PaperCompleteR20
#print axioms ErdosProblems.Erdos251.PaperCompleteR20.bounded_test_finite_coupling
#print axioms ErdosProblems.Erdos251.PaperR9.SparseAmbient.arbitrary_word_sparse_rationalisation_uniform
#print axioms ErdosProblems.Erdos251.PaperR11.SparsePaper.polylogarithmic_word_interval_uniform
#print axioms ErdosProblems.Erdos251.PaperR11.GrowingBlocks.blockTV_le_supportSlice
#print axioms ErdosProblems.Erdos251.PaperR11.GrowingBlocks.growing_block_TV_uniform
