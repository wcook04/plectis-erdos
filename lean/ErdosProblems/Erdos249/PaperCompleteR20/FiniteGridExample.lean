import ErdosProblems.Erdos249.PaperCompleteR20.FiniteGridCorrespondence

/-! The manuscript's concrete H=840, L=12 four-point example.
Arithmetic is kernel evaluated; the real arcs use representatives in [0,4096).
This does not assert the cofinal supply hypothesis. -/
namespace ErdosProblems.Erdos249.PaperCompleteR20
open Erdos249257.TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem four_grid_numerators :
    paperGridNumerator 840 12 1 % 4096 = 2920 ∧
    paperGridNumerator 840 12 2 % 4096 = 2024 ∧
    paperGridNumerator 840 12 3 % 4096 = 3532 ∧
    paperGridNumerator 840 12 4 % 4096 = 3796 := by decide

theorem four_grid_certificate :
    paperGridCertificate 840 12 {1, 2, 3, 4} := by
  intro qi hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact ⟨3, by simp, by decide⟩
  · exact ⟨1, by simp, by decide⟩
  · exact ⟨4, by simp, by decide⟩
  · exact ⟨1, by simp, by decide⟩

/-- Closed positively oriented arc, using a representative x in [0,4096). -/
def gridArc (a b x : ℝ) : Prop :=
  0 ≤ x ∧ x < 4096 ∧ ((a ≤ x ∧ x ≤ a + b) ∨ x + 4096 ≤ a + b)

theorem four_arcs_pairwise :
    (∃ x, gridArc 2920 854 x ∧ gridArc 2024 1694 x) ∧
    (∃ x, gridArc 2920 854 x ∧ gridArc 3532 2534 x) ∧
    (∃ x, gridArc 2920 854 x ∧ gridArc 3796 3374 x) ∧
    (∃ x, gridArc 2024 1694 x ∧ gridArc 3532 2534 x) ∧
    (∃ x, gridArc 2024 1694 x ∧ gridArc 3796 3374 x) ∧
    (∃ x, gridArc 3532 2534 x ∧ gridArc 3796 3374 x) := by
  refine ⟨⟨2920, ?_⟩, ⟨3532, ?_⟩, ⟨2920, ?_⟩,
    ⟨3532, ?_⟩, ⟨2024, ?_⟩, ⟨0, ?_⟩⟩ <;> norm_num [gridArc]

theorem four_arcs_no_common_point :
    ¬ ∃ x, gridArc 2920 854 x ∧ gridArc 2024 1694 x ∧
      gridArc 3532 2534 x ∧ gridArc 3796 3374 x := by
  simp only [gridArc]
  rintro ⟨x, ⟨h0, h1, h2⟩, ⟨_, _, h3⟩, ⟨_, _, h4⟩, ⟨_, _, h5⟩⟩
  rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4 <;>
    rcases h5 with h5 | h5 <;> linarith

end ErdosProblems.Erdos249.PaperCompleteR20
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.four_grid_numerators
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.four_grid_certificate
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.four_arcs_pairwise
#print axioms ErdosProblems.Erdos249.PaperCompleteR20.four_arcs_no_common_point
