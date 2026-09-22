import ErdosProblems.Erdos257.GreedyRepairCriterion

namespace ErdosProblems.Erdos257.PaperCompleteR20
open Erdos249257

noncomputable def paperIntegerDefect (x : ℝ) (N : ℕ) : ℤ :=
  ⌊(2 : ℝ)^N*x⌋ - binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N

theorem paperIntegerDefect_eq {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    paperIntegerDefect x N = (greedyBinaryDefect x N : ℤ) := by
  unfold paperIntegerDefect greedyBinaryDefect
  rw [Int.ofNat_sub (greedyBinaryPrefix_le_floor hx N),
    Int.natCast_floor_eq_floor (by positivity)]

theorem paper_general_repair_criteria {x : ℝ} (hx : 0 ≤ x) :
    (x ∈ mersenneAchievementSet ↔ ∀ K : ℕ, ∃ N, K ≤ N ∧
      paperIntegerDefect x (N+1) ≤ paperIntegerDefect x N) ∧
    (x ∈ mersenneAchievementSet ↔ ∀ K : ℕ, ∃ N, K ≤ N ∧
      N < K+2*Nat.sqrt K+12 ∧ paperIntegerDefect x (N+1) ≤ paperIntegerDefect x N) := by
  simp only [paperIntegerDefect_eq hx, Int.ofNat_le]
  exact ⟨mem_iff_greedyBinaryDefect_cofinal_repairs hx,
    mem_iff_greedyBinaryDefect_sqrt_windows hx⟩

end ErdosProblems.Erdos257.PaperCompleteR20
#print axioms ErdosProblems.Erdos257.PaperCompleteR20.paperIntegerDefect_eq
#print axioms ErdosProblems.Erdos257.PaperCompleteR20.paper_general_repair_criteria
