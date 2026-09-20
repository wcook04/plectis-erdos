import Erdos249257.DiagonalPincerCertificates
import Erdos249257.DiagonalPincerCertificateT64Endpoint
import ErdosProblems.Skip.LadderT67

/-! Paper-form restatement of the long paper's diagonal certificate table for
Erdős #249: the twelve landed scales `t ∈ {1,2,3,4,5,7,8,9,11,13,16,17}` each
carry a diagonal certificate, at the listed depths
`{6,5,7,7,9,14,15,14,21,22,23,26}`; the `t = 64` endpoint fires at depth `93`;
the later aggregate theorem closes every scale `t ≤ 82` with no holes; and the
`t = 17` window data `H₁₇ = 12252240` with endpoints `12252241` and
`24504506` at depth `26`.

Here `H(t) = periodLcm t` and `C(h,N,L) = certifiedKill h N L`. -/
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Erdos249257.TotientTailPeriodKiller

/-! ### The diagonal certificate table -/

/-- The twelve landed scales. -/
theorem diagonalPincerCertificateScales_list :
    diagonalPincerCertificateScales = [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17] := rfl

/-- The listed depths, in the same order. -/
theorem diagonalPincerKillDepth_list :
    diagonalPincerCertificateScales.map diagonalPincerKillDepth =
      [6, 5, 7, 7, 9, 14, 15, 14, 21, 22, 23, 26] := by
  decide

/-- **The table.**  Every listed scale carries a diagonal certificate, at the
listed depth. -/
theorem certifiedKill_diagonal_table :
    ∀ t ∈ diagonalPincerCertificateScales,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepth t) :=
  certifiedKill_diagonal_all_imported

/-- The displayed existential form: `∀ t ∈ {1,2,3,4,5,7,8,9,11,13,16,17},
∃ L, C(H_t, H_t, L)`. -/
theorem exists_diagonalKill_on_table :
    ∀ t ∈ diagonalPincerCertificateScales,
      ∃ L, certifiedKill (periodLcm t) (periodLcm t) L :=
  fun t ht => ⟨diagonalPincerKillDepth t, certifiedKill_diagonal_all_imported t ht⟩

/-- The `t = 64` endpoint of the historical extension. -/
theorem certifiedKill_diagonal_t64_paper :
    certifiedKill (periodLcm 64) (periodLcm 64) 93 :=
  certifiedKill_diagonal_t64

/-- **The later aggregate theorem** closes every scale `t ≤ 82` with no
holes. -/
theorem exists_diagonalKill_le_82_paper (t : ℕ) (ht : t ≤ 82) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L :=
  ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82 t ht

/-- The `t = 17` window data: `H₁₇ = 12252240`, and at depth `L = 26` the two
finite windows run from `H₁₇ + 1 = 12252241` and from `2H₁₇ + 1 = 24504481` up
to `2H₁₇ + 26 = 24504506`. -/
theorem periodLcm_seventeen_window_data :
    periodLcm 17 = 12252240 ∧ periodLcm 17 + 1 = 12252241 ∧
      2 * periodLcm 17 + 1 = 24504481 ∧ 2 * periodLcm 17 + 26 = 24504506 ∧
      diagonalPincerKillDepth 17 = 26 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

end ErdosProblems.Erdos249.PaperCompleteR21

#print axioms ErdosProblems.Erdos249.PaperCompleteR21.diagonalPincerCertificateScales_list
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.diagonalPincerKillDepth_list
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_diagonal_table
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_diagonalKill_on_table
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_diagonal_t64_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.exists_diagonalKill_le_82_paper
#print axioms ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_seventeen_window_data
