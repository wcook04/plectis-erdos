import Erdos249257.HalfCylinderSkippedRankLimit

/-!
# Cofinal terminal-false supply for the half-cylinder seam

A false terminal bit at the successor of row `p` is exactly the skipped
rank `p`.  This module packages that dependent index calculation and feeds
a cofinal supply of such bits into the existing unbounded-skipped-rank
consumer.
-/

namespace Erdos249257

open Set Filter
open HalfCylinderIntegerGreedy

/-- A cofinal sequence of false terminal seam bits supplies unbounded
skipped ranks along the corresponding successor rows.  The skipped
coordinate at row `p j + 1` has array index `p j - 2` and Mersenne rank
`p j`. -/
theorem seamGreedyUnboundedSkippedRanksAlong_succ_of_cofinalTerminalFalse
    (p : ℕ → ℕ)
    (hp : Tendsto p atTop atTop)
    (hp5 : ∀ j, 5 ≤ p j)
    (hterminal : ∀ j,
      SeamRowWord.terminal
          (by have := hp5 j; omega)
          (seamGreedyWord (p j + 1)) = false) :
    SeamGreedyUnboundedSkippedRanksAlong (fun j => p j + 1) := by
  let skip : ∀ j, Fin ((p j + 1) - 2) := fun j =>
    ⟨p j - 2, by have := hp5 j; omega⟩
  refine ⟨skip, ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun j => by omega) hp
  · have hrank :
        (fun j => ((skip j : ℕ) + 2)) = p := by
      funext j
      dsimp [skip]
      have := hp5 j
      omega
    rw [hrank]
    exact hp
  · intro j
    simpa [skip, SeamRowWord.terminal] using hterminal j

/-- Cofinal false terminal seam bits therefore give the exact
half-membership conclusion through the skipped-rank compactness route. -/
theorem half_mem_mersenneAchievementSet_of_cofinalTerminalFalse
    (p : ℕ → ℕ)
    (hp : Tendsto p atTop atTop)
    (hp5 : ∀ j, 5 ≤ p j)
    (hterminal : ∀ j,
      SeamRowWord.terminal
          (by have := hp5 j; omega)
          (seamGreedyWord (p j + 1)) = false) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  exact half_mem_mersenneAchievementSet_of_unboundedSkippedRanks
    (fun j => p j + 1)
    (seamGreedyUnboundedSkippedRanksAlong_succ_of_cofinalTerminalFalse
      p hp hp5 hterminal)

/-- The quantifier form most convenient for an arithmetic producer: a false
terminal bit occurs beyond every requested row.  Choice extracts a cofinal
sequence, after which the preceding consumer applies. -/
theorem half_mem_mersenneAchievementSet_of_unboundedTerminalFalse
    (hterminal : ∀ N, ∃ p, ∃ hp5 : 5 ≤ p,
      N ≤ p ∧
        SeamRowWord.terminal
            (by omega)
            (seamGreedyWord (p + 1)) = false) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  classical
  choose p hp5 hNp hfalse using hterminal
  exact half_mem_mersenneAchievementSet_of_cofinalTerminalFalse
    p
    (tendsto_atTop_mono hNp tendsto_id)
    hp5
    (fun j => by simpa using hfalse j)

#print axioms seamGreedyUnboundedSkippedRanksAlong_succ_of_cofinalTerminalFalse
#print axioms half_mem_mersenneAchievementSet_of_cofinalTerminalFalse
#print axioms half_mem_mersenneAchievementSet_of_unboundedTerminalFalse

end Erdos249257
