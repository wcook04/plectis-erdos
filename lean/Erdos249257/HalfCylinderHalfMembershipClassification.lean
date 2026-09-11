import Erdos249257.HalfCylinderFatalGapRightTail

/-!
# Exact half-membership classification in seam coordinates

The fatal-gap/right-tail theorem identifies half nonmembership with eventual
right extension of the integer seam.  This companion takes the Boolean
complement of that classification and packages the positive endpoint needed by
future arithmetic work:

* `1 / 2` belongs to the Mersenne achievement set exactly when false successor
  terminal bits occur beyond every bound;
* equivalently, such bits occur along one cofinal sequence;
* equivalently, some cofinal integer-seam sequence has skipped ranks tending to
  infinity;
* this seam condition is exactly infinitude of the skipped support of the real
  greedy half orbit.

These are consumer equivalences.  They isolate the remaining arithmetic task
without asserting that any of the equivalent positive conditions holds.
-/

namespace Erdos249257

open Set Filter
open HalfCylinderIntegerGreedy

/-- False successor terminal bits occur beyond every requested seam row. -/
def SeamGreedyUnboundedTerminalFalse : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, ∃ hp5 : 5 ≤ p,
    N ≤ p ∧
      SeamRowWord.terminal (by omega)
        (seamGreedyWord (p + 1)) = false

/-- A cofinal sequence consists entirely of false successor terminal bits. -/
def SeamGreedyCofinalTerminalFalse : Prop :=
  ∃ p : ℕ → ℕ, ∃ hp5 : ∀ j, 5 ≤ p j,
    Tendsto p atTop atTop ∧
      ∀ j, SeamRowWord.terminal
          (by have := hp5 j; omega)
          (seamGreedyWord (p j + 1)) = false

/-- The arithmetic `U/M` producer at row `s`: either the old successor carries
to the upper word, or there is no carry and the new terminal weight exceeds the
explicit prefix remainder. -/
def SeamGreedyUpperOrMiddleAt (s : ℕ) (hs : 5 ≤ s) : Prop :=
  (seamAdjacentCut s hs).successorCarries ∨
    (¬ (seamAdjacentCut s hs).successorCarries ∧
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
        (seamAdjacentCut s hs).terminalWeight)

/-- Exact local removal of the empirical `U/M/R` labels: a false successor
terminal is equivalent to the source-level upper-or-middle arithmetic
disjunction. -/
theorem seamGreedy_terminal_false_iff_upperOrMiddle
    (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = false ↔
      SeamGreedyUpperOrMiddleAt s hs := by
  constructor
  · intro hfalse
    by_cases hcarry : (seamAdjacentCut s hs).successorCarries
    · exact Or.inl hcarry
    · right
      refine ⟨hcarry, ?_⟩
      by_contra hnotmiddle
      have hright : (seamAdjacentCut s hs).terminalWeight ≤
          4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse :=
        Nat.le_of_not_gt hnotmiddle
      have hword := seamGreedyWord_succ_eq_rightBranch
        s hs hcarry hright
      have htrue : SeamRowWord.terminal (by omega)
          (seamGreedyWord (s + 1)) = true := by
        rw [hword]
        exact SeamRowWord.terminal_extend (by omega)
          (seamAdjacentCut s hs).below true
      rw [hfalse] at htrue
      contradiction
  · rintro (hcarry | ⟨hcarry, hmiddle⟩)
    · rw [seamGreedyWord_succ_eq_upperBranch s hs hcarry]
      exact SeamRowWord.terminal_extend (by omega)
        (seamAdjacentCut s hs).above false
    · rw [seamGreedyWord_succ_eq_middleBranch s hs hcarry hmiddle]
      exact SeamRowWord.terminal_extend (by omega)
        (seamAdjacentCut s hs).below false

/-- Upper-or-middle arithmetic transitions occur beyond every requested row. -/
def SeamGreedyUnboundedUpperOrMiddle : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, ∃ hp5 : 5 ≤ p,
    N ≤ p ∧ SeamGreedyUpperOrMiddleAt p hp5

/-- The Boolean terminal producer and its exact arithmetic branch
classification are equivalent beyond every bound. -/
theorem unboundedTerminalFalse_iff_unboundedUpperOrMiddle :
    SeamGreedyUnboundedTerminalFalse ↔
      SeamGreedyUnboundedUpperOrMiddle := by
  constructor
  · intro hterminal N
    obtain ⟨p, hp5, hNp, hfalse⟩ := hterminal N
    exact ⟨p, hp5, hNp,
      (seamGreedy_terminal_false_iff_upperOrMiddle p hp5).mp hfalse⟩
  · intro hbranch N
    obtain ⟨p, hp5, hNp, hnonright⟩ := hbranch N
    exact ⟨p, hp5, hNp,
      (seamGreedy_terminal_false_iff_upperOrMiddle p hp5).mpr hnonright⟩

/-- Half membership excludes an eventual right seam tail. -/
theorem half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ SeamGreedyEventuallyRight := by
  constructor
  · intro hhalf hright
    exact (seamGreedyEventuallyRight_iff_half_not_mem.mp hright) hhalf
  · intro hnotright
    by_contra hnotmem
    exact hnotright
      (seamGreedyEventuallyRight_iff_half_not_mem.mpr hnotmem)

/-- Exact positive complement of the eventual-terminal classification: half
membership is equivalent to false successor terminal bits beyond every bound.
-/
theorem half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedTerminalFalse := by
  constructor
  · intro hhalf
    have hnotright : ¬ SeamGreedyEventuallyRight :=
      half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight.mp hhalf
    have hnotterminal :
        ¬ ∃ S : ℕ, ∃ hS5 : 5 ≤ S, ∀ (s : ℕ) (hs : S ≤ s),
          SeamRowWord.terminal (by omega)
            (seamGreedyWord (s + 1)) = true := by
      intro hterminal
      exact hnotright
        (seamGreedyEventuallyRight_iff_eventually_terminal_true.mpr hterminal)
    push Not at hnotterminal
    intro N
    obtain ⟨p, hp, hterminal⟩ :=
      hnotterminal (max 5 N) (by omega)
    have hp5 : 5 ≤ p := by omega
    refine ⟨p, hp5, by omega, ?_⟩
    have hne : SeamRowWord.terminal (by omega)
        (seamGreedyWord (p + 1)) ≠ true := by
      simpa using hterminal
    exact Bool.eq_false_of_not_eq_true hne
  · intro hterminal
    exact half_mem_mersenneAchievementSet_of_unboundedTerminalFalse
      (by simpa [SeamGreedyUnboundedTerminalFalse] using hterminal)

/-- Strongest current arithmetic socket: half membership is exactly cofinal
occurrence of the explicit upper-or-middle successor disjunction. -/
theorem half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedUpperOrMiddle :=
  half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse.trans
    unboundedTerminalFalse_iff_unboundedUpperOrMiddle

/-- The unbounded-terminal predicate is precisely failure of eventual right
extension. -/
theorem unboundedTerminalFalse_iff_not_seamGreedyEventuallyRight :
    SeamGreedyUnboundedTerminalFalse ↔
      ¬ SeamGreedyEventuallyRight :=
  half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse.symm.trans
    half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight

/-- Choice turns the beyond-every-bound form into one cofinal false-terminal
sequence. -/
theorem cofinalTerminalFalse_of_unboundedTerminalFalse
    (hunbounded : SeamGreedyUnboundedTerminalFalse) :
    SeamGreedyCofinalTerminalFalse := by
  classical
  change ∀ N : ℕ, ∃ p : ℕ, ∃ hp5 : 5 ≤ p,
      N ≤ p ∧
        SeamRowWord.terminal (by omega)
          (seamGreedyWord (p + 1)) = false at hunbounded
  choose p hp5 hNp hfalse using hunbounded
  refine ⟨p, hp5, tendsto_atTop_mono hNp tendsto_id, ?_⟩
  intro j
  simpa using hfalse j

/-- A cofinal false-terminal sequence is, in particular, unbounded. -/
theorem unboundedTerminalFalse_of_cofinalTerminalFalse
    (hcofinal : SeamGreedyCofinalTerminalFalse) :
    SeamGreedyUnboundedTerminalFalse := by
  rcases hcofinal with ⟨p, hp5, hp, hfalse⟩
  apply half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse.mp
  exact half_mem_mersenneAchievementSet_of_cofinalTerminalFalse
    p hp hp5 hfalse

/-- The quantifier and cofinal-sequence forms of terminal-false supply are
exactly equivalent. -/
theorem unboundedTerminalFalse_iff_cofinalTerminalFalse :
    SeamGreedyUnboundedTerminalFalse ↔
      SeamGreedyCofinalTerminalFalse :=
  ⟨cofinalTerminalFalse_of_unboundedTerminalFalse,
    unboundedTerminalFalse_of_cofinalTerminalFalse⟩

/-- Cofinal false successor terminals are an exact half-membership endpoint. -/
theorem half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyCofinalTerminalFalse :=
  half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse.trans
    unboundedTerminalFalse_iff_cofinalTerminalFalse

/-- Half membership is also equivalent to existence of a cofinal seam sequence
whose skipped ranks themselves tend to infinity.  The forward direction uses
the terminal coordinate as the skipped coordinate; the reverse direction is
the existing compactness consumer. -/
theorem half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∃ rows : ℕ → ℕ, SeamGreedyUnboundedSkippedRanksAlong rows := by
  constructor
  · intro hhalf
    obtain ⟨p, hp5, hp, hfalse⟩ :=
      half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse.mp hhalf
    refine ⟨fun j => p j + 1, ?_⟩
    exact seamGreedyUnboundedSkippedRanksAlong_succ_of_cofinalTerminalFalse
      p hp hp5 hfalse
  · rintro ⟨rows, hrows⟩
    exact half_mem_mersenneAchievementSet_of_unboundedSkippedRanks rows hrows

/-- Integer-seam cofinal false terminals and infinitude of the actual real
greedy skipped support are the same endpoint. -/
theorem unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite :
    SeamGreedyUnboundedTerminalFalse ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite :=
  half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse.symm.trans
    half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite

/-- Equivalent no-final-skip form of the positive classification. -/
theorem half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ ∃ M : ℕ, IsLastHalfGreedySkip M := by
  rw [half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight,
    seamGreedyEventuallyRight_iff_exists_isLastHalfGreedySkip]

#print axioms half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight
#print axioms seamGreedy_terminal_false_iff_upperOrMiddle
#print axioms half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse
#print axioms half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle
#print axioms unboundedTerminalFalse_iff_not_seamGreedyEventuallyRight
#print axioms unboundedTerminalFalse_iff_cofinalTerminalFalse
#print axioms half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse
#print axioms half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong
#print axioms unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite
#print axioms half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip

end Erdos249257
