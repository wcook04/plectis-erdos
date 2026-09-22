import Erdos249257.HalfCylinderFullShellSeamBridge
import Erdos249257.TerminalOnlyCofinal
import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.DyadicPrefixCompression

/-!
Paper-form restatements of three asserted environments from the long
Erdős #257 manuscript `paper/reasoning-parts/erdos257/a257_front.tex`.

* `record:257bm-c15` (`a257_front.tex:4298`), "A sufficient lower bound for the
  integer remainder": `paper_seam_escape_forces_remainder_band`,
  `paper_seam_escape_implies_full_shell_nonnegative`,
  `paper_seam_escape_implies_half_membership`.
* `record:257rig-c17` (`a257_front.tex:4325`), "Terminal bounds at unbounded
  depths": `paper_terminal_bounds_at_unbounded_depths`.
* `record:257bm-c19` (`a257_front.tex:4373`), "An eventual nonnegative margin
  suffices": `paper_eventual_nonnegative_margin_iff`.

Paper notation: `B(m) = halfStripBound m = 2⌊√m⌋ + 4`,
`rem(n) = seamIntegerGreedyRemainder n`,
`ihc(D,N) = integerHalfCarry D N`, `F_k(J) = greedyHalfFrozenMargin k J`,
`r_k(1/2) = greedyMersenneRemainder (1/2) k`, and
`2^(-(k+1)) = halfDyadicCap (k+1)`.
-/

namespace ErdosProblems.Erdos257.PaperCompleteR21

open Erdos249257 Erdos249257.HalfCarryReachability
open Erdos249257.HalfCylinderIntegerGreedy

/-! ## `record:257bm-c15` -- a sufficient lower bound for the integer
remainder -/

/-- The mechanism the environment quotes: at an actual skipped rank `n ≥ 3`,
a negative frozen margin forces `1 ≤ rem(n) ≤ B(2n)`. -/
theorem paper_seam_escape_forces_remainder_band
    {n : ℕ} (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))
    (hneg : greedyHalfFrozenMargin (n - 1) n < 0) :
    1 ≤ seamIntegerGreedyRemainder n ∧
      seamIntegerGreedyRemainder n ≤ halfStripBound (2 * n) :=
  neg_greedyHalfFrozenMargin_fullShell_implies_seamRemainder_small n hn hskip hneg

/-- Paper display of `record:257bm-c15`: `∀` skipped rank `n ≥ 3`,
`B(2n) < rem(n)` is a sufficient condition for the nonnegativity condition
`∀` skipped rank `n ≥ 3`, `0 ≤ F(n-1,n)`. -/
theorem paper_seam_escape_implies_full_shell_nonnegative
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    HalfGreedySkippedFullShellNonnegative := by
  intro n hn hskip
  by_contra hnot
  have hneg : greedyHalfFrozenMargin (n - 1) n < 0 := lt_of_not_ge hnot
  have hsmall :=
    neg_greedyHalfFrozenMargin_fullShell_implies_seamRemainder_small n hn hskip hneg
  have hlarge := hescape n hn hskip
  omega

/-- Consequently the escape bound is itself sufficient for half-membership. -/
theorem paper_seam_escape_implies_half_membership
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet :=
  half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
    (paper_seam_escape_implies_full_shell_nonnegative hescape)

/-! ## `record:257rig-c17` -- terminal bounds at unbounded depths -/

/-- Paper display of `record:257rig-c17`: if for every `N ≥ 0` there are
`M ≥ max{N,1}` and `D ⊆ {2,…,M}` with `|ihc(D,M-1)| ≤ B(M) = 2⌊√M⌋+4`, then
some infinite `A ⊆ ℕ_{≥1}` satisfies `X_A(2) = 1/2`.  No compatibility between
the different finite supports is required. -/
theorem paper_terminal_bounds_at_unbounded_depths
    (hcofinal : ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ ∃ D : Finset ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
      |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ (halfStripBound M : ℝ)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
  classical
  have hstrip : HalfCarryCofinalTerminalOnlyStrip := by
    intro N
    obtain ⟨M, hM, D, hD, hcarry⟩ := hcofinal N
    refine ⟨M, hM, fun i ↦ decide (i.val ∈ D), ?_, ?_, ?_⟩
    · have h0 : (0 : ℕ) ∉ D := fun h ↦ by have := (hD 0 h).1; omega
      simp [h0]
    · intro _
      have h1 : (1 : ℕ) ∉ D := fun h ↦ by have := (hD 1 h).1; omega
      simp [h1]
    · have hsupp :
          wordSupport (fun i : Fin (M + 1) ↦ decide (i.val ∈ D)) = (↑D : Set ℕ) := by
        ext m
        simp only [wordSupport, Set.mem_setOf_eq, Finset.mem_coe, decide_eq_true_eq]
        constructor
        · rintro ⟨_, hm⟩
          exact hm
        · intro hm
          exact ⟨by have := (hD m hm).2; omega, hm⟩
      rw [hsupp]
      exact hcarry
  obtain ⟨A, hA0, hvalue⟩ :=
    half_mem_mersenneAchievementSet_of_cofinalTerminalOnlyStrip hstrip
  have hseries : erdosSupportSeries 2 A = (1 : ℝ) / 2 := by
    rw [← positiveMersenneSupportValue_eq_erdosSupportSeries]
    exact hvalue.symm
  exact ⟨A, fun hfinite ↦ finite_boolSupport_ne_half A hfinite hA0 hseries,
    hA0, hseries⟩

/-! ## `record:257bm-c19` -- an eventual nonnegative margin suffices -/

/-- At positive depth the greedy half remainder never lands exactly on the
next dyadic cap: the reduced excess numerator is odd, hence nonzero.  This is
the "oddness of the reduced excess numerator excludes equality at zero" clause
of the environment. -/
private theorem greedyHalfRemainder_ne_nextDyadicCap {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k ≠ halfDyadicCap (k + 1) := by
  intro heq
  have hL : 0 < halfGreedyPrefixDenominator k := Rat.den_pos (halfGreedyPrefixRat k)
  have hcapR : (((1 / (2 : ℚ) ^ (k + 1)) : ℚ) : ℝ) = halfDyadicCap (k + 1) := by
    unfold halfDyadicCap
    push_cast
    rw [div_pow]
    norm_num
  have hhalf : (((1 / 2 : ℚ)) : ℝ) = (1 / 2 : ℝ) := by norm_num
  have hratEq : greedyMersenneRemainderRat (1 / 2 : ℚ) k = 1 / (2 : ℚ) ^ (k + 1) := by
    have hcast : ((greedyMersenneRemainderRat (1 / 2 : ℚ) k : ℚ) : ℝ)
        = (((1 / (2 : ℚ) ^ (k + 1)) : ℚ) : ℝ) := by
      rw [cast_greedyMersenneRemainderRat, hcapR, hhalf]
      exact heq
    exact_mod_cast hcast
  have hsub : Rat.divInt (halfGreedyResidualDisplayedNumerator k)
      ((2 * halfGreedyPrefixDenominator k : ℕ) : ℤ) - 1 / (2 : ℚ) ^ (k + 1) = 0 := by
    rw [← greedyHalfRemainderRat_eq_displayed_divInt, hratEq, sub_self]
  rw [divInt_sub_nextDyadic_eq_excess_divInt _ k _ hL, Rat.divInt_eq_div] at hsub
  have hdenPos : 0 < 2 ^ (k + 1) * halfGreedyPrefixDenominator k :=
    Nat.mul_pos (by positivity) hL
  have hden : ((((2 ^ (k + 1) * halfGreedyPrefixDenominator k : ℕ) : ℤ)) : ℚ) ≠ 0 := by
    simp only [ne_eq, Int.cast_natCast, Nat.cast_eq_zero]
    omega
  rcases div_eq_zero_iff.mp hsub with hz | hz
  · have hE : halfGreedyNextDyadicExcessNumerator k = 0 := by
      have hzInt :
          nextDyadicExcessIntNumerator (halfGreedyResidualDisplayedNumerator k) k
            (halfGreedyPrefixDenominator k) = 0 := by exact_mod_cast hz
      simpa [halfGreedyNextDyadicExcessNumerator] using hzInt
    have hodd := halfGreedyNextDyadicExcessNumerator_odd hk
    rw [hE] at hodd
    simp at hodd
  · exact hden hz

/-- Paper display of `record:257bm-c19`: for a positive depth `k`,

`r_k(1/2) < 2^(-(k+1))  ↔  F_k(J) ≥ 0 for some J ≥ 0`. -/
theorem paper_eventual_nonnegative_margin_iff {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) ↔
      ∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J := by
  rw [exists_greedyHalfFrozenMargin_nonneg_iff_excess_neg k hk]
  constructor
  · intro hlt
    have hE := (greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos k).1 hlt.le
    obtain ⟨m, hm⟩ := halfGreedyNextDyadicExcessNumerator_odd hk
    omega
  · intro hE
    exact lt_of_le_of_ne
      ((greedyHalfRemainder_le_nextDyadic_iff_excess_nonpos k).2 hE.le)
      (greedyHalfRemainder_ne_nextDyadicCap hk)

#print axioms paper_seam_escape_forces_remainder_band
#print axioms paper_seam_escape_implies_full_shell_nonnegative
#print axioms paper_seam_escape_implies_half_membership
#print axioms paper_terminal_bounds_at_unbounded_depths
#print axioms paper_eventual_nonnegative_margin_iff

end ErdosProblems.Erdos257.PaperCompleteR21
