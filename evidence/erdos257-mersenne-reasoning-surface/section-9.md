# Formal evidence: Reciprocal Mersenne Subseries, Section 9

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="thm-lower-bound-every-reset"></a>

## Theorem 9.46, page 106

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_half_membership`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L595)

```lean
theorem paper_theoremA_half_membership (h : PaperResetSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paperResetSqrtEscape_iff_square`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L545)

```lean
theorem paperResetSqrtEscape_iff_square :
    PaperResetSqrtEscape ↔ SeamResetSqrtEscape
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_crossing_bound_square_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L121)

```lean
theorem paper_theoremA_crossing_bound_square_le (r : ℕ) (hr : 10 ≤ r) :
    resetCrossingBound r ^ 2 ≤ 2 ^ (r + 5)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_right_branch_forces_small_deviation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L261)

```lean
theorem paper_theoremA_right_branch_forces_small_deviation
    {s d : ℕ} (hs14 : 14 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hcross : 3 * d ≤ 2 * (s + 1))
    (hR : ¬ SeamGreedyUpperOrMiddleAt s (by omega)) :
    (seamResetDeviation d).natAbs ≤ resetCrossingBound d
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.half_mem_mersenneAchievementSet_of_resetSqrtEscape`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L526)

```lean
theorem half_mem_mersenneAchievementSet_of_resetSqrtEscape
    (hsqrt : SeamResetSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="thm-lower-bound-every-reset-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-one-sided-finite-decision-boundary"></a>

## Theorem 9.48, page 107

The Lean declaration below states a result at least as strong as this one. The Lean statement gives the mathematical facts behind the theorem, for every real $x$: the survival equivalence, that a rank with $r_n(x)>R_n$ certifies $x\notin\mathcal A$, and that membership forces $r_n(x)\le R_n$ at every rank. The remaining sentences describe what the corpus and its searches establish and have no Lean counterpart.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sided_finite_decision_boundary`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/CentredCompletionAndDecisionBoundary.lean#L77)

```lean
theorem paper_one_sided_finite_decision_boundary :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
        0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
      (∀ x : ℝ, (∃ n : ℕ, mersenneTail n < greedyMersenneRemainder x n) →
        x ∉ mersenneAchievementSet) ∧
      (∀ x : ℝ, x ∈ mersenneAchievementSet →
        ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n)
```

<a id="thm-one-sided-finite-decision-boundary-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_one_sided_finite_decision_boundary` | [E257_35/Challenge.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L118) | [PaperStatementsN.lean, line 261](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsN.lean#L261) | [E257_35](../../evidence/comparator/replay-35882032091/receipt-E257_35.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
