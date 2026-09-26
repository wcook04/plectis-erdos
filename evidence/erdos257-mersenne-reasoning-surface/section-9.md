# Formal evidence: Reciprocal Mersenne Subseries, Section 9

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="thm-lower-bound-every-reset"></a>

## Theorem 9.46 (A: a sufficient lower bound at every reset), page 106

> *Assume that $`|\mathrm{rem}(r+1)-2^{r+1}|>2^{(r+5)/2}`$ for every upper or middle reset $`r\ge10`$. Then $`1/2\in\mathcal A`$.*
> 
> *Here is the role of the constants. Put
> ``` math
> B(r)=2^{\lfloor(r+4)/2\rfloor}+2r+3.
> ```
> For $`r\ge10`$, one has $`B(r)^2\le2^{r+5}`$. A right branch at the first crossing of the largest omitted rank $`r`$ would force $`|\Delta_{r+1}|\le B(r)`$, by tracing the exact affine recurrence back to that reset. The assumed strict lower bound excludes this crossing. The largest-skip induction then gives half-membership. The hypothesis concerns every actual reset beyond the threshold; neither a long finite check nor an asserted run-length asymptotic supplies it.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_half_membership`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L595)

```lean
theorem paper_theoremA_half_membership (h : PaperResetSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paperResetSqrtEscape_iff_square`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L545)

```lean
theorem paperResetSqrtEscape_iff_square :
    PaperResetSqrtEscape ↔ SeamResetSqrtEscape
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_crossing_bound_square_le`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L121)

```lean
theorem paper_theoremA_crossing_bound_square_le (r : ℕ) (hr : 10 ≤ r) :
    resetCrossingBound r ^ 2 ≤ 2 ^ (r + 5)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_right_branch_forces_small_deviation`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L261)

```lean
theorem paper_theoremA_right_branch_forces_small_deviation
    {s d : ℕ} (hs14 : 14 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hcross : 3 * d ≤ 2 * (s + 1))
    (hR : ¬ SeamGreedyUpperOrMiddleAt s (by omega)) :
    (seamResetDeviation d).natAbs ≤ resetCrossingBound d
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.half_mem_mersenneAchievementSet_of_resetSqrtEscape`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L526)

```lean
theorem half_mem_mersenneAchievementSet_of_resetSqrtEscape
    (hsqrt : SeamResetSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="thm-lower-bound-every-reset-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_theoremA_half_membership`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_11/Challenge.lean#L312) (E257_11, line 312), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_11/PaperStructuresBL.lean#L96) (PaperStructuresBL.lean, line 96), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_11.json) (E257_11)
- `paperResetSqrtEscape_iff_square`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_09/Challenge.lean#L335) (E257_09, line 335), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_09/PaperStructuresBB.lean#L111) (PaperStructuresBB.lean, line 111), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_09.json) (E257_09)
- `paper_theoremA_crossing_bound_square_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L226) (E257_43, line 226), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsAA.lean#L283) (PaperStatementsAA.lean, line 283), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)
- `paper_theoremA_right_branch_forces_small_deviation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_37/Challenge.lean#L285) (E257_37, line 285), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_37/Statement.lean#L294) (Statement.lean, line 294), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_37.json) (E257_37)
- `half_mem_mersenneAchievementSet_of_resetSqrtEscape`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_31/Challenge.lean#L324) (E257_31, line 324), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_31/PaperStructuresBK.lean#L254) (PaperStructuresBK.lean, line 254), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_31.json) (E257_31)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-one-sided-finite-decision-boundary"></a>

## Theorem 9.48 (C: the one-sided finite decision boundary), page 107

> *The equivalence of Theorem 5.10 separates two logically different kinds of evidence. A fatal greedy gap found at a finite rank is a finite certificate that $`1/2\notin\mathcal A`$. By contrast, membership requires survival at every rank; this paper supplies no finite certificate that the orbit survives forever and no completion theorem turning a long surviving prefix into membership.*
> 
> *The reset-crossing hypotheses, truncation-rung ladder, and sharp-capacity inequalities feed sufficient conditions for membership. They are not proved equivalent to one another, nor is failure to find one at a given depth evidence of survival. Consequently these searches give at most a semi-decision procedure for *nonmembership of the specific value $`1/2`$*. Halting does not prove the universal statement in \#257, and non-halting does not prove that $`1/2`$ is represented. In particular, neither truth nor falsity of the universal problem is shown semi-decidable here. Deeper negative search alone establishes nothing beyond the tested finite ranks; this is the quantifier boundary of Theorem 2.11.*

The Lean declaration below states this result or one that implies it. The Lean statement gives the mathematical facts behind the theorem, for every real $x$: the survival equivalence, that a rank with $r_n(x)>R_n$ certifies $x\notin\mathcal A$, and that membership forces $r_n(x)\le R_n$ at every rank. The remaining sentences describe what the corpus and its searches establish and have no Lean counterpart.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sided_finite_decision_boundary`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/CentredCompletionAndDecisionBoundary.lean#L77)

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

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_one_sided_finite_decision_boundary`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L118) (E257_43, line 118), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsN.lean#L261) (PaperStatementsN.lean, line 261), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
