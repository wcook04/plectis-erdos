# Formal evidence: Reciprocal Mersenne Subseries, Section 6, results 6.1 to 6.34

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="thm-fatal-absorbing"></a>

## Theorem 6.1 (Infinitely many greedy skips force membership), page 42

> *Fix $`x\ge0`$. If $`r_n(x)>R_n`$ at some rank $`n`$, every later rank is selected and $`r_{n+k}(x)>R_{n+k}`$ for every $`k\ge0`$. Consequently, infinitely many omitted positive ranks imply $`x\in\mathcal A`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.fatal_absorbing`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L27)

```lean
theorem fatal_absorbing {x : ℝ} (hx : 0 ≤ x) :
    (∀ n : ℕ, mersenneTail n < greedyMersenneRemainder x n →
        (∀ k : ℕ, n + k + 1 ∈ greedyMersenneSupport x) ∧
          ∀ k : ℕ, mersenneTail (n + k) < greedyMersenneRemainder x (n + k)) ∧
      ((greedyMersenneSkippedSupport x).Infinite → x ∈ mersenneAchievementSet)
```

<a id="thm-fatal-absorbing-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `fatal_absorbing`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_08/Challenge.lean#L65) (E257_08, line 65), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_08/PaperStatementsN.lean#L135) (PaperStatementsN.lean, line 135), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_08.json) (E257_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-seam-limit"></a>

## Theorem 6.2 (The quotient remainders converge to the greedy deficit), page 42

> *Let $`G`$ be the real greedy support for $`1/2`$, and let $`D_s`$ be the integer-greedy support at row $`s`$. Then
> ``` math
> X_{D_s}(2)\longrightarrow X_G(2),\qquad
>  \frac{\mathrm{rem}(s)}{4^s}\longrightarrow
>  \delta:=\frac12-X_G(2)\ge0.
> ```
> In particular, the following conditions are equivalent: $`1/2\in\mathcal A`$; the full sequence $`\mathrm{rem}(s)/4^s`$ tends to zero; and there exist $`s_j\to\infty`$ with $`\mathrm{rem}(s_j)/4^{s_j}\to0`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_limit_unconditional`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L560)

```lean
theorem paper_seam_limit_unconditional :
    Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfTargetValue) ∧
      Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyLimitDeficit) ∧
      seamGreedyLimitDeficit = 1 / 2 - greedyHalfTargetValue ∧
      0 ≤ seamGreedyLimitDeficit ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
        Tendsto seamGreedyNormalizedRemainder atTop (nhds 0)) ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
        ∃ rows : ℕ → ℕ, SeamGreedyRemainderSubquadraticAlong rows)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.tendsto_seamGreedyFiniteValue_greedyHalfTargetValue`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L438)

```lean
theorem tendsto_seamGreedyFiniteValue_greedyHalfTargetValue :
    Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfTargetValue)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.tendsto_seamGreedyNormalizedRemainder`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L537)

```lean
theorem tendsto_seamGreedyNormalizedRemainder :
    Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyLimitDeficit)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.eventually_seamSupport_agrees`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L370)

```lean
theorem eventually_seamSupport_agrees (K : ℕ) :
    ∀ᶠ s in atTop, ∀ d : ℕ, 1 ≤ d → d ≤ K →
      (d ∈ seamWordSupport (seamGreedyWord s)
        ↔ d ∈ greedyMersenneSupport (1 / 2 : ℝ))
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.seamScaledRem_eq_tailGreedyRemainder`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L259)

```lean
theorem seamScaledRem_eq_tailGreedyRemainder {s : ℕ} (hs : 2 ≤ s) :
    ∀ m : ℕ, m ≤ s - 2 →
      ((seamIntRem s m : ℕ) : ℝ) / (4 : ℝ) ^ s
        = tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) m
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.mem_seamGreedySupport_iff_scaled`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L332)

```lean
theorem mem_seamGreedySupport_iff_scaled {s d : ℕ} (hs : 2 ≤ s) (h2 : 2 ≤ d)
    (hd : d < s) :
    d ∈ seamWordSupport (seamGreedyWord s)
      ↔ seamScaledWeight s d
          ≤ tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) (d - 2)
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.abs_supportValue_sub_le_mersenneTail`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L398)

```lean
theorem abs_supportValue_sub_le_mersenneTail {A B : Set ℕ} {K : ℕ}
    (h : ∀ d : ℕ, 1 ≤ d → d ≤ K → (d ∈ A ↔ d ∈ B)) :
    |positiveMersenneSupportValue A - positiveMersenneSupportValue B|
      ≤ mersenneTail K
```

<a id="thm-seam-limit-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_seam_limit_unconditional`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_11/Challenge.lean#L301) (E257_11, line 301), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_11/PaperStructuresBL.lean#L84) (PaperStructuresBL.lean, line 84), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_11.json) (E257_11)
- `tendsto_seamGreedyFiniteValue_greedyHalfTargetValue`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_11/Challenge.lean#L321) (E257_11, line 321), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_11/PaperStructuresBL.lean#L105) (PaperStructuresBL.lean, line 105), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_11.json) (E257_11)
- `tendsto_seamGreedyNormalizedRemainder`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_11/Challenge.lean#L325) (E257_11, line 325), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_11/PaperStructuresBL.lean#L110) (PaperStructuresBL.lean, line 110), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_11.json) (E257_11)
- `eventually_seamSupport_agrees`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_10/Challenge.lean#L128) (E257_10, line 128), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_10/PaperStructuresBJ.lean#L1379) (PaperStructuresBJ.lean, line 1379), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_10.json) (E257_10)
- `seamScaledRem_eq_tailGreedyRemainder`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_12/Challenge.lean#L83) (E257_12, line 83), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_12/PaperStructuresBV.lean#L219) (PaperStructuresBV.lean, line 219), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_12.json) (E257_12)
- `mem_seamGreedySupport_iff_scaled`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_09/Challenge.lean#L328) (E257_09, line 328), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_09/PaperStructuresBB.lean#L103) (PaperStructuresBB.lean, line 103), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_09.json) (E257_09)
- `abs_supportValue_sub_le_mersenneTail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_08/Challenge.lean#L81) (E257_08, line 81), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_08/PaperStatementsAM.lean#L143) (PaperStatementsAM.lean, line 143), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_08.json) (E257_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-two-channel-cap"></a>

## Theorem 6.3 (Two-channel and dyadic cap sufficiency), page 42

> *Suppose that for every $`n\ge0`$ at which the next weight is skipped,
> ``` math
> w_{n+1}>r_n(1/2)\quad\Longrightarrow\quad
>  r_n(1/2)\le 2^{-(n+1)}+\frac13\,4^{-(n+1)}.
> ```
> Then $`1/2\in\mathcal A`$. The stronger bound $`r_n(1/2)\le2^{-(n+1)}`$ at the same skipped ranks also suffices. The first bound retains two positive geometric terms of the full tail; it is larger, and hence less restrictive, than the second. Both are sufficient tests on the specified greedy orbit. The result does not assert that either bound holds at all its skipped ranks.*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_skipped_twoChannelCap`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L1425)

```lean
theorem half_mem_mersenneAchievementSet_of_skipped_twoChannelCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfTwoChannelCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_of_skipped_dyadicCap`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L1444)

```lean
theorem half_mem_mersenneAchievementSet_of_skipped_dyadicCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfDyadicCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="thm-two-channel-cap-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `half_mem_mersenneAchievementSet_of_skipped_twoChannelCap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_12/Challenge.lean#L159) (E257_12, line 159), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_12/PaperStatementsB.lean#L67) (PaperStatementsB.lean, line 67), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_12.json) (E257_12)
- `half_mem_mersenneAchievementSet_of_skipped_dyadicCap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_12/Challenge.lean#L150) (E257_12, line 150), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_12/PaperStatementsB.lean#L57) (PaperStatementsB.lean, line 57), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_12.json) (E257_12)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-second-channel"></a>

## Theorem 6.4 (Second-channel phase separation sufficiency), page 43

> *Define $`P_n=4^n\bigl(2r_n(1/2)-2^{-n}\bigr)`$. If
> ``` math
> \frac16+\frac{37}{56}\,2^{-n}\le
>  \left|P_n-\frac13\right|\qquad\text{for every }n\ge1,
> ```
> then $`1/2\in\mathcal A`$. These are exact rational inequalities because the target and every finite greedy remainder are rational. The cited finite calculation establishes them for $`1\le n\le6`$; it therefore suffices to prove them for every $`n\ge7`$.*
> 
> *Unlike Theorem 6.3, this hypothesis concerns every positive rank, not only skipped ranks. It excludes an explicit interval around $`1/3`$. For example, $`P_n\notin(0,1)`$ implies the displayed inequality when $`n\ge2`$, but no such avoidance theorem for the whole orbit is proved here.*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L3118)

```lean
theorem half_mem_mersenneAchievementSet_of_secondChannelSeparation
    (hseparate : ∀ n : ℕ, 0 < n →
      (1 / 6 : ℝ) + (37 / 56 : ℝ) * ((1 : ℝ) / 2) ^ n
        ≤ |greedyMersenneSecondChannelPhase n - 1 / 3|) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L3151)

```lean
theorem half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven
    (hseparate : ∀ n : ℕ, 7 ≤ n → HalfSecondChannelSeparatedRat n) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="thm-second-channel-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `half_mem_mersenneAchievementSet_of_secondChannelSeparation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_12/Challenge.lean#L138) (E257_12, line 138), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_12/PaperStatementsB.lean#L43) (PaperStatementsB.lean, line 43), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_12.json) (E257_12)
- `half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_12/Challenge.lean#L145) (E257_12, line 145), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_12/PaperStatementsB.lean#L51) (PaperStatementsB.lean, line 51), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_12.json) (E257_12)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-straddle-closed-set"></a>

## Theorem 6.5 (Straddle-prefix closed-set criterion), page 43

> *Suppose that for every $`d\ge0`$ there is a finite support $`D_d\subseteq\{1,\ldots,d\}`$ such that
> ``` math
> X_{D_d}(2)\le t\le X_{D_d}(2)+R_d.
> ```
> Then $`t\in\mathcal A`$. The supports need not agree at different depths: compactness, together with $`R_d\to0`$, supplies a limiting support. Conversely, truncating a support representing $`t`$ supplies such finite supports. Thus this condition is an exact finite-approximation formulation of membership, not a criterion already known to hold for an unresolved target.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.straddle_all_depths_iff_mem`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L42)

```lean
theorem straddle_all_depths_iff_mem (t : ℝ) :
    (∀ d : ℕ, ∃ D : Finset ℕ, (∀ n ∈ D, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑D : Set ℕ) ≤ t ∧
        t ≤ positiveMersenneSupportValue (↑D : Set ℕ) + mersenneTail d) ↔
      t ∈ mersenneAchievementSet
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.straddle_limiting_support_inputs`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L103)

```lean
theorem straddle_limiting_support_inputs :
    IsCompact mersenneAchievementSet ∧
      Filter.Tendsto mersenneTail Filter.atTop (nhds 0)
```

<a id="thm-straddle-closed-set-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `straddle_all_depths_iff_mem`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_12/Challenge.lean#L180) (E257_12, line 180), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_12/PaperStatementsAM.lean#L254) (PaperStatementsAM.lean, line 254), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_12.json) (E257_12)
- `straddle_limiting_support_inputs`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_12/Challenge.lean#L187) (E257_12, line 187), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_12/PaperStatementsAM.lean#L260) (PaperStatementsAM.lean, line 260), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_12.json) (E257_12)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-largest-skip-late"></a>

## Theorem 6.6 (Keeping the largest skipped rank beyond two thirds), page 43

> *Let $`D_s\subseteq\{2,\ldots,s-1\}`$ be the support of the integer-greedy row defined in Section <a href="#ssec:seam-model" data-reference-type="ref" data-reference="ssec:seam-model">5.4</a>. Assume the following implication for every $`s\ge14`$ and every largest omitted rank $`d=\max(\{2,\ldots,s-1\}\smallsetminus D_s)`$:
> ``` math
> 2s<3d\quad\Longrightarrow\quad
>  2(s+1)<3d\quad\text{or}\quad s\notin D_{s+1}.
> ```
> Then $`1/2\in\mathcal A`$. The hypothesis says that either the same omitted rank remains beyond two thirds of the next row, or the next row omits its terminal rank. The latter alternative is exactly an upper or middle transition in the preceding classification.*
> 
> *The cited finite calculation establishes the initial inequality at row $`14`$. The displayed implication then preserves the inequality by induction and supplies omitted ranks tending to infinity. It is an unproved condition on every later row; the verified base case alone does not establish it.*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderLargestSkipInduction.lean#L167)

```lean
theorem half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket
    (hstep : LargestSkipLateStepSocket) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.largestSkipLateAt_fourteen`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderLargestSkipInduction.lean#L73)

```lean
theorem largestSkipLateAt_fourteen : LargestSkipLateAt 14
```

where [`LargestSkipLateAt`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderLargestSkipInduction.lean#L27) is

```lean
def LargestSkipLateAt (s : ℕ) : Prop :=
  ∃ d : ℕ,
    IsLargestFalseRank (seamGreedyWord s) d ∧ 2 * s < 3 * d
```

3. [`Erdos249257.seamGreedy_terminal_false_iff_upperOrMiddle`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L57)

```lean
theorem seamGreedy_terminal_false_iff_upperOrMiddle
    (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = false ↔
      SeamGreedyUpperOrMiddleAt s hs
```

<a id="thm-largest-skip-late-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_13/Challenge.lean#L312) (E257_13, line 312), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_13/PaperStructuresCD.lean#L89) (PaperStructuresCD.lean, line 89), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_13.json) (E257_13)
- `largestSkipLateAt_fourteen`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_09/Challenge.lean#L309) (E257_09, line 309), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_09/PaperStructuresBB.lean#L89) (PaperStructuresBB.lean, line 89), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_09.json) (E257_09)
- `seamGreedy_terminal_false_iff_upperOrMiddle`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_09/Challenge.lean#L312) (E257_09, line 312), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_09/Statement.lean#L312) (Statement.lean, line 312), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_09.json) (E257_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-middle-producer-escape"></a>

## Theorem 6.7 (Two sufficient bounds at middle transitions), page 43

> *Suppose that at every middle transition with row $`s\ge13`$,
> ``` math
> |D_s|+p_s^-+5<4\,\mathrm{rem}(s).
> ```
> Then $`1/2\in\mathcal A`$. The stronger condition $`\mathrm{rem}(s)\ge s`$ at all such rows also suffices.*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerCardEscape`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2364)

```lean
theorem half_mem_mersenneAchievementSet_of_middleProducerCardEscape
    (hcard : SeamMiddleProducerCardEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerRowEscape`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2371)

```lean
theorem half_mem_mersenneAchievementSet_of_middleProducerRowEscape
    (hrow : SeamMiddleProducerRowEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="thm-middle-producer-escape-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `half_mem_mersenneAchievementSet_of_middleProducerCardEscape`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_13/Challenge.lean#L317) (E257_13, line 317), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_13/PaperStructuresCD.lean#L95) (PaperStructuresCD.lean, line 95), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_13.json) (E257_13)
- `half_mem_mersenneAchievementSet_of_middleProducerRowEscape`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_13/Challenge.lean#L322) (E257_13, line 322), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_13/PaperStructuresCD.lean#L101) (PaperStructuresCD.lean, line 101), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_13.json) (E257_13)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-middle-allright-defect"></a>

## Theorem 6.8 (The tail inequality at a final middle transition), page 44

> *Suppose row $`D\ge13`$ is middle and all rows after it are right. Let $`F_D=D_D\cup\{D\}`$ and put
> ``` math
> C_D=4\,\mathrm{rem}(D)-p_D^--4,\qquad
>  \Theta_D=\sum_{j\ge1}c_{F_D}(2D+2+j)2^{-j}.
> ```
> Then $`C_D<\Theta_D`$. Since $`0\le\Theta_D\le|F_D|`$, an estimate in the opposite direction would exclude this scenario. No such reverse estimate is assumed or proved here. Remark <a href="#rem:tail-dominance-open" data-reference-type="ref" data-reference="rem:tail-dominance-open">260</a> states the corresponding sufficient hypothesis with the value $`-3`$ excepted.*

The Lean declarations below together state this result or one that implies it. The hypotheses are the printed ones: row $D$ is middle through its two branch inequalities, where the natural-number subtraction is exact since $p_D^-<2^{D+1}$, and each later row $s$ is right, written as $D_{s+1}=D_s\cup\{s\}$. Under them the Lean statements prove $C_D<\Theta_D$, with $C_D=4\,\mathrm{rem}(D)-p_D^--4$ identified separately, and the bounds $0\le\Theta_D\le|F_D|$; they add a second conclusion, $\tfrac12-X_{D_D}(2)<w_D$.

1. [`Erdos249257.middleProducer_allRight_forces_carry_lt_tail`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1814)

```lean
theorem middleProducer_allRight_forces_carry_lt_tail
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (producerCarry
        (insert D
          (↑(seamWordSupport
            (seamAdjacentCut D (by omega)).below) : Set ℕ)) D : ℝ) <
      binaryCoeffTail
        (supportCoeff
          (insert D
            (↑(seamWordSupport
              (seamAdjacentCut D (by omega)).below) : Set ℕ)))
        (2 * D + 2)
```

2. [`Erdos249257.middleProducer_allRight_forces_rational_skip`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1888)

```lean
theorem middleProducer_allRight_forces_rational_skip
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    seamWordRationalRemainder (seamGreedyWord D) <
      mersenneWeightRat D
```

3. [`Erdos249257.producerCarry_insert_seamBelowSupport_eq_middleCoordinate`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderProducerLowerBound.lean#L150)

```lean
theorem producerCarry_insert_seamBelowSupport_eq_middleCoordinate
    (s : ℕ) (hs : 5 ≤ s) :
    producerCarry
        (insert s
          (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)) s =
      4 * ((seamAdjacentCut s hs).remainder : ℤ) -
        ((seamAdjacentCut s hs).belowPulse : ℤ) - 4
```

4. [`Erdos249257.binaryCoeffTail_nonneg`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GenericTailOrbitRigidity.lean#L78)

```lean
theorem binaryCoeffTail_nonneg (c : ℕ → ℕ) (N : ℕ) :
    0 ≤ binaryCoeffTail c N
```

5. [`Erdos249257.binaryCoeffTail_supportCoeff_coe_finset_le_card`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L222)

```lean
theorem binaryCoeffTail_supportCoeff_coe_finset_le_card
    (F : Finset ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff (↑F : Set ℕ)) N ≤ (F.card : ℝ)
```

<a id="thm-middle-allright-defect-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `middleProducer_allRight_forces_carry_lt_tail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_14/Challenge.lean#L259) (E257_14, line 259), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_14/Statement.lean#L262) (Statement.lean, line 262), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_14.json) (E257_14)
- `middleProducer_allRight_forces_rational_skip`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_13/Challenge.lean#L332) (E257_13, line 332), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_13/Statement.lean#L316) (Statement.lean, line 316), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_13.json) (E257_13)
- `producerCarry_insert_seamBelowSupport_eq_middleCoordinate`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_14/Challenge.lean#L281) (E257_14, line 281), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_14/PaperStructuresCE.lean#L81) (PaperStructuresCE.lean, line 81), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_14.json) (E257_14)
- `binaryCoeffTail_nonneg`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_03/Challenge.lean#L73) (E257_03, line 73), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_03/PaperStatementsAE.lean#L69) (PaperStatementsAE.lean, line 69), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_03.json) (E257_03)
- `binaryCoeffTail_supportCoeff_coe_finset_le_card`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_14/Challenge.lean#L45) (E257_14, line 45), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_14/PaperStatementsAT.lean#L41) (PaperStatementsAT.lean, line 41), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_14.json) (E257_14)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-two-sided-dyadic"></a>

## Theorem 6.9 (A conditional two-sided dyadic bound), page 44

> *Assume the following two conditions for every row $`s\ge5`$:
> ``` math
> \begin{aligned}
>  \mathrm M\text{ at }s&\quad\Longrightarrow\quad
>  4\,\mathrm{rem}(s)-p_s^--4\notin\{-3,-2,-1\},\\
>  \mathrm R\text{ at }s\text{ and }o_s\le2^s
>  &\quad\Longrightarrow\quad 4o_s+p_s^+\le2^{s+2}.
>  \end{aligned}
> ```
> Then at every row $`s\ge5`$,
> ``` math
> \mathrm{rem}(s)\le2^s\quad\text{or}\quad o_s\le2^s.
> ```
> The first hypothesis concerns only middle transitions. The second concerns only right transitions at which the old overshoot is at most $`2^s`$. Neither condition is asserted here for the whole sequence.*

The Lean declaration below states this result or one that implies it. The Lean hypothesis is the printed pair of conditions at every row $s\ge5$, with the branches $\mathrm M$ and $\mathrm R$ written as their defining inequalities, and the conclusion $\mathrm{rem}(s)\le2^s$ or $o_s\le2^s$ at every row $s\ge5$ is the printed one.

[`Erdos249257.SeamTwoSidedDyadicCellEscape.twoSided`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4448)

```lean
theorem SeamTwoSidedDyadicCellEscape.twoSided
    (hescape : SeamTwoSidedDyadicCellEscape)
    (s : ℕ) (hs : 5 ≤ s) :
    seamIntegerGreedyRemainder s ≤ 2 ^ s ∨
      (seamAdjacentCut s hs).overshoot ≤ 2 ^ s
```

<a id="thm-two-sided-dyadic-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `twoSided`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_09/Challenge.lean#L302) (E257_09, line 302), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_09/PaperStructuresBB.lean#L81) (PaperStructuresBB.lean, line 81), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_09.json) (E257_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-upper-reset-band"></a>

## Theorem 6.10 (Upper-reset dyadic-band escape, checked for $`13\le d\le30`$), page 44

> *The upper-reset dyadic-band escape condition requires the following at every actual upper reset $`d\ge13`$: for every $`0\le j\le d`$, the reset charge avoids a linear-width band immediately below the dyadic power $`2^{d-j+1}`$ ($`2^{d-j+1}<\mathrm{resetCharge}`$ or $`\mathrm{resetCharge}+2(d+j)\le 2^{d-j+1}`$). Granted this, $`1/2\in
> \ensuremath{\mathcal A}`$. The linked proof verifies this condition for $`13\le d\le30`$, using exact successor remainders at rows $`14`$–$`31`$ (for example, $`\mathrm{rem}(14)=392`$ and $`\mathrm{rem}(31)=4187487147`$). This finite verification does not supply the hypothesis for every $`d\ge13`$.*

The Lean declarations below together state this result or one that implies it. The first Lean statement is the printed implication from the band condition to $1/2\in\mathcal A$. The second gives the band disjunction, with reset charge $4o_d+p_d^+$, at every actual upper reset $13\le d\le30$ and every $0\le j\le d$, and the third states the successor remainders $\mathrm{rem}(14)=392$ through $\mathrm{rem}(31)=4187487147$. Together they have the printed hypotheses and conclusions.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4790)

```lean
theorem half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape
    (hband : SeamUpperResetDyadicBandEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.seamUpperResetDyadicBandEscape_through_thirty`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderUpperResetBandCertificates.lean#L78)

```lean
theorem seamUpperResetDyadicBandEscape_through_thirty
    (d : ℕ) (hd13 : 13 ≤ d) (hd30 : d ≤ 30)
    (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    ∀ j : ℕ, j ≤ d →
      2 ^ (d - j + 1) <
          4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse ∨
          4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
          2 ^ (d - j + 1)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_successor_remainders_fourteen_through_thirtyone`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L44)

```lean
theorem paper_successor_remainders_fourteen_through_thirtyone :
    seamIntegerGreedyRemainder 14 = 392 ∧
      seamIntegerGreedyRemainder 15 = 34333 ∧
      seamIntegerGreedyRemainder 16 = 71791 ∧
      seamIntegerGreedyRemainder 17 = 156085 ∧
      seamIntegerGreedyRemainder 18 = 362187 ∧
      seamIntegerGreedyRemainder 19 = 924455 ∧
      seamIntegerGreedyRemainder 20 = 549353 ∧
      seamIntegerGreedyRemainder 21 = 100251 ∧
      seamIntegerGreedyRemainder 22 = 4595307 ∧
      seamIntegerGreedyRemainder 23 = 9992613 ∧
      seamIntegerGreedyRemainder 24 = 23193229 ∧
      seamIntegerGreedyRemainder 25 = 59218477 ∧
      seamIntegerGreedyRemainder 26 = 35546625 ∧
      seamIntegerGreedyRemainder 27 = 7968765 ∧
      seamIntegerGreedyRemainder 28 = 300310513 ∧
      seamIntegerGreedyRemainder 29 = 664371133 ∧
      seamIntegerGreedyRemainder 30 = 1583742700 ∧
      seamIntegerGreedyRemainder 31 = 4187487147
```

<a id="thm-upper-reset-band-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_13/Challenge.lean#L327) (E257_13, line 327), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_13/PaperStructuresCD.lean#L107) (PaperStructuresCD.lean, line 107), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_13.json) (E257_13)
- `seamUpperResetDyadicBandEscape_through_thirty`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_15/Challenge.lean#L236) (E257_15, line 236), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_15/PaperStructuresBN.lean#L75) (PaperStructuresBN.lean, line 75), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_15.json) (E257_15)
- `paper_successor_remainders_fourteen_through_thirtyone`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_38/Challenge.lean#L352) (E257_38, line 352), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_38/PaperStructuresBP.lean#L109) (PaperStructuresBP.lean, line 109), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_38.json) (E257_38)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-mobius-centred-nonneg"></a>

## Theorem 6.11 (Möbius-centred carry nonnegativity below $`1/2`$), page 45

> *If $`1\notin A`$ and $`X_A(2)<1/2`$, then $`C_A(N)\ge0`$ for every $`N`$. Indeed,
> ``` math
> \operatorname{ihc}(A,N)=2^{N+1}(1/2-X_A(2))+
>  \sum_{j>N+1}c_A(j)2^{N+1-j}>0.
> ```
> The carry is an integer, so it is at least $`1`$; subtracting $`1`$ gives the asserted nonnegativity of the centred carry. The strict inequality and integrality are both needed in this argument. The statement is about the divisor counts $`c_A`$, not a new irrationality criterion.*

The Lean declarations below together state this result.

1. [`Erdos249257.mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L94)

```lean
theorem mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
    (A : Set ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry A N
```

2. [`Erdos249257.HalfCarryReachability.integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCarryReachability.lean#L871)

```lean
theorem integerHalfCarry_eq_scaled_residual_add_tail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (integerHalfCarry A N : ℝ) =
      (2 : ℝ) ^ (N + 1) * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) +
        binaryCoeffTail (supportCoeff A) (N + 1)
```

<a id="thm-mobius-centred-nonneg-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L111) (E257_16, line 111), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStatementsI.lean#L34) (PaperStatementsI.lean, line 34), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)
- `integerHalfCarry_eq_scaled_residual_add_tail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_03/Challenge.lean#L99) (E257_03, line 99), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_03/PaperStatementsE.lean#L35) (PaperStatementsE.lean, line 35), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_03.json) (E257_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-sqrt-bound-route"></a>

## Theorem 6.12 (A square-root bound on the greedy carry), page 45

> *For the greedy support $`G=G_{1/2}`$, the centred carry is nonnegative. If in addition
> ``` math
> C_G(N)\le2\sqrt N+4\qquad\text{for every }N\ge0,
> ```
> then $`G`$ has infinitely many skipped indices and $`X_G(2)=1/2`$. The unresolved part is the upper bound along this particular orbit. The carry identity explains its strength: a positive gap $`1/2-X_G(2)`$ would contribute a term of order $`2^N`$, which cannot satisfy a square-root bound. This is distinct from the reset-deviation hypothesis of Theorem 6.10; no equivalence between the two hypotheses is asserted.*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfCarryReachability.greedy_mobiusCenteredHalfCarry_nonneg`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCarryReachability.lean#L919)

```lean
theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N
```

2. [`Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCarryReachability.lean#L834)

```lean
theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
    (hnonneg : ∀ N : ℕ,
      0 ≤ mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2
```

3. [`Erdos249257.HalfCarryReachability.infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCarryReachability.lean#L817)

```lean
theorem infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound
    (A : Set ℕ) (hzero : 0 ∉ A) (hone : 1 ∉ A)
    (hnonneg : ∀ N : ℕ, 0 ≤ mobiusCenteredHalfCarry A N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry A N : ℝ) ≤
        2 * Real.sqrt (N : ℝ) + 4) :
    A.Infinite ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2
```

<a id="thm-sqrt-bound-route-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `greedy_mobiusCenteredHalfCarry_nonneg`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L144) (E257_16, line 144), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStatementsD.lean#L139) (PaperStatementsD.lean, line 139), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)
- `greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L131) (E257_16, line 131), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStatementsD.lean#L114) (PaperStatementsD.lean, line 114), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)
- `infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L155) (E257_16, line 155), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStatementsE.lean#L25) (PaperStatementsE.lean, line 25), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-frozen-margin"></a>

## Theorem 6.13 (Equivalent sign and vanishing conditions), page 45

> *For the prefix $`D=G\cap\{1,\ldots,k\}`$ define
> ``` math
> F_k(J)=\sum_{i=1}^{J}c_D(k+1+i)2^{J-i}-2^J C_D(k).
> ```
> This is a finite integer expression: it compares the next $`J`$ divisor counts of the fixed prefix with its centred carry. Let $`s_n`$ denote the integer greedy remainder at depth $`2n`$, with weights $`q(2n,d)`$ for $`2\le d<n`$ and target $`2^{2n-1}-2^n`$. The following conditions each imply $`1/2\in\mathcal A`$:*
> 
> 1.  *For every skipped rank $`n\ge3`$, $`F_{n-1}(n)\ge0`$.*
> 
> 2.  *For every skipped rank $`n\ge3`$ at which the real and integer greedy words agree on $`\{2,\ldots,n-1\}`$, $`s_n=0`$.*
> 
> 3.  *For every skipped rank $`n\ge3`$, $`B(2n)<s_n`$.*
> 
> *Conditions (i) and (ii) are equivalent. Condition (iii) implies them; no converse or strict separation is established here. These hypotheses must hold at every indicated skipped rank, not merely through a finite computed range.*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L633)

```lean
theorem half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
    (hsign : HalfGreedySkippedFullShellNonnegative) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.skippedSeamAlignmentZero_iff_skippedFullShellNonnegative`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L671)

```lean
theorem skippedSeamAlignmentZero_iff_skippedFullShellNonnegative :
    HalfGreedySkippedSeamAlignmentZero ↔
      HalfGreedySkippedFullShellNonnegative
```

3. [`Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L722)

```lean
theorem half_mem_mersenneAchievementSet_of_skippedSeamEscape
    (hescape : HalfGreedySkippedSeamEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="thm-frozen-margin-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L174) (E257_16, line 174), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStatementsF.lean#L185) (PaperStatementsF.lean, line 185), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)
- `skippedSeamAlignmentZero_iff_skippedFullShellNonnegative`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L260) (E257_16, line 260), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStructuresBJ.lean#L1313) (PaperStructuresBJ.lean, line 1313), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)
- `half_mem_mersenneAchievementSet_of_skippedSeamEscape`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L255) (E257_16, line 255), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStructuresBJ.lean#L1294) (PaperStructuresBJ.lean, line 1294), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-full-support-catalogue"></a>

## Theorem 6.14 (Erdős–Borwein full-support irrationality, unconditional), page 45

> *For every integer $`b\ge2`$, the sum $`\sum_{n\ge1}(b^n-1)^{-1}`$ is irrational. This is Erdős’s theorem \[erdos1948\]; at base $`2`$ the sum is the Erdős–Borwein constant. The result concerns full support, not all its infinite subsets.*

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSum_full_support`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L8328)

```lean
theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1))
```

<a id="thm-full-support-catalogue-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSum_full_support`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L48) (E257_05, line 48), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L52) (PaperStatementsAG.lean, line 52), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-pairwise-coprime"></a>

## Theorem 6.15 (Pairwise-coprime support irrationality, Erdős 1968), page 45

> *For every integer $`b\ge2`$ and every infinite pairwise-coprime support $`A\subseteq\mathbb{N}_{>0}`$ with summable reciprocals, $`\sum_{a\in A} 1/(b^a-1)`$ is irrational.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one; its set $A$ may formally contain $0$, which no infinite pairwise-coprime set does, since $\gcd(0,a)=a$.

[`Erdos249257.irrational_erdosSupportSeries_pairwise_coprime`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L10776)

```lean
theorem irrational_erdosSupportSeries_pairwise_coprime (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (hA : A.Infinite) (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable (Set.indicator A fun a : ℕ => (1 : ℝ) / a)) :
    Irrational (erdosSupportSeries b A)
```

<a id="thm-pairwise-coprime-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSupportSeries_pairwise_coprime`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L292) (E257_16, line 292), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStatementsAG.lean#L81) (PaperStatementsAG.lean, line 81), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-weighted-coeff-engine"></a>

## Theorem 6.16 (Irrationality from divisible coefficient blocks), page 46

> *Let $`b\ge2`$ be an integer and let $`c:\mathbb N\to\mathbb N`$ satisfy $`c(n)\le n`$ for every $`n`$. Suppose that for every integer $`q\ge1`$ there are nonnegative integers $`N,K,L,C`$, with $`K\le L`$, such that
> ``` math
> \begin{aligned}
>  b^r&\mid c(N+r) &&(1\le r\le K),\\
>  \sum_{r=K+1}^{L}c(N+r)b^{L-r}&\le C,\\
>  c(N+L+1+t)&>0 &&\text{for some integer }t\ge0,\\
>  q(C+N+L+2)&<b^L.
>  \end{aligned}
> ```
> Then $`\sum_{n\ge1}c(n)b^{-n}`$ is irrational.*

The Lean declaration below states this result.

[`Erdos249257.irrational_coeff_series_of_weighted_coeff_block_certificates`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L8665)

```lean
theorem irrational_coeff_series_of_weighted_coeff_block_certificates
    (b : ℕ) (c : ℕ → ℕ) (hb : 2 ≤ b) (hgrowth : ∀ m : ℕ, c m ≤ m)
    (hcert : ∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
        (∀ r ∈ Finset.Icc 1 K, b ^ r ∣ c (N + r)) ∧
        (∑ r ∈ Finset.Icc (K + 1) L, c (N + r) * b ^ (L - r) ≤ C) ∧
        (∃ t : ℕ, 0 < c (N + L + 1 + t)) ∧
        q * (C + (N + L + 2)) < b ^ L) :
    Irrational (∑' m : ℕ, ((c (m + 1) : ℝ)) / (b : ℝ) ^ (m + 1))
```

<a id="thm-weighted-coeff-engine-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_coeff_series_of_weighted_coeff_block_certificates`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L271) (E257_16, line 271), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStatementsAG.lean#L40) (PaperStatementsAG.lean, line 40), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-lcm-gap-engine"></a>

## Theorem 6.17 (Irrationality from a gap beyond the preceding least common multiple), page 46

> *For an integer base $`b\ge2`$ and strictly increasing support $`a:\mathbb N\to\mathbb N`$ with $`a(0)\ge
> 1`$: if $`a(k)-\mathrm{lcm}(a(0),\dots,a(k-1))\to\infty`$, then $`\sum'_k 1/(b^{a(k)}-1)`$ is irrational. The base may vary over the integers, but the denominators remain $`b^{a(k)}-1`$. Applying the argument to another denominator sequence would require its own divisibility and tail estimates.*

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSum_of_lcm_gap`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L5883)

```lean
theorem irrational_erdosSum_of_lcm_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (hgap : Tendsto (fun k => a k - ((Finset.range k).image a).lcm id)
      atTop atTop) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1))
```

<a id="thm-lcm-gap-engine-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSum_of_lcm_gap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L285) (E257_16, line 285), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStatementsAG.lean#L55) (PaperStatementsAG.lean, line 55), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-factorial-twopow-support"></a>

## Theorem 6.18 (Factorial-support and $`2^k`$-support instances), page 46

> *For every integer $`b\ge2`$, both
> ``` math
> \sum_{k\ge0}\frac1{b^{(k+1)!}-1}
>  \quad\text{and}\quad
>  \sum_{k\ge0}\frac1{b^{2^k}-1}
> ```
> are irrational. These are instances of the preceding theorem. For the factorial support the preceding least common multiple is $`k!`$ when $`k\ge1`$, so the gap is $`k\,k!`$. For the powers of two it is $`2^{k-1}`$, so the gap is $`2^{k-1}`$. Both tend to infinity. The conclusion concerns these two supports, not every infinite support.*

The Lean declarations below together state this result or one that implies it. The two Lean statements are the two irrationality claims for every $b\ge2$, indexed as printed by $k\ge0$. The remarks on the preceding least common multiples and gaps are elementary identities outside the Lean statements: $\operatorname{lcm}(1!,\ldots,k!)=k!$ with $(k+1)!-k!=k\,k!$, and $\operatorname{lcm}(1,2,\ldots,2^{k-1})=2^{k-1}$ with $2^k-2^{k-1}=2^{k-1}$.

1. [`Erdos249257.irrational_erdosSum_factorial_support`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L6035)

```lean
theorem irrational_erdosSum_factorial_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (Nat.factorial (k + 1)) - 1))
```

2. [`Erdos249257.irrational_erdosSum_two_pow_support`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L6059)

```lean
theorem irrational_erdosSum_two_pow_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (2 ^ k) - 1))
```

<a id="thm-factorial-twopow-support-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSum_factorial_support`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_16/Challenge.lean#L281) (E257_16, line 281), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_16/PaperStatementsAG.lean#L49) (PaperStatementsAG.lean, line 49), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_16.json) (E257_16)
- `irrational_erdosSum_two_pow_support`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L44) (E257_17, line 44), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAG.lean#L54) (PaperStatementsAG.lean, line 54), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-multiples-support"></a>

## Theorem 6.19 (Multiples-support irrationality via dilation), page 47

> *For integers $`b\ge2`$ and $`d\ge1`$,
> ``` math
> X_{d\mathbb{N}_{>0}}(b)=\sum_{k\ge1}\frac1{(b^d)^k-1}
> ```
> is irrational. This is the full-support result (Theorem 6.14) at the integer base $`b^d`$; no new support argument is required.*

The Lean declarations below together state this result or one that implies it. The Lean statements give the printed identity and irrationality for $b\ge2$ and $d\ge1$. The Lean set of multiples of $d$ also contains $0$, whose term $1/(b^0-1)$ is $0$ under the convention $1/0=0$.

1. [`Erdos249257.erdosSupportSeries_multiples_eq_pow_base_full_support`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L9054)

```lean
theorem erdosSupportSeries_multiples_eq_pow_base_full_support
    (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    erdosSupportSeries b {n : ℕ | d ∣ n}
      = ∑' k : ℕ, (1 : ℝ) / (((b : ℝ) ^ d) ^ (k + 1) - 1)
```

2. [`Erdos249257.irrational_erdosSupportSeries_multiples`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L9103)

```lean
theorem irrational_erdosSupportSeries_multiples (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    Irrational (erdosSupportSeries b {n : ℕ | d ∣ n})
```

<a id="thm-multiples-support-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `erdosSupportSeries_multiples_eq_pow_base_full_support`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L38) (E257_17, line 38), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAG.lean#L28) (PaperStatementsAG.lean, line 28), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `irrational_erdosSupportSeries_multiples`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L48) (E257_17, line 48), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAG.lean#L64) (PaperStatementsAG.lean, line 64), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-periodic-support"></a>

## Theorem 6.20 (Periodic-support irrationality), page 47

> *Let $`b\ge2`$ and $`m\ge1`$ be integers. Suppose $`A\subseteq\mathbb{N}_{>0}`$ is nonempty and satisfies $`n\in A`$ if and only if $`n+m\in A`$ for every $`n\ge1`$. Then $`X_A(b)`$ is irrational.*
> 
> *The indicator of $`A`$ is a nonzero purely periodic integer weight, so this follows from Luca and Tachiya’s theorem stated above. The linked declaration supplies a separate formal proof. At $`m=1`$ the only nonempty periodic support is full support; residue classes and unions of residue classes give the other immediate examples.*

The Lean declaration below states this result or one that implies it. The Lean statement takes a set $A\subseteq\N$ with a positive element and asks for $n+m\in A\iff n\in A$ at every $n\ge1$. The printed support is such a set, since it is nonempty and lies in $\Npos$, so the Lean theorem gives the printed conclusion. It is more general only in allowing $0\in A$, whose term is $0$ under the convention $1/0=0$.

[`ErdosProblems.Erdos257.PaperCompleteR20.irrational_erdosSupportSeries_positivePeriodic`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR20/PositivePeriodicSupport.lean#L49)

```lean
theorem irrational_erdosSupportSeries_positivePeriodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, 0 < n → (n + m ∈ A ↔ n ∈ A))
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A)
```

<a id="thm-periodic-support-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-eventually-periodic"></a>

## Theorem 6.21 (Eventually-periodic support irrationality), page 47

> *Let $`b\ge2`$ and $`m\ge1`$ be integers. An infinite support whose membership is $`m`$-periodic from some threshold $`N_0`$ onward has irrational $`X_A(b)`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one and also allows $0\in A$, whose term $1/(b^0-1)$ is $0$ under the convention $1/0=0$.

[`Erdos249257.irrational_erdosSupportSeries_eventuallyPeriodic`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L11604)

```lean
theorem irrational_erdosSupportSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → (n + m ∈ A ↔ n ∈ A))
    (hinf : A.Infinite) :
    Irrational (erdosSupportSeries b A)
```

<a id="thm-eventually-periodic-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSupportSeries_eventuallyPeriodic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L52) (E257_05, line 52), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L64) (PaperStatementsAG.lean, line 64), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-residue-odd"></a>

## Theorem 6.22 (Residue-class and odd-support irrationality), page 47

> *For integers $`b\ge2`$, $`m\ge1`$ and a residue $`c`$, $`\sum_{\substack{n\ge1\\n\equiv c\pmod m}}(b^n-1)^{-1}`$ is irrational. Specializing $`m=2,c=1`$: $`\sum_{n\text{ odd}} 1/(b^n-1)`$ is irrational for every $`b\ge 2`$, the case treated explicitly in \[lucatachiya2017, Example 2, p. 140\].*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones, with the residue $c$ taken in $\N$, which covers every class modulo $m$. The Lean class also contains $0$ when $m\mid c$, and that term is $0$ under the convention $1/0=0$.

1. [`Erdos249257.irrational_erdosSupportSeries_residueClass`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L11672)

```lean
theorem irrational_erdosSupportSeries_residueClass
    (b m c : ℕ) (hb : 2 ≤ b) (hm : 0 < m) :
    Irrational (erdosSupportSeries b {n : ℕ | n % m = c % m})
```

2. [`Erdos249257.irrational_erdosSupportSeries_odd`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L11686)

```lean
theorem irrational_erdosSupportSeries_odd (b : ℕ) (hb : 2 ≤ b) :
    Irrational (erdosSupportSeries b {n : ℕ | Odd n})
```

<a id="thm-residue-odd-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSupportSeries_residueClass`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L52) (E257_17, line 52), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAG.lean#L85) (PaperStatementsAG.lean, line 85), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `irrational_erdosSupportSeries_odd`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L59) (E257_05, line 59), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L74) (PaperStatementsAG.lean, line 74), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-signed-periodic"></a>

## Theorem 6.23 (A formal dichotomy for signed periodic weights), page 47

> *Let $`b\ge2`$ and $`m\ge1`$ be integers, and let $`w:\mathbb{N}_{>0}\to\mathbb{Z}`$ be $`m`$-periodic. Put
> ``` math
> x=\sum_{a\ge1}\frac{w(a)}{b^a-1},\qquad
>  c_w(n)=\sum_{d\mid n}w(d).
> ```
> The cited formal argument gives the dichotomy that $`x`$ is irrational or $`b^kx\in\mathbb{Z}`$ for some integer $`k\ge0`$. It excludes the latter alternative if $`c_w`$ has one sign throughout and is nonzero at arbitrarily large indices. These sign assumptions concern $`c_w`$, not $`w`$. As noted above, Luca and Tachiya’s theorem already excludes the terminating alternative for every nonzero periodic $`w`$, without either sign restriction. The zero weight gives $`x=0`$.*

The Lean declarations below together state this result or one that implies it. The dichotomy and the two sign versions, with $c_w(n)\ge0$ for every $n\ge1$ or $c_w(n)\le0$ for every $n\ge1$ and $c_w$ nonzero at arbitrarily large $n$, are the three Lean statements. The Lean weight is defined on $\N$ and periodic from $0$, which for the printed $w$ means setting $w(0)=w(m)$; the term at $a=0$ is $0$ under the convention $1/0=0$, and $c_w(n)$ uses only positive divisors.

1. [`Erdos249257.irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L14175)

```lean
theorem irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n) :
    Irrational (intWeightedErdosSeries b w)
      ∨ ∃ (k : ℕ) (z : ℤ), (b : ℝ) ^ k * intWeightedErdosSeries b w = (z : ℝ)
```

2. [`Erdos249257.irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L14583)

```lean
theorem irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hc0 : ∀ n : ℕ, 0 < n → 0 ≤ intWeightedCoeff w n)
    (hne : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) :
    Irrational (intWeightedErdosSeries b w)
```

3. [`Erdos249257.irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L14643)

```lean
theorem irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hc0 : ∀ n : ℕ, 0 < n → intWeightedCoeff w n ≤ 0)
    (hne : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) :
    Irrational (intWeightedErdosSeries b w)
```

<a id="thm-signed-periodic-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L73) (E257_17, line 73), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAG.lean#L107) (PaperStatementsAG.lean, line 107), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L57) (E257_17, line 57), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAG.lean#L93) (PaperStatementsAG.lean, line 93), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L65) (E257_17, line 65), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAG.lean#L100) (PaperStatementsAG.lean, line 100), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-mersenne-channel-survival"></a>

## Theorem 6.24 (Denominators of finite Mersenne sums), page 48

> *Let $`t\ge1`$ and $`h\ge1`$ be integers, and let $`r\ge1`$ be squarefree with every prime factor at most $`t`$. Let $`P`$ be a set of prime divisors of $`r`$ such that $`t<2p`$ for each $`p\in P`$, and put $`C=\prod_{p\in P}(2^p-1)`$. Then
> ``` math
> \frac{C}{\gcd(C,h)}\ \bigm|\ \operatorname{den}\bigl(hB(r)\bigr).
> ```
> In particular, $`C`$ divides this reduced denominator when $`\gcd(C,h)=1`$. The factors in $`C`$ are pairwise coprime, since $`\gcd(2^p-1,2^q-1)=2^{\gcd(p,q)}-1=1`$ for distinct primes. The assertion concerns this finite signed sum; it does not replace the approximation hypotheses in Theorem 6.14.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L210)

```lean
theorem paper_mersenne_channel_survival
    (P : Finset ℕ) {t h r : ℕ}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hr1 : 1 ≤ r) (hrsf : Squarefree r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p) :
    (∏ p ∈ P, (2 ^ p - 1)) / Nat.gcd (∏ p ∈ P, (2 ^ p - 1)) h ∣
      ((h : ℚ) * paperB r).den
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival_of_coprime_scale`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L234)

```lean
theorem paper_mersenne_channel_survival_of_coprime_scale
    (P : Finset ℕ) {t h r : ℕ}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hr1 : 1 ≤ r) (hrsf : Squarefree r)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hscale : Nat.gcd (∏ p ∈ P, (2 ^ p - 1)) h = 1) :
    (∏ p ∈ P, (2 ^ p - 1)) ∣ ((h : ℚ) * paperB r).den
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factor_gcd_eq_one`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L248)

```lean
theorem paper_channel_factor_gcd_eq_one
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 2 ^ Nat.gcd p q - 1 ∧
      Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 1
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factors_pairwise_coprime`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L260)

```lean
theorem paper_channel_factors_pairwise_coprime
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) :
    (P : Set ℕ).Pairwise fun p q => Nat.Coprime (2 ^ p - 1) (2 ^ q - 1)
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paperB_eq_divInt_paperA`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L118)

```lean
theorem paperB_eq_divInt_paperA {r : ℕ} (hr : Squarefree r) :
    paperB r = Rat.divInt (paperA r) (RadicalMobiusShadow.mersenne r : ℤ)
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paperB_eq_baseMobiusShadow`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L100)

```lean
theorem paperB_eq_baseMobiusShadow {r : ℕ} (hr : Squarefree r) :
    paperB r = RadicalMobiusShadow.baseMobiusShadow r
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.paperA_eq_mobiusNumerator`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L83)

```lean
theorem paperA_eq_mobiusNumerator {r : ℕ} (hr : Squarefree r) :
    paperA r = RadicalMobiusShadow.mobiusNumerator r
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.channelProduct_coprime_mobiusNumerator_of_one_le`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L163)

```lean
theorem channelProduct_coprime_mobiusNumerator_of_one_le
    {P : Finset ℕ} {t r : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    Nat.Coprime (∏ p ∈ P, RadicalMobiusShadow.mersenne p)
      (RadicalMobiusShadow.mobiusNumerator r).natAbs
```

9. [`ErdosProblems.Erdos257.PaperCompleteR21.upperHalfChannel_survivorProduct_dvd_den_of_one_le`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L187)

```lean
theorem upperHalfChannel_survivorProduct_dvd_den_of_one_le
    (P : Finset ℕ) {t r h : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    (∏ p ∈ P, RadicalMobiusShadow.mersenne p) /
        Nat.gcd (∏ p ∈ P, RadicalMobiusShadow.mersenne p) h ∣
      (Rat.divInt ((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r)
        (RadicalMobiusShadow.mersenne r : ℤ)).den
```

<a id="thm-mersenne-channel-survival-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_mersenne_channel_survival`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L161) (E257_17, line 161), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L148) (PaperStatementsAD.lean, line 148), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `paper_mersenne_channel_survival_of_coprime_scale`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L171) (E257_17, line 171), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L157) (PaperStatementsAD.lean, line 157), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `paper_channel_factor_gcd_eq_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L150) (E257_17, line 150), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L118) (PaperStatementsAD.lean, line 118), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `paper_channel_factors_pairwise_coprime`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L156) (E257_17, line 156), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L123) (PaperStatementsAD.lean, line 123), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `paperB_eq_divInt_paperA`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L146) (E257_17, line 146), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L115) (PaperStatementsAD.lean, line 115), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `paperB_eq_baseMobiusShadow`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L142) (E257_17, line 142), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L112) (PaperStatementsAD.lean, line 112), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `paperA_eq_mobiusNumerator`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L138) (E257_17, line 138), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L109) (PaperStatementsAD.lean, line 109), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `channelProduct_coprime_mobiusNumerator_of_one_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L129) (E257_17, line 129), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L101) (PaperStatementsAD.lean, line 101), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `upperHalfChannel_survivorProduct_dvd_den_of_one_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L181) (E257_17, line 181), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L186) (PaperStatementsAD.lean, line 186), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `paperB_eq_divInt_paperA`:

```lean
theorem paperB_eq_divInt_paperA {r : ℕ} (hr : Squarefree r) :
    paperB r = Rat.divInt (paperA r) (mersenne r : ℤ) := by sorry
```

Challenge for `paperB_eq_baseMobiusShadow`:

```lean
theorem paperB_eq_baseMobiusShadow {r : ℕ} (hr : Squarefree r) :
    paperB r = baseMobiusShadow r := by sorry
```

Challenge for `paperA_eq_mobiusNumerator`:

```lean
theorem paperA_eq_mobiusNumerator {r : ℕ} (hr : Squarefree r) :
    paperA r = mobiusNumerator r := by sorry
```

Challenge for `channelProduct_coprime_mobiusNumerator_of_one_le`:

```lean
theorem channelProduct_coprime_mobiusNumerator_of_one_le
    {P : Finset ℕ} {t r : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    Nat.Coprime (∏ p ∈ P, mersenne p)
      (mobiusNumerator r).natAbs := by sorry
```

Challenge for `upperHalfChannel_survivorProduct_dvd_den_of_one_le`:

```lean
theorem upperHalfChannel_survivorProduct_dvd_den_of_one_le
    (P : Finset ℕ) {t r h : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    (∏ p ∈ P, mersenne p) /
        Nat.gcd (∏ p ∈ P, mersenne p) h ∣
      (Rat.divInt ((h : ℤ) * mobiusNumerator r)
        (mersenne r : ℤ)).den := by sorry
```

<a id="thm-mersenne-channel-growth"></a>

## Theorem 6.25 (Exponential growth of the reduced denominators), page 48

> *For an integer $`t\ge5`$, put
> ``` math
> H_t=\operatorname{lcm}(1,\ldots,t),\quad
>  r_t=\prod_{p\le t}p,\quad h_t=H_t/r_t,\quad
>  D_t=\operatorname{den}\bigl(h_tB(r_t)\bigr),
> ```
> where the product is over primes. Then $`D_t\ge2^{t/2}`$. Its exact denominator is
> ``` math
> D_t=\frac{2^{r_t}-1}{\gcd(2^{r_t}-1,h_tA_{r_t})}.
> ```*

The Lean declarations below together state this result.

1. [`Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/MersenneShadowDenominatorGrowth.lean#L85)

```lean
theorem lcmHeight_scaledMobiusShadow_den_lower_bound
    {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den
```

2. [`Erdos249257.MersenneShadowDenominatorGrowth.upperHalfMersenneProduct_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/MersenneShadowDenominatorGrowth.lean#L60)

```lean
theorem upperHalfMersenneProduct_lower_bound {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p
```

3. [`Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_exact`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/MersenneShadowDenominatorGrowth.lean#L147)

```lean
theorem lcmHeight_scaledMobiusShadow_den_exact (t : ℕ) :
    ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den =
      RadicalMobiusShadow.mersenne (lcmRadical t) /
        Nat.gcd (RadicalMobiusShadow.mersenne (lcmRadical t))
          (lcmScale t *
            (CyclicTensorMobiusShadow.oddJordanScalar (lcmRadical t)).natAbs)
```

<a id="thm-mersenne-channel-growth-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `lcmHeight_scaledMobiusShadow_den_lower_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L117) (E257_17, line 117), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L62) (PaperStatementsAD.lean, line 62), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `upperHalfMersenneProduct_lower_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_17/Challenge.lean#L124) (E257_17, line 124), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_17/PaperStatementsAD.lean#L68) (PaperStatementsAD.lean, line 68), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_17.json) (E257_17)
- `lcmHeight_scaledMobiusShadow_den_exact`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_06/Challenge.lean#L95) (E249_06, line 95), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_06/PaperStatementsAR.lean#L20) (PaperStatementsAR.lean, line 20), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_06.json) (E249_06)

Challenge for `lcmHeight_scaledMobiusShadow_den_lower_bound`:

```lean
theorem lcmHeight_scaledMobiusShadow_den_lower_bound
    {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den := by sorry
```

Challenge for `upperHalfMersenneProduct_lower_bound`:

```lean
theorem upperHalfMersenneProduct_lower_bound {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ∏ p ∈ upperHalfPrimes t, mersenne p := by sorry
```

Challenge for `lcmHeight_scaledMobiusShadow_den_exact`:

```lean
theorem lcmHeight_scaledMobiusShadow_den_exact (t : ℕ) :
    ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den =
      mersenne (lcmRadical t) /
        Nat.gcd (mersenne (lcmRadical t))
          (lcmScale t *
            (oddJordanScalar (lcmRadical t)).natAbs) := by sorry
```

<a id="thm-mobius-lambert-identity"></a>

## Theorem 6.28 (The Lambert-series identity for the Möbius function), page 49

> *The absolutely convergent signed series satisfies
> ``` math
> \sum_{d\ge1}\frac{\mu(d)}{2^d-1}=\frac12.
> ```
> This classical identity is also recorded in \[duverneytachiya, Example 1.1, p. 4\]. Expand each denominator geometrically and interchange the absolutely convergent sums. The coefficient of $`2^{-n}`$ is $`\sum_{d\mid n}\mu(d)`$, equal to $`1`$ for $`n=1`$ and $`0`$ otherwise. This proves the identity. Its coefficients are $`-1,0,1`$, not indicators of a support; the identity therefore does not represent $`1/2`$ as a subseries with all coefficients in $`\{0,1\}`$.*

The Lean declaration below states this result or one that implies it. The Lean statement is the printed identity, summed over the positive integers. Absolute convergence follows from $|\mu(d)|/(2^d-1)\le2^{1-d}$.

[`MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/MersenneLambertLadder.lean#L587)

```lean
theorem tsum_moebius_div_two_pow_sub_one_eq_half :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 1 / 2
```

<a id="thm-mobius-lambert-identity-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `tsum_moebius_div_two_pow_sub_one_eq_half`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L60) (E257_18, line 60), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStatementsAJ.lean#L16) (PaperStatementsAJ.lean, line 16), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-negative-mobius-overshoot"></a>

## Corollary 6.29 (Negative-Möbius Boolean support overshoots $`1/2`$), page 49

> *Let $`N=\{d\ge2:\mu(d)=-1\}`$. Isolating the $`d=1`$ term in Theorem 6.28 gives
> ``` math
> X_N(2)=\frac12+
>        \sum_{\substack{d\ge2\\\mu(d)=1}}\frac1{2^d-1}
>        \ge\frac12+\frac1{63}>\frac12,
> ```
> since $`\mu(6)=1`$. This rules out the particular candidate $`N`$. It does not rule out other infinite supports representing $`1/2`$.*

The Lean declarations below together state this result or one that implies it. The Lean statements give the identity $X_N(2)=\frac12+\sum_{d\ge2,\,\mu(d)=1}1/(2^d-1)$ and the conclusion $X_N(2)>\frac12$. The intermediate bound $X_N(2)\ge\frac12+\frac1{63}$ follows from the identity, since every term of the sum is nonnegative and the term at $d=6$ is $1/63$.

1. [`Erdos249257.MobiusSignSupportNoGo.tsum_negativeMobius_eq_half_add_positiveMobiusTail`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/MobiusSignSupportNoGo.lean#L111)

```lean
theorem tsum_negativeMobius_eq_half_add_positiveMobiusTail :
    (∑' d : ℕ+, negativeMobiusTerm d) =
      1 / 2 + ∑' d : ℕ+, positiveMobiusTailTerm d
```

2. [`Erdos249257.MobiusSignSupportNoGo.half_lt_tsum_negativeMobius`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/MobiusSignSupportNoGo.lean#L164)

```lean
theorem half_lt_tsum_negativeMobius :
    (1 : ℝ) / 2 < ∑' d : ℕ+, negativeMobiusTerm d
```

<a id="cor-negative-mobius-overshoot-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `tsum_negativeMobius_eq_half_add_positiveMobiusTail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L84) (E257_18, line 84), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStatementsAQ.lean#L27) (PaperStatementsAQ.lean, line 27), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)
- `half_lt_tsum_negativeMobius`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L80) (E257_18, line 80), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStatementsAQ.lean#L24) (PaperStatementsAQ.lean, line 24), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-half-skip-dichotomy"></a>

## Theorem 6.31 (The half-skip dichotomy via Erdős–Borwein irrationality), page 50

> *The half target satisfies
> ``` math
> \frac12\in\mathcal A\quad\Longleftrightarrow\quad
>  \mathbb N_{>0}\smallsetminus G\text{ is infinite},
> ```
> where $`G`$ is the greedy support for $`1/2`$. In the forward direction, finitely many skipped exponents would express the full Mersenne sum as $`1/2`$ plus a finite rational sum, contradicting Erdős’s full-support irrationality theorem. The reverse implication uses the greedy tail criterion: once a remainder exceeds the whole available tail, every later exponent is selected. Infinitely many skips exclude that failure. The equivalence does not establish that infinitely many skips actually occur.*

The Lean declarations below together state this result or one that implies it. The equivalence is stated as printed, with $\N_{>0}\smallsetminus G$ written as the set of positive exponents omitted by the greedy rule for $1/2$. Irrationality of the full Mersenne sum $\sum_{n\ge1}1/(2^n-1)$, used in the forward direction, is the second Lean statement.

1. [`Erdos249257.half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L2583)

```lean
theorem half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite
```

2. [`Erdos249257.irrational_erdosBorweinMersenneConstant`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L2469)

```lean
theorem irrational_erdosBorweinMersenneConstant :
    Irrational erdosBorweinMersenneConstant
```

<a id="thm-half-skip-dichotomy-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L117) (E257_18, line 117), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStatementsB.lean#L62) (PaperStatementsB.lean, line 62), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)
- `irrational_erdosBorweinMersenneConstant`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L104) (E257_18, line 104), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStatementsAH.lean#L31) (PaperStatementsAH.lean, line 31), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-nine-way-hub"></a>

## Theorem 6.32 (Equivalent descriptions of half-membership), page 50

> *Each of the following is equivalent to $`1/2\in\mathcal A`$:*
> 
> 1.  *The integer-greedy sequence is not eventually always on branch $`\mathrm R`$.*
> 
> 2.  *There are arbitrarily large $`s\ge5`$ with $`s\notin D_{s+1}`$.*
> 
> 3.  *Upper or middle transitions occur at arbitrarily large rows.*
> 
> 4.  *Some sequence $`s_j\to\infty`$ satisfies $`s_j\notin D_{s_j+1}`$ for every $`j`$.*
> 
> 5.  *There are rows $`s_j\to\infty`$ and omitted ranks $`d_j\in\{2,\ldots,s_j-1\}\smallsetminus D_{s_j}`$ with $`d_j\to\infty`$.*
> 
> 6.  *The positive ranks omitted by the real half-greedy rule form an infinite set.*
> 
> 7.  *The real half-greedy rule has no last omitted positive rank.*

The Lean declarations below together state this result or one that implies it. Items (1) to (5) and (7) are each proved equivalent to $1/2\in\mathcal A$, with branch $\mathrm R$ at row $s$ written as $D_{s+1}=D_s\cup\{s\}$ and the omitted ranks in (5) read off the greedy word of row $s_j$. Item (6) follows by combining the equivalence for (2) with the Lean equivalence between (2) and (6).

1. [`Erdos249257.half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L112)

```lean
theorem half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ SeamGreedyEventuallyRight
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L126)

```lean
theorem half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedTerminalFalse
```

3. [`Erdos249257.half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L156)

```lean
theorem half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedUpperOrMiddle
```

4. [`Erdos249257.half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L203)

```lean
theorem half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyCofinalTerminalFalse
```

5. [`Erdos249257.half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L213)

```lean
theorem half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∃ rows : ℕ → ℕ, SeamGreedyUnboundedSkippedRanksAlong rows
```

6. [`Erdos249257.unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L228)

```lean
theorem unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite :
    SeamGreedyUnboundedTerminalFalse ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite
```

7. [`Erdos249257.half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L235)

```lean
theorem half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ ∃ M : ℕ, IsLastHalfGreedySkip M
```

<a id="thm-nine-way-hub-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L265) (E257_18, line 265), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStructuresBJ.lean#L1290) (PaperStructuresBJ.lean, line 1290), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)
- `half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L270) (E257_18, line 270), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStructuresBJ.lean#L1296) (PaperStructuresBJ.lean, line 1296), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)
- `half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_13/Challenge.lean#L307) (E257_13, line 307), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_13/PaperStructuresCD.lean#L83) (PaperStructuresCD.lean, line 83), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_13.json) (E257_13)
- `half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L255) (E257_18, line 255), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStructuresBJ.lean#L1278) (PaperStructuresBJ.lean, line 1278), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)
- `half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L260) (E257_18, line 260), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStructuresBJ.lean#L1284) (PaperStructuresBJ.lean, line 1284), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)
- `unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L275) (E257_18, line 275), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStructuresBJ.lean#L1338) (PaperStructuresBJ.lean, line 1338), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)
- `half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_18/Challenge.lean#L136) (E257_18, line 136), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_18/PaperStatementsG.lean#L31) (PaperStatementsG.lean, line 31), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_18.json) (E257_18)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-eventually-right-impossible"></a>

## Lemma 6.33 (The values on either side of an eventual right continuation), page 51

> *If the seam eventually always extends “true” (right branch) from some row $`S`$ on with a fixed lower prefix $`u`$, the resulting cofinite-support value stays strictly below $`1/2`$; the matching alternative “upper competitor” word gives a strict excess *above* $`1/2`$. Neither of these two cofinite continuations represents $`1/2`$. This does not rule out an eventually-right integer orbit; it describes the two values in that case. The inequalities are used in Theorem 6.44.*

The Lean declarations below together state this result or one that implies it. With the seam right from row $S\ge5$ on and support $u\cup\{D+1,\ldots,S-1\}$ at row $S$, where $u\subseteq\{2,\ldots,D-1\}$ and $2\le D<S$, the Lean statements prove $X_u(2)+R_D<\frac12$ for the cofinite continuation $u\cup\{D+1,D+2,\ldots\}$ and $\frac12<X_{u\cup\{D\}}(2)$ for the upper competitor.

1. [`Erdos249257.prefix_add_mersenneTail_lt_half_of_eventually_right`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderFatalGapRightTail.lean#L402)

```lean
theorem prefix_add_mersenneTail_lt_half_of_eventually_right
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail D <
      (1 / 2 : ℝ)
```

2. [`Erdos249257.half_lt_upper_competitor_of_eventually_right`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/HalfCylinderFatalGapRightTail.lean#L627)

```lean
theorem half_lt_upper_competitor_of_eventually_right
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hD2 : 2 ≤ D) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) :
    (1 / 2 : ℝ) <
      positiveMersenneSupportValue (↑(insert D u) : Set ℕ)
```

<a id="lem-eventually-right-impossible-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `prefix_add_mersenneTail_lt_half_of_eventually_right`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_20/Challenge.lean#L130) (E257_20, line 130), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_20/PaperStructuresBJ.lean#L1346) (PaperStructuresBJ.lean, line 1346), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_20.json) (E257_20)
- `half_lt_upper_competitor_of_eventually_right`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_19/Challenge.lean#L334) (E257_19, line 334), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_19/PaperStructuresBI.lean#L283) (PaperStructuresBI.lean, line 283), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_19.json) (E257_19)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-mersenne-tail-weight"></a>

## Lemma 6.34 (Each Mersenne weight exceeds its remaining tail), page 51

> *For $`n\ge1`$, let $`w_n=(2^n-1)^{-1}`$ and $`R_n=\sum_{j>n}w_j`$. Then
> ``` math
> R_n=w_{n+1}+R_{n+1},\qquad
>  2^{-n}<R_n\le2w_{n+1}<w_n.
> ```
> For the upper bound, compare each tail term with $`2^{1-j}w_{n+1}`$ at index $`n+j`$, $`j\ge1`$, and sum the geometric series. The last inequality follows by comparing $`2/(2^{n+1}-1)`$ with $`1/(2^n-1)`$. This strict term-versus-tail inequality is the separation hypothesis used in the greedy arguments.*
> 
> *It is not available for the totient weights $`\varphi(n)/2^n`$: the terms at indices $`4`$ and $`5`$ already sum to $`2/16+4/32=1/4=\varphi(3)/2^3`$, and the remaining tail is positive. A general strict-tail argument therefore cannot be transferred to that sequence without a different hypothesis or proof.*

The Lean declarations below together state this result or one that implies it. The Lean lower bound is $2^{-n}+\tfrac13\,4^{-n}<R_n$, sharper than the printed $2^{-n}<R_n$, and this bound, the identity $R_n=w_{n+1}+R_{n+1}$ and $R_n\le2w_{n+1}$ hold for every $n\ge0$; the printed statement takes $n\ge1$, where $2w_{n+1}<w_n$ and $R_n<w_n$ are as printed. The remark on the totient weights is the arithmetic $\varphi(4)/2^4+\varphi(5)/2^5=\frac14=\varphi(3)/2^3$, outside the Lean statements.

1. [`Erdos249257.mersenneTail_eq_weight_add`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L114)

```lean
theorem mersenneTail_eq_weight_add (n : ℕ) :
    mersenneTail n = mersenneWeight (n + 1) + mersenneTail (n + 1)
```

2. [`Erdos249257.halfTwoChannelCap_lt_mersenneTail`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L1226)

```lean
theorem halfTwoChannelCap_lt_mersenneTail (n : ℕ) :
    halfTwoChannelCap n < mersenneTail n
```

3. [`Erdos249257.mersenneTail_le_two_mul_weight`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L155)

```lean
theorem mersenneTail_le_two_mul_weight (n : ℕ) :
    mersenneTail n ≤ 2 * mersenneWeight (n + 1)
```

4. [`Erdos249257.two_mul_mersenneWeight_succ_lt`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L125)

```lean
theorem two_mul_mersenneWeight_succ_lt {n : ℕ} (hn : 0 < n) :
    2 * mersenneWeight (n + 1) < mersenneWeight n
```

5. [`Erdos249257.mersenneTail_lt_weight`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L180)

```lean
theorem mersenneTail_lt_weight {n : ℕ} (hn : 0 < n) :
    mersenneTail n < mersenneWeight n
```

<a id="lem-mersenne-tail-weight-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `mersenneTail_eq_weight_add`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_20/Challenge.lean#L159) (E257_20, line 159), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_20/PaperStatementsAH.lean#L36) (PaperStatementsAH.lean, line 36), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_20.json) (E257_20)
- `halfTwoChannelCap_lt_mersenneTail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_20/Challenge.lean#L155) (E257_20, line 155), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_20/PaperStatementsAH.lean#L27) (PaperStatementsAH.lean, line 27), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_20.json) (E257_20)
- `mersenneTail_le_two_mul_weight`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_20/Challenge.lean#L163) (E257_20, line 163), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_20/PaperStatementsAH.lean#L39) (PaperStatementsAH.lean, line 39), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_20.json) (E257_20)
- `two_mul_mersenneWeight_succ_lt`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_20/Challenge.lean#L171) (E257_20, line 171), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_20/PaperStatementsAH.lean#L45) (PaperStatementsAH.lean, line 45), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_20.json) (E257_20)
- `mersenneTail_lt_weight`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_20/Challenge.lean#L167) (E257_20, line 167), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_20/PaperStatementsAH.lean#L42) (PaperStatementsAH.lean, line 42), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_20.json) (E257_20)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
