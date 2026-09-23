# Formal evidence: Reciprocal Mersenne Subseries, Section 6

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="record-257bm-k9"></a>

## Theorem 6.136 (Vanishing of the specified linear-channel determinant), page 84

> *Let $`V`$ be a vector space over $`\mathbb{Q}`$, let $`e:V\to\mathbb{Q}`$ be linear, and let $`(\ell_j)_{j\in\iota}`$ be a finite family of linear functionals vanishing on $`\ker e`$. For any vectors $`(v_i)_{i\in\iota}`$, the matrix $`(\ell_j(v_i))_{i,j\in\iota}`$ has rank at most one, so every square minor of size at least two vanishes. Indeed, the functionals descend to $`V/\ker e`$, which has dimension at most one. This elementary linear-algebra argument applies at every matrix size. It does not cover additional functionals that fail to vanish on $`\ker e`$.*
> 
> *<span class="sans-serif">(uniform)</span> *linear-algebra* [`relationInvariantLinearChannels_det_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L42)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_rank_le_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L37)

```lean
theorem paper_relationInvariant_channels_rank_le_one
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    ∃ u w : ι → ℚ, ∀ i j : ι, channel j (row i) = u i * w j
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_det_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L63)

```lean
theorem paper_relationInvariant_channels_det_eq_zero
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    [Nontrivial ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    Matrix.det (fun i j : ι => channel j (row i)) = 0
```

<a id="record-257bm-k9-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_relationInvariant_channels_rank_le_one` | [E257_33/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L80) | [PaperStatementsAA.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L228) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_relationInvariant_channels_det_eq_zero` | [E257_33/Challenge.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L71) | [PaperStatementsAA.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L219) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-k12"></a>

## Theorem 6.139 (Excluding the cell with value minus three), page 84

> *At a middle row $`D\ge13`$ followed only by right transitions, $`4\,\mathrm{rem}(D)-p_D^--4\ne-3`$, by Theorem <a href="#thm:final-middle-cell" data-reference-type="ref" data-reference="thm:final-middle-cell">87</a>. Its proof uses the nonnegative centred carry for the completed support, not a finite search. The values $`-2,-1`$ remain among the three exceptional negative cells. Excluding them under this extra tail assumption would still not exclude nonnegative values of the coordinate, or establish the all-middle-row and right-branch hypotheses in Theorem <a href="#thm:two-sided-dyadic" data-reference-type="ref" data-reference="thm:two-sided-dyadic">52</a>. The complete remaining tail inequality is stated in Remark <a href="#rem:tail-dominance-open" data-reference-type="ref" data-reference="rem:tail-dominance-open">260</a>.*
> 
> *<span class="sans-serif">(uniform)</span> *mobius-centred-carry* [`finalMiddleCell_neg_three_not_last`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L587) [`mobiusCenteredHalfCarry_add_two`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L39) [`cofiniteRightTail_ne_zero_centeredEndpoint`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L547)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_ne_neg_three`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L100)

```lean
theorem paper_final_middle_cell_ne_neg_three
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
        ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≠ -3
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_remaining_negative_values`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L118)

```lean
theorem paper_final_middle_cell_remaining_negative_values
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≤ -4 ∨
      0 ≤ 4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ∨
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_mobiusCenteredHalfCarry_add_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L155)

```lean
theorem paper_mobiusCenteredHalfCarry_add_two (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_cofiniteRightTail_ne_zero_centeredEndpoint`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L163)

```lean
theorem paper_cofiniteRightTail_ne_zero_centeredEndpoint
    (A : Set ℕ) (D : ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (hcofinite : Set.Ioi D ⊆ A) :
    mobiusCenteredHalfCarry A (2 * D + 1) ≠ 0
```

<a id="record-257hg-k12-comparator"></a>

**Comparator:** not yet compared.

<a id="prop-exact-lebesgue-measure-dichotomy"></a>

## Proposition 6.146, page 89

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_volume_supportedMersenneAchievementSet_dichotomy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SharedPrefixFamiliesAndMeasureDichotomy.lean#L68)

```lean
theorem paper_volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ENNReal) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0)
```

<a id="prop-exact-lebesgue-measure-dichotomy-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_volume_supportedMersenneAchievementSet_dichotomy` | [E257_34/Challenge.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_34/Challenge.lean#L229) | [PaperStatementsAM.lean, line 236](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_34/PaperStatementsAM.lean#L236) | [E257_34](../../evidence/comparator/replay-35882032091/receipt-E257_34.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
