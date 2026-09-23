# Formal evidence: Reciprocal Mersenne Subseries, Section 12

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="prop-cpgs-equiv"></a>

## Proposition 12.3 (Infinitely many positive skips are equivalent to half-membership), page 130

> *Define
> ``` math
> \mathrm{CPGS}\ :=\ \forall N,\ \exists c\ge N,\ c\ \text{skipped by the rational half-greedy
> orbit}\ \wedge\ 0<\ensuremath{r}(1/2)(c-1)
> ```
> The positivity conjunct is unconditionally true for every skipped $`c`$ (an odd-denominator parity fact), hence deletable without changing the Prop’s meaning. What survives, $`\forall N\,\exists c\ge N`$ skipped, is exactly $`(\mathtt{greedyMersenneSkippedSupport}(1/2)).\mathrm{Infinite}`$, so
> ``` math
> \mathrm{CPGS}\ \Longleftrightarrow\ \mathrm{HALF}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_cpgs_equiv`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquareDepthAndHalfMembershipEquivalences.lean#L44)

```lean
theorem paper_cpgs_equiv :
    ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
        0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
      ↔ CofinalPositiveHalfGreedySkips) ∧
      (∀ n : ℕ, 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ ∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
            greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet)
```

<a id="prop-cpgs-equiv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_cpgs_equiv` | [E257_38/Challenge.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L139) | [PaperStatementsN.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsN.lean#L99) | [E257_38](../../evidence/comparator/replay-35882032091/receipt-E257_38.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-strip-equiv"></a>

## Proposition 12.4 (Terminal carry bounds are equivalent to half-membership), page 131

> *Consider finite sets $`D\subseteq\{2,\ldots,M\}`$ at arbitrarily large depths $`M`$ with
> ``` math
> |\operatorname{ihc}(D,M-1)|\le2\lfloor\sqrt M\rfloor+4.
> ```
> This is the exact terminal-strip condition. It is equivalent to $`1/2\in\mathcal A`$: the forward direction follows from the displayed finite-approximation estimate; for the converse, truncate an achieving support at $`M=k^2`$ and apply Lemma <a href="#lem:sqrt-witness" data-reference-type="ref" data-reference="lem:sqrt-witness">17</a>. Thus constant $`4`$ already suffices at cofinally many depths. The relaxed constant $`6`$ gives a bound at every depth, using $`\sqrt M\le\lfloor\sqrt M\rfloor+1`$, but that relaxation is not needed for the cofinal statement.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_equiv`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquareDepthAndHalfMembershipEquivalences.lean#L130)

```lean
theorem paper_terminal_strip_equiv :
    ((∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
        (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
        |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 4)
      ↔ HalfCarryCofinalTerminalOnlyStrip) ∧
      ((∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
          (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
          |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 4)
        ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_relaxed_constant_six_every_depth`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquareDepthAndHalfMembershipEquivalences.lean#L112)

```lean
theorem paper_relaxed_constant_six_every_depth
    (A : Set ℕ) (hone : 1 ∉ A) (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (M : ℕ) (hM : 1 ≤ M) :
    |(integerHalfCarry A (M - 1) : ℝ)| ≤ 2 * (Nat.sqrt M : ℝ) + 6
```

<a id="prop-strip-equiv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_terminal_strip_equiv` | [E257_38/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L159) | [PaperStatementsN.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsN.lean#L227) | [E257_38](../../evidence/comparator/replay-35882032091/receipt-E257_38.json) |
| `paper_relaxed_constant_six_every_depth` | [E257_38/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L180) | [PaperStatementsL.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsL.lean#L51) | [E257_38](../../evidence/comparator/replay-35882032091/receipt-E257_38.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
