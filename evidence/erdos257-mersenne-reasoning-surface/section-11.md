# Formal evidence: Reciprocal Mersenne Subseries, Section 11

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="lem-sqwitness"></a>

## Lemma 11.3 (The terminal bound at square depths), page 124

> *Let $`A\subseteq\mathbb{N}`$ with $`1\notin A`$ and $`X_{A}(2)=1/2`$. Then for every $`k\ge1`$,
> ``` math
> \bigl(\ensuremath{\operatorname{ihc}}\ A\ (k^{2}-1)\ :\ \mathbb{R}\bigr)
> \ =\ \mathtt{binaryCoeffTail}\ (c_{A})\ (k^{2})
> \ \le\ 2k+4\ =\ \ensuremath{B}\ (k^{2}).
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_square_depth_terminal_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquareDepthAndHalfMembershipEquivalences.lean#L27)

```lean
theorem paper_square_depth_terminal_bound (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2) (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k ^ 2 - 1) : ℝ) = binaryCoeffTail (supportCoeff A) (k ^ 2) ∧
      binaryCoeffTail (supportCoeff A) (k ^ 2) ≤ 2 * (k : ℝ) + 4 ∧
      (halfStripBound (k ^ 2) : ℝ) = 2 * (k : ℝ) + 4
```

2. [`ErdosProblems.Erdos257.PaperCompleteR20.square_depth_witness`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR20/CarryCollapseCorrespondence.lean#L8)

```lean
theorem square_depth_witness (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k^2-1) : ℝ) = binaryCoeffTail (supportCoeff A) (k^2) ∧
    binaryCoeffTail (supportCoeff A) (k^2) ≤ 2*(k : ℝ)+4 ∧
    (halfStripBound (k^2) : ℝ) = 2*(k : ℝ)+4
```

<a id="lem-sqwitness-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_square_depth_terminal_bound` | [E257_37/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L146) | [PaperStatementsL.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsL.lean#L52) | [E257_37](../../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `square_depth_witness` | [E257_03/Challenge.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L136) | [PaperStatementsL.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsL.lean#L28) | [E257_03](../../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
