# Formal evidence: Reciprocal Mersenne Subseries, Section 6, results 6.72 to 6.105

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="record-257bm-c6"></a>

## Theorem 6.72 (The quotient condition on greedy prefixes), page 62

> *Let $`D_c=G\cap\{2,\ldots,c-1\}`$. The condition on the actual greedy prefixes is
> ``` math
> \begin{gathered}
>  c\ge4,\quad c\notin G\\
>  \Longrightarrow\qquad Q(D_c\cup\{c\},2c-2)\ge2^{2c-3}.
>  \end{gathered}
> ```
> It asks for the quotient bound at every skipped rank of the specified half-greedy orbit. This restricts the crossing test of Theorem <a href="#record:257bm-c4" data-reference-type="ref" data-reference="record:257bm-c4">113</a> to its actual greedy prefixes. The finite uniqueness results justify that restriction where the cited induction uses it; they do not prove the displayed inequality.*

The Lean declaration below states this result.

[`Erdos249257.skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1068)

```lean
theorem skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped :
    SkippedCoreCriticalQuotientSupply ↔
      HalfGreedySkippedCriticalQuotientSupply
```

<a id="record-257bm-c6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped` | [E257_22/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L199) | [PaperStatementsF.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsF.lean#L200) | [E257_22](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c6a"></a>

## Theorem 6.73 (Two consecutive skips), page 62

> *If $`c\ge6`$ and the real half-greedy rule skips both $`c`$ and $`c+1`$, put $`D=G\cap\{2,\ldots,c-1\}`$. Then
> ``` math
> S(D,1,2c-3)<2^{c-3}.
> ```
> The one-step quotient recurrence gives $`S(D,1,2c-2)<2^{c-2}`$, so Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a> supplies an exact row at depth $`2c-2`$ whose new ranks are all greater than $`c`$. The hypothesis concerns this pair of skipped ranks; no unbounded sequence of such pairs is proved here. For the stated precritical-suffix condition at every skipped rank, the remaining tests are the skip-then-take cases, with ranks $`4`$ and $`5`$ handled separately in the cited proof.*

The Lean declarations below together state this result.

1. [`Erdos249257.halfGreedy_precriticalSuffix_lt_of_next_skip`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L682)

```lean
theorem halfGreedy_precriticalSuffix_lt_of_next_skip
    {c : ℕ} (hc : 6 ≤ c)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c)
    (hnext : greedyMersenneRemainderRat (1 / 2 : ℚ) c <
      mersenneWeightRat (c + 1)) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)
```

2. [`Erdos249257.halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1001)

```lean
theorem halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix
    (hpre : HalfGreedySkippedPrecriticalSuffixSupply) :
    HalfGreedySkippedCriticalQuotientSupply
```

where [`HalfGreedySkippedCriticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L178) is

```lean
def HalfGreedySkippedCriticalQuotientSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient
        (insert c (halfGreedyPrefixSupport (c - 1))) (2 * c - 2)
```

3. [`Erdos249257.halfGreedySkippedPrecriticalSuffixSupply_iff_preTake`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L838)

```lean
theorem halfGreedySkippedPrecriticalSuffixSupply_iff_preTake :
    HalfGreedySkippedPrecriticalSuffixSupply ↔
      HalfGreedyPreTakePrecriticalSuffixSupply
```

<a id="record-257bm-c6a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `halfGreedy_precriticalSuffix_lt_of_next_skip` | [E257_23/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L120) | [PaperStatementsF.lean, line 189](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsF.lean#L189) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix` | [E257_23/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L96) | [PaperStatementsF.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsF.lean#L149) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `halfGreedySkippedPrecriticalSuffixSupply_iff_preTake` | [E257_23/Challenge.lean, line 101](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L101) | [PaperStatementsF.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsF.lean#L155) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c6b"></a>

## Theorem 6.74 (A later skip after a selected block), page 62

> *Suppose the real half-greedy rule skips rank $`c`$, takes $`c+1,\ldots,c+t-1`$, and skips $`c+t`$. If
> ``` math
> 0<t\le c-3,\qquad c-2\le2^{c-t-3},
> ```
> then the precritical suffix bound at $`c`$ holds. It yields sharp capacity and hence an exact row at depth $`2c-2`$. The case $`t=1`$ includes Theorem <a href="#record:257bm-c6a" data-reference-type="ref" data-reference="record:257bm-c6a">116</a>; the proof also permits longer selected blocks. The arithmetic condition is precisely $`t\le c-3-\lceil\log_2(c-2)\rceil`$. Its role in the proof is to make the dyadic allowance $`2^{c-t-3}`$ cover the bound $`|D|\le c-2`$ for the earlier selected support.*
> 
> *To obtain cofinal exact rows by this result, the stated gap condition must hold at cofinally many skipped ranks $`c`$, not just at one rank or throughout a finite sample. A finite empirical skip frequency alone gives no such pointwise gap bound.*

The Lean declarations below together state this result.

1. [`Erdos249257.halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L603)

```lean
theorem halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock
    {c t : ℕ} (hc : 4 ≤ c) (htPos : 0 < t) (ht : t ≤ c - 3)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c)
    (htake : ∀ j ∈ Finset.range (t - 1),
      mersenneWeightRat (c + j + 1) ≤
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c + j))
    (hfuture : greedyMersenneRemainderRat (1 / 2 : ℚ) (c + t - 1) <
      mersenneWeightRat (c + t))
    (hroom : c - 2 ≤ 2 ^ (c - t - 3)) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)
```

2. [`Erdos249257.precriticalCrossingTax_of_futureThreshold`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L472)

```lean
theorem precriticalCrossingTax_of_futureThreshold
    {D : Finset ℕ} {c t : ℕ}
    (hc : 4 ≤ c)
    (ht : t ≤ c - 3)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hres :
      (1 / 2 : ℚ) - localMersennePrefixValue D <
        ∑ j ∈ Finset.range t, mersenneWeightRat (c + j + 1))
    (hroom : c - 2 ≤ 2 ^ (c - t - 3)) :
    localFractionMass (insert c D) (2 * c - 3) - 1 <
      (2 : ℚ) ^ (2 * c - 3) *
        (localMersennePrefixValue (insert c D) - (1 / 2 : ℚ))
```

3. [`Erdos249257.sub_two_le_two_pow_sub_four`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L432)

```lean
theorem sub_two_le_two_pow_sub_four
    {c : ℕ} (hc : 6 ≤ c) :
    c - 2 ≤ 2 ^ (c - 4)
```

<a id="record-257bm-c6b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock` | [E257_23/Challenge.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L106) | [PaperStatementsF.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsF.lean#L174) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `precriticalCrossingTax_of_futureThreshold` | [E257_23/Challenge.lean, line 185](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L185) | [PaperStatementsAR.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAR.lean#L187) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `sub_two_le_two_pow_sub_four` | [E257_23/Challenge.lean, line 133](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L133) | [PaperStatementsAA.lean, line 93](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAA.lean#L93) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c7"></a>

## Theorem 6.75 (Filling the remaining binary positions), page 63

> *For any $`c\ge4`$ and any finite $`D\subseteq[2,c)`$ with $`\mathrm{value}(D)<1/2`$ and the sharp capacity
> ``` math
> \ensuremath{S}(D,1,2c-2) < 2^{c-2},
> ```
> there is an exact row $`E`$ at endpoint $`2c-2`$ with $`D\subseteq E`$ and every new rank strictly above $`c`$. The implication requires the displayed capacity bound, but neither a crossing condition nor a specified real greedy prefix. The crossing hypothesis used in Theorem <a href="#record:257bm-c4" data-reference-type="ref" data-reference="record:257bm-c4">113</a> is one way to seek that input, not an additional premise of this filling result. No strict comparison between the corresponding cofinal existence statements is asserted.*

The Lean declaration below states this result.

[`Erdos249257.exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusSkipRow.lean#L238)

```lean
theorem exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, d ∉ D → c < d) ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) =
        2 ^ ((2 * c - 2) - 1) - 1
```

<a id="record-257bm-c7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity` | [E257_23/Challenge.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L171) | [PaperStatementsAR.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAR.lean#L119) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c8"></a>

## Theorem 6.76 (An exact sum at depth $`2c-2`$), page 63

> *Under the hypotheses of Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a>, there is a set $`E\subseteq\{2,\ldots,2c-2\}`$ with
> ``` math
> Q(E,2c-2)=2^{2c-3}-1.
> ```
> This conclusion forgets the additional support-extension information in that theorem. It is the form used when only the existence of an exact row is needed.*

The Lean declaration below states this result.

[`Erdos249257.exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusSkipRow.lean#L332)

```lean
theorem exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hsharp : localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    ExactLocalMersenneHalfRow (2 * c - 2)
```

<a id="record-257bm-c8-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity` | [E257_23/Challenge.lean, line 162](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L162) | [PaperStatementsAR.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAR.lean#L96) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c9"></a>

## Proposition 6.77 (Quotients in the upper half of the index range), page 63

> *For integers $`d\ge2`$ and $`d\le M<2d`$,
> ``` math
> q(M,d)=\left\lfloor\frac{2^M}{2^d-1}\right\rfloor=2^{M-d}.
> ```
> Indeed, the quotient is $`2^{M-d}+2^{M-d}/(2^d-1)`$, whose second term is strictly between zero and one. In Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a>, the available ranks $`d=c+1,\ldots,2c-2`$ therefore supply the binary weights $`2^{c-3},\ldots,1`$. They represent every integer from $`0`$ to $`2^{c-2}-1`$, which explains both the capacity bound and the choice of terminal depth.*

The Lean declarations below together state this result.

1. [`Erdos249257.localMersenneQuotient_eq_two_pow_sub_of_half_lt`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusLocalRepair.lean#L26)

```lean
theorem localMersenneQuotient_eq_two_pow_sub_of_half_lt
    {M d : ℕ} (hd2 : 2 ≤ d) (hhalf : M / 2 < d) (hdM : d ≤ M) :
    localMersenneQuotient M d = 2 ^ (M - d)
```

2. [`Erdos249257.exists_boolean_word_of_lt_two_pow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusLocalRepair.lean#L525)

```lean
theorem exists_boolean_word_of_lt_two_pow
    {V L : ℕ} (hV : V < 2 ^ L) :
    ∃ y : List ℕ,
      y.length = L ∧
      (∀ b ∈ y, b = 0 ∨ b = 1) ∧
      Nat.ofDigits 2 y = V
```

<a id="record-257bm-c9-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `localMersenneQuotient_eq_two_pow_sub_of_half_lt` | [E257_23/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L223) | [PaperStatementsAD.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAD.lean#L114) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `exists_boolean_word_of_lt_two_pow` | [E257_23/Challenge.lean, line 215](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L215) | [PaperStatementsAD.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAD.lean#L103) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c10"></a>

## Theorem 6.78 (A finite sum from a skipped prefix), page 63

> *Let $`c\ge4`$ and $`D\subseteq\{2,\ldots,c-1\}`$ satisfy
> ``` math
> 0<\frac12-X_D(2)<\frac1{2^c-1}.
> ```
> Then there is $`E`$ with $`D\subseteq E\subseteq\{2,\ldots,2c-2\}`$ and $`Q(E,2c-2)=2^{2c-3}-1`$. No separate sharp-capacity assumption is required. The binary completion in the linked proof uses ranks $`c,\ldots,2c-2`$; it may therefore insert $`c`$. Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a> instead assumes the sharper $`(c-2)`$-bit bound so that every added rank is strictly greater than $`c`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_from_skipped_prefix`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L264)

```lean
theorem paper_exact_row_from_skipped_prefix {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * c - 2) ∧
      localPrefixQuotient E (2 * c - 2) = 2 ^ (2 * c - 3) - 1
```

<a id="record-257bm-c10-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_exact_row_from_skipped_prefix` | [E257_23/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L199) | [PaperStatementsAR.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAR.lean#L228) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c11"></a>

## Theorem 6.79 (Testing one nearest dyadic boundary), page 64

> *Let $`d,E`$ be nonnegative integers with $`E\le2^{d+1}`$, and let
> ``` math
> j_*:=\max\{0\le j\le d:E\le2^{d-j+1}\}.
> ```
> The boundary $`2^{d-j_*+1}`$ is the smallest power at least $`E`$ among the finite list $`2,4,\ldots,2^{d+1}`$; in particular $`j_*=d`$ when $`E\le2`$. The following conditions are equivalent:
> ``` math
> \begin{gathered}
>  \text{for every }0\le j\le d,\quad
>  2^{d-j+1}<E\ \text{or}\ E+2(d+j)\le2^{d-j+1};\\
>  E+2(d+j_*)\le2^{d-j_*+1}.
>  \end{gathered}
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_band_index_unique`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/DyadicBandAndTwoSidedBounds.lean#L26)

```lean
theorem paper_critical_dyadic_band_index_unique {d E : ℕ}
    (hE : E ≤ 2 ^ (d + 1)) :
    ∃! j : ℕ, CriticalDyadicBandIndex d E j
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_boundary_is_smallest`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/DyadicBandAndTwoSidedBounds.lean#L52)

```lean
theorem paper_critical_dyadic_boundary_is_smallest {d E j : ℕ}
    (hj : CriticalDyadicBandIndex d E j) :
    E ≤ 2 ^ (d - j + 1) ∧
      ∀ i : ℕ, i ≤ d → E ≤ 2 ^ (d - i + 1) →
        (2 : ℕ) ^ (d - j + 1) ≤ 2 ^ (d - i + 1)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_band_index_eq_top_of_le_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/DyadicBandAndTwoSidedBounds.lean#L71)

```lean
theorem paper_critical_dyadic_band_index_eq_top_of_le_two {d E j : ℕ}
    (hE : E ≤ 2) (hj : CriticalDyadicBandIndex d E j) :
    j = d
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_dyadic_band_escape_iff_single_test`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/DyadicBandAndTwoSidedBounds.lean#L89)

```lean
theorem paper_dyadic_band_escape_iff_single_test {d E j : ℕ}
    (hj : CriticalDyadicBandIndex d E j) :
    DyadicBandEscape d E ↔ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)
```

<a id="record-257bm-c11-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_critical_dyadic_band_index_unique` | [E257_23/Challenge.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L246) | [PaperStatementsBE.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsBE.lean#L21) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `paper_critical_dyadic_boundary_is_smallest` | [E257_23/Challenge.lean, line 251](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L251) | [PaperStatementsBE.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsBE.lean#L25) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `paper_critical_dyadic_band_index_eq_top_of_le_two` | [E257_23/Challenge.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L241) | [PaperStatementsBE.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsBE.lean#L17) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `paper_dyadic_band_escape_iff_single_test` | [E257_23/Challenge.lean, line 258](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L258) | [PaperStatementsBE.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsBE.lean#L31) | [E257_23](../../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c12"></a>

## Proposition 6.80 (An upper bound for the reset expression), page 64

> *Let $`d\ge5`$ be an actual upper-reset row. Write $`E_d`$ for its reset charge, the sum of four times the adjacent upper overshoot and the corresponding nonnegative correction term. The upper-reset identity is
> ``` math
> \mathrm{rem}(d+1)+E_d=2^{d+1}.
> ```
> The nonnegativity of the successor remainder therefore gives $`E_d\le2^{d+1}`$, the side condition needed for Theorem <a href="#record:257bm-c11" data-reference-type="ref" data-reference="record:257bm-c11">122</a>. This argument uses the upper-reset branch assumption. It does not require the separate, conditional two-sided bound of Theorem <a href="#thm:two-sided-dyadic" data-reference-type="ref" data-reference="thm:two-sided-dyadic">52</a>, and does not assert the charge bound at arbitrary rows.*

The Lean declarations below together state this result.

1. [`Erdos249257.seamUpperBranch_remainder_add_resetCharge_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3542)

```lean
theorem seamUpperBranch_remainder_add_resetCharge_eq
    {d : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    seamIntegerGreedyRemainder (d + 1) +
        (4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse) =
      2 ^ (d + 1)
```

2. [`Erdos249257.HalfUpperResetCriticalBand.seamUpperResetCharge_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfUpperResetCriticalBand.lean#L131)

```lean
theorem seamUpperResetCharge_le
    {d : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    seamUpperResetCharge d hd5 ≤ 2 ^ (d + 1)
```

<a id="record-257bm-c12-comparator"></a>

**Comparator:** not yet compared.

<a id="record-257bm-c14"></a>

## Theorem 6.82 (An equivalent vanishing condition), page 65

> *``` math
> \begin{gathered}
>  \forall\ \text{skipped rank }n\ge3\text{ whose actual word equals the seam-greedy word},\\
>  \text{the integer remainder at }n\text{ is zero}.
> \end{gathered}
> ```
> This condition is equivalent to Definition <a href="#record:257bm-c13" data-reference-type="ref" data-reference="record:257bm-c13">124</a>. At an actual skipped rank, the source proves that $`F(n-1,n)<0`$ holds exactly when the real prefix agrees with the integer greedy word and its integer remainder is positive. On agreement, $`F(n-1,n)`$ is the negative of that nonnegative remainder. Thus nonnegativity of the margin at every skip is equivalent to vanishing of the remainder at every aligned skip. The equivalence is proved; neither condition is established for all required ranks.*

The Lean declarations below together state this result.

1. [`Erdos249257.skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L569)

```lean
theorem skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos
    (n : ℕ) (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) :
    greedyHalfFrozenMargin (n - 1) n < 0 ↔
      stemBits n (halfGreedyPrefixSupport (n - 1)) =
          integerGreedyBits (seamWeights n) (seamSubsetTarget n) ∧
        1 ≤ seamIntegerGreedyRemainder n
```

2. [`Erdos249257.greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L531)

```lean
theorem greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment
    (n : ℕ) (hn : 3 ≤ n)
    (halign :
      stemBits n (halfGreedyPrefixSupport (n - 1)) =
        integerGreedyBits (seamWeights n) (seamSubsetTarget n)) :
    greedyHalfFrozenMargin (n - 1) n =
      -(seamIntegerGreedyRemainder n : ℤ)
```

3. [`Erdos249257.skippedSeamAlignmentZero_iff_skippedFullShellNonnegative`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L671)

```lean
theorem skippedSeamAlignmentZero_iff_skippedFullShellNonnegative :
    HalfGreedySkippedSeamAlignmentZero ↔
      HalfGreedySkippedFullShellNonnegative
```

<a id="record-257bm-c14-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos` | [E257_24/Challenge.lean, line 143](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_24/Challenge.lean#L143) | [PaperStructuresBJ.lean, line 1347](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_24/PaperStructuresBJ.lean#L1347) | [E257_24](../../evidence/comparator/replay-35882032091/receipt-E257_24.json) |
| `greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment` | [E257_16/Challenge.lean, line 307](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_16/Challenge.lean#L307) | [PaperStructuresBI.lean, line 254](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_16/PaperStructuresBI.lean#L254) | [E257_16](../../evidence/comparator/replay-35882032091/receipt-E257_16.json) |
| `skippedSeamAlignmentZero_iff_skippedFullShellNonnegative` | [E257_13/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L260) | [PaperStructuresBJ.lean, line 1313](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStructuresBJ.lean#L1313) | [E257_13](../../evidence/comparator/replay-35882032091/receipt-E257_13.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c15"></a>

## Theorem 6.83 (A sufficient lower bound for the integer remainder), page 65

> *``` math
> \forall\ \text{skipped rank }n\ge3,\quad B(2n) < \mathrm{rem}(n),
> ```
> a sufficient condition for the nonnegativity condition above. Indeed, a negative margin at an actual skip would force $`1\le\mathrm{rem}(n)\le B(2n)`$, contradicting this bound. This proves the implication, not a converse or strict separation of the conditions.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_forces_remainder_band`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamEscapeAndTerminalStrip.lean#L36)

```lean
theorem paper_seam_escape_forces_remainder_band
    {n : ℕ} (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))
    (hneg : greedyHalfFrozenMargin (n - 1) n < 0) :
    1 ≤ seamIntegerGreedyRemainder n ∧
      seamIntegerGreedyRemainder n ≤ halfStripBound (2 * n)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_full_shell_nonnegative`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamEscapeAndTerminalStrip.lean#L47)

```lean
theorem paper_seam_escape_implies_full_shell_nonnegative
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    HalfGreedySkippedFullShellNonnegative
```

where [`HalfGreedySkippedFullShellNonnegative`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L604) is

```lean
def HalfGreedySkippedFullShellNonnegative : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    0 ≤ greedyHalfFrozenMargin (n - 1) n
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_half_membership`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamEscapeAndTerminalStrip.lean#L61)

```lean
theorem paper_seam_escape_implies_half_membership
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="record-257bm-c15-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_seam_escape_forces_remainder_band` | [E257_25/Challenge.lean, line 329](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_25/Challenge.lean#L329) | [PaperStructuresBK.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_25/PaperStructuresBK.lean#L260) | [E257_25](../../evidence/comparator/replay-35882032091/receipt-E257_25.json) |
| `paper_seam_escape_implies_full_shell_nonnegative` | [E257_25/Challenge.lean, line 337](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_25/Challenge.lean#L337) | [PaperStructuresBK.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_25/PaperStructuresBK.lean#L269) | [E257_25](../../evidence/comparator/replay-35882032091/receipt-E257_25.json) |
| `paper_seam_escape_implies_half_membership` | [E257_26/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L117) | [PaperStructuresBW.lean, line 304](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStructuresBW.lean#L304) | [E257_26](../../evidence/comparator/replay-35882032091/receipt-E257_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-c16"></a>

## Theorem 6.84 (A square-root carry bound implies half-membership), page 65

> *Write $`G`$ for the greedy support and $`C_G(N)`$ for its centred carry. If
> ``` math
> \forall N,\qquad C_G(N) \le 2\sqrt N + 4,
> ```
> then the greedy selected support $`G`$ is infinite and $`X_G(2)=1/2`$. Nonnegativity of $`C_G`$ is unconditional (see Theorem <a href="#thm:mobius-centred-nonneg" data-reference-type="ref" data-reference="thm:mobius-centred-nonneg">54</a> and the greedy case above); only the upper $`2\sqrt N+4`$ bound remains open. This is a different hypothesis from the dyadic-band condition and the largest-skip condition; logical independence is not asserted.*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfCarryReachability.greedy_mobiusCenteredHalfCarry_nonneg`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCarryReachability.lean#L919)

```lean
theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N
```

2. [`Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCarryReachability.lean#L953)

```lean
theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2
```

<a id="record-257rig-c16-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `greedy_mobiusCenteredHalfCarry_nonneg` | [E257_13/Challenge.lean, line 144](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L144) | [PaperStatementsD.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsD.lean#L139) | [E257_13](../../evidence/comparator/replay-35882032091/receipt-E257_13.json) |
| `greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound` | [E257_26/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L152) | [PaperStatementsD.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsD.lean#L120) | [E257_26](../../evidence/comparator/replay-35882032091/receipt-E257_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-c17"></a>

## Theorem 6.85 (Terminal bounds at unbounded depths), page 65

> *Suppose that for every $`N\ge0`$ there are $`M\ge\max\{N,1\}`$ and $`D\subseteq\{2,\ldots,M\}`$ such that
> ``` math
> |\operatorname{ihc}(D,M-1)|\le B(M)
>        =2\lfloor\sqrt M\rfloor+4.
> ```
> Then some infinite $`A\subseteq\mathbb{N}_{>0}`$ satisfies $`X_A(2)=1/2`$. No compatibility between different finite supports or bound on their earlier carries is required.*
> 
> *These are not the exact-row conditions of Definition <a href="#record:257bm-d4" data-reference-type="ref" data-reference="record:257bm-d4">109</a>. For such a finite support,
> ``` math
> \operatorname{ihc}(D,M-1)=2^{M-1}-Q(D,M),
> ```
> so an exact row has carry $`1`$, whereas the displayed bound allows several positive and negative values. At $`M=6`$, for example, $`D=\{2,3\}`$ has $`Q(D,6)=30`$ and carry $`2`$: it satisfies the terminal bound but is not an exact row. Both cofinal existence statements nevertheless imply, and are implied by, half-membership, as explained in Proposition <a href="#prop:collapsed-list" data-reference-type="ref" data-reference="prop:collapsed-list">18</a>. The difference between their finite data must not be confused with a strict logical weakening of the membership problem.*

The Lean declarations below together state a result at least as strong as this one. The Lean statements have the same hypotheses and conclusions as the printed ones: an infinite $A\subseteq\mathbb N_{>0}$ with $X_A(2)=1/2$, the carry identity, the carry $1$ of an exact row, the example at $M=6$, and both equivalences with half-membership. The carry identity is stated for every finite $D$ with elements at least $2$, and in the last equivalence the terminal-bound condition is written with a binary word whose support, which omits $0$ and $1$, is the set $D$.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_forces_half_membership`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/TerminalStripExactRowGap.lean#L44)

```lean
theorem paper_terminal_strip_forces_half_membership
    (hcofinal : ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ ∃ D : Finset ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
      |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ (halfStripBound M : ℝ)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/TerminalStripExactRowGap.lean#L88)

```lean
theorem paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) =
      (2 : ℤ) ^ (M - 1) - (localPrefixQuotient D M : ℤ)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_integerHalfCarry_eq_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/TerminalStripExactRowGap.lean#L106)

```lean
theorem paper_exact_row_integerHalfCarry_eq_one
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hexact : localPrefixQuotient D M = 2 ^ (M - 1) - 1) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) = 1
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_witness_six`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/TerminalStripExactRowGap.lean#L122)

```lean
theorem paper_terminal_strip_witness_six :
    (∀ d ∈ ({2, 3} : Finset ℕ), 2 ≤ d ∧ d ≤ 6) ∧
      localPrefixQuotient ({2, 3} : Finset ℕ) 6 = 30 ∧
      integerHalfCarry (↑({2, 3} : Finset ℕ) : Set ℕ) (6 - 1) = 2 ∧
      |(integerHalfCarry (↑({2, 3} : Finset ℕ) : Set ℕ) (6 - 1) : ℝ)| ≤
        (halfStripBound 6 : ℝ) ∧
      localPrefixQuotient ({2, 3} : Finset ℕ) 6 ≠ 2 ^ (6 - 1) - 1
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_both_cofinal_statements_iff_half_membership`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/TerminalStripExactRowGap.lean#L160)

```lean
theorem paper_both_cofinal_statements_iff_half_membership :
    ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows) ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip)
```

<a id="record-257rig-c17-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_terminal_strip_forces_half_membership` | [E257_26/Challenge.lean, line 224](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L224) | [PaperStatementsL.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsL.lean#L63) | [E257_26](../../evidence/comparator/replay-35882032091/receipt-E257_26.json) |
| `paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient` | [E257_26/Challenge.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L245) | [PaperStatementsQ.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsQ.lean#L40) | [E257_26](../../evidence/comparator/replay-35882032091/receipt-E257_26.json) |
| `paper_exact_row_integerHalfCarry_eq_one` | [E257_26/Challenge.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L239) | [PaperStatementsQ.lean, line 33](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsQ.lean#L33) | [E257_26](../../evidence/comparator/replay-35882032091/receipt-E257_26.json) |
| `paper_terminal_strip_witness_six` | [E257_26/Challenge.lean, line 170](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L170) | [PaperStatementsAT.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsAT.lean#L32) | [E257_26](../../evidence/comparator/replay-35882032091/receipt-E257_26.json) |
| `paper_both_cofinal_statements_iff_half_membership` | [E257_26/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L212) | [PaperStatementsK.lean, line 101](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsK.lean#L101) | [E257_26](../../evidence/comparator/replay-35882032091/receipt-E257_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-c18"></a>

## Theorem 6.86 (Cofinal returns of the greedy carry), page 66

> *Suppose that for every $`N\ge0`$ there is $`M\ge N`$ such that
> ``` math
> \operatorname{ihc}(G,M)\le B(M+1)
>        =2\lfloor\sqrt{M+1}\rfloor+4.
> ```
> Then $`G`$ is infinite and $`X_G(2)=1/2`$. Unlike Theorem <a href="#record:257rig-c16" data-reference-type="ref" data-reference="record:257rig-c16">127</a>, this hypothesis bounds the actual greedy carry only at unboundedly many indices. It still concerns the same fixed support $`G`$, not independently chosen finite supports. Comparing this carry with the carry obtained by fixing a finite prefix introduces a contribution from later omitted ranks. No equivalence with the finite-support hypothesis of Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a> follows without controlling that additional contribution. The hypothesis is not established.*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CofinalStripReturn.lean#L130)

```lean
theorem greedy_half_infinite_of_cofinalStripReturn
    (hreturn : GreedyHalfCarryCofinalStripReturn) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2
```

2. [`Erdos249257.halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L949)

```lean
theorem halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage
    {c : ℕ} (hc : 4 ≤ c)
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c) :
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
        2 ^ (c - 3) ↔
      mobiusCenteredHalfCarry
          (greedyMersenneSupport (1 / 2 : ℝ)) (2 * c - 4) ≤
        (futureSkipCapacity
          (greedyMersenneSupport (1 / 2 : ℝ)) c (c - 3) : ℤ)
```

<a id="record-257rig-c18-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `greedy_half_infinite_of_cofinalStripReturn` | [E257_26/Challenge.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L145) | [PaperStatementsD.lean, line 98](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsD.lean#L98) | [E257_26](../../evidence/comparator/replay-35882032091/receipt-E257_26.json) |
| `halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage` | [E257_27/Challenge.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L109) | [PaperStatementsF.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsF.lean#L150) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c19"></a>

## Theorem 6.87 (An eventual nonnegative margin suffices), page 66

> *Fix a positive depth $`k`$ and put $`D=G\cap\{2,\ldots,k\}`$. The following conditions are equivalent:
> ``` math
> r_k(1/2)<2^{-(k+1)}
>  \quad\Longleftrightarrow\quad
>  F_k(J)\ge0\ \text{for some }J\ge0.
> ```
> Here $`F_k(J)`$ is the integer expression defined in Theorem <a href="#thm:frozen-margin" data-reference-type="ref" data-reference="thm:frozen-margin">56</a>. Its normalised value is
> ``` math
> 2^{-J}F_k(J)=\sum_{i=1}^{J}c_D(k+1+i)2^{-i}-C_D(k).
> ```
> This normalised expression, not necessarily $`F_k(J)`$ itself, is nondecreasing in $`J`$. Its limit is $`1-2^{k+1}r_k(1/2)`$, by the finite-support Lambert identity. This is positive exactly under the strict dyadic inequality on the left. At positive $`k`$, oddness of the reduced excess numerator excludes equality at zero.*
> 
> *The result supplies some finite horizon, not the horizon $`J=c-3`$ required in the crossing application. More quantitatively, write $`\eta=1-2^{k+1}r_k(1/2)>0`$. Since $`\sum_{r\ge1}c_D(m+r)2^{-r}\le m+2`$, the omitted tail shows that $`(k+J+3)2^{-J}<\eta`$ suffices for $`F_k(J)>0`$. The value $`\eta`$ is rational for the finite support $`D`$, so this is an effective sufficient test. Proving it at the prescribed horizon is a separate arithmetic obligation.*

The Lean declarations below together state a result at least as strong as this one. The Lean tail bound $\sum_{r\ge1}c_A(m+r)2^{-r}\le m+2$ holds for every set $A\subseteq\N$, of which $D$ is a case, and the normalised value, its monotonicity and limit, the positivity criterion, the effective test and the rationality of $\eta$ are proved for every $k\ge0$; the equivalence and the exclusion of $r_k(1/2)=2^{-(k+1)}$ assume $k\ge1$ as printed.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L56)

```lean
theorem paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc (k : ℕ) :
    (↑(halfGreedyPrefixSupport k) : Set ℕ) =
      greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Icc 2 k
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_eventual_nonnegative_margin_equivalence`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L131)

```lean
theorem paper_eventual_nonnegative_margin_equivalence {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) ↔
      ∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_value`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L165)

```lean
theorem paper_frozen_margin_normalised_value (k J : ℕ) :
    (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J =
      (∑ i ∈ Finset.Icc 1 J,
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + i) : ℝ) /
            (2 : ℝ) ^ i) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_monotone`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L180)

```lean
theorem paper_frozen_margin_normalised_monotone (k : ℕ) :
    Monotone (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J)
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_eq_coeffTail_sub_carry`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L200)

```lean
theorem paper_eta_eq_coeffTail_sub_carry (k : ℕ) :
    1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k =
      binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ)
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_tendsto`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L221)

```lean
theorem paper_frozen_margin_normalised_tendsto (k : ℕ) :
    Tendsto (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J)
      atTop
      (nhds (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k))
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_limit_pos_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L239)

```lean
theorem paper_frozen_margin_limit_pos_iff (k : ℕ) :
    0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k ↔
      greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1)
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_greedyHalfRemainder_ne_dyadicCap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L92)

```lean
theorem paper_greedyHalfRemainder_ne_dyadicCap {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k ≠ halfDyadicCap (k + 1)
```

9. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_coeffTail_le_index_add_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L258)

```lean
theorem paper_coeffTail_le_index_add_two (A : Set ℕ) (m : ℕ) :
    binaryCoeffTail (supportCoeff A) m ≤ (m : ℝ) + 2
```

10. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_effective_horizon_test`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L266)

```lean
theorem paper_effective_horizon_test (k J : ℕ)
    (heta : 0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)
    (htest : ((k + J + 3 : ℕ) : ℝ) / (2 : ℝ) ^ J <
      1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) :
    0 < greedyHalfFrozenMargin k J
```

11. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_hasRationalValue`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L311)

```lean
theorem paper_eta_hasRationalValue (k : ℕ) :
    HasRationalValue
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)
```

<a id="record-257bm-c19-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc` | [E257_27/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L212) | [PaperStatementsN.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L180) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_eventual_nonnegative_margin_equivalence` | [E257_27/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L180) | [PaperStatementsN.lean, line 142](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L142) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_frozen_margin_normalised_value` | [E257_27/Challenge.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L200) | [PaperStatementsN.lean, line 166](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L166) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_frozen_margin_normalised_monotone` | [E257_27/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L190) | [PaperStatementsN.lean, line 154](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L154) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_eta_eq_coeffTail_sub_carry` | [E257_27/Challenge.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L168) | [PaperStatementsN.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L128) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_frozen_margin_normalised_tendsto` | [E257_27/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L194) | [PaperStatementsN.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L159) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_frozen_margin_limit_pos_iff` | [E257_27/Challenge.lean, line 185](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L185) | [PaperStatementsN.lean, line 148](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L148) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_greedyHalfRemainder_ne_dyadicCap` | [E257_27/Challenge.lean, line 208](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L208) | [PaperStatementsN.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L175) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_coeffTail_le_index_add_two` | [E257_27/Challenge.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L128) | [PaperStatementsAL.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsAL.lean#L65) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_effective_horizon_test` | [E257_27/Challenge.lean, line 161](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L161) | [PaperStatementsN.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L120) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_eta_hasRationalValue` | [E257_27/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L175) | [PaperStatementsN.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L136) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c20"></a>

## Theorem 6.88 (Half-membership and infinitely many skips), page 66

> *``` math
> \tfrac12\in\ensuremath{\mathcal A} \;\Longleftrightarrow\; \text{the set of ranks skipped by the greedy rule for }\tfrac12\text{ is infinite}.
> ```
> Odd-denominator parity supplies the positivity clause in Theorem <a href="#record:257bm-c2" data-reference-type="ref" data-reference="record:257bm-c2">111</a> automatically. Thus its cofinal-positive-skip hypothesis is exactly the assertion that the greedy skipped support is infinite, which the displayed theorem identifies with half-membership. See Observation <a href="#record:257bm-k5" data-reference-type="ref" data-reference="record:257bm-k5">175</a> for the reason this restatement does not itself prove membership.*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GreedyAchievementSet.lean#L2583)

```lean
theorem half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite
```

2. [`Erdos249257.mem_mersenneAchievementSet_of_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GreedyAchievementSet.lean#L1528)

```lean
theorem mem_mersenneAchievementSet_of_greedySkippedSupport_infinite
    {x : ℝ} (hx : 0 ≤ x)
    (hskips : (greedyMersenneSkippedSupport x).Infinite) :
    x ∈ mersenneAchievementSet
```

<a id="record-257bm-c20-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite` | [E257_15/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_15/Challenge.lean#L117) | [PaperStatementsB.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_15/PaperStatementsB.lean#L62) | [E257_15](../../evidence/comparator/replay-35882032091/receipt-E257_15.json) |
| `mem_mersenneAchievementSet_of_greedySkippedSupport_infinite` | [E257_27/Challenge.lean, line 235](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L235) | [PaperStatementsB.lean, line 108](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsB.lean#L108) | [E257_27](../../evidence/comparator/replay-35882032091/receipt-E257_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i1a"></a>

## Theorem 6.89 (The next floor quotient), page 67

> *For $`d\ge2`$ and $`M\ge0`$, the floor quotient satisfies
> ``` math
> q(M+1,d)=2q(M,d)+\mathbf1_{d\mid M+1}.
> ```
> Indeed, $`q(M,d)=\sum_{j=1}^{\lfloor M/d\rfloor}2^{M-jd}`$. Increasing $`M`$ doubles each existing term and adds $`1`$ exactly when $`M+1`$ is divisible by $`d`$. Thus a quotient doubles or doubles plus one; it does not remain unchanged except when both values are zero. Summing over a fixed finite support gives the corresponding update with added term $`c_D(M+1)`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L37)

```lean
theorem paper_next_floor_quotient {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient (M + 1) d =
      2 * localMersenneQuotient M d + (if d ∣ M + 1 then 1 else 0)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient_no_fixed_point`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L74)

```lean
theorem paper_next_floor_quotient_no_fixed_point {M d : ℕ} (hd : 2 ≤ d)
    (hfix : localMersenneQuotient (M + 1) d = localMersenneQuotient M d) :
    localMersenneQuotient M d = 0 ∧ localMersenneQuotient (M + 1) d = 0
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_next_quotient_sum`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L82)

```lean
theorem paper_next_quotient_sum {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M + endpointDivisorContribution D (M + 1)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_floor_quotient_geometric_sum`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L44)

```lean
theorem paper_floor_quotient_geometric_sum {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = ∑ j ∈ Finset.Icc 1 (M / d), 2 ^ (M - j * d)
```

<a id="record-257bm-i1a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_next_floor_quotient` | [E257_28/Challenge.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L67) | [PaperStatementsAK.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L22) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_next_floor_quotient_no_fixed_point` | [E257_28/Challenge.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L72) | [PaperStatementsAK.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L26) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_next_quotient_sum` | [E257_28/Challenge.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L77) | [PaperStatementsAK.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L30) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_floor_quotient_geometric_sum` | [E257_28/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L63) | [PaperStatementsAK.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L19) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i1b"></a>

## Theorem 6.90 (The next quotient sum), page 67

> *For a fixed finite set $`D\subseteq\{2,3,\ldots\}`$ and $`M\ge0`$,
> ``` math
> Q(D,M+1)=2Q(D,M)+c_D(M+1).
> ```
> This is the sum of Theorem <a href="#record:257bm-i1a" data-reference-type="ref" data-reference="record:257bm-i1a">132</a> over $`d\in D`$. Keeping $`D`$ fixed is essential: changing the support between steps adds a separate difference of quotient sums. The exclusion of $`d=1`$ is also essential for the displayed correction term, since $`q(M,1)=2^M`$ doubles without an added unit.*

The Lean declaration below states this result.

[`Erdos249257.localPrefixQuotient_succ`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusExactTransition.lean#L131)

```lean
theorem localPrefixQuotient_succ
    {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M +
        endpointDivisorContribution D (M + 1)
```

<a id="record-257bm-i1b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `localPrefixQuotient_succ` | [E257_28/Challenge.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L107) | [PaperStatementsAD.lean, line 112](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAD.lean#L112) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i1c"></a>

## Theorem 6.91 (The signed endpoint recurrence), page 67

> *The signed next-step expression is $`H(D,k,n)=2S(D,k,n-1)+1-c_D(n)`$. The last term counts the selected exponents dividing the new endpoint. This is the same recurrence shape as the generic tempered-orbit recurrence $`u(N+1)=2u(N)-v\cdot c(N+1)`$ from the tempered-orbit criterion (Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a> below), specialised to Mersenne local repair. A matching recurrence alone does not imply rationality: Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a> also requires one fixed coefficient sequence, integer states and a vanishing scaled limit. Those additional conditions must be checked before that criterion can be applied to these finite-row quantities.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_recurrence`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L92)

```lean
theorem paper_signed_endpoint_recurrence (D : Finset ℕ) (k n : ℕ) :
    localRepairInteger D k n =
      2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
        (endpointDivisorContribution D n : ℤ)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_endpoint_term_counts_divisors`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L99)

```lean
theorem paper_endpoint_term_counts_divisors {D : Finset ℕ} {n : ℕ}
    (hn : 0 < n) :
    endpointDivisorContribution D n = (D.filter fun d ↦ d ∣ n).card ∧
      endpointDivisorContribution D n = supportCoeff (↑D : Set ℕ) n
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_defect_succ`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L106)

```lean
theorem paper_signed_endpoint_defect_succ {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    localEndpointDefect D (M + 1) =
      2 * localEndpointDefect D M + 1 -
        (endpointDivisorContribution D (M + 1) : ℤ)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_repair_integer_eq_endpoint_defect`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L114)

```lean
theorem paper_repair_integer_eq_endpoint_defect {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hbelow : localPrefixQuotient D M ≤ halfEndpointTarget M) :
    localRepairInteger D 1 (M + 1) = localEndpointDefect D (M + 1)
```

<a id="record-257bm-i1c-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_signed_endpoint_recurrence` | [E257_28/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L96) | [PaperStatementsAK.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L46) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_endpoint_term_counts_divisors` | [E257_28/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L150) | [PaperStatementsAN.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAN.lean#L28) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_signed_endpoint_defect_succ` | [E257_28/Challenge.lean, line 89](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L89) | [PaperStatementsAK.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L40) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_repair_integer_eq_endpoint_defect` | [E257_28/Challenge.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L83) | [PaperStatementsAK.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L35) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i5"></a>

## Theorem 6.93 (Equivalent forms of the sharper bound), page 67

> *Under the hypotheses of Definition <a href="#record:257bm-i-cap" data-reference-type="ref" data-reference="record:257bm-i-cap">135</a>:
> ``` math
> \ensuremath{S}(D,1,2c-2) < 2^{c-2} \;\Longleftrightarrow\; 2^{(2c-2)-1} \le \ensuremath{Q}(D\cup\{c\},\ 2c-2).
> ```
> The threshold on the right is one greater than the exact-row target $`2^{2c-3}-1`$. Thus this is a test for omitting rank $`c`$, not for including it in the completed row.*

The Lean declaration below states this result.

[`Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusSkippedCoreCriticalCapacity.lean#L22)

```lean
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localPrefixQuotient (insert c D) (2 * c - 2)
```

<a id="record-257bm-i5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff` | [E257_28/Challenge.lean, line 215](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L215) | [PaperStatementsAR.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAR.lean#L171) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i6"></a>

## Theorem 6.94 (An unconditional bound with one extra bit), page 68

> *Unconditionally, for every $`c\ge4`$ and every below-half core $`D\subseteq[2,c)`$ with deficit $`<\ensuremath{w}(c)`$:
> ``` math
> \ensuremath{S}(D,1,2c-2) < 2^{c-1}.
> ```
> The bound holds uniformly in $`c`$, but is twice the threshold needed in Theorem <a href="#record:257bm-i5" data-reference-type="ref" data-reference="record:257bm-i5">136</a> to apply Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a>. Before using $`|D|\le c-2\le2^{c-2}`$, the proof gives the sharper additive estimate $`\ensuremath{S}(D,1,2c-2)<2^{c-2}+|D|`$. Thus the critical-capacity inequality would follow by excluding the integer band $`[2^{c-2},\,2^{c-2}+c-3]`$, which contains $`c-2`$ integers. This is the same band shape as Theorem <a href="#record:257bm-c11" data-reference-type="ref" data-reference="record:257bm-c11">122</a>’s dyadic-band condition. Its width is linear in $`c`$, whereas the square-root reset condition discussed in Section <a href="#sec:o4" data-reference-type="ref" data-reference="sec:o4">12.5</a> has width $`2^{(r+5)/2}`$ in a different parameter $`r`$. Comparing these widths alone proves no implication between the two hypotheses.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_unconditional_bound_one_extra_bit`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L126)

```lean
theorem paper_unconditional_bound_one_extra_bit {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 1) ∧ D.card ≤ c - 2
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharper_additive_estimate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L141)

```lean
theorem paper_sharper_additive_estimate {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) + D.card
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_capacity_band_exclusion`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L236)

```lean
theorem paper_capacity_band_exclusion {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    D.card ≤ c - 2 ∧ c - 2 ≤ 2 ^ (c - 2) ∧
      (Finset.Icc (2 ^ (c - 2)) (2 ^ (c - 2) + (c - 3))).card = c - 2 ∧
      (localBinarySuffix D 1 (2 * c - 2) ∉
          Finset.Icc (2 ^ (c - 2)) (2 ^ (c - 2) + (c - 3)) →
        localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2))
```

<a id="record-257bm-i6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_unconditional_bound_one_extra_bit` | [E257_28/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L255) | [PaperStatementsAS.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAS.lean#L43) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_sharper_additive_estimate` | [E257_28/Challenge.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L247) | [PaperStatementsAS.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAS.lean#L31) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_capacity_band_exclusion` | [E257_28/Challenge.lean, line 225](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L225) | [PaperStatementsAR.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAR.lean#L228) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i7"></a>

## Theorem 6.95 (The binary bound after doubling), page 68

> *Let $`n\ge6`$ and $`D\subseteq\{2,\ldots,n\}`$ satisfy $`2\in D`$, $`Q(D,n)=2^{n-1}-1`$, and $`X_D(2)<1/2`$. Then
> ``` math
> S(D,1,2n-1)<2^{n-1}.
> ```
> The missing quotient can therefore be filled using only the ranks $`n+1,\ldots,2n-1`$, without changing $`D`$.*

The Lean declarations below together state this result.

1. [`Erdos249257.localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusExactRowDoubling.lean#L44)

```lean
theorem localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * n - 1) < 2 ^ (n - 1)
```

2. [`Erdos249257.exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusExactRowDoubling.lean#L185)

```lean
theorem exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below
    {D : Finset ℕ} {n : ℕ}
    (hn : 6 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (htwo : 2 ∈ D)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    ∃ E : Finset ℕ,
      D ⊆ E ∧
      (∀ d ∈ E, d ∉ D → n < d) ∧
      2 ∈ E ∧
      (∀ d ∈ E, 2 ≤ d ∧ d ≤ 2 * n - 1) ∧
      localPrefixQuotient E (2 * n - 1) =
        2 ^ ((2 * n - 1) - 1) - 1
```

<a id="record-257bm-i7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below` | [E257_28/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L205) | [PaperStatementsAR.lean, line 162](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAR.lean#L162) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below` | [E257_28/Challenge.lean, line 189](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L189) | [PaperStatementsAR.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAR.lean#L115) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i-rank2"></a>

## Proposition 6.96 (Every exact sum contains exponent two), page 69

> *Let $`n\ge3`$ and let $`D\subseteq\{2,\ldots,n\}`$ satisfy $`Q(D,n)=2^{n-1}-1`$. Then $`2\in D`$. Thus the rank-two hypothesis in Theorem <a href="#record:257bm-i7" data-reference-type="ref" data-reference="record:257bm-i7">138</a> is automatic for its exact rows. The interval restriction on $`D`$ is part of the assertion, not an assumption about arbitrary finite quotient sums.*

The Lean declaration below states this result.

[`Erdos249257.two_mem_of_exact_localMersenneQuotient`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusExactRowRankTwo.lean#L23)

```lean
theorem two_mem_of_exact_localMersenneQuotient
    {D : Finset ℕ} {n : ℕ}
    (hn : 3 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    2 ∈ D
```

<a id="record-257bm-i-rank2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `two_mem_of_exact_localMersenneQuotient` | [E257_28/Challenge.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L115) | [PaperStatementsAD.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAD.lean#L119) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i9"></a>

## Proposition 6.98 (Error in the finite subseries value), page 69

> *An exact row at endpoint $`n`$ has real value within $`O(n/2^n)`$ of $`1/2`$: the quantitative bound $`|y_n-1/2|\le(n+1)/2^n`$ consumed by Theorem <a href="#record:257bm-c1" data-reference-type="ref" data-reference="record:257bm-c1">110</a> to turn a sequence of exact rows tending to depth infinity into a sequence of values tending to $`1/2`$.*

The Lean declaration below states this result.

[`Erdos249257.abs_localMersennePrefixValue_sub_half_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusGlobalRepair.lean#L243)

```lean
theorem abs_localMersennePrefixValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    |((localMersennePrefixValue D : ℚ) : ℝ) - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
```

<a id="record-257bm-i9-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `abs_localMersennePrefixValue_sub_half_le` | [E257_28/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L181) | [PaperStatementsAR.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAR.lean#L96) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i10"></a>

## Proposition 6.99 (No finite support has value one half), page 69

> *A finite sum of reciprocals of odd integers has odd denominator in lowest terms, so it cannot equal $`1/2`$. Applied to the denominators $`2^a-1`$, this proves that a support representing $`1/2`$ must be infinite, as used in Theorem <a href="#record:257bm-c1" data-reference-type="ref" data-reference="record:257bm-c1">110</a>.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_den_odd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OddReciprocalDenominators.lean#L54)

```lean
theorem paper_finite_sum_inv_odd_den_odd {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    Odd (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)).den
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_ne_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OddReciprocalDenominators.lean#L73)

```lean
theorem paper_finite_sum_inv_odd_ne_half {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)) ≠ (1 : ℚ) / 2
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finiteErdosSum_den_odd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OddReciprocalDenominators.lean#L94)

```lean
theorem paper_finiteErdosSum_den_odd (F : Finset ℕ) (h0 : 0 ∉ F) :
    Odd (finiteErdosSum F 2).den
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_support_series_ne_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OddReciprocalDenominators.lean#L114)

```lean
theorem paper_finite_support_series_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_half_representing_support_is_infinite`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OddReciprocalDenominators.lean#L142)

```lean
theorem paper_half_representing_support_is_infinite
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2) :
    A.Infinite
```

<a id="record-257bm-i10-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_finite_sum_inv_odd_den_odd` | [E257_28/Challenge.lean, line 123](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L123) | [PaperStatementsAD.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAD.lean#L155) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_finite_sum_inv_odd_ne_half` | [E257_28/Challenge.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L128) | [PaperStatementsAD.lean, line 160](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAD.lean#L160) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_finiteErdosSum_den_odd` | [E257_28/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L156) | [PaperStatementsAN.lean, line 33](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAN.lean#L33) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_finite_support_series_ne_half` | [E257_28/Challenge.lean, line 160](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L160) | [PaperStatementsAN.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAN.lean#L36) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_half_representing_support_is_infinite` | [E257_28/Challenge.lean, line 165](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L165) | [PaperStatementsAN.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAN.lean#L40) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i11a"></a>

## Theorem 6.100 (Small remainder forces the greedy word), page 69

> *Let $`g\ge1`$ and let $`w_1,\ldots,w_m`$ be nonnegative integer weights satisfying
> ``` math
> w_i\ge g+\sum_{j>i}w_j\qquad(1\le i\le m).
> ```
> Fix an integer capacity $`C\ge0`$. The greedy word $`\gamma`$ is obtained by taking $`w_i`$ exactly when it does not exceed the remaining capacity. For an admissible Boolean word $`\varepsilon`$, meaning $`\sum_i\varepsilon_iw_i\le C`$, one has
> ``` math
> C-\sum_i\varepsilon_iw_i<g
>  \quad\Longleftrightarrow\quad
>  \varepsilon=\gamma\ \text{and}\
>  C-\sum_i\gamma_iw_i<g.
> ```
> Indeed, two different words have sums separated by at least $`g`$, as seen at their first differing index; the greedy sum is the largest admissible sum. Thus there is at most one admissible word with remainder below $`g`$, and any such word is greedy. The greedy word alone need not have remainder below $`g`$: for weights $`(5)`$, gap $`g=2`$ and capacity $`C=3`$, its remainder is $`3`$.*

The Lean declaration below states this result.

[`Erdos249257.BooleanMobiusGreedyReduction.remainder_lt_gap_iff_eq_integerGreedyBits`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L918)

```lean
theorem remainder_lt_gap_iff_eq_integerGreedyBits
    {gap C : ℕ} {weights : List ℕ} {bits : List Bool} (hgap : 0 < gap)
    (hdom : GapDominates gap weights)
    (hlen : bits.length = weights.length)
    (hadm : weightedBoolSum weights bits ≤ C) :
    C - weightedBoolSum weights bits < gap ↔
      bits = integerGreedyBits weights C ∧
        integerGreedyRemainder weights C < gap
```

<a id="record-257bm-i11a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `remainder_lt_gap_iff_eq_integerGreedyBits` | [E257_02/Challenge.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_02/Challenge.lean#L157) | [PaperStatementsC.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_02/PaperStatementsC.lean#L17) | [E257_02](../../evidence/comparator/replay-35882032091/receipt-E257_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i11b"></a>

## Proposition 6.101 (Gap domination of the integer weights), page 70

> *For integers $`1\le d\le R\le M`$, the quotient weights satisfy
> ``` math
> \left\lfloor\frac{2^M}{2^d-1}\right\rfloor
>  \ge 2^{M-R}+
>  \sum_{j=d+1}^{R}\left\lfloor\frac{2^M}{2^j-1}\right\rfloor.
> ```
> Thus the finite weight list at ranks $`2,\ldots,R`$ satisfies the hypothesis of Theorem <a href="#record:257bm-i11a" data-reference-type="ref" data-reference="record:257bm-i11a">143</a> with $`g=2^{M-R}`$. At $`M=2R-1`$ this gap is $`2^{R-1}`$, and at $`M=2R`$ it is $`2^R`$. The inequality is unconditional; it does not assert that the greedy remainder is smaller than the gap.*

The Lean declarations below together state this result.

1. [`Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom_gapDominates`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L684)

```lean
theorem localMersenneWeightsFrom_gapDominates
    {M R d : ℕ} (hRM : R ≤ M) (hd : 1 ≤ d) :
    GapDominates (lowerBinaryWindow M R)
      (localMersenneWeightsFrom M R d)
```

2. [`Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_even`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L846)

```lean
theorem localMersenneWeights_gapDominates_even
    (R : ℕ) (hR : 1 ≤ R) :
    GapDominates (2 ^ (R - 1)) (localMersenneWeights (2 * R - 1) R)
```

3. [`Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_odd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L855)

```lean
theorem localMersenneWeights_gapDominates_odd (R : ℕ) :
    GapDominates (2 ^ R) (localMersenneWeights (2 * R) R)
```

<a id="record-257bm-i11b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `localMersenneWeightsFrom_gapDominates` | [E257_28/Challenge.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L287) | [PaperStructuresAY.lean, line 284](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStructuresAY.lean#L284) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `localMersenneWeights_gapDominates_even` | [E257_28/Challenge.lean, line 293](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L293) | [PaperStructuresAY.lean, line 291](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStructuresAY.lean#L291) | [E257_28](../../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `localMersenneWeights_gapDominates_odd` | [E257_29/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L110) | [PaperStructuresAY.lean, line 281](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStructuresAY.lean#L281) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i11c"></a>

## Proposition 6.102 (Uniqueness of the finite greedy representation), page 70

> *Let $`1\le M`$, $`0\le R\le M`$, and $`0\le a<2^{M-R}`$. If
> ``` math
> \sum_{d=2}^{R}\varepsilon_d
>        \left\lfloor\frac{2^M}{2^d-1}\right\rfloor+a
>        =2^{M-1}-1,\qquad \varepsilon_d\in\{0,1\},
> ```
> then $`\varepsilon`$ is the greedy word for capacity $`2^{M-1}-1`$ and $`a`$ is its remainder. This follows by applying Theorem <a href="#record:257bm-i11a" data-reference-type="ref" data-reference="record:257bm-i11a">143</a> with the preceding gap inequality. The statement identifies any such representation; it does not prove that a representation with $`a<2^{M-R}`$ exists. The degenerate formal case $`M=0`$ has empty word and zero target, using truncated natural-number subtraction.*

The Lean declaration below states this result.

[`Erdos249257.BooleanMobiusGreedyReduction.localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L997)

```lean
theorem localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq
    {M R A : ℕ} {bits : List Bool}
    (hRM : R ≤ M)
    (hlen : bits.length = (localMersenneWeights M R).length)
    (hfill :
      weightedBoolSum (localMersenneWeights M R) bits + A =
        2 ^ (M - 1) - 1)
    (hA : A < lowerBinaryWindow M R) :
    bits = integerGreedyBits (localMersenneWeights M R)
        (2 ^ (M - 1) - 1) ∧
      A = integerGreedyRemainder (localMersenneWeights M R)
        (2 ^ (M - 1) - 1)
```

<a id="record-257bm-i11c-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq` | [E257_29/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L96) | [PaperStructuresAY.lean, line 253](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStructuresAY.lean#L253) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i12"></a>

## Theorem 6.103 (A division-free form of the binary bound), page 70

> *For $`M\ge0`$ and $`d\ge2`$,
> ``` math
> \left\lfloor\frac{2^M}{2^d-1}\right\rfloor
>    =\sum_{j=1}^{\lfloor M/d\rfloor}2^{M-jd},
> ```
> where an empty sum is zero. To see this, write $`M=qd+r`$ with $`0\le r<d`$ and expand the finite geometric sum. The remaining fraction is $`2^r/(2^d-1)`$, which lies strictly between $`0`$ and $`1`$. Substitution in Theorem <a href="#record:257bm-i5" data-reference-type="ref" data-reference="record:257bm-i5">136</a> expresses its quotient condition as a finite sum of powers of $`2`$. This is an exact rewriting, not a weaker hypothesis or a new existence result.*

The Lean declarations below together state this result.

1. [`Erdos249257.localMersenneQuotient_eq_geometric`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L27)

```lean
theorem localMersenneQuotient_eq_geometric
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = localMersenneGeometricQuotient M d
```

2. [`Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L196)

```lean
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localGeometricPrefixQuotient (insert c D) (2 * c - 2)
```

3. [`Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L208)

```lean
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) - 2 ^ (c - 2) ≤
        localGeometricPrefixQuotient D (2 * c - 2)
```

<a id="record-257bm-i12-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `localMersenneQuotient_eq_geometric` | [E257_29/Challenge.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L119) | [PaperStatementsAD.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAD.lean#L107) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric` | [E257_29/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L149) | [PaperStatementsAR.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAR.lean#L174) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore` | [E257_29/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L159) | [PaperStatementsAR.lean, line 183](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAR.lean#L183) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i2"></a>

## Theorem 6.104 (An upper bound for a binary coefficient tail), page 70

> *Let $`c:\mathbb{N}\to\mathbb{N}`$ satisfy $`c(n)\le n`$ for every $`n`$. Then
> ``` math
> \sum_{r\ge1}c(N+r)2^{-r}\le N+2\qquad(N\ge0).
> ```
> Indeed, $`c(N+r)\le N+r`$, while $`\sum_{r\ge1}2^{-r}=1`$ and $`\sum_{r\ge1}r2^{-r}=2`$. Thus the scaled tail is $`O(N)`$, and in particular $`o(2^N)`$, as required in Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a>. The coefficient bound also holds for Euler’s totient function.*

The Lean declarations below together state a result at least as strong as this one. The Lean statement has the same hypotheses and conclusion as the printed one, for every $N\ge0$. A second Lean statement gives the consequence $2^{-N}\sum_{r\ge1}c(N+r)2^{-r}\to0$.

1. [`Erdos249257.binaryCoeffTail_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L85)

```lean
theorem binaryCoeffTail_le (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (N : ℕ) :
    binaryCoeffTail c N ≤ (N : ℝ) + 2
```

2. [`Erdos249257.binaryCoeffTail_div_pow_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L91)

```lean
theorem binaryCoeffTail_div_pow_tendsto_zero
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    Tendsto (fun N : ℕ ↦ binaryCoeffTail c N / (2 : ℝ) ^ N) atTop (nhds 0)
```

<a id="record-257bm-i2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `binaryCoeffTail_le` | [E257_29/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L180) | [PaperStatementsAE.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAE.lean#L58) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `binaryCoeffTail_div_pow_tendsto_zero` | [E257_29/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L175) | [PaperStatementsAE.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAE.lean#L54) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i-t7"></a>

## Theorem 6.105 (Rationality through an integer recurrence), page 71

> *Let $`c:\mathbb{N}\to\mathbb{N}`$ satisfy $`c(n)\le n`$ for every $`n`$. Then $`\sum_{n\ge1}c(n)2^{-n}`$ is rational if and only if there exist a positive integer $`v`$ and a sequence $`u:\mathbb{N}\to\mathbb{Z}`$ such that
> ``` math
> u(N+1)=2u(N)-v c(N+1)\quad(N\ge0),\qquad
>  \frac{u(N)}{2^N}\longrightarrow0.
> ```
> The limit condition is $`u(N)=o(2^N)`$; it does not assume that $`u`$ is bounded. No divisor-count hypothesis is imposed on $`c`$. Thus the ordinary statement also applies to $`c=\varphi`$; the identification with the separate formal \#249 development, including its indexing conventions, is not asserted here.*

The Lean declaration below states a result at least as strong as this one. The Lean statement has the same hypotheses and conclusion as the printed one, with rationality written as the negation of irrationality.

[`Erdos249257.not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L435)

```lean
theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ¬ Irrational (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u
```

<a id="record-257bm-i-t7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit` | [E257_29/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L184) | [PaperStatementsAE.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAE.lean#L64) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
