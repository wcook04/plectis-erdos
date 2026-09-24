# Formal evidence: Reciprocal Mersenne Subseries, Section 6, results 6.35 to 6.71

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="thm-greedy-survival-catalogue"></a>

## Theorem 6.35 (Greedy survival and membership), page 51

> *With the greedy remainder $`r_n(x)`$ and complete tail $`R_n`$,
> ``` math
> x\in\mathcal A\quad\Longleftrightarrow\quad
>  x\ge0\ \text{and}\ r_n(x)\le R_n\text{ for every }n\ge0.
> ```
> If all inequalities hold, the nonnegative remainders tend to zero because $`R_n\to0`$, so the greedy partial sums converge to $`x`$. Conversely, strict tail domination $`w_n>R_n`$ forces the greedy choices in any representation and therefore gives every inequality. The argument applies to positive summable weights satisfying that separation hypothesis; it is not a consequence of summability alone.*

The Lean declaration below states this result or one that implies it. The Lean statement is the displayed equivalence for the Mersenne weights and every real $x$, with the same hypotheses and conclusion as the printed one. The closing remark that the argument extends to other positive summable weights with $w_n>R_n$ describes the proof and has no Lean counterpart.

[`Erdos249257.mem_mersenneAchievementSet_iff_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GreedyAchievementSet.lean#L1458)

```lean
theorem mem_mersenneAchievementSet_iff_greedy_survival (x : ℝ) :
    x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n
```

<a id="thm-greedy-survival-catalogue-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `mem_mersenneAchievementSet_iff_greedy_survival`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L134) (E257_05, line 134), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsB.lean#L106) (PaperStatementsB.lean, line 106), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-rank-step-trichotomy"></a>

## Lemma 6.36 (The two next-prefix intervals and their gap), page 51

> *Let $`d\ge0`$ be an integer, let $`u\subseteq\{1,\ldots,d\}`$, and suppose the target $`t`$ lies in the interval $`[X_u(2),X_u(2)+R_d]`$. At depth $`d+1`$, either $`t`$ lies in the lower interval
> ``` math
> [X_u(2),X_u(2)+R_{d+1}],
> ```
> or in the upper interval
> ``` math
> [X_u(2)+w_{d+1},X_u(2)+w_{d+1}+R_{d+1}],
> ```
> or in the open gap between them. These alternatives are disjoint because $`R_{d+1}<w_{d+1}`$, and exhaustive because $`R_d=w_{d+1}+R_{d+1}`$. For $`t=1/2`$, Lemma 6.38 also excludes the interval endpoints, so all relevant comparisons are strict. Endpoint exclusion is not what makes the two child intervals disjoint; the strict-tail inequality does that.*

The Lean declarations below together state this result or one that implies it. The Lean statements give the three alternatives for every real target $t$ (`isStraddlePrefix_step_trichotomy`); the left endpoint $X_{u\cup\{d+1\}}(2)$ of the upper interval equals $X_u(2)+w_{d+1}$ by `positiveMersenneSupportValue_insert`, since $d+1\notin u$. Disjointness is one line from $R_{d+1}<w_{d+1}$ (`mersenneTail_lt_weight`) and the strict inequalities defining the gap. For $t=1/2$, `IsStraddlePrefix.half_strict` makes every endpoint comparison strict and `IsStraddlePrefix.half_step_forced` gives the three cases as mutually exclusive.

1. [`Erdos249257.isStraddlePrefix_step_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L205)

```lean
theorem isStraddlePrefix_step_trichotomy {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix t u d) :
    IsStraddlePrefix t u (d + 1) ∨
      IsStraddlePrefix t (insert (d + 1) u) (d + 1) ∨
        (positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t ∧
          t < positiveMersenneSupportValue (↑u : Set ℕ)
              + mersenneWeight (d + 1))
```

2. [`Erdos249257.IsStraddlePrefix.half_step_forced`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L301)

```lean
theorem IsStraddlePrefix.half_step_forced {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    (IsStraddlePrefix (1 / 2 : ℝ) u (d + 1) ∧
        ¬ IsStraddlePrefix (1 / 2 : ℝ) (insert (d + 1) u) (d + 1)) ∨
      (IsStraddlePrefix (1 / 2 : ℝ) (insert (d + 1) u) (d + 1) ∧
          ¬ IsStraddlePrefix (1 / 2 : ℝ) u (d + 1)) ∨
        (positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
            < 1 / 2 ∧
          (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
            + mersenneWeight (d + 1))
```

3. [`Erdos249257.mersenneTail_lt_weight`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GreedyAchievementSet.lean#L180)

```lean
theorem mersenneTail_lt_weight {n : ℕ} (hn : 0 < n) :
    mersenneTail n < mersenneWeight n
```

4. [`Erdos249257.positiveMersenneSupportValue_insert`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L144)

```lean
theorem positiveMersenneSupportValue_insert {F : Finset ℕ} {a : ℕ}
    (ha : a ∉ F) :
    positiveMersenneSupportValue (↑(insert a F) : Set ℕ)
      = mersenneWeight a + positiveMersenneSupportValue (↑F : Set ℕ)
```

5. [`Erdos249257.IsStraddlePrefix.half_strict`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L287)

```lean
theorem IsStraddlePrefix.half_strict {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    positiveMersenneSupportValue (↑u : Set ℕ) < 1 / 2 ∧
      (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
        + mersenneTail d
```

<a id="lem-rank-step-trichotomy-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-fatal-gap-exclusion"></a>

## Lemma 6.37 (A greedy gap excludes every representation), page 51

> *Let $`d\ge0`$ be an integer and $`u\subseteq\{1,\ldots,d\}`$ a finite prefix. If
> ``` math
> X_u(2)+R_{d+1}<t<X_u(2)+w_{d+1},
> ```
> then no support agreeing with $`u`$ through rank $`d`$ represents $`t`$: omitting $`d+1`$ leaves value at most the lower endpoint, while including it gives value at least the upper endpoint. Other length-$`d`$ prefixes have disjoint containing intervals by the first-difference argument using $`w_n>R_n`$. Since the displayed gap lies inside the interval for $`u`$, none of those prefixes can represent $`t`$ either. Thus a certified strict gap excludes every representation, not just one proposed continuation.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_excludes_every_representation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L174)

```lean
theorem fatal_gap_excludes_every_representation {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    ∀ A : Set ℕ, 0 ∉ A → positiveMersenneSupportValue A ≠ t
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_endpoint_bounds`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L114)

```lean
theorem fatal_gap_endpoint_bounds {A : Set ℕ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hagree : ∀ n : ℕ, 0 < n → n ≤ d → (n ∈ A ↔ n ∈ u)) :
    (d + 1 ∉ A →
        positiveMersenneSupportValue A
          ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)) ∧
      (d + 1 ∈ A →
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)
          ≤ positiveMersenneSupportValue A)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.depth_prefix_interval_disjoint`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L144)

```lean
theorem depth_prefix_interval_disjoint {t : ℝ} {u v : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d) (hv : ∀ n ∈ v, 0 < n ∧ n ≤ d)
    (hut : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d)
    (hvt : positiveMersenneSupportValue (↑v : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑v : Set ℕ) + mersenneTail d) :
    u = v
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_within_prefix_interval`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L162)

```lean
theorem fatal_gap_within_prefix_interval {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
```

<a id="lem-fatal-gap-exclusion-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `fatal_gap_excludes_every_representation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L251) (E257_17, line 251), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L185) (PaperStatementsAM.lean, line 185), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_17.json) (E257_17)
- `fatal_gap_endpoint_bounds`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L240) (E257_17, line 240), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L175) (PaperStatementsAM.lean, line 175), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_17.json) (E257_17)
- `depth_prefix_interval_disjoint`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L231) (E257_17, line 231), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L161) (PaperStatementsAM.lean, line 161), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_17.json) (E257_17)
- `fatal_gap_within_prefix_interval`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L258) (E257_17, line 258), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L191) (PaperStatementsAM.lean, line 191), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_17.json) (E257_17)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-half-endpoint-kills"></a>

## Lemma 6.38 (No finite Mersenne sum equals one half), page 52

> *For every finite $`u\subseteq\mathbb N_{>0}`$, $`X_u(2)\ne1/2`$: its reduced denominator is odd. Also $`X_u(2)+R_d\ne1/2`$ for every $`d\ge0`$, since $`R_d`$ is the irrational full Mersenne sum minus a finite rational sum. These observations exclude equality at the finite-prefix and complete-tail endpoints of Lemma 6.36.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same conclusions as the printed ones; the second holds for every finite $u$ and every $d\ge0$, where an index $0$ in $u$ contributes nothing to $X_u(2)$. Their proofs use the printed reasons: the reduced denominator of $X_u(2)$ is odd, and the full Mersenne sum is irrational.

1. [`Erdos249257.positiveMersenneSupportValue_coe_finset_ne_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L243)

```lean
theorem positiveMersenneSupportValue_coe_finset_ne_half
    {u : Finset ℕ} (h0 : 0 ∉ u) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≠ (1 / 2 : ℝ)
```

2. [`Erdos249257.half_ne_coe_finset_add_mersenneTail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L263)

```lean
theorem half_ne_coe_finset_add_mersenneTail
    (u : Finset ℕ) (d : ℕ) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
      ≠ (1 / 2 : ℝ)
```

<a id="lem-half-endpoint-kills-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `positiveMersenneSupportValue_coe_finset_ne_half`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L226) (E257_17, line 226), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L110) (PaperStatementsAM.lean, line 110), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_17.json) (E257_17)
- `half_ne_coe_finset_add_mersenneTail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L220) (E257_17, line 220), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L98) (PaperStatementsAM.lean, line 98), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_17.json) (E257_17)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-straddle-agrees-greedy"></a>

## Lemma 6.39 (Straddle words are canonical: they agree with the greedy prefix), page 52

> *Let $`u\subseteq\{1,\ldots,d\}`$ satisfy $`X_u(2)\le1/2\le X_u(2)+R_d`$. Then
> ``` math
> u=G\cap\{1,\ldots,d\},
> ```
> where $`G`$ is the real greedy support for $`1/2`$. At the first disagreement, if $`u`$ takes rank $`k`$ and the greedy rule skips it, then $`X_u(2)>1/2`$. In the opposite case, the greedy remainder before $`k`$ is at least $`w_k`$, whereas the remaining contribution allowed by $`u`$, including $`R_d`$, is at most $`R_k<w_k`$. Both cases contradict the displayed interval. Thus there is at most one such word at each depth; the lemma does not assert its existence at every depth.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one: it gives $n\in u\Leftrightarrow n\in G$ for $1\le n\le d$, which is $u=G\cap\{1,\ldots,d\}$.

[`Erdos249257.IsStraddlePrefix.half_agrees_greedy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L442)

```lean
theorem IsStraddlePrefix.half_agrees_greedy
    {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    ∀ n : ℕ, 0 < n → n ≤ d →
      (n ∈ u ↔ n ∈ greedyMersenneSupport (1 / 2 : ℝ))
```

<a id="lem-straddle-agrees-greedy-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-last-skip-iff-fatal"></a>

## Theorem 6.40 (Last-skip iff local fatality: a pointwise criterion), page 52

> *Keep $`G`$ for the selected half-greedy support, $`r_M(1/2)`$ for its remainder and $`R_M`$ for the complete tail after rank $`M`$. A positive rank $`M`$ is the last omitted rank if and only if $`M\notin G`$ and $`r_M(1/2)>R_M`$. Consequently,
> ``` math
> \frac12\in\mathcal A
>  \quad\Longleftrightarrow\quad
>  r_M(1/2)\le R_M\quad\text{for every positive }M\notin G.
> ```
> Thus it suffices to check the tail inequality at the ranks actually omitted by the greedy rule. This is an equivalence on that fixed orbit; it does not establish the inequality at its unboundedly many possible omitted ranks.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones, with the omitted ranks taken as the positive ranks outside $G$.

1. [`Erdos249257.isLastHalfGreedySkip_iff_skip_and_fatal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderFixedTailSocket.lean#L22)

```lean
theorem isLastHalfGreedySkip_iff_skip_and_fatal
    {M : ℕ} :
    IsLastHalfGreedySkip M ↔
      M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) ∧
        GreedyMersenneFatalAt (1 / 2 : ℝ) M
```

2. [`Erdos249257.half_mem_iff_every_actual_skip_survives`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderFixedTailSocket.lean#L73)

```lean
theorem half_mem_iff_every_actual_skip_survives :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ M : ℕ,
        M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) →
          greedyMersenneRemainder (1 / 2 : ℝ) M ≤ mersenneTail M
```

<a id="thm-last-skip-iff-fatal-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `isLastHalfGreedySkip_iff_skip_and_fatal`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_18/Challenge.lean#L64) (E257_18, line 64), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_18/PaperStatementsG.lean#L36) (PaperStatementsG.lean, line 36), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_18.json) (E257_18)
- `half_mem_iff_every_actual_skip_survives`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L292) (E257_17, line 292), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsD.lean#L166) (PaperStatementsD.lean, line 166), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_17.json) (E257_17)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-seam-upper-or-middle"></a>

## Lemma 6.41 (Seam upper-or-middle classification), page 52

> *At a row $`s\ge5`$, the terminal rank is omitted in the next row, $`s\notin D_{s+1}`$, if and only if either
> ``` math
> 4o_s+p_s^+\le2^{s+1},
> ```
> or this inequality fails and
> ``` math
> 4\,\mathrm{rem}(s)+2^{s+1}-p_s^-<2^{s+2}+4.
> ```
> These are exactly branches $`\mathrm U`$ and $`\mathrm M`$ of Theorem 5.16. On either branch the new terminal weight does not fit; on $`\mathrm R`$ it does. This is an exact classification, not a conjecture inferred from observed branch labels.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one: for $s\ge5$ the bit of index $s$ in the greedy word of row $s+1$ is zero exactly when branch $\mathrm U$ or branch $\mathrm M$ holds at $s$. The subtraction in the $\mathrm M$ inequality is natural-number subtraction, which agrees with the printed one because $p_s^-\le2(s-2)<2^{s+1}$.

[`Erdos249257.seamGreedy_terminal_false_iff_upperOrMiddle`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L57)

```lean
theorem seamGreedy_terminal_false_iff_upperOrMiddle
    (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = false ↔
      SeamGreedyUpperOrMiddleAt s hs
```

<a id="lem-seam-upper-or-middle-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `seamGreedy_terminal_false_iff_upperOrMiddle`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_08/Challenge.lean#L312) (E257_08, line 312), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_08/Statement.lean#L312) (Statement.lean, line 312), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_08.json) (E257_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-largest-false-rank-algebra"></a>

## Lemma 6.42 (The exact gap at the largest omitted rank), page 52

> *Let $`2\le d<s`$ and $`2s<3d`$. Write $`W_s(E)=\sum_{e\in E}\lfloor4^s/(2^e-1)\rfloor`$ for a finite set $`E\subseteq\{2,\ldots,s-1\}`$. For $`u\subseteq\{2,\ldots,d-1\}`$, put $`E_-=u\cup\{d+1,\ldots,s-1\}`$ and $`E_+=u\cup\{d\}`$. Then
> ``` math
> 3W_s(E_-)+3\cdot2^{s+1}+2\cdot4^{s-d}+4=3W_s(E_+).
> ```
> The correction is independent of the common prefix $`u`$. For the integer-greedy rows $`s\ge5`$, a right transition preserves the largest omitted rank, whereas an upper or middle transition makes $`s`$ the largest omitted rank in the next row.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.largest_false_rank_algebra`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamRowGapAndCarry.lean#L39)

```lean
theorem largest_false_rank_algebra {s d : ℕ} {u : Finset ℕ}
    (hd2 : 2 ≤ d) (hds : d < s) (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d)
    (hlate : 2 * s < 3 * d) :
    3 * rowWeightSum s (u ∪ Finset.Ico (d + 1) s)
        + (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4)
      = 3 * rowWeightSum s (insert d u)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_largest_false_rank_algebra`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamRowGapAndCarry.lean#L98)

```lean
theorem paper_largest_false_rank_algebra :
    (∀ (s d : ℕ) (u : Finset ℕ), 2 ≤ d → d < s → (∀ e ∈ u, 2 ≤ e ∧ e < d) →
        2 * s < 3 * d →
        3 * rowWeightSum s (u ∪ Finset.Ico (d + 1) s)
            + (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4)
          = 3 * rowWeightSum s (insert d u)) ∧
    (∀ (s d : ℕ) (hs : 5 ≤ s), IsLargestFalseRank (seamGreedyWord s) d →
        ¬ SeamGreedyUpperOrMiddleAt s hs →
        IsLargestFalseRank (seamGreedyWord (s + 1)) d) ∧
    (∀ (s : ℕ) (hs : 5 ≤ s), SeamGreedyUpperOrMiddleAt s hs →
        IsLargestFalseRank (seamGreedyWord (s + 1)) s)
```

<a id="lem-largest-false-rank-algebra-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `largest_false_rank_algebra`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_18/Challenge.lean#L77) (E257_18, line 77), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_18/PaperStatementsAA.lean#L163) (PaperStatementsAA.lean, line 163), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_18.json) (E257_18)
- `paper_largest_false_rank_algebra`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_19/Challenge.lean#L319) (E257_19, line 319), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_19/PaperStructuresBH.lean#L204) (PaperStructuresBH.lean, line 204), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_19.json) (E257_19)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-critical-dyadic-band"></a>

## Theorem 6.43 (Reduction to the nearest dyadic boundary), page 53

> *Let $`d,E`$ be nonnegative integers with $`E\le2^{d+1}`$, and let $`j_*`$ be the largest $`j\in\{0,\ldots,d\}`$ for which $`E\le2^{d-j+1}`$. The set is nonempty, so $`j_*`$ is well defined, including when $`E=0`$. Then
> ``` math
> \begin{aligned}
>  &\forall j\in\{0,\ldots,d\},\quad
>   2^{d-j+1}<E\ \text{or}\ E+2(d+j)\le2^{d-j+1}\\
>  &\hspace{35mm}\Longleftrightarrow\quad
>  E+2(d+j_*)\le2^{d-j_*+1}.
>  \end{aligned}
> ```
> For $`j>j_*`$ the first alternative holds by maximality. For $`j\le j_*`$, the left side of the required inequality increases with $`j`$ and its right side decreases, so the condition at $`j_*`$ implies all the others. This is an elementary reduction from $`d+1`$ inequalities to one. Specialized to the seam reset charge (where the actual upper-reset condition gives $`E\le2^{d+1}`$, as explained in Proposition 6.80), the reduced hypothesis at the single index $`j_*`$ is proved logically equivalent to Theorem 6.10’s band-avoidance hypothesis.*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfUpperResetCriticalBand.exists_criticalDyadicBandIndex`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfUpperResetCriticalBand.lean#L46)

```lean
theorem exists_criticalDyadicBandIndex
    {d E : ℕ} (hE : E ≤ 2 ^ (d + 1)) :
    ∃ j : ℕ, CriticalDyadicBandIndex d E j
```

2. [`Erdos249257.HalfUpperResetCriticalBand.dyadicBandEscape_iff_exists_critical`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfUpperResetCriticalBand.lean#L108)

```lean
theorem dyadicBandEscape_iff_exists_critical
    {d E : ℕ} (hE : E ≤ 2 ^ (d + 1)) :
    DyadicBandEscape d E ↔
      ∃ j : ℕ, CriticalDyadicBandIndex d E j ∧
        E + 2 * (d + j) ≤ 2 ^ (d - j + 1)
```

3. [`Erdos249257.HalfUpperResetCriticalBand.seamUpperResetCriticalBandEscape_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfUpperResetCriticalBand.lean#L883)

```lean
theorem seamUpperResetCriticalBandEscape_iff :
    SeamUpperResetCriticalBandEscape ↔ SeamUpperResetDyadicBandEscape
```

<a id="thm-critical-dyadic-band-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-final-middle-cell"></a>

## Theorem 6.44 (Excluding minus three at a final middle transition), page 53

> *Suppose that row $`D\ge13`$ is a middle transition in Theorem 5.16 and every transition at a row $`s\ge D+1`$ is right. Then
> ``` math
> C_D:=4\,\mathrm{rem}(D)-p_D^--4\ne-3.
> ```
> This excludes one particular value under the stated tail assumption; it neither excludes every final middle transition nor proves the all-middle-row hypothesis of Theorem 6.9.*

The Lean declarations below together state this result.

1. [`Erdos249257.finalMiddleCell_neg_three_not_last`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L587)

```lean
theorem finalMiddleCell_neg_three_not_last
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hcell :
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -3) :
    False
```

2. [`Erdos249257.mobiusCenteredHalfCarry_add_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L39)

```lean
theorem mobiusCenteredHalfCarry_add_two
    (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N
```

<a id="thm-final-middle-cell-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-skipped-endpoint-trichotomy"></a>

## Lemma 6.45 (The signed position of a skipped greedy prefix), page 54

> *Let $`s\ge5`$ be omitted by the real greedy support $`G`$, and put
> ``` math
> H_s=G\cap\{2,\ldots,s-1\},\qquad
>  f_s=\sum_{d\in H_s}\left\lfloor\frac{4^s}{2^d-1}\right\rfloor-T_s.
> ```
> Exactly one of the following holds:
> ``` math
> \begin{array}{lll}
>  f_s<0:& H_s=D_s,& f_s=-\mathrm{rem}(s),\quad \mathrm{rem}(s)\ge1;\\
>  f_s=0:& H_s=D_s,& \mathrm{rem}(s)=0;\\
>  f_s>0:& H_s=B_s,& f_s=o_s.
>  \end{array}
> ```
> Thus the real greedy prefix is one of the two adjacent integer words. This classifies its signed distance $`f_s`$ from $`T_s`$; it does not exclude the negative case. Nor does it identify $`f_s`$ with the different coordinate $`C_s=4\mathrm{rem}(s)-p_s^- -4`$ used in the final-middle argument.*

The Lean declaration below states this result.

[`Erdos249257.halfGreedy_skipped_endpoint_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L246)

```lean
theorem halfGreedy_skipped_endpoint_trichotomy
    (s : ℕ) (hs : 5 ≤ s)
    (hskip : ¬ mersenneWeight s ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (s - 1)) :
    (greedyHalfFrozenMargin (s - 1) s < 0 ∧
        halfActualSeamWord s = seamGreedyWord s ∧
        1 ≤ seamIntegerGreedyRemainder s ∧
        greedyHalfFrozenMargin (s - 1) s =
          -(seamIntegerGreedyRemainder s : ℤ)) ∨
      (greedyHalfFrozenMargin (s - 1) s = 0 ∧
        halfActualSeamWord s = seamGreedyWord s ∧
        seamIntegerGreedyRemainder s = 0) ∨
      (0 < greedyHalfFrozenMargin (s - 1) s ∧
        halfActualSeamWord s = seamAboveWord s hs ∧
        greedyHalfFrozenMargin (s - 1) s =
          ((seamAdjacentCut s hs).overshoot : ℤ))
```

<a id="lem-skipped-endpoint-trichotomy-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `halfGreedy_skipped_endpoint_trichotomy`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_16/Challenge.lean#L316) (E257_16, line 316), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_16/PaperStructuresBI.lean#L264) (PaperStructuresBI.lean, line 264), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_16.json) (E257_16)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-reverse-carry-word"></a>

## Lemma 6.46 (Spacing of reverse-carry words), page 54

> *For $`i=1,2`$, let integer sequences $`a_i,b_i,u_i`$ satisfy
> ``` math
> b_i(m)+2u_i(m)=a_i(m)+u_i(m+1).
> ```
> Let $`k,L\ge0`$ be integers. Suppose that at index $`k`$ the coefficients agree and $`b_1(k)-b_2(k)=1`$. Suppose also that both coefficients and bits agree at indices $`k+1,\ldots,k+L`$. Then
> ``` math
> u_1(k+L+1)-u_2(k+L+1)
>    =2^L\bigl(2(u_1(k)-u_2(k))+1\bigr).
> ```
> The factor in parentheses is an odd integer. If the two terminal carries have absolute values at most $`B_1,B_2`$, respectively, then $`2^L\le B_1+B_2`$. For a common bound $`B`$ the conclusion is $`2^L\le2B`$, not $`2^L\le B`$. The formula follows by subtracting the two recurrences: the initial bit difference gives the odd factor, and each subsequent agreement doubles it. An application must supply the stated agreements and terminal bounds.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_reverse_carry_word`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamRowGapAndCarry.lean#L240)

```lean
theorem paper_reverse_carry_word :
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ k L : ℕ, a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        u₁ (k + L + 1) - u₂ (k + L + 1) = 2 ^ L * (2 * (u₁ k - u₂ k) + 1) ∧
          Odd (2 * (u₁ k - u₂ k) + 1)) ∧
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ (k L : ℕ) (B₁ B₂ : ℝ), a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B₁ →
        |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B₂ →
        (2 : ℝ) ^ L ≤ B₁ + B₂) ∧
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ (k L : ℕ) (B : ℝ), a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B →
        |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B →
        (2 : ℝ) ^ L ≤ 2 * B)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.reverse_carry_word_common_bound_sharp`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamRowGapAndCarry.lean#L209)

```lean
theorem reverse_carry_word_common_bound_sharp :
    ∃ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ) (k L : ℕ) (B : ℝ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) ∧
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) ∧
      a₁ k = a₂ k ∧ b₁ k - b₂ k = 1 ∧
      (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) ∧
      (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) ∧
      |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B ∧ |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B ∧
      ¬ ((2 : ℝ) ^ L ≤ B)
```

<a id="lem-reverse-carry-word-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_reverse_carry_word`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L110) (E257_20, line 110), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAA.lean#L238) (PaperStatementsAA.lean, line 238), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)
- `reverse_carry_word_common_bound_sharp`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L169) (E257_20, line 169), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAA.lean#L344) (PaperStatementsAA.lean, line 344), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-linear-channel-nogo"></a>

## Lemma 6.47 (Linear functionals factoring through one value), page 54

> *Let $`V`$ be a vector space over $`\mathbb Q`$, let $`\mathrm{ev}:V\to\mathbb Q`$ be linear, and choose $`e\in V`$ with $`\mathrm{ev}(e)=1`$. Suppose that each linear functional $`\ell_j:V\to\mathbb Q`$ vanishes on $`\ker(\mathrm{ev})`$. Then $`v-\mathrm{ev}(v)e\in\ker(\mathrm{ev})`$ gives $`\ell_j(v)=\ell_j(e)\mathrm{ev}(v)`$. Consequently any finite evaluation matrix $`(\ell_j(v_i))_{i,j}`$ is an outer product and has rank at most one. Every square minor of order at least two therefore vanishes. This excludes determinant arguments formed from these particular functionals, not determinant methods with additional independent information.*

The Lean declarations below together state this result or one that implies it. The Lean factorisation $\Lambda(v)=\mathrm{ev}(v)\,w_0$ holds for a linear map $\Lambda$ into any $\mathbb Q$-vector space $W$ whose kernel contains $\ker(\mathrm{ev})$; the printed identity is its case $W=\mathbb Q$, $\Lambda=\ell_j$, where $w_0=\ell_j(e)$. The vanishing of every square minor of order at least two is the second Lean statement (a square matrix $(\ell_j(v_i))$ over an index set with at least two elements), and rank at most one follows from the $2\times2$ minors.

1. [`Erdos249257.AdelicHeightObstruction.linearDescender_eq_smul_eval`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/AdelicHeightObstruction.lean#L120)

```lean
theorem linearDescender_eq_smul_eval
    {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (ev : V →ₗ[ℚ] ℚ) (Λ : V →ₗ[ℚ] W)
    (hker : LinearMap.ker ev ≤ LinearMap.ker Λ)
    (he : ∃ e : V, ev e = 1) :
    ∃ w₀ : W, ∀ v : V, Λ v = ev v • w₀
```

2. [`Erdos249257.HalfTrappingReturnCarry.relationInvariantLinearChannels_det_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfTrappingReturnCarry.lean#L42)

```lean
theorem relationInvariantLinearChannels_det_eq_zero
    {V ι : Type*} [AddCommGroup V] [Module ℚ V]
    [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (he : ∃ e : V, ev e = 1) (row : ι → V) :
    Matrix.det (fun i j : ι ↦ channel j (row i)) = 0
```

<a id="lem-linear-channel-nogo-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `linearDescender_eq_smul_eval`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L101) (E257_20, line 101), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAA.lean#L68) (PaperStatementsAA.lean, line 68), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)
- `relationInvariantLinearChannels_det_eq_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L184) (E257_20, line 184), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAB.lean#L16) (PaperStatementsAB.lean, line 16), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-two-thirds-band"></a>

## Theorem 6.48 (Two-thirds band: exact localisation of post-take skip-unsafety), page 54

> *Write a positive residual as $`1/R`$. A skipped rank $`k`$ passes the sufficient dyadic test precisely when $`R\ge2^k`$. Suppose a weight at rank $`b`$ is taken without exhausting the residual: with $`q=2^b-1`$, assume $`0<R<q`$. The new reciprocal residual is $`Rq/(q-R)`$. If the next take is at rank $`c\ge b+2`$, put $`m=2^{c-1}`$. The last skipped rank is dyadically unsafe exactly when
> ``` math
> m-1<\frac{Rq}{q-R}<m,
>  \quad\text{equivalently}\quad
>  \frac{q(m-1)}{q+m-1}<R<\frac{qm}{q+m}.
> ```
> Clearing the positive denominators proves the equivalence. The interval has width $`q^2/((q+m)(q+m-1))`$.*
> 
> *For a single skipped rank, $`c=b+2`$ and $`m=2q+2`$. The width is then $`q^2/((3q+1)(3q+2))<1/9`$, and the interval lies inside $`2q<3R<2q+2/3`$. In this single-skip case, the cited corollaries exclude integral $`R`$ and show that a reduced pre-take residual $`p/(2D)`$ with $`p,D,q`$ odd can be unsafe only if $`p\ge7`$. The latter conclusion uses the divisibility by $`4`$ of $`6D-2pq`$ under the unsafe-band inequalities.*
> 
> *These are local transition statements, not bounds on the actual half-greedy orbit. Dyadic safety is only sufficient for the current tail test. The odd-coprime data $`(p,D,b)=(17,41,3)`$ give an unsafe single-skip example; no conclusion that the half-greedy orbit avoids such data follows from the band calculation.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_two_thirds_band`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/PostTakeBandLocalisation.lean#L96)

```lean
theorem paper_two_thirds_band :
    (∀ (R : ℚ) (k : ℕ), 0 < R → (1 / R ≤ 1 / 2 ^ k ↔ (2 : ℚ) ^ k ≤ R)) ∧
    (∀ R q : ℚ, 0 < R → R < q → 1 / (1 / R - 1 / q) = R * q / (q - R)) ∧
    (∀ R q m : ℚ, 0 < R → R < q → 1 ≤ m →
        ((m - 1 < R * q / (q - R) ∧ R * q / (q - R) < m) ↔
          (q * (m - 1) / (q + m - 1) < R ∧ R < q * m / (q + m)))) ∧
    (∀ q m : ℚ, 0 < q → 1 ≤ m →
        q * m / (q + m) - q * (m - 1) / (q + m - 1)
          = q ^ 2 / ((q + m) * (q + m - 1))) ∧
    (∀ b : ℕ, (2 : ℚ) ^ (b + 1) = 2 * ((2 : ℚ) ^ b - 1) + 2) ∧
    (∀ q : ℚ, 0 < q →
        2 * q * (q + 1) / (3 * q + 2) - q * (2 * q + 1) / (3 * q + 1)
            = q ^ 2 / ((3 * q + 1) * (3 * q + 2)) ∧
          q ^ 2 / ((3 * q + 1) * (3 * q + 2)) < 1 / 9) ∧
    (∀ R q : ℚ, 0 < q →
        (q * (2 * q + 1) / (3 * q + 1) < R ∧ R < 2 * q * (q + 1) / (3 * q + 2)) →
        2 * q < 3 * R ∧ 3 * R < 2 * q + 2 / 3) ∧
    (∀ (R q : ℚ) (mm n : ℤ), 0 < q → R = (mm : ℚ) → q = (n : ℚ) →
        ¬ (q * (2 * q + 1) / (3 * q + 1) < R ∧
          R < 2 * q * (q + 1) / (3 * q + 2))) ∧
    (∀ p D q : ℤ, 0 < p → 0 < D → 0 < q → Odd p → Odd D → Odd q →
        (q * (2 * q + 1) * p < 2 * D * (3 * q + 1) ∧
          2 * D * (3 * q + 2) < 2 * p * q * (q + 1)) →
        (4 : ℤ) ∣ (6 * D - 2 * p * q) ∧ 7 ≤ p) ∧
    (Odd (17 : ℤ) ∧ Odd (41 : ℤ) ∧ Odd (7 : ℤ) ∧ (∃ x y : ℤ, x * 17 + y * 41 = 1) ∧
      (2 : ℚ) ^ 3 - 1 = 7 ∧
      ((7 : ℚ) * (2 * 7 + 1) / (3 * 7 + 1) < (2 * 41 : ℚ) / 17 ∧
        (2 * 41 : ℚ) / 17 < 2 * 7 * (7 + 1) / (3 * 7 + 2)))
```

<a id="thm-two-thirds-band-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_two_thirds_band`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L139) (E257_20, line 139), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAA.lean#L308) (PaperStatementsAA.lean, line 308), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-sharp-fatal-gap"></a>

## Theorem 6.49 (A weaker sufficient test against the remaining tail), page 55

> *Let $`k,u,L`$ be positive integers, and put $`a=2L-(2^k-1)u`$. Suppose $`a>0`$, equivalently that $`\rho=u/(2L)<w_k`$ and the greedy rule skips weight $`w_k`$. The dyadic sufficient test $`\rho\le2^{-k}`$ is equivalent to $`u\le a`$. The weaker sufficient condition
> ``` math
> 2u\le3a
> ```
> ensures $`\rho<R_k`$, by comparison with $`2^{-k}+(3\cdot4^k)^{-1}+(7\cdot8^k)^{-1}<R_k`$. This conclusion excludes a fatal tail-mass deficit at the current step; it does not assert that $`\rho`$ is representable by the remaining weights, or that all future greedy steps survive.*
> 
> *The containment of these sufficient conditions is strict even for valid rational data: $`(k,u,L,a)=(2,7,13,5)`$ gives $`1/4<7/26<R_2`$. In contrast, the scalar pair $`(u,a)=(3,2)`$ in the linked inequality lemma does not arise from integral $`L`$ under the present parity relation. Unit numerators are nonfatal at such a skipped step, since then $`a\ge1`$. Conversely, a fatal step requires $`3a<2u`$, hence $`u\ge2`$, or $`u\ge3`$ when $`u`$ is odd.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_fatal_gap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L299)

```lean
theorem paper_sharp_fatal_gap :
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ (u : ℝ) / (2 * L) < mersenneWeight k)) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ ¬ (mersenneWeight k ≤ (u : ℝ) / (2 * L)))) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k ↔ u ≤ a)) ∧
    (∀ k : ℕ, (1 : ℝ) / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        2 * u ≤ 3 * a → (u : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ u a : ℕ, u ≤ a → 2 * u ≤ 3 * a) ∧
    ((2 : ℕ) ^ 2 * 7 + 5 = 2 * 13 + 7 ∧ 2 * 7 ≤ 3 * 5 ∧ ¬ (7 ≤ 5) ∧
      (1 : ℝ) / 2 ^ 2 < (7 : ℝ) / (2 * 13) ∧ (7 : ℝ) / (2 * 13) < mersenneTail 2) ∧
    (∀ k L : ℕ, 1 ≤ k → 2 ^ k * 3 + 2 ≠ 2 * L + 3) ∧
    (∀ k L a : ℕ, 1 ≤ k → 0 < a → 2 ^ k * 1 + a = 2 * L + 1 →
        (1 : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        mersenneTail k < (u : ℝ) / (2 * L) →
        3 * a < 2 * u ∧ 2 ≤ u ∧ (Odd u → 3 ≤ u))
```

<a id="thm-sharp-fatal-gap-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_sharp_fatal_gap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L214) (E257_20, line 214), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L221) (PaperStatementsAM.lean, line 221), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-gap-mass-summability"></a>

## Lemma 6.50 (Summability of one gap length per level), page 55

> *For $`n\ge1`$, put $`g_n=w_n-R_n>0`$. The sum of one gap length per level satisfies, for $`N\ge0`$,
> ``` math
> \sum_{n>N}g_n\le\frac29\,4^{-N}+\frac37\,8^{-N}.
> ```
> This follows by summing the per-level upper bounds geometrically. It is not the measure of the union of all gaps: level $`n`$ has $`2^{n-1}`$ translated gaps of length $`g_n`$. The corresponding weighted sum and its geometric interpretation are given after Theorem 6.118. Neither estimate decides membership of a specified point such as $`1/2`$.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones: $g_n>0$ for $n\ge1$, and the tail bound for every $N\ge0$. They also record that $\sum_n g_n$ converges and that its tails tend to $0$.

1. [`Erdos249257.mersenneGap_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GreedyAchievementSet.lean#L2346)

```lean
theorem mersenneGap_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneGap n
```

2. [`Erdos249257.summable_mersenneGap_succ`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGapMass.lean#L77)

```lean
theorem summable_mersenneGap_succ : Summable (fun k : ℕ => mersenneGap (k + 1))
```

3. [`Erdos249257.mersenneGap_tail_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGapMass.lean#L83)

```lean
theorem mersenneGap_tail_le (N : ℕ) :
    ∑' k : ℕ, mersenneGap (N + k + 1)
      ≤ (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N
```

4. [`Erdos249257.tendsto_mersenneGap_tail_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGapMass.lean#L104)

```lean
theorem tendsto_mersenneGap_tail_zero :
    Tendsto (fun N : ℕ => ∑' k : ℕ, mersenneGap (N + k + 1)) atTop (nhds 0)
```

<a id="lem-gap-mass-summability-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `mersenneGap_pos`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L244) (E257_20, line 244), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAH.lean#L34) (PaperStatementsAH.lean, line 34), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)
- `summable_mersenneGap_succ`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L207) (E257_20, line 207), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L117) (PaperStatementsAM.lean, line 117), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)
- `mersenneGap_tail_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L202) (E257_20, line 202), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L106) (PaperStatementsAM.lean, line 106), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)
- `tendsto_mersenneGap_tail_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L210) (E257_20, line 210), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L119) (PaperStatementsAM.lean, line 119), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-half-divisor-unit-drop"></a>

## Lemma 6.51 (The effect of adding one divisor), page 55

> *Let $`N\ge0`$ and let finite supports $`D_0,D_1`$ differ only by $`D_1=D_0\cup\{N+1\}`$, with $`N+1\notin D_0`$. For every positive integer $`m`$,
> ``` math
> c_{D_1}(m)-c_{D_0}(m)=\mathbf1_{N+1\mid m}.
> ```
> In particular, the difference is $`1`$ at $`m=2(N+1)`$. This follows directly from the definition of a divisor count. Its use in another coefficient sequence requires proving that sequence has the same support-incidence description.*

The Lean declarations below together state this result or one that implies it. The Lean identity $c_{A\cup\{d\}}(m)=c_A(m)+\mathbf 1_{d\mid m}$ holds for every positive $m$, every set $A\subseteq\mathbb N$, finite or infinite, and every $d\notin A$; the printed statement is its case of a finite support $D_0$ and $d=N+1$. The value $1$ at $m=2(N+1)$ is also stated separately for finite binary words.

1. [`Erdos249257.HalfCylinderIntegerGreedy.supportCoeff_insert_eq_add_indicator`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderIntegerGreedy.lean#L882)

```lean
theorem supportCoeff_insert_eq_add_indicator
    (A : Set ℕ) {d n : ℕ} (hdA : d ∉ A) :
    supportCoeff (insert d A) n =
      supportCoeff A n + if d ∈ n.divisors then 1 else 0
```

2. [`Erdos249257.HalfDivisorUnitDrop.supportCoeff_extend_true_eq_false_add_one_at_double`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfDivisorUnitDrop.lean#L20)

```lean
theorem supportCoeff_extend_true_eq_false_add_one_at_double
    {N : ℕ} (a : HalfWord N) :
    supportCoeff (wordSupport (extendHalfWord a true)) (2 * (N + 1)) =
      supportCoeff (wordSupport (extendHalfWord a false)) (2 * (N + 1)) + 1
```

<a id="lem-half-divisor-unit-drop-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `supportCoeff_insert_eq_add_indicator`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L276) (E257_20, line 276), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAN.lean#L32) (PaperStatementsAN.lean, line 32), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)
- `supportCoeff_extend_true_eq_false_add_one_at_double`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L263) (E257_20, line 263), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAL.lean#L55) (PaperStatementsAL.lean, line 55), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) (E257_20)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-tempered-orbit-rigidity"></a>

## Theorem 6.52 (Uniqueness of an integer recurrence with a vanishing scaled limit), page 56

> *For any nonnegative-integer coefficient sequence $`c:\mathbb N\to\mathbb N`$ with $`c(n)\le
> n`$: the binary coefficient series $`X_c = \sum'_{n\ge 1} c(n)/2^n`$ is rational iff there exists a positive integer multiplier $`v`$ and an integer orbit $`u:\mathbb N\to\mathbb Z`$ satisfying the exact carry recurrence $`u(N{+}1)=2u(N)-v\cdot c(N{+}1)`$ together with the condition $`u(N)/2^N\to0`$. Every integer sequence satisfying both conditions obeys $`u(N) = v\cdot T_c(N)`$ exactly, where $`T_c(N)=\sum_{j\ge 1} c(N{+}j)/2^j`$ is the scaled tail. For each fixed $`v`$ there is at most one such sequence. Positivity of the orbit alone is deliberately *not* used as an equivalent criterion: a homogeneous $`2^N`$-scaled perturbation can be added to any orbit without breaking the recurrence, so the limit condition cannot be dropped. The choices $`c=c_A`$ for Problem 257 and $`c=\varphi`$ for Problem 249 both satisfy $`0\le c(n)\le n`$. The telescoping argument is given again, with an example, in Theorem 6.105.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones, with rationality written as $X_c=p/v$ for an integer $p$ and a positive integer $v$. Uniqueness for each fixed $v$ follows at once from $u(N)=v\,T_c(N)$.

1. [`Erdos249257.binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L426)

```lean
theorem binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u
```

2. [`Erdos249257.temperedBinaryOrbit_eq_scaledTail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L339)

```lean
theorem temperedBinaryOrbit_eq_scaledTail
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    {v : ℕ} {u : ℕ → ℤ} (horbit : IsTemperedBinaryOrbit c v u) :
    ∀ N : ℕ, (u N : ℝ) = (v : ℝ) * binaryCoeffTail c N
```

<a id="thm-tempered-orbit-rigidity-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L58) (E257_21, line 58), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAE.lean#L45) (PaperStatementsAE.lean, line 45), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)
- `temperedBinaryOrbit_eq_scaledTail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L64) (E257_21, line 64), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAE.lean#L65) (PaperStatementsAE.lean, line 65), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-tail-transfer"></a>

## Lemma 6.53 (Changing finitely many support elements), page 56

> *Let $`b\ge2`$ be an integer, and let $`A,B\subseteq\mathbb N_{\ge1}`$. If $`X_A(b)`$ is irrational and $`A,B`$ have finite symmetric difference, then $`X_B(b)`$ is irrational too: the two sums differ by a finite sum of rational numbers. This observation supplies the finite modifications in Theorem 6.21.*

The Lean declarations below together state this result or one that implies it. The Lean statements say that, for every $M\ge0$, $X_A(b)$ is irrational exactly when $X_{A\cap(M,\infty)}(b)$ is. The printed lemma follows in one line: sets with finite symmetric difference agree above some $M$, so irrationality passes from $X_A(b)$ to the common tail and back to $X_B(b)$.

1. [`Erdos249257.irrational_erdosSupportSeries_of_tail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L9467)

```lean
theorem irrational_erdosSupportSeries_of_tail (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b)
    (B : ℕ) (h : Irrational (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n})) :
    Irrational (erdosSupportSeries b A)
```

2. [`Erdos249257.irrational_erdosSupportSeries_tail_of_irrational`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L9476)

```lean
theorem irrational_erdosSupportSeries_tail_of_irrational (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (B : ℕ) (h : Irrational (erdosSupportSeries b A)) :
    Irrational (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n})
```

<a id="lem-tail-transfer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSupportSeries_of_tail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L78) (E257_21, line 78), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAG.lean#L76) (PaperStatementsAG.lean, line 76), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)
- `irrational_erdosSupportSeries_tail_of_irrational`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L83) (E257_21, line 83), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAG.lean#L95) (PaperStatementsAG.lean, line 95), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-dyadic-excess-reformulation"></a>

## Lemma 6.54 (An integer test for the interval between the dyadic and Mersenne weights), page 56

> *For positive integers $`p,L`$ and $`n\ge0`$, write the residual as $`p/(2L)`$ and put $`E=2^np-L`$. Clearing positive denominators gives
> ``` math
> \frac{p}{2L}\le\frac1{2^{n+1}}\quad\Longleftrightarrow\quad E\le0,
>  \qquad
>  \frac1{2^{n+1}}<\frac{p}{2L}<\frac1{2^{n+1}-1}
>  \quad\Longleftrightarrow\quad 0<E<\frac p2.
> ```
> The first test concerns the dyadic bound, not the greedy selection threshold itself. The second identifies precisely the interval in which a Mersenne weight is skipped but the dyadic safety test fails.*

The Lean declarations below together state this result or one that implies it. The Lean statements prove both equivalences for every integer $p$, every $L\ge1$ and every $n\ge0$, so the hypothesis $p>0$ is unnecessary; the second right-hand side is written as $0<E$ and $2E<p$. A third statement is the second equivalence for the half-greedy residual $r_n(1/2)$.

1. [`Erdos249257.divInt_le_nextDyadic_iff_excess_nonpos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/DyadicPrefixCompression.lean#L198)

```lean
theorem divInt_le_nextDyadic_iff_excess_nonpos
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    Rat.divInt p ((2 * L : ℕ) : ℤ) ≤ 1 / (2 : ℚ) ^ (n + 1) ↔
      nextDyadicExcessIntNumerator p n L ≤ 0
```

2. [`Erdos249257.greedyHalf_mem_nextMersenneDyadicSliver_iff_excess`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/DyadicPrefixCompression.lean#L1044)

```lean
theorem greedyHalf_mem_nextMersenneDyadicSliver_iff_excess (n : ℕ) :
    (halfDyadicCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n ∧
        greedyMersenneRemainder (1 / 2 : ℝ) n <
          mersenneWeight (n + 1)) ↔
      (0 < halfGreedyNextDyadicExcessNumerator n ∧
        2 * halfGreedyNextDyadicExcessNumerator n <
          halfGreedyResidualDisplayedNumerator n)
```

3. [`Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/DyadicPrefixCompression.lean#L262)

```lean
theorem divInt_mem_nextMersenneDyadicSliver_iff_excess
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    (1 / (2 : ℚ) ^ (n + 1) < Rat.divInt p ((2 * L : ℕ) : ℤ) ∧
        Rat.divInt p ((2 * L : ℕ) : ℤ) < mersenneWeightRat (n + 1)) ↔
      (0 < nextDyadicExcessIntNumerator p n L ∧
        2 * nextDyadicExcessIntNumerator p n L < p)
```

<a id="lem-dyadic-excess-reformulation-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-denominator-sandwich"></a>

## Lemma 6.55 (The odd denominator survives dyadic subtraction), page 56

> *Let $`r/D`$ be a reduced fraction with $`D>0`$ odd, let $`p\in\mathbb Z`$, and let $`c\ge0`$ be an integer. The reduced denominator of $`p/2^c-r/D`$ is divisible by $`D`$ and divides $`2^cD`$. Indeed, its unreduced numerator $`pD-2^cr`$ is coprime to $`D`$, since $`\gcd(r,D)=\gcd(2^c,D)=1`$. Reduction can therefore remove only powers of $`2`$ from the displayed denominator. No property of Mersenne weights is used.*

The Lean declarations below together state this result or one that implies it. The Lean statements take integers $p,r$ with no sign condition on $p/2^c-r/D$. `dyadicResidualIntNumerator_coprime_oddDenominator` shows that $pD-2^cr$ is coprime to $D$ when $D$ is odd and $\gcd(r,D)=1$, and `dyadicResidualInt_denominator_sandwich` then gives both divisibilities for the reduced denominator of $(pD-2^cr)/(2^cD)$, so the printed lemma is their one-line composition. `dyadicResidual_denominator_sandwich` is the special case $p,r\ge0$ with $2^cr\le pD$.

1. [`Erdos249257.dyadicResidual_denominator_sandwich`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/DyadicPrefixCompression.lean#L118)

```lean
theorem dyadicResidual_denominator_sandwich
    (p r c D : ℕ) (hDpos : 0 < D) (hDodd : Odd D)
    (hrD : r.Coprime D) (hle : 2 ^ c * r ≤ p * D) :
    D ∣ (dyadicResidualRat p r c D).den ∧
      (dyadicResidualRat p r c D).den ∣ 2 ^ c * D
```

2. [`Erdos249257.dyadicResidualInt_denominator_sandwich`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/DyadicPrefixCompression.lean#L57)

```lean
theorem dyadicResidualInt_denominator_sandwich
    (p r : ℤ) (c D : ℕ) (hDpos : 0 < D)
    (hND : (dyadicResidualIntNumerator p r c D).natAbs.Coprime D) :
    D ∣ (dyadicResidualIntRat p r c D).den ∧
      (dyadicResidualIntRat p r c D).den ∣ 2 ^ c * D
```

3. [`Erdos249257.dyadicResidualIntNumerator_coprime_oddDenominator`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/DyadicPrefixCompression.lean#L35)

```lean
theorem dyadicResidualIntNumerator_coprime_oddDenominator
    (p r : ℤ) (c D : ℕ) (hDodd : Odd D)
    (hrD : r.natAbs.Coprime D) :
    (dyadicResidualIntNumerator p r c D).natAbs.Coprime D
```

<a id="lem-denominator-sandwich-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-denominator-survival"></a>

## Lemma 6.56 (A guaranteed divisor of a reduced denominator), page 56

> *Let $`a\in\mathbb Z`$, $`D\in\mathbb N_{>0}`$ and $`m,C,h\in\mathbb N`$. Write $`\operatorname{den}(x)`$ for the positive reduced denominator of a rational number $`x`$. If $`m\mid D`$ and $`\gcd(m,|a|)=1`$, then $`m\mid\operatorname{den}(a/D)`$. If $`C\mid D`$ and $`\gcd(C,|a|)=1`$, then
> ``` math
> \frac{C}{\gcd(C,h)}\mid\operatorname{den}(ha/D).
> ```
> Thus scaling may remove part of the guaranteed divisor. Indeed, reduction divides $`D`$ by $`\gcd(D,|a|)`$, so no prime power in $`m`$ can be lost. After scaling, a prime $`p\mid C`$ can lose at most $`v_p(h)`$ powers from the guaranteed divisor. This is a lower bound on the reduced denominator, not an equality: for $`D=12`$, $`C=6`$, $`a=1`$, $`h=2`$, it guarantees the divisor $`3`$, while the reduced denominator is $`6`$. The lemma feeds Theorem 6.24 directly.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones; $C/\gcd(C,h)$ is an exact quotient, so natural-number division agrees with the printed one.

1. [`Erdos249257.RationalDenominatorSurvival.divisor_dvd_divInt_den`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RationalDenominatorSurvival.lean#L17)

```lean
theorem divisor_dvd_divInt_den
    {a : ℤ} {D m : ℕ} (hD : 0 < D) (hmD : m ∣ D)
    (hcop : Nat.Coprime m a.natAbs) :
    m ∣ (Rat.divInt a (D : ℤ)).den
```

2. [`Erdos249257.RationalDenominatorSurvival.survivingDivisor_dvd_scaled_divInt_den`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RationalDenominatorSurvival.lean#L38)

```lean
theorem survivingDivisor_dvd_scaled_divInt_den
    {a : ℤ} {D C h : ℕ} (hD : 0 < D) (hCD : C ∣ D)
    (hcop : Nat.Coprime C a.natAbs) :
    C / Nat.gcd C h ∣
      (Rat.divInt ((h : ℤ) * a) (D : ℤ)).den
```

<a id="lem-denominator-survival-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `divisor_dvd_divInt_den`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L186) (E257_21, line 186), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAA.lean#L80) (PaperStatementsAA.lean, line 80), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)
- `survivingDivisor_dvd_scaled_divInt_den`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L192) (E257_21, line 192), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAA.lean#L85) (PaperStatementsAA.lean, line 85), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-mixed-prime-power-layer"></a>

## Lemma 6.57 (Commuting prime-power differences), page 56

> *For a function $`g:\mathbb N_{>0}\to\mathbb Z`$, a positive integer $`p`$ and an integer $`e\ge1`$, define
> ``` math
> (\Delta_{p,e}g)(n)=g(p^en)-g(p^{e-1}n).
> ```
> These operators commute. If $`p\ne q`$ are primes, $`e,f\ge1`$, $`A\subseteq\mathbb N_{>0}`$, $`n\ge1`$ and $`\gcd(n,pq)=1`$, then
> ``` math
> (\Delta_{q,f}\Delta_{p,e}c_A)(n)
>    =\sum_{d\mid n}\mathbf1_A(p^eq^fd).
> ```
> Thus the mixed difference counts precisely the support elements whose $`p`$- and $`q`$-adic exponents are $`e`$ and $`f`$ in this divisor sum.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones, with the commutation proved for every $p,e$ and every $g$ defined on all of $\mathbb N$. The right side of the mixed identity is written as $c_{A'}(n)$ with $A'=\{d:\gcd(d,pq)=1,\ p^eq^fd\in A\}$, which equals $\sum_{d\mid n}\mathbf 1_A(p^eq^fd)$ because every divisor of $n$ is prime to $pq$.

1. [`Erdos249257.MaximalOmegaLayer.primePowerLayer_comm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MaximalOmegaLayer.lean#L29)

```lean
theorem primePowerLayer_comm
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) :
    primePowerLayer q f (primePowerLayer p e g) n =
      primePowerLayer p e (primePowerLayer q f g) n
```

2. [`Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_supportCoeffInt`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MaximalOmegaLayer.lean#L39)

```lean
theorem mixedPrimePowerLayerTwo_supportCoeffInt
    (A : Set ℕ) {p e q f n : ℕ}
    (hp : p.Prime) (he : 0 < e) (hq : q.Prime) (hf : 0 < f)
    (hpq : p ≠ q) (hn : n.Coprime (p * q)) :
    mixedPrimePowerLayerTwo p e q f (supportCoeffInt A) n =
      supportCoeffInt
        (exactPrimePowerPullback q f (exactPrimePowerPullback p e A)) n
```

<a id="lem-mixed-prime-power-layer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `primePowerLayer_comm`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L180) (E257_21, line 180), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAA.lean#L75) (PaperStatementsAA.lean, line 75), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)
- `mixedPrimePowerLayerTwo_supportCoeffInt`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L220) (E257_21, line 220), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAO.lean#L22) (PaperStatementsAO.lean, line 22), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-achievement-set-topology"></a>

## Proposition 6.59 (Achievement-set topology: compact, closed, perfect, measure exactly one), page 57

> *$`\ensuremath{\mathcal A}`$ is compact (continuous image of the binary-sequence Cantor space $`\mathbb N\to\mathrm{Fin}\,2`$ under the product topology, via the positive-index digit map), hence closed; it is also perfect, totally disconnected, and nowhere dense, with Lebesgue measure exactly $`1`$. The compactness/closedness argument (binary coding $`\to`$ Cantor space $`\to`$ continuous image) is a fully generic technique for characterizing the achievement set of *any* absolutely convergent digit-weighted series, not specific to Mersenne denominators ; reusable for a $`\varphi(n)/2^n`$ subsum set after checking summability. No separation of successive weights is needed for compactness or closedness; the stronger topological conclusions require their own hypotheses. Closedness alone is what powers every “limit of a sequence of achieved points is achieved” argument in this catalogue (e.g. Theorem 6.2, Theorem 6.5).*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_achievement_set_topology`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/AchievementSetTopologyAndFiniteHalf.lean#L27)

```lean
theorem paper_achievement_set_topology :
    Continuous positiveMersenneDigitValue ∧
      Set.range positiveMersenneDigitValue = mersenneAchievementSet ∧
      IsCompact mersenneAchievementSet ∧
      IsClosed mersenneAchievementSet ∧
      Perfect mersenneAchievementSet ∧
      IsTotallyDisconnected mersenneAchievementSet ∧
      IsNowhereDense mersenneAchievementSet ∧
      volume mersenneAchievementSet = 1
```

<a id="prop-achievement-set-topology-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_achievement_set_topology`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L273) (E257_21, line 273), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAM.lean#L187) (PaperStatementsAM.lean, line 187), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-master-dichotomy"></a>

## Theorem 6.60 (Nonmembership of one half and a finite fatal gap), page 58

> *The value $`1/2`$ is not in $`\mathcal A`$ if and only if there are an integer $`d\ge0`$ and a finite set $`u\subseteq\{1,\ldots,d\}`$ such that
> ``` math
> X_u(2)+R_{d+1}<\frac12<X_u(2)+w_{d+1}.
> ```
> One implication is Lemma 6.37. For the other, follow the greedy prefixes: nonmembership forces a first failure of the tail inequality, hence one of these gaps. The endpoint equalities are excluded by Lemma 6.38.*
> 
> *A finite prefix and strict gap provide a nonmembership witness. The tail inequality can be certified by rational truncation bounds as in Theorem 2.11. Membership, in contrast, asserts that no such witness exists; failure to find one in a finite search is not a proof. The reduction uses $`w_n>R_n`$, not compactness alone. The totient weights fail this hypothesis, as the example after Lemma 6.34 shows.*

The Lean declarations below together state this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one, in the form $1/2\in\mathcal A$ exactly when no such $d$ and $u$ exist. A second Lean statement records the direction from nonmembership to a gap as the disjunction that $1/2\in\mathcal A$ or such a gap exists.

1. [`Erdos249257.half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L654)

```lean
theorem half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ¬ ExistsFatalHalfGap
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_or_exists_fatal_gap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L623)

```lean
theorem half_mem_mersenneAchievementSet_or_exists_fatal_gap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
          < 1 / 2 ∧
        (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
          + mersenneWeight (d + 1)
```

<a id="thm-master-dichotomy-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L260) (E257_21, line 260), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAM.lean#L71) (PaperStatementsAM.lean, line 71), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)
- `half_mem_mersenneAchievementSet_or_exists_fatal_gap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L264) (E257_21, line 264), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAM.lean#L74) (PaperStatementsAM.lean, line 74), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) (E257_21)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-perturbed-family-maximality"></a>

## Theorem 6.62 (Perturbed-family maximality and the three-branch recurrence), page 58

> *Use the family and adjacent pair of Definition 6.61, and assume in addition that $`B<g`$. At capacity $`C'=4C+g`$, the largest admissible updated value is $`t(x_+)`$ if $`4o+p_+\le g`$, and $`t(x_-)`$ otherwise. After this choice, apply the take-if-possible rule to an additional weight $`W=2g+4`$. The resulting remainder is
> ``` math
> \begin{cases}
>  g-4o-p_+,&4o+p_+\le g,\\
>  4r+g-p_-,&4o+p_+>g\ \text{and}\ 4r+g-p_-<W,\\
>  4r-g-p_--4,&4o+p_+>g\ \text{and}\ 4r+g-p_-\ge W.
>  \end{cases}
> ```*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones. Under $B<g$, `prefixChoice_maximal` bounds every admissible updated value by $t$ of the chosen element, which is admissible by `above_newSum_le_capacity_iff` when $4o+p_+\le g$ and by `below_newSum_le_capacity` otherwise, and `prefixRemainder_eq_capacity_sub_choice` identifies the remainder before the weight $W$ with $C'$ minus that value. `nextRemainder_trichotomy` gives the three remainders, whose natural-number subtractions agree with the printed ones because $p_-\le B<g$ and because of each case's inequality.

1. [`Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.prefixChoice_maximal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderIntegerGreedy.lean#L1390)

```lean
theorem prefixChoice_maximal
    (hcap : F.pulseCap < F.gap)
    [Decidable K.successorCarries]
    {x : α} (hx : F.newSum x ≤ K.newCapacity) :
    F.newSum x ≤ F.newSum K.prefixChoice
```

2. [`Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.nextRemainder_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderIntegerGreedy.lean#L1463)

```lean
theorem nextRemainder_trichotomy
    [Decidable K.successorCarries] :
    K.nextRemainder =
      if K.successorCarries then
        F.gap - (4 * K.overshoot + K.abovePulse)
      else if 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight then
        4 * K.remainder + F.gap - K.belowPulse
      else
        4 * K.remainder - F.gap - K.belowPulse - 4
```

3. [`Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.below_newSum_le_capacity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderIntegerGreedy.lean#L1360)

```lean
theorem below_newSum_le_capacity
    (hcap : F.pulseCap < F.gap) :
    F.newSum K.below ≤ K.newCapacity
```

4. [`Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.above_newSum_le_capacity_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderIntegerGreedy.lean#L1368)

```lean
theorem above_newSum_le_capacity_iff :
    F.newSum K.above ≤ K.newCapacity ↔ K.successorCarries
```

5. [`Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.prefixRemainder_eq_capacity_sub_choice`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderIntegerGreedy.lean#L1446)

```lean
theorem prefixRemainder_eq_capacity_sub_choice
    [Decidable K.successorCarries] :
    K.prefixRemainder = K.newCapacity - F.newSum K.prefixChoice
```

<a id="thm-perturbed-family-maximality-comparator"></a>

**Comparator:** not yet compared.

<a id="record-257bm-c1"></a>

## Theorem 6.67 (Compactness from exact finite sums), page 60

> *Suppose the cofinal exact-row condition in Definition 6.66 holds. Then $`1/2\in\mathcal A`$. For each $`N`$, choose an exact row $`D_N`$ at depth $`n_N\ge\max\{N,1\}`$. Proposition 6.98 gives
> ``` math
> \left|X_{D_N}(2)-\frac12\right|
>        \le\frac{n_N+1}{2^{n_N}}\longrightarrow0.
> ```
> Every $`X_{D_N}(2)`$ belongs to the closed set $`\mathcal A`$, so its limit does too. No finite support represents $`1/2`$; the representing support is therefore infinite. The proof does not require the chosen rows to be nested. The unproved input is their existence at unbounded depths.*

The Lean declarations below together state this result.

1. [`Erdos249257.abs_exactLocalMersenneRowValue_sub_half_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCofinalExactRows.lean#L58)

```lean
theorem abs_exactLocalMersenneRowValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    |exactLocalMersenneRowValue D - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_of_cofinalExactLocalRows`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCofinalExactRows.lean#L71)

```lean
theorem half_mem_mersenneAchievementSet_of_cofinalExactLocalRows
    (hcofinal : CofinalExactLocalMersenneHalfRows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

3. [`Erdos249257.HalfCarryReachability.finite_boolSupport_ne_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCarryReachability.lean#L589)

```lean
theorem finite_boolSupport_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2
```

<a id="record-257bm-c1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `abs_exactLocalMersenneRowValue_sub_half_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L117) (E257_22, line 117), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAR.lean#L63) (PaperStatementsAR.lean, line 63), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)
- `half_mem_mersenneAchievementSet_of_cofinalExactLocalRows`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L130) (E257_22, line 130), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAR.lean#L128) (PaperStatementsAR.lean, line 128), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)
- `finite_boolSupport_ne_half`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L99) (E257_22, line 99), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAL.lean#L48) (PaperStatementsAL.lean, line 48), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c2"></a>

## Theorem 6.68 (Infinitely many greedy skips suffice), page 60

> *Suppose that the greedy remainder for $`1/2`$ satisfies
> ``` math
> \forall N\ \exists c\ge\max\{N,4\}:\qquad
>  0<r_{c-1}(1/2)<w_c.
> ```
> Then exact quotient rows exist at unbounded depths, and $`1/2\in\mathcal A`$. A single such skip at $`c`$ gives an exact row at depth $`2c-2`$ without an additional capacity hypothesis. Taking arbitrarily large $`c`$ therefore supplies the rows needed for the compactness implication in Theorem 6.67. The existence of arbitrarily late positive skips is the hypothesis, not an established property of the greedy sequence. It is equivalent to half-membership and remains unproved here.*

The Lean declarations below together state this result.

1. [`Erdos249257.exactLocalMersenneHalfRow_of_positiveHalfGreedySkip`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L55)

```lean
theorem exactLocalMersenneHalfRow_of_positiveHalfGreedySkip
    {c : ℕ} (hc : 4 ≤ c)
    (hpos : 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1))
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c) :
    ExactLocalMersenneHalfRow (2 * c - 2)
```

2. [`Erdos249257.cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L84)

```lean
theorem cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    CofinalExactLocalMersenneHalfRows
```

where [`CofinalExactLocalMersenneHalfRows`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCofinalExactRows.lean#L38) is

```lean
def CofinalExactLocalMersenneHalfRows : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ExactLocalMersenneHalfRow n
```

3. [`Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L97)

```lean
theorem half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

4. [`Erdos249257.cofinalPositiveHalfGreedySkips_iff_half_mem`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L110)

```lean
theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="record-257bm-c2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exactLocalMersenneHalfRow_of_positiveHalfGreedySkip`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L191) (E257_22, line 191), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsF.lean#L134) (PaperStatementsF.lean, line 134), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)
- `cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L186) (E257_22, line 186), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsF.lean#L117) (PaperStatementsF.lean, line 117), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)
- `half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L154) (E257_22, line 154), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsD.lean#L174) (PaperStatementsD.lean, line 174), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)
- `cofinalPositiveHalfGreedySkips_iff_half_mem`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L149) (E257_22, line 149), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsD.lean#L149) (PaperStatementsD.lean, line 149), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c3"></a>

## Theorem 6.69 (A compatible family of finite supports), page 61

> *Let $`b_{n,d}\in\{0,1\}`$ satisfy $`b_{n+1,d}=b_{n,d}`$ whenever $`2d\le n`$. Define
> ``` math
> E_n=\{d:2\le d\le n,\ b_{n,d}=1\},\qquad
>  D_n=E_n\cap\{2,\ldots,\lfloor n/2\rfloor\}.
> ```
> The four conditions on the finite rows, required for every $`n\ge2`$, are
> ``` math
> \begin{aligned}
>  2^{\max\{c_{D_n}(n)-1,0\}}-1&\le S(D_n,1,n-1),\\
>  \sum_{\substack{d\in E_n\\d>\lfloor n/2\rfloor}}2^{n-d}
>      &=H(D_n,1,n),\\
>  H(D_n,1,n)&<2^{n-\lfloor n/2\rfloor},\\
>  Q(E_n,n)&=2^{n-1}-1.
>  \end{aligned}
> ```
> The first condition implies that the integer in the next two lines is nonnegative. The second specifies the binary value of the upper half of the row, the third bounds that value by its available number of bits, and the fourth is the exact quotient equation. The maximum in the first line records natural-number subtraction at the case $`c_{D_n}(n)=0`$.*
> 
> *These are the finite hypotheses of the compatible-limit construction. The bit condition fixes coordinate $`d`$ from row $`2d`$ onward. Unlike the independent finite supports in Definition 6.66, the rows therefore have a prescribed common limit. This extra structure is not, by itself, a proof of strictness between the corresponding existence statements.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_bit_stable`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/CompatibleFiniteRowFamily.lean#L95)

```lean
theorem paper_compatible_bit_stable
    (T : BooleanMobiusGlobalRepairTrajectory) {d n : ℕ} (hdn : 2 * d ≤ n) :
    T.bit n d = T.bit (2 * d) d
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_finite_row_conditions`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/CompatibleFiniteRowFamily.lean#L111)

```lean
theorem paper_compatible_finite_row_conditions
    (T : BooleanMobiusGlobalRepairTrajectory) :
    GlobalBooleanMobiusRepairFeasible T ↔
      ((∀ n : ℕ, 2 ≤ n →
          2 ^ (endpointDivisorContribution
                (globalRepairLowerSupport T.bit n) n - 1) - 1 ≤
            localBinarySuffix (globalRepairLowerSupport T.bit n) 1 (n - 1)) ∧
       (∀ n : ℕ, 2 ≤ n →
          ((∑ d ∈ (globalRepairStageSupport T.bit n).filter
                (fun d ↦ n / 2 < d), 2 ^ (n - d) : ℕ) : ℤ) =
            localRepairInteger (globalRepairLowerSupport T.bit n) 1 n) ∧
       (∀ n : ℕ, 2 ≤ n →
          localRepairInteger (globalRepairLowerSupport T.bit n) 1 n <
            ((2 ^ (n - n / 2) : ℕ) : ℤ)) ∧
       (∀ n : ℕ, 2 ≤ n →
          localPrefixQuotient (globalRepairStageSupport T.bit n) n =
            2 ^ (n - 1) - 1))
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_first_condition_gives_nonneg`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/CompatibleFiniteRowFamily.lean#L146)

```lean
theorem paper_compatible_first_condition_gives_nonneg
    (T : BooleanMobiusGlobalRepairTrajectory)
    (hbound : ∀ n : ℕ, 2 ≤ n →
      2 ^ (endpointDivisorContribution (globalRepairLowerSupport T.bit n) n - 1)
          - 1 ≤
        localBinarySuffix (globalRepairLowerSupport T.bit n) 1 (n - 1))
    {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ localRepairInteger (globalRepairLowerSupport T.bit n) 1 n
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_rows_agree_with_limit`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/CompatibleFiniteRowFamily.lean#L158)

```lean
theorem paper_compatible_rows_agree_with_limit
    (T : BooleanMobiusGlobalRepairTrajectory) {n d : ℕ} (hd : d ≤ n / 2) :
    d ∈ globalRepairStageSupport T.bit n ↔ d ∈ globalRepairLimitSupport T
```

<a id="record-257bm-c3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_compatible_bit_stable`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L261) (E257_22, line 261), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStructuresW.lean#L37) (PaperStructuresW.lean, line 37), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)
- `paper_compatible_finite_row_conditions`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_19/Challenge.lean#L300) (E257_19, line 300), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_19/PaperStructuresBH.lean#L184) (PaperStructuresBH.lean, line 184), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_19.json) (E257_19)
- `paper_compatible_first_condition_gives_nonneg`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L224) (E257_22, line 224), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStructuresAW.lean#L40) (PaperStructuresAW.lean, line 40), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)
- `paper_compatible_rows_agree_with_limit`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L249) (E257_22, line 249), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStructuresT.lean#L37) (PaperStructuresT.lean, line 37), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c4"></a>

## Theorem 6.70 (A sufficient quotient bound at a crossing), page 61

> *Consider the following condition on finite sets $`D`$ and integers $`c\ge4`$:
> ``` math
> \begin{gathered}
>  D\subseteq\{2,\ldots,c-1\},\qquad
>  X_D(2)<\frac12<X_D(2)+w_c\\[2pt]
>  \Longrightarrow\qquad Q(D\cup\{c\},2c-2)\ge2^{2c-3}.
>  \end{gathered}
> ```
> It requires the quotient inequality at every strict crossing of one half by an added weight. Theorem 6.93 identifies this inequality with the binary bound needed in the finite construction. If the condition holds for all such $`D,c`$, the induction below produces exact sums at unbounded depths and hence an infinite support of value $`1/2`$. The universal crossing condition itself is unproved.*

The Lean declarations below together state this result.

1. [`Erdos249257.cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1309)

```lean
theorem cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    CofinalExactLocalMersenneHalfRows
```

where [`CofinalExactLocalMersenneHalfRows`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCofinalExactRows.lean#L38) is

```lean
def CofinalExactLocalMersenneHalfRows : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ExactLocalMersenneHalfRow n
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_of_criticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1321)

```lean
theorem half_mem_mersenneAchievementSet_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

3. [`Erdos249257.HalfCarryReachability.finite_boolSupport_ne_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCarryReachability.lean#L589)

```lean
theorem finite_boolSupport_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2
```

<a id="record-257bm-c4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L125) (E257_22, line 125), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAR.lean#L77) (PaperStatementsAR.lean, line 77), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)
- `half_mem_mersenneAchievementSet_of_criticalQuotientSupply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L135) (E257_22, line 135), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAR.lean#L132) (PaperStatementsAR.lean, line 132), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)
- `finite_boolSupport_ne_half`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L99) (E257_22, line 99), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAL.lean#L48) (PaperStatementsAL.lean, line 48), [replay report](../../evidence/comparator/replay-35882032091/receipt-E257_22.json) (E257_22)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c5"></a>

## Theorem 6.71 (Induction from the depth-six example), page 61

> *An already-formalised induction from the endpoint-six seed (Definition 6.97) consumes Theorem 6.70 at every step: each protected exact row either doubles below half (unconditional) or recycles at its first crossing rank $`e >`$ cutoff, giving endpoint $`2e-2 >`$ previous endpoint; protection (endpoint $`< 2\cdot`$cutoff, new ranks $`>`$ cutoff) is exactly what converts the non-growing recycle endpoint of the bare dichotomy (Theorem 6.127) into strict progress. The below-half branch never fires twice from the seed arithmetic, so the supply is needed at essentially every step. Its conclusion is the cofinal exact-row condition of Definition 6.66.*

The Lean declarations below together state this result.

1. [`Erdos249257.ProtectedExactLocalMersenneRow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1087)

```lean
structure ProtectedExactLocalMersenneRow where
  endpoint : ℕ
  cutoff : ℕ
  support : Finset ℕ
  core : Finset ℕ
  endpoint_six : 6 ≤ endpoint
  cutoff_four : 4 ≤ cutoff
  core_subset : core ⊆ support
  new_above_cutoff : ∀ d ∈ support, d ∉ core → cutoff < d
  core_bounds : ∀ d ∈ core, 2 ≤ d ∧ d ≤ cutoff
  support_bounds : ∀ d ∈ support, 2 ≤ d ∧ d ≤ endpoint
  exact_quotient :
    localPrefixQuotient support endpoint = 2 ^ (endpoint - 1) - 1
  core_below_half : localMersennePrefixValue core < (1 / 2 : ℚ)
  two_mem_core : 2 ∈ core
  endpoint_lt_twice_cutoff : endpoint < 2 * cutoff
```

2. [`Erdos249257.exists_laterProtectedExactLocalMersenneRow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1139)

```lean
theorem exists_laterProtectedExactLocalMersenneRow
    (hcap : SkippedCoreCriticalQuotientSupply)
    (s : ProtectedExactLocalMersenneRow) :
    ∃ t : ProtectedExactLocalMersenneRow, s.endpoint < t.endpoint
```

3. [`Erdos249257.cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1309)

```lean
theorem cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    CofinalExactLocalMersenneHalfRows
```

where [`CofinalExactLocalMersenneHalfRows`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCofinalExactRows.lean#L38) is

```lean
def CofinalExactLocalMersenneHalfRows : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ExactLocalMersenneHalfRow n
```

<a id="record-257bm-c5-comparator"></a>

**Comparator:** not yet compared.
