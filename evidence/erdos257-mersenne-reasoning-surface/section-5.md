# Formal evidence: Reciprocal Mersenne Subseries, Section 5

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="thm-full-support"></a>

## Theorem 5.4 (Full-support irrationality, unconditional, every base $`b \ge 2`$), page 35

> *For every integer $`b \ge 2`$,
> ``` math
> \sum_{k=0}^{\infty} \frac{1}{b^{k+1}-1} \quad \text{is irrational.}
> ```
> **Hypotheses:** $`b \in \mathbb{N}`$, $`b \ge 2`$. **Conclusion:** unconditional irrationality of the full-support Erdős–Borwein-type series at every base, not merely base $`2`$. The base-$`2`$ instance recovering the classical Erdős–Borwein constant’s irrationality is a one-line corollary.*

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSum_full_support`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L8328)

```lean
theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1))
```

<a id="thm-full-support-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSum_full_support`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L48) (E257_05, line 48), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L52) (PaperStatementsAG.lean, line 52), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-purely-periodic-support"></a>

## Theorem 5.5 (Purely periodic support), page 36

> *For integers $`b\ge2`$ and $`m\ge1`$, and every $`m`$-periodic $`A\subseteq\mathbb N`$ (i.e. $`n+m \in A \Leftrightarrow n \in A`$ for all $`n`$) containing a positive element, the support series $`\sum_{a\in A,\ a\ge1}(b^a-1)^{-1}`$ is irrational. **Hypotheses:** $`b \ge 2`$, $`m \ge 1`$, $`A`$ $`m`$-periodic, $`\exists a > 0,\ a \in A`$.*

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSupportSeries_periodic`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L11590)

```lean
theorem irrational_erdosSupportSeries_periodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, n + m ∈ A ↔ n ∈ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A)
```

<a id="thm-purely-periodic-support-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSupportSeries_periodic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L63) (E257_05, line 63), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L86) (PaperStatementsAG.lean, line 86), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-eventually-periodic-support"></a>

## Theorem 5.6 (Eventually periodic support), page 36

> *For integers $`b\ge2`$ and $`m\ge1`$, if $`A\subseteq\mathbb N`$ is infinite and its membership is $`m`$-periodic from some threshold $`N_0`$ on (i.e. $`n+m \in A \Leftrightarrow n \in A`$ for all $`n \ge N_0`$), then $`\sum_{a\in A,\ a\ge1}(b^a-1)^{-1}`$ is irrational, by transferring irrationality across the finite symmetric difference from the shifted purely periodic set $`A_{\mathrm{pure}} := \{n : n + m N_0 \in
> A\}`$. **Hypotheses:** $`b \ge 2`$, $`m \ge 1`$, $`N_0 \in \mathbb{N}`$, eventual $`m`$-periodicity from $`N_0`$, $`A`$ infinite.*

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSupportSeries_eventuallyPeriodic`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L11604)

```lean
theorem irrational_erdosSupportSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → (n + m ∈ A ↔ n ∈ A))
    (hinf : A.Infinite) :
    Irrational (erdosSupportSeries b A)
```

<a id="thm-eventually-periodic-support-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSupportSeries_eventuallyPeriodic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L52) (E257_05, line 52), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L64) (PaperStatementsAG.lean, line 64), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-residue-class-support"></a>

## Theorem 5.7 (Residue-class support), page 36

> *For integers $`b\ge2`$, $`m\ge1`$ and $`c`$, the series $`\sum_{n\ge1,\ n\equiv c\pmod m}(b^n-1)^{-1}`$ is irrational.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.irrational_residueClass_positive_support`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResidueClassSupport.lean#L21)

```lean
theorem irrational_residueClass_positive_support
    (b m : ℕ) (c : ℤ) (hb : 2 ≤ b) (hm : 1 ≤ m) :
    Irrational (erdosSupportSeries b
      {n : ℕ | 0 < n ∧ (n : ℤ) % (m : ℤ) = c % (m : ℤ)})
```

<a id="thm-residue-class-support-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_residueClass_positive_support`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L76) (E257_05, line 76), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsBC.lean#L53) (PaperStatementsBC.lean, line 53), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-odd-support"></a>

## Theorem 5.8 (Odd support), page 36

> *For every integer $`b\ge2`$, the series $`\sum_{n\ge1,\ n\text{ odd}}(b^n-1)^{-1}`$ is irrational. This density-$`1/2`$ support is the case treated explicitly by Luca and Tachiya \[lucatachiya2017, Example 2, p. 140\].*

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSupportSeries_odd`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L11686)

```lean
theorem irrational_erdosSupportSeries_odd (b : ℕ) (hb : 2 ≤ b) :
    Irrational (erdosSupportSeries b {n : ℕ | Odd n})
```

<a id="thm-odd-support-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSupportSeries_odd`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L59) (E257_05, line 59), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L74) (PaperStatementsAG.lean, line 74), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-topology"></a>

## Theorem 5.9 (Achievement-set topology and measure), page 36

> *$`\mathcal{A}`$ (Definition 5.2) is compact, closed, perfect, totally disconnected, and nowhere dense; its Lebesgue measure is exactly $`1`$: $`\operatorname{volume}(\mathcal{A}) = 1`$. **Hypotheses:** none. **Conclusion:** $`\mathcal A`$ is a Cantor set of positive measure, often called a fat Cantor set. Its measure is $`1`$, not the length of its ambient interval $`[0,E]`$, where $`E\approx1.6067`$. Strict separation and summability give the compactness, unique coding, and Cantor topology, and Hornich’s strict-tail theorem, as proved by Nitecki \[nitecki2013, Theorem 4(1), p. 9\], gives the measure as $`\lim_N2^NR_N`$ with $`R_N=\sum_{n>N}x_n`$: each level-$`N`$ cylinder has length $`R_N`$, and the $`2^N`$ disjoint cylinders have total length $`2^NR_N`$. The Mersenne-specific input is $`2^NR_N\to1`$. Other weight sequences require their own tail asymptotic.\
> *Use:* Theorem 5.10 below (compactness is exactly what powers every “limit of achieved points is achieved” argument used downstream, including the seam-limit route of Part 2).*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR20.paper_achievement_geometry`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR20/AchievementGeometry.lean#L40)

```lean
theorem paper_achievement_geometry :
    IsCompact mersenneAchievementSet ∧ IsClosed mersenneAchievementSet ∧
    Perfect mersenneAchievementSet ∧ IsTotallyDisconnected mersenneAchievementSet ∧
    IsNowhereDense mersenneAchievementSet ∧ volume mersenneAchievementSet = 1 ∧
    convexHull ℝ mersenneAchievementSet = Icc 0 erdosBorweinMersenneConstant ∧
    Function.Injective positiveMersenneDigitValue ∧
    ∀ x ∈ mersenneAchievementSet, ∃! A : Set ℕ,
      0 ∉ A ∧ positiveMersenneSupportValue A = x
```

2. [`ErdosProblems.Erdos257.PaperCompleteR20.mersenne_topology_quantitative`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR20/MersenneConstantDecimal.lean#L21)

```lean
theorem mersenne_topology_quantitative :
    |erdosBorweinMersenneConstant-(16067 : ℝ)/10000| < 1/20000 ∧
    1 < erdosBorweinMersenneConstant ∧
    Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ)^n*mersenneTail n) Filter.atTop (nhds 1)
```

<a id="thm-topology-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_achievement_geometry`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_02/Challenge.lean#L78) (E257_02, line 78), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L109) (PaperStatementsAM.lean, line 109), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_02.json) (E257_02)
- `mersenne_topology_quantitative`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L96) (E257_05, line 96), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAM.lean#L126) (PaperStatementsAM.lean, line 126), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-greedy-survival-record"></a>

## Theorem 5.10 (Membership equals greedy survival at every level), page 37

> *For a real $`x`$, let $`r_n(x)`$ be its greedy remainder after rank $`n`$, and let $`R_n=\sum_{j>n}w_j`$, as in the initial notation. Then
> ``` math
> x\in\mathcal A\quad\Longleftrightarrow\quad
>  x\ge0\ \text{and}\ r_n(x)\le R_n\text{ for every }n\ge0.
> ```
> The inequality says that the unselected tail has enough total mass at every rank. A failure at any one rank excludes membership; the inequalities at all ranks give a representation.*

The Lean declarations below together state this result.

1. [`Erdos249257.mem_mersenneAchievementSet_iff_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L1458)

```lean
theorem mem_mersenneAchievementSet_iff_greedy_survival (x : ℝ) :
    x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n
```

2. [`Erdos249257.greedy_survives_of_mem_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L1375)

```lean
theorem greedy_survives_of_mem_mersenneAchievementSet {x : ℝ}
    (hx : x ∈ mersenneAchievementSet) :
    0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n
```

3. [`Erdos249257.mem_mersenneAchievementSet_of_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GreedyAchievementSet.lean#L1394)

```lean
theorem mem_mersenneAchievementSet_of_greedy_survival {x : ℝ} (hx : 0 ≤ x)
    (hsurvive : ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) :
    x ∈ mersenneAchievementSet
```

<a id="thm-greedy-survival-record-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `mem_mersenneAchievementSet_iff_greedy_survival`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L134) (E257_05, line 134), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsB.lean#L106) (PaperStatementsB.lean, line 106), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)
- `greedy_survives_of_mem_mersenneAchievementSet`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L129) (E257_05, line 129), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsB.lean#L60) (PaperStatementsB.lean, line 60), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)
- `mem_mersenneAchievementSet_of_greedy_survival`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L139) (E257_05, line 139), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsB.lean#L119) (PaperStatementsB.lean, line 119), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-master-identity"></a>

## Theorem 5.14 (Decomposition of the integer remainder), page 38

> *For every quotient row $`n \ge 6`$,
> ``` math
> \begin{equation*}
> \Delta_n \;=\; K(2n) \;+\; \sum_{d \in \mathrm{Skip}_n} \left\lfloor \frac{4^n}{2^d-1} \right\rfloor.
> \tag{I}
> \end{equation*}
> ```
> Here the take and skip sets, capacity and remainder are those defined at the start of this subsection. The identity separates the contribution of the full exponent range from that of the omitted ranks. It makes no claim that there are few omitted ranks; controlling their sum is a separate part of any application.\
> **Proof.** For $`d=n`$ the quotient is $`2^n+1`$, and for $`n<d\le2n`$ it is $`2^{2n-d}`$. Hence
> ``` math
> \sum_{d=n}^{2n}\left\lfloor\frac{4^n}{2^d-1}\right\rfloor
>  =2^n+1+\sum_{j=0}^{n-1}2^j=2^{n+1}.
> ```
> Substitute this in the definition of $`K(2n)`$, split $`\{2,\ldots,n-1\}=D_n\sqcup\mathrm{Skip}_n`$, and use $`\Delta_n=2^{2n-1}-2^{n+1}-\sum_{d\in D_n}w(n,d)`$. This gives (I). **Certification:** rows $`6\le n\le200`$ rechecked with zero mismatches by an exact [program](https://github.com/wcook04/plectis-erdos/blob/f757115e03bebe5c04431a147da559015c680a37/research/experiments/erdos257/check_master_identity.py) (§5.7).\
> *Use:* (I) permits substitution of information about $`K(2n)`$. A resulting estimate for $`\Delta_n`$ must also retain or bound the skip-set sum; information about $`K`$ alone need not control their cancellation.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.paper_master_identity_floors`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR20/QuotientRowIdentity.lean#L89)

```lean
theorem paper_master_identity_floors {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    ((2 : ℤ)^(2*n-1) - (2 : ℤ)^n -
      ∑ d ∈ D, ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋) - (2 : ℤ)^n =
    ((2 : ℤ)^(2*n-1) -
      ∑ d ∈ Finset.Ico 2 (2*n+1), ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋) +
      ∑ d ∈ (Finset.Ico 2 n) \ D, ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋
```

<a id="thm-master-identity-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_master_identity_floors`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L147) (E257_05, line 147), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAA.lean#L97) (PaperStatementsAA.lean, line 97), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-real-form"></a>

## Theorem 5.15 (Real (non-integer) form of the quotient identity), page 39

> *Let $`x_d := 1/(2^d-1)`$ and define the constant
> ``` math
> C \;:=\; \sum_{d \ge 2} x_d \;-\; \tfrac12 \;=\; E - \tfrac32 \;=\; 0.1066951524152917\ldots,
> ```
> where $`E`$ is the Erdős–Borwein constant. Then, for every quotient row $`n \ge 6`$,
> ``` math
> \begin{equation*}
> \Delta_n \;=\; 4^n \Big( \sum_{d \in \mathrm{Skip}_n} x_d \;-\; C \Big) \;+\; \eta_n, \qquad
> |\eta_n| < 2n+2.
> \tag{II}
> \end{equation*}
> ```
> **Proof.** Splitting the full series at $`n`$ gives
> ``` math
> \eta_n=4^nR_{n-1}-2^{n+1}
>        +\sum_{d\in D_n}\left\{\frac{4^n}{2^d-1}\right\}.
> ```
> The tail bounds $`2^{-(n-1)}<R_{n-1}\le
> 2^{-(n-1)}+\tfrac23 4^{-(n-1)}`$ and $`|D_n|\le n-2`$ show $`0<\eta_n<n+2/3<2n+2`$.*
> 
> ***Use of the error bound.** For $`H>2n+2`$, the condition $`|\sum_{d\in\mathrm{Skip}_n}x_d-C|>(H+2n+2)/4^n`$ is sufficient for $`|\Delta_n|>H`$. Conversely, $`|\Delta_n|>H`$ implies $`|\sum_{d\in\mathrm{Skip}_n}x_d-C|>(H-2n-2)/4^n`$. Thus a square-root-exponential deviation corresponds to a separation of order $`2^{-3n/2}`$, with the displayed additive error retained. This is not an exact equivalence after simply discarding that error.\
> **Note:** $`C = E - 3/2`$ is Mersenne-specific, but the shape “scaled deviation $`=`$ $`4^n \cdot`$(finite skip-sum $`-`$ target constant) $`+ O(n)`$” is a template, not yet matched to any analogous constant on the \#249 side.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_core`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR20/QuotientRowReal.lean#L84)

```lean
theorem paper_real_quotient_core {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    ∃ eta : ℝ,
      (rowDeviation n D : ℝ) = (4 : ℝ)^n *
        ((∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) -
          (erdosBorweinMersenneConstant-3/2)) + eta ∧
      0 < eta ∧ eta < (n : ℝ)+2/3 ∧ |eta| < 2*(n : ℝ)+2
```

2. [`ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_margins`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR20/QuotientRowReal.lean#L103)

```lean
theorem paper_real_quotient_margins {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) (H : ℝ) :
    ((H+(2*(n : ℝ)+2))/(4 : ℝ)^n <
      |(∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) - (erdosBorweinMersenneConstant-3/2)| →
      H < |(rowDeviation n D : ℝ)|) ∧
    (H < |(rowDeviation n D : ℝ)| →
      (H-(2*(n : ℝ)+2))/(4 : ℝ)^n <
      |(∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) - (erdosBorweinMersenneConstant-3/2)|)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR20.row_constant_eq_tail`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR20/QuotientRowReal.lean#L94)

```lean
theorem row_constant_eq_tail :
    erdosBorweinMersenneConstant-3/2 = mersenneTail 1-1/2
```

4. [`ErdosProblems.Erdos257.PaperCompleteR20.mersenne_constant_decimal`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR20/MersenneConstantDecimal.lean#L8)

```lean
theorem mersenne_constant_decimal :
    (1066951524152917 : ℝ)/10^16 < erdosBorweinMersenneConstant-3/2 ∧
      erdosBorweinMersenneConstant-3/2 < (1066951524152918 : ℝ)/10^16
```

<a id="thm-real-form-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_real_quotient_core`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L172) (E257_05, line 172), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAR.lean#L211) (PaperStatementsAR.lean, line 211), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)
- `paper_real_quotient_margins`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L181) (E257_05, line 181), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAR.lean#L219) (PaperStatementsAR.lean, line 219), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)
- `row_constant_eq_tail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L102) (E257_05, line 102), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAM.lean#L140) (PaperStatementsAM.lean, line 140), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)
- `mersenne_constant_decimal`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_05/Challenge.lean#L91) (E257_05, line 91), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_05/PaperStatementsAM.lean#L122) (PaperStatementsAM.lean, line 122), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_05.json) (E257_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-dynamics"></a>

## Theorem 5.16 (Exact recurrences for the three branches), page 39

> *Fix $`n\ge5`$. Among the quotient sums over subsets of $`\{2,\ldots,n-1\}`$, let $`D_n`$ give the largest sum at most $`T_n`$ and let $`B_n`$ give the smallest sum strictly greater than $`T_n`$. Thus $`D_n`$ is the greedy support already defined. Put
> ``` math
> r=\mathrm{rem}(n),\qquad o=Q(B_n,2n)-T_n,
> ```
> and define the two correction terms by
> ``` math
> p^- =\sum_{d\in D_n}\bigl(2\mathbf1_{d\mid2n+1}
>                               +\mathbf1_{d\mid2n+2}\bigr),\qquad
>  p^+ =\sum_{d\in B_n}\bigl(2\mathbf1_{d\mid2n+1}
>                               +\mathbf1_{d\mid2n+2}\bigr).
> ```
> Both lie in $`[0,2(n-2)]`$, since $`d\ge2`$ cannot divide both consecutive integers. The next remainder is
> ``` math
> \mathrm{rem}(n+1)=
>  \begin{cases}
>  2^{n+1}-4o-p^+,&\text{if }4o+p^+\le2^{n+1}\quad(\mathrm U),\\
>  4r+2^{n+1}-p^-,&\text{if not }\mathrm U\text{ and }
>                    4r+2^{n+1}-p^-<2^{n+2}+4\quad(\mathrm M),\\
>  4r-2^{n+1}-p^--4,&\text{otherwise}\quad(\mathrm R).
>  \end{cases}
> ```
> Consequently, for $`\lambda_n=(\mathrm{rem}(n)-2^n)/2^n`$,
> ``` math
> \begin{equation*}
>  \lambda_{n+1}=
>  \begin{cases}
>  -(4o+p^+)/2^{n+1},&\mathrm U,\\
>  2\lambda_n+2-p^-/2^{n+1},&\mathrm M,\\
>  2\lambda_n-(p^-+4)/2^{n+1},&\mathrm R.
>  \end{cases}
>  \tag{III}
> \end{equation*}
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_dynamics`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L424)

```lean
theorem paper_dynamics {n : ℕ} (hn : 5 ≤ n) {D B D' : Finset ℕ}
    (hD : IsRowLower n D) (hB : IsRowUpper n B) (hD' : IsRowLower (n + 1) D')
    {r o pm pp rem : ℕ}
    (hr : localPrefixQuotient D (2 * n) + r = seamSubsetTarget n)
    (ho : seamSubsetTarget n + o = localPrefixQuotient B (2 * n))
    (hpm : pm = ∑ d ∈ D, rowPulse n d)
    (hpp : pp = ∑ d ∈ B, rowPulse n d)
    (hrem : localPrefixQuotient D' (2 * (n + 1)) + rem = seamSubsetTarget (n + 1)) :
    D = greedySupport n ∧
      pm ≤ 2 * (n - 2) ∧ pp ≤ 2 * (n - 2) ∧
      ((rem : ℤ) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          (2 : ℤ) ^ (n + 1) - 4 * (o : ℤ) - (pp : ℤ)
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ)
        else 4 * (r : ℤ) - 2 ^ (n + 1) - (pm : ℤ) - 4) ∧
      (((rem : ℚ) - 2 ^ (n + 1)) / 2 ^ (n + 1) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          -((4 * (o : ℚ) + (pp : ℚ)) / 2 ^ (n + 1))
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) + 2 - (pm : ℚ) / 2 ^ (n + 1)
        else 2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) - ((pm : ℚ) + 4) / 2 ^ (n + 1))
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowLower_existsUnique`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L398)

```lean
theorem paper_rowLower_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! D : Finset ℕ, IsRowLower n D
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowUpper_existsUnique`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L404)

```lean
theorem paper_rowUpper_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! B : Finset ℕ, IsRowUpper n B
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_isRowLower`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L279)

```lean
theorem paper_greedySupport_isRowLower {n : ℕ} (hn : 5 ≤ n) :
    IsRowLower n (greedySupport n)
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_upperSupport_isRowUpper`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L364)

```lean
theorem paper_upperSupport_isRowUpper {n : ℕ} (hn : 5 ≤ n) :
    IsRowUpper n (rowSupport n (seamAboveWord n hn))
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowLower_unique`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L379)

```lean
theorem paper_isRowLower_unique {n : ℕ} (hn : 5 ≤ n) {D D₀ : Finset ℕ}
    (hD : IsRowLower n D) (hD₀ : IsRowLower n D₀) : D = D₀
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowUpper_unique`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L388)

```lean
theorem paper_isRowUpper_unique {n : ℕ} (hn : 5 ≤ n) {B B₀ : Finset ℕ}
    (hB : IsRowUpper n B) (hB₀ : IsRowUpper n B₀) : B = B₀
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_greedy_rule`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L301)

```lean
theorem paper_greedySupport_greedy_rule {n : ℕ} (hn : 5 ≤ n) {d : ℕ}
    (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔
      truncatedMersenneWeight n d +
          ∑ e ∈ (greedySupport n).filter (fun e => e < d),
            truncatedMersenneWeight n e ≤ seamSubsetTarget n
```

9. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_mem`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L254)

```lean
theorem paper_greedySupport_mem {n d : ℕ} (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔ seamGreedyWord n ⟨d - 2, by omega⟩ = true
```

10. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_greedy_step`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L244)

```lean
theorem paper_greedy_step {n d : ℕ} (hd : d < n) (C : ℕ) :
    integerGreedyBits (seamWeightsFrom n d) C =
      (decide (truncatedMersenneWeight n d ≤ C)) ::
        integerGreedyBits (seamWeightsFrom n (d + 1))
          (if truncatedMersenneWeight n d ≤ C then
            C - truncatedMersenneWeight n d else C)
```

11. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_consecutive_not_both_divisible`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L69)

```lean
theorem paper_consecutive_not_both_divisible {d m : ℕ} (hd : 2 ≤ d) :
    ¬ (d ∣ m + 1 ∧ d ∣ m + 2)
```

12. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowPulse_eq_indicators`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L50)

```lean
theorem paper_rowPulse_eq_indicators (n d : ℕ) :
    rowPulse n d =
      2 * (if d ∣ 2 * n + 1 then 1 else 0) +
        (if d ∣ 2 * n + 2 then 1 else 0)
```

13. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowQuotient_eq_weightSum`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L58)

```lean
theorem paper_rowQuotient_eq_weightSum (n : ℕ) (S : Finset ℕ) :
    localPrefixQuotient S (2 * n) = ∑ d ∈ S, truncatedMersenneWeight n d
```

14. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowWeight_eq_floor`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L41)

```lean
theorem paper_rowWeight_eq_floor (n d : ℕ) :
    truncatedMersenneWeight n d = 4 ^ n / (2 ^ d - 1)
```

15. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowTarget_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L45)

```lean
theorem paper_rowTarget_eq (n : ℕ) :
    seamSubsetTarget n = 2 ^ (2 * n - 1) - 2 ^ n
```

<a id="thm-dynamics-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_dynamics`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L178) (E257_06, line 178), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStructuresAZ.lean#L299) (PaperStructuresAZ.lean, line 299), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_rowLower_existsUnique`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L72) (E257_06, line 72), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStatementsAD.lean#L170) (PaperStatementsAD.lean, line 170), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_rowUpper_existsUnique`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L90) (E257_06, line 90), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStatementsAD.lean#L184) (PaperStatementsAD.lean, line 184), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_greedySupport_isRowLower`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L210) (E257_06, line 210), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStructuresAZ.lean#L333) (PaperStructuresAZ.lean, line 333), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_upperSupport_isRowUpper`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_07/Challenge.lean#L133) (E257_07, line 133), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_07/PaperStructuresBX.lean#L101) (PaperStructuresBX.lean, line 101), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_07.json) (E257_07)
- `paper_isRowLower_unique`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L64) (E257_06, line 64), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStatementsAD.lean#L144) (PaperStatementsAD.lean, line 144), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_isRowUpper_unique`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L68) (E257_06, line 68), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStatementsAD.lean#L148) (PaperStatementsAD.lean, line 148), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_greedySupport_greedy_rule`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L202) (E257_06, line 202), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStructuresAZ.lean#L324) (PaperStructuresAZ.lean, line 324), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_greedySupport_mem`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L214) (E257_06, line 214), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStructuresAZ.lean#L338) (PaperStructuresAZ.lean, line 338), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_greedy_step`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L218) (E257_06, line 218), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStructuresAZ.lean#L343) (PaperStructuresAZ.lean, line 343), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_consecutive_not_both_divisible`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L60) (E257_06, line 60), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStatementsAD.lean#L131) (PaperStatementsAD.lean, line 131), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_rowPulse_eq_indicators`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L76) (E257_06, line 76), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStatementsAD.lean#L173) (PaperStatementsAD.lean, line 173), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_rowQuotient_eq_weightSum`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L82) (E257_06, line 82), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStatementsAD.lean#L178) (PaperStatementsAD.lean, line 178), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_rowWeight_eq_floor`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L94) (E257_06, line 94), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStatementsAD.lean#L187) (PaperStatementsAD.lean, line 187), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)
- `paper_rowTarget_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_06/Challenge.lean#L86) (E257_06, line 86), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_06/PaperStatementsAD.lean#L181) (PaperStatementsAD.lean, line 181), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_06.json) (E257_06)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
