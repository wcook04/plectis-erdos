# Formal evidence: Weighted Support Criteria for Reciprocal Mersenne Subseries

This record belongs to the paper [erdos-257-mersenne-support-subseries.pdf](../paper/257/erdos-257-mersenne-support-subseries.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`e6c2d8f77ac2`](https://github.com/wcook04/plectis-erdos/tree/e6c2d8f77ac24753c5216a49f4daf7f7388b309f) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35882032091](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35882032091) at corpus commit [`a2faa350b45a`](https://github.com/wcook04/plectis-erdos-lean/tree/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3) (tag `paper-evidence-2026-09-23`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 9 results: 9 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 8 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="res-weighted-support"></a>

## Theorem (a weighted condition on the support)

> *Let $`b\ge2`$ be an integer, let $`A\subseteq\mathbb{N}_{>0}`$ be infinite, and let $`P`$ be a finite nonempty set of primes. Set $`h(a)=\prod_{p\in P}p^{v_p(a)}`$. If
> ``` math
> \begin{equation}
> \label{eq:weighted-fixed-base}
>  W_{b,P}(A):=\sum_{a\in A}
>  \frac{h(a)}{a(b^{h(a)}-1)}<\infty,
> \end{equation}
> ```
> then $`X_A(b)`$ is irrational. In particular, the base-two condition
> ``` math
> \begin{equation*}
> \label{eq:weighted-return}
>  \sum_{a\in A}\frac{h(a)}{a(2^{h(a)}-1)}<\infty
>  \tag{W}
> \end{equation*}
> ```
> implies that $`X_A(b)`$ is irrational for every integer $`b\ge2`$. Both conclusions are hereditary under passage to infinite subsets.*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L120)

```lean
theorem divisibilityWeightedClaim : DivisibilityWeightedClaim
```

2. [`ErdosProblems.Erdos257.PaperCompleteR8.finitePrimeWeighted_fixedBase_hereditary`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedHereditaryClaim.lean#L31)

```lean
theorem finitePrimeWeighted_fixedBase_hereditary
    (b : ℕ) (H : Set ℕ) (hb : 2 ≤ b) (hH0 : 0 ∉ H)
    (hH : FinitePrimeWeighted b H) :
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      Irrational (erdosSupportSeries b A)
```

<a id="res-weighted-support-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `divisibilityWeightedClaim` | [E257_01/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_01/Challenge.lean#L76) | [DivisibilityWeightedSupport.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_01/DivisibilityWeightedSupport.lean#L42) | [E257_01](../evidence/comparator/replay-35882032091/receipt-E257_01.json) |
| `finitePrimeWeighted_fixedBase_hereditary` | [E257_39/Challenge.lean, line 133](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_39/Challenge.lean#L133) | [PaperStatementsBC.lean, line 38](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_39/PaperStatementsBC.lean#L38) | [E257_39](../evidence/comparator/replay-35882032091/receipt-E257_39.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-reciprocal-support"></a>

## Theorem (reciprocal-summable supports)

> *Let $`A\subseteq\mathbb{N}_{>0}`$ be infinite. If
> ``` math
> \sum_{a\in A}\frac1a<\infty,
> ```
> then $`X_A(b)`$ is irrational for every integer $`b\ge2`$.*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L395)

```lean
theorem irrational_erdosSupportSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (reciprocalSupportTerm A)) :
    Irrational (erdosSupportSeries b A)
```

<a id="res-reciprocal-support-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSupportSeries_of_summable_reciprocal` | [E257_39/Challenge.lean, line 151](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_39/Challenge.lean#L151) | [PaperStatementsAV.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_39/PaperStatementsAV.lean#L52) | [E257_39](../evidence/comparator/replay-35882032091/receipt-E257_39.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-variable-fractional-cover"></a>

## Theorem (a summable divisor-cover criterion)

> *For each $`j\ge1`$, let $`F_j\subseteq\mathbb{N}_{>0}`$ be finite, let $`0<\alpha_j\le1`$, and let $`c_{j,d}\ge0`$ satisfy
> ``` math
> f_{F_j}(n)^{\alpha_j}\le\sum_{d\mid n}c_{j,d}\quad(n\ge1).
> ```
> Set $`C_j=\sum_{d\ge1}c_{j,d}/d`$. If
> ``` math
> \begin{equation*}
>  \sum_{j\ge1}\frac{C_j2^{j\alpha_j}}{2^{\alpha_j}-1}<\infty,
>  \tag{V}\label{eq:strengthened-cover}
> \end{equation*}
> ```
> then $`X_A(b)`$ is irrational for every infinite $`A\subseteq\bigcup_jF_j`$ and every integer $`b\ge2`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR8.strengthenedPositiveCoverClaim`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR8/PositiveCoverReturn.lean#L241)

```lean
theorem strengthenedPositiveCoverClaim : StrengthenedPositiveCoverClaim
```

<a id="thm-variable-fractional-cover-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `strengthenedPositiveCoverClaim` | [E257_01/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_01/Challenge.lean#L113) | [VariableExponentCover.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_01/VariableExponentCover.lean#L86) | [E257_01](../evidence/comparator/replay-35882032091/receipt-E257_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-mixed-supports"></a>

## Theorem (mixed weighted and cover supports)

> *Let $`E,V\subseteq\mathbb{N}_{>0}`$. Suppose $`E`$ satisfies <a href="#eq:weighted-return" data-reference-type="eqref" data-reference="eq:weighted-return">[eq:weighted-return]</a> for a finite nonempty prime set $`P`$, and $`V\subseteq\bigcup_jF_j`$ for finite sets and nonnegative majorants satisfying the hypotheses of Theorem <a href="#thm:variable-fractional-cover" data-reference-type="ref" data-reference="thm:variable-fractional-cover">4</a>, with either <a href="#eq:strengthened-cover" data-reference-type="eqref" data-reference="eq:strengthened-cover">[eq:strengthened-cover]</a> or its positive-weight variant. Then $`X_A(b)`$ is irrational for every infinite $`A\subseteq E\cup V`$ and every integer $`b\ge2`$.*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos257.PaperCompleteR8.mixedSupportClaim`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L126)

```lean
theorem mixedSupportClaim : MixedSupportClaim
```

2. [`ErdosProblems.Erdos257.PaperCompleteR8.arbitraryWeightMixedSupport_allBase_hereditary`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR8/ArbitraryWeightMixedClaim.lean#L101)

```lean
theorem arbitraryWeightMixedSupport_allBase_hereditary
    (E V : Set ℕ) (hE0 : 0 ∉ E) (hE : FinitePrimeWeighted 2 E)
    (D : LogBudgetCover V) :
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
      Irrational (erdosSupportSeries b A)
```

<a id="res-mixed-supports-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mixedSupportClaim` | [E257_01/Challenge.lean, line 130](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_01/Challenge.lean#L130) | [MixedWeightedCover.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_01/MixedWeightedCover.lean#L109) | [E257_01](../evidence/comparator/replay-35882032091/receipt-E257_01.json) |
| `arbitraryWeightMixedSupport_allBase_hereditary` | [E257_01/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_01/Challenge.lean#L159) | [PaperStructuresBO.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_01/PaperStructuresBO.lean#L65) | [E257_01](../evidence/comparator/replay-35882032091/receipt-E257_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-period"></a>

## Theorem (the exact denominator period)

> *Let $`F\subseteq\mathbb{N}_{>0}`$ be finite and nonempty, let $`b\ge2`$ be an integer, and let $`D_F>0`$ be the denominator of $`X_F(b)`$ in lowest terms. Then $`D_F`$ is coprime to $`b`$, and
> ``` math
> \operatorname{ord}_{D_F}(b)=\operatorname{lcm}\{n:n\in F\}.
> ```
> If moreover $`\operatorname{lcm}(F)\ge2`$, then $`\operatorname{lcm}(F)<D_F`$. We use $`\operatorname{ord}_1(b)=1`$, so the statement includes $`F=\{1\}`$ at $`b=2`$.*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.coprime_base_den_finiteErdosSum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L5221)

```lean
theorem coprime_base_den_finiteErdosSum
    (F : Finset Nat) (b : Nat) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    Nat.Coprime b (finiteErdosSum F b).den
```

2. [`Erdos249257.finite_period_noncollapse_rat_den`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L5246)

```lean
theorem finite_period_noncollapse_rat_den
    (F : Finset Nat) (b : Nat)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    orderOf (ZMod.unitOfCoprime b (coprime_base_den_finiteErdosSum F b h0 hb))
      = F.lcm id
```

3. [`Erdos249257.lcm_lt_den_finiteErdosSum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L5260)

```lean
theorem lcm_lt_den_finiteErdosSum
    (F : Finset Nat) (b : Nat)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (finiteErdosSum F b).den
```

<a id="res-period-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `coprime_base_den_finiteErdosSum` | [E257_39/Challenge.lean, line 165](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_39/Challenge.lean#L165) | [PaperStatementsAG.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_39/PaperStatementsAG.lean#L30) | [E257_39](../evidence/comparator/replay-35882032091/receipt-E257_39.json) |
| `finite_period_noncollapse_rat_den` | [E257_41/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_41/Challenge.lean#L97) | [FinitePeriodNoncollapse.lean, line 12](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_41/FinitePeriodNoncollapse.lean#L12) | [E257_41](../evidence/comparator/replay-35882032091/receipt-E257_41.json) |
| `lcm_lt_den_finiteErdosSum` | [E257_39/Challenge.lean, line 170](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_39/Challenge.lean#L170) | [PaperStatementsAG.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_39/PaperStatementsAG.lean#L119) | [E257_39](../evidence/comparator/replay-35882032091/receipt-E257_39.json) |

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `finite_period_noncollapse_rat_den`:

```lean
theorem finite_period_noncollapse_rat_den
    (F : Finset ℕ) (b : ℕ)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    ∃ hcop : Nat.Coprime b (finiteErdosSum F b).den,
      orderOf (ZMod.unitOfCoprime b hcop) = F.lcm id := by sorry
```

<a id="res-general-repair"></a>

## Theorem (membership and nonincreasing integer remainders)

> *For every real $`x\ge0`$, the following are equivalent:
> ``` math
> \begin{gathered}
>  x\in\mathcal A;\\
>  \forall K\ge0\ \exists N\ge K:\quad Q_{N+1}\le Q_N;\\
>  \forall K\ge0\ \exists N\in[K,K+2\lfloor\sqrt K\rfloor+12):
>  \quad Q_{N+1}\le Q_N.
>  \end{gathered}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.paper_general_repair_criteria`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/GeneralRepairCorrespondence.lean#L15)

```lean
theorem paper_general_repair_criteria {x : ℝ} (hx : 0 ≤ x) :
    (x ∈ mersenneAchievementSet ↔ ∀ K : ℕ, ∃ N, K ≤ N ∧
      paperIntegerDefect x (N+1) ≤ paperIntegerDefect x N) ∧
    (x ∈ mersenneAchievementSet ↔ ∀ K : ℕ, ∃ N, K ≤ N ∧
      N < K+2*Nat.sqrt K+12 ∧ paperIntegerDefect x (N+1) ≤ paperIntegerDefect x N)
```

<a id="res-general-repair-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_general_repair_criteria` | [E257_39/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_39/Challenge.lean#L207) | [PaperStatementsM.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_39/PaperStatementsM.lean#L26) | [E257_39](../evidence/comparator/replay-35882032091/receipt-E257_39.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-one-over-twenty-one-frontier"></a>

## Theorem (integer-quotient tests for $`1/21`$)

> *The following statements hold.*
> 
> 1.  *$`1/21\in\mathcal A`$ if and only if $`\mathcal F_{21}`$ does not hold.*
> 
> 2.  *If there is an unbounded sequence of ranks $`R`$ with $`s_R\le 2^R`$, then $`1/21\in\mathcal A`$.*
> 
> 3.  *On $`\mathcal F_{21}`$, eventually $`s_R>2^R`$, the boundary rank $`R+1`$ belongs to $`D_{R+1}`$, and, for all sufficiently large $`R`$,
>     ``` math
>     \begin{aligned}
>      D_{R+1}&=D_R\cup\{R+1\},\\
>      s_{R+1}&=4s_R+
>      \left\lfloor\frac{4(2^{2R}\bmod21)}{21}\right\rfloor
>      -2c_{D_R}(2R+1)-c_{D_R}(2R+2)\\
>      &\hspace{3em}{}-(2^{R+1}+1).
>      \end{aligned}
>     ```
>     Here $`c_{D_R}(m)=\#\{d\in D_R:d\mid m\}`$.*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.one_div_twenty_one_mem_iff_not_fatalAlignedBranch`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L3507)

```lean
theorem one_div_twenty_one_mem_iff_not_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ TwentyOneFatalAlignedBranch
```

2. [`Erdos249257.twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L5554)

```lean
theorem twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows
    {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop)
    (hrow : ∀ k : ℕ,
      2 ≤ R k ∧
        twentyOneEvenQuotientGreedyRemainder (R k) ≤ 2 ^ (R k)) :
    TwentyOneCofinalEvenQuotientGreedyDecay
```

where [`TwentyOneCofinalEvenQuotientGreedyDecay`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L5425) is

```lean
def TwentyOneCofinalEvenQuotientGreedyDecay : Prop :=
  ∃ R : ℕ → ℕ,
    Tendsto R atTop atTop ∧
      (∀ k : ℕ, 2 ≤ R k) ∧
      Tendsto
        (fun k : ℕ =>
          ((twentyOneEvenQuotientGreedyRemainder (R k) +
              (2 * R k + 1) : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * R k))
        atTop (nhds 0)
```

3. [`Erdos249257.one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L5458)

```lean
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay
    (hcofinal : TwentyOneCofinalEvenQuotientGreedyDecay) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet
```

4. [`Erdos249257.twentyOneFatalAlignedBranch_eventually_strict_supercapacity`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L5625)

```lean
theorem twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      2 ^ R < twentyOneEvenQuotientGreedyRemainder R
```

5. [`Erdos249257.twentyOneFatalAlignedBranch_eventually_affine_supercapacity`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L5658)

```lean
theorem twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      twentyOneEvenQuotientGreedySupport (R + 1) =
          insert (R + 1) (twentyOneEvenQuotientGreedySupport R) ∧
        twentyOneEvenQuotientGreedyRemainder (R + 1) =
          (4 * twentyOneEvenQuotientGreedyRemainder R +
              twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse
                  (twentyOneEvenQuotientGreedySupport R) (2 * R)) -
            (2 ^ (R + 1) + 1)
```

<a id="res-one-over-twenty-one-frontier-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `one_div_twenty_one_mem_iff_not_fatalAlignedBranch` | [E257_43/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_43/Challenge.lean#L175) | [TwentyOneFatalBranch.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_43/TwentyOneFatalBranch.lean#L233) | [E257_43](../evidence/comparator/replay-35882032091/receipt-E257_43.json) |
| `twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows` | [E257_39/Challenge.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_39/Challenge.lean#L238) | [PaperStructuresBQ.lean, line 299](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_39/PaperStructuresBQ.lean#L299) | [E257_39](../evidence/comparator/replay-35882032091/receipt-E257_39.json) |
| `one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay` | [E257_39/Challenge.lean, line 225](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_39/Challenge.lean#L225) | [PaperStructuresBM.lean, line 302](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_39/PaperStructuresBM.lean#L302) | [E257_39](../evidence/comparator/replay-35882032091/receipt-E257_39.json) |
| `twentyOneFatalAlignedBranch_eventually_strict_supercapacity` | [E257_43/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_43/Challenge.lean#L180) | [TwentyOneFatalBranch.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_43/TwentyOneFatalBranch.lean#L239) | [E257_43](../evidence/comparator/replay-35882032091/receipt-E257_43.json) |
| `twentyOneFatalAlignedBranch_eventually_affine_supercapacity` | [E257_43/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_43/Challenge.lean#L186) | [TwentyOneFatalBranch.lean, line 248](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_43/TwentyOneFatalBranch.lean#L248) | [E257_43](../evidence/comparator/replay-35882032091/receipt-E257_43.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-terminalhalf"></a>

## Theorem (finite approximations with vanishing scaled error)

> *Suppose there are integers $`M_j\ge1`$ tending to infinity and sets $`A_j\subseteq\{2,\ldots,M_j\}`$ such that
> ``` math
> \frac{|K_{A_j}(M_j)|}{2^{M_j}}\longrightarrow0.
> ```
> Then $`X_A(2)=1/2`$ for some infinite set $`A\subseteq\mathbb{N}_{>0}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/TerminalSetCorrespondence.lean#L51)

```lean
theorem paper_terminalhalf
    (M : ℕ → ℕ) (A : ℕ → Set ℕ)
    (hM : ∀ j, 1 ≤ M j)
    (hlim : Filter.Tendsto M Filter.atTop Filter.atTop)
    (hA : ∀ j n, n ∈ A j → 2 ≤ n ∧ n ≤ M j)
    (herr : Filter.Tendsto
      (fun j ↦ |(terminalPaperCarry (A j) (M j) : ℝ)| / (2 : ℝ) ^ M j)
      Filter.atTop (nhds 0)) :
    ∃ B : Set ℕ, 0 ∉ B ∧ B.Infinite ∧
      erdosSupportSeries 2 B = (1 : ℝ) / 2
```

<a id="res-terminalhalf-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_terminalhalf` | [E257_39/Challenge.lean, line 121](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_39/Challenge.lean#L121) | [PaperStatementsBC.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_39/PaperStatementsBC.lean#L22) | [E257_39](../evidence/comparator/replay-35882032091/receipt-E257_39.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-cylinderhalf"></a>

## Theorem (unbounded shared-prefix families imply a half-support)

> *Suppose that for every $`N`$ there are $`M,K`$ with $`\max\{N,1\}\le M`$, $`0\le K\le M`$, and a family satisfying all the conditions in the preceding paragraph. Then $`X_A(2)=1/2`$ for some infinite set $`A\subseteq\mathbb{N}_{>0}`$.*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.SuffixCylinderTerminalOnlyBridge.exists_infinite_positive_support_half_of_cofinalCylinderStages`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L287)

```lean
theorem exists_infinite_positive_support_half_of_cofinalCylinderStages
    (hstages : ∀ N : ℕ, ∃ M K : ℕ,
      max N 1 ≤ M ∧ Nonempty (CylinderStage K M)) :
    ∃ A : Set ℕ, 0 ∉ A ∧ A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2
```

<a id="res-cylinderhalf-comparator"></a>

**Comparator:** not yet compared.
