# Formal evidence: Reciprocal Mersenne Subseries

This record belongs to the paper [erdos257-mersenne-reasoning-surface.pdf](../paper/257/erdos257-mersenne-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`e6c2d8f77ac2`](https://github.com/wcook04/plectis-erdos/tree/e6c2d8f77ac24753c5216a49f4daf7f7388b309f) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35882032091](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35882032091) at corpus commit [`a2faa350b45a`](https://github.com/wcook04/plectis-erdos-lean/tree/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3) (tag `paper-evidence-2026-09-23`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 174 results: 174 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 155 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="thm-257-weighted"></a>

## Theorem (A weighted summability criterion)

> *Let $`b\ge2`$ be an integer, let $`\mathcal P`$ be a finite nonempty set of primes, and let $`A\subseteq\mathbb N_{>0}`$ be infinite. Write
> ``` math
> h(a)=\prod_{p\in\mathcal P}p^{v_p(a)},
> ```
> where $`v_p(a)`$ is the exponent of $`p`$ in $`a`$; thus $`h(a)`$ is the $`\mathcal P`$-part of $`a`$. If
> ``` math
> \begin{equation}
> \label{eq:257-weighted-mass}
>  W_{b,\mathcal P}(A):=
>  \sum_{a\in A}\frac{h(a)}{a\bigl(b^{h(a)}-1\bigr)}<\infty,
> \end{equation}
> ```
> then
> ``` math
> X_A(b)=\sum_{a\in A}\frac1{b^a-1}
> ```
> is irrational. More precisely, for
> ``` math
> \Delta_{b,A}(m)=
>  \sum_{a\in A}\frac{b^{m\bmod a}-1}{b^a-1},
> ```
> for every $`\varepsilon>0`$ and every $`N`$ there is an $`m\ge N`$ with $`0<\Delta_{b,A}(m)<\varepsilon`$.*
> 
> *<span class="sans-serif">\[Math\]</span><span class="sans-serif">(uniform)</span>*divisibility-weighted**

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L120)

```lean
theorem divisibilityWeightedClaim : DivisibilityWeightedClaim
```

2. [`ErdosProblems.Erdos257.PaperCompleteR8.weighted_displacement_cofinal_close_return`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L100)

```lean
theorem weighted_displacement_cofinal_close_return
    (b : ℕ) (E : Set ℕ) (hb : 2 ≤ b) (hE0 : 0 ∉ E)
    (hE : FinitePrimeWeighted b E) (hInf : E.Infinite)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < displacement b E m ∧ displacement b E m < ε
```

<a id="thm-257-weighted-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `divisibilityWeightedClaim` | [E257_01/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_01/Challenge.lean#L76) | [DivisibilityWeightedSupport.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_01/DivisibilityWeightedSupport.lean#L42) | [E257_01](../evidence/comparator/replay-35882032091/receipt-E257_01.json) |
| `weighted_displacement_cofinal_close_return` | [E257_01/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_01/Challenge.lean#L96) | [WeightedCloseReturn.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_01/WeightedCloseReturn.lean#L19) | [E257_01](../evidence/comparator/replay-35882032091/receipt-E257_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-257-variable-fractional-cover"></a>

## Theorem (A summable family of divisor majorants)

> *For each $`j\ge1`$, let $`F_j\subseteq\mathbb{N}_{>0}`$ be finite, let $`0<\alpha_j\le1`$, and let $`c_{j,d}\ge0`$ satisfy
> ``` math
> f_{F_j}(n)^{\alpha_j}\le\sum_{d\mid n}c_{j,d}\quad(n\ge1).
> ```
> Set $`C_j=\sum_{d\ge1}c_{j,d}/d`$. If
> ``` math
> \begin{equation}
>  \sum_{j\ge1}\frac{C_j2^{j\alpha_j}}{2^{\alpha_j}-1}<\infty,
>  \label{eq:257-strengthened-cover}
> \end{equation}
> ```
> then $`X_A(b)`$ is irrational for every infinite $`A\subseteq\bigcup_jF_j`$ and every integer $`b\ge2`$.*

The Lean declaration below states a result at least as strong as this one.

[`ErdosProblems.Erdos257.PaperCompleteR8.strengthenedPositiveCoverClaim`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR8/PositiveCoverReturn.lean#L241)

```lean
theorem strengthenedPositiveCoverClaim : StrengthenedPositiveCoverClaim
```

<a id="thm-257-variable-fractional-cover-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `strengthenedPositiveCoverClaim` | [E257_01/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_01/Challenge.lean#L113) | [VariableExponentCover.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_01/VariableExponentCover.lean#L86) | [E257_01](../evidence/comparator/replay-35882032091/receipt-E257_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-257-mixed-supports"></a>

## Theorem (mixed weighted and cover supports)

> *Let $`E,V\subseteq\mathbb{N}_{>0}`$. Suppose $`E`$ has finite weighted mass <a href="#eq:257-weighted-mass" data-reference-type="eqref" data-reference="eq:257-weighted-mass">[eq:257-weighted-mass]</a> at $`b=2`$ for a finite nonempty prime set $`\mathcal P`$. Suppose also that $`V\subseteq\bigcup_jF_j`$ for sets and majorants satisfying Theorem <a href="#thm:257-variable-fractional-cover" data-reference-type="ref" data-reference="thm:257-variable-fractional-cover">2</a>, with <a href="#eq:257-strengthened-cover" data-reference-type="eqref" data-reference="eq:257-strengthened-cover">[eq:257-strengthened-cover]</a> or its positive-weight variant. Then $`X_A(b)`$ is irrational for every infinite $`A\subseteq E\cup V`$ and every integer $`b\ge2`$.*

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

<a id="thm-257-mixed-supports-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mixedSupportClaim` | [E257_01/Challenge.lean, line 130](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_01/Challenge.lean#L130) | [MixedWeightedCover.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_01/MixedWeightedCover.lean#L109) | [E257_01](../evidence/comparator/replay-35882032091/receipt-E257_01.json) |
| `arbitraryWeightMixedSupport_allBase_hereditary` | [E257_01/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_01/Challenge.lean#L159) | [PaperStructuresBO.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_01/PaperStructuresBO.lean#L65) | [E257_01](../evidence/comparator/replay-35882032091/receipt-E257_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-geometry"></a>

## Theorem (Achievement-set geometry)

> *$`\mathcal{A}`$ is compact, closed, perfect, totally disconnected and nowhere dense, and $`\operatorname{volume}(\mathcal{A}) = 1`$. Thus its measure is positive although it contains no interval. Its convex hull is $`[0,E]`$, where $`E=\sum_{n\ge1}w_n`$. The positive-index digit coding onto $`\mathcal{A}`$ is injective: each achievable real has *exactly one* support. *achievement-set* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>\
> *Sources:* [`isCompact_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L656), [`perfect_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1656), [`isTotallyDisconnected_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1672), [`isNowhereDense_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1681), [`volume_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L996), [`positiveMersenneDigitValue_injective`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1582).*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.paper_achievement_geometry`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/AchievementGeometry.lean#L40)

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

<a id="thm-geometry-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_achievement_geometry` | [E257_02/Challenge.lean, line 70](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_02/Challenge.lean#L70) | [PaperStatementsAM.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L109) | [E257_02](../evidence/comparator/replay-35882032091/receipt-E257_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-supported-dichotomy"></a>

## Theorem (Support-restricted refinement)

> *Use zero-based indices in this statement: coordinate $`j\in\mathbb{N}`$ carries weight $`w_{j+1}`$. For $`J\subseteq\mathbb{N}`$, consider the sums that use only coordinates in $`J`$. If $`\mathbb{N}\smallsetminus J`$ is finite, this achievement set has measure $`2^{-|\mathbb{N}\smallsetminus J|}`$; if infinitely many coordinates are omitted, its measure is zero. Injectivity survives every restriction; perfectness is proved when $`J`$ is infinite. No perfectness claim is made for finite $`J`$, whose coding range is finite. *achievement-set* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>\
> *Sources:* [`volume_supportedMersenneAchievementSet_dichotomy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L397), [`volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L368), [`perfect_supportedMersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L167), [`supportedMersenneDigitValue_injective`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L54).*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L397)

```lean
theorem volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧
        volume (supportedMersenneAchievementSet J) = 0)
```

2. [`ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L368)

```lean
theorem volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite
    {J : Set ℕ} (hJ : Jᶜ.Infinite) :
    volume (supportedMersenneAchievementSet J) = 0
```

3. [`ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L167)

```lean
theorem perfect_supportedMersenneAchievementSet
    {J : Set ℕ} (hJ : J.Infinite) :
    Perfect (supportedMersenneAchievementSet J)
```

4. [`ErdosProblems.Erdos257.supportedMersenneDigitValue_injective`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L54)

```lean
theorem supportedMersenneDigitValue_injective (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J)
```

<a id="thm-supported-dichotomy-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `volume_supportedMersenneAchievementSet_dichotomy` | [E257_02/Challenge.lean, line 89](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_02/Challenge.lean#L89) | [PaperStatementsAM.lean, line 252](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L252) | [E257_02](../evidence/comparator/replay-35882032091/receipt-E257_02.json) |
| `volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite` | [E257_02/Challenge.lean, line 98](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_02/Challenge.lean#L98) | [PaperStatementsAM.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L260) | [E257_02](../evidence/comparator/replay-35882032091/receipt-E257_02.json) |
| `perfect_supportedMersenneAchievementSet` | [E257_02/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_02/Challenge.lean#L80) | [PaperStatementsAM.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L245) | [E257_02](../evidence/comparator/replay-35882032091/receipt-E257_02.json) |
| `supportedMersenneDigitValue_injective` | [E257_02/Challenge.lean, line 85](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_02/Challenge.lean#L85) | [PaperStatementsAM.lean, line 249](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L249) | [E257_02](../evidence/comparator/replay-35882032091/receipt-E257_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-greedy-survival"></a>

## Theorem (Membership equals greedy survival; the fatal-gap dichotomy)

> *For a real target $`x\ge0`$, let $`r_n(x)`$ be the remainder after the greedy rule has processed weights $`w_1,\ldots,w_n`$, and let $`R_n=\sum_{j>n}w_j`$, with $`r_0(x)=x`$ and $`R_0=E`$. Then
> ``` math
> x\in\mathcal A\quad\Longleftrightarrow\quad
>  x\ge0\ \text{ and }\ r_n(x)\le R_n\ \text{for every }n\ge0.
> ```
> For every $`x\in[0,E]`$, nonmembership is equivalent to a finite strict gap between the two next-prefix intervals; see Observation <a href="#obs:general-target-gap" data-reference-type="ref" data-reference="obs:general-target-gap">244</a>. *greedy recurrence* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>\
> *Sources:* [`mem_mersenneAchievementSet_iff_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1458); [`half_mem_mersenneAchievementSet_or_exists_fatal_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L623); [`existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L643); [`half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L654); witness type [`ExistsFatalHalfGap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L526). The general-target statement is checked by [`paper_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/168bf6727758f918a430ef056a1c93d3160b53a6/lean/ErdosProblems/Erdos257/PaperCompleteR20/GeneralTargetGap.lean#L183).*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.paper_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/GeneralTargetGap.lean#L183)

```lean
theorem paper_greedy_survival :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ erdosBorweinMersenneConstant →
      (x ∉ mersenneAchievementSet ↔ InternalMersenneGap x))
```

<a id="thm-greedy-survival-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_greedy_survival` | [E257_02/Challenge.lean, line 126](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_02/Challenge.lean#L126) | [PaperStatementsD.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_02/PaperStatementsD.lean#L186) | [E257_02](../evidence/comparator/replay-35882032091/receipt-E257_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-canon"></a>

## Proposition (Uniqueness under the stated finite conditions)

> *Put $`G=\mathrm{greedyMersenneSupport}(1/2)`$, $`w_n=(2^n-1)^{-1}`$ and $`R_d=\sum_{n>d}w_n`$. The following are three separate uniqueness statements.*
> 
> 1.  *If $`D\subseteq\{1,\ldots,d\}`$ and $`X_D(2)\le1/2\le X_D(2)+R_d`$, then $`D=G\cap\{1,\ldots,d\}`$.*
> 
> 2.  *If $`c\ge4`$, $`D\subseteq\{2,\ldots,c-1\}`$ and $`0<1/2-X_D(2)<w_c`$, then $`D=G\cap\{1,\ldots,c-1\}`$.*
> 
> 3.  *Let positive integer weights $`v_1,\ldots,v_k`$ satisfy $`v_i\ge g+\sum_{j>i}v_j`$ for a positive integer $`g`$. For a nonnegative integer target $`T`$, let $`y^*`$ be the word obtained by visiting these weights in order and taking each when it fits. An admissible Boolean word $`y`$ has $`0\le T-\sum_i y_iv_i<g`$ if and only if $`y=y^*`$ and $`0\le T-\sum_i y_i^*v_i<g`$.*
> 
> *Part (iii) gives uniqueness under the small-remainder condition, not existence. Theorem <a href="#record:257bm-i11a" data-reference-type="ref" data-reference="record:257bm-i11a">143</a> gives a one-weight counterexample to dropping that condition. *straddle-prefix ; integer-greedy* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>\
> *Sources:* [`IsStraddlePrefix.half_agrees_greedy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L442); [`eq_halfGreedyPrefixSupport_of_critical_crossing`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L50); [`remainder_lt_gap_iff_eq_integerGreedyBits`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGreedyReduction.lean#L918).*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.IsStraddlePrefix.half_agrees_greedy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCutLocator.lean#L442)

```lean
theorem IsStraddlePrefix.half_agrees_greedy
    {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    ∀ n : ℕ, 0 < n → n ≤ d →
      (n ∈ u ↔ n ∈ greedyMersenneSupport (1 / 2 : ℝ))
```

2. [`Erdos249257.eq_halfGreedyPrefixSupport_of_critical_crossing`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L50)

```lean
theorem eq_halfGreedyPrefixSupport_of_critical_crossing
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1)
```

3. [`Erdos249257.BooleanMobiusGreedyReduction.remainder_lt_gap_iff_eq_integerGreedyBits`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L918)

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

<a id="prop-canon-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-collapse-mech"></a>

## Lemma (Carry and residual value)

> *Let $`A \subseteq \mathbb{N}`$ with $`1 \notin A`$, put $`\delta := 1/2 - x_A`$, and let $`\operatorname{ihc}(A,N)`$ denote the integer half-carry at level $`N`$. Then
> ``` math
> \operatorname{ihc}(A,N) \;=\; 2^{N+1}\,\delta \;+\; \mathrm{T}(N+1),
>   \qquad 0 \;\le\; \mathrm{T}(N+1) \;\le\; 2\sqrt{N+1} + 4 ,
> ```
> where $`\mathrm T(m)=\sum_{r\ge1}c_A(m+r)2^{-r}`$. *half-carry recurrence* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>\
> *Sources:* [`integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L871); [`binaryCoeffTail_nonneg`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L78); [`binaryCoeffTail_supportCoeff_le_two_sqrt_add_four`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L290).*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.HalfCarryReachability.integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCarryReachability.lean#L871)

```lean
theorem integerHalfCarry_eq_scaled_residual_add_tail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (integerHalfCarry A N : ℝ) =
      (2 : ℝ) ^ (N + 1) * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) +
        binaryCoeffTail (supportCoeff A) (N + 1)
```

2. [`Erdos249257.binaryCoeffTail_nonneg`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L78)

```lean
theorem binaryCoeffTail_nonneg (c : ℕ → ℕ) (N : ℕ) :
    0 ≤ binaryCoeffTail c N
```

3. [`Erdos249257.binaryCoeffTail_supportCoeff_le_two_sqrt_add_four`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCarry.lean#L290)

```lean
theorem binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    (A : Set ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff A) N ≤
      2 * Real.sqrt (N : ℝ) + 4
```

<a id="lem-collapse-mech-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `integerHalfCarry_eq_scaled_residual_add_tail` | [E257_03/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L99) | [PaperStatementsE.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsE.lean#L35) | [E257_03](../evidence/comparator/replay-35882032091/receipt-E257_03.json) |
| `binaryCoeffTail_nonneg` | [E257_03/Challenge.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L73) | [PaperStatementsAE.lean, line 69](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsAE.lean#L69) | [E257_03](../evidence/comparator/replay-35882032091/receipt-E257_03.json) |
| `binaryCoeffTail_supportCoeff_le_two_sqrt_add_four` | [E257_03/Challenge.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L86) | [PaperStatementsAU.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsAU.lean#L47) | [E257_03](../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-collapse"></a>

## Proposition (A cofinal carry bound)

> *If $`|\operatorname{ihc}(A,N)|\le C\sqrt{N+1}+C'`$ for arbitrarily large $`N`$, with fixed constants $`C,C'`$, then $`\delta=0`$. For the particular greedy support $`A=G`$ of $`1/2`$, a one-sided upper bound $`\operatorname{ihc}(G,N)\le C\sqrt{N+1}+C'`$ already suffices.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR20.half_of_cofinal_absolute_carry`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/CofinalCarryCollapse.lean#L46)

```lean
theorem half_of_cofinal_absolute_carry (A : Set ℕ) (hone : 1 ∉ A)
    (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      |(integerHalfCarry A N : ℝ)| ≤ C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 A = (1 : ℝ)/2
```

2. [`ErdosProblems.Erdos257.PaperCompleteR20.greedy_half_of_cofinal_upper_carry`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/CofinalCarryCollapse.lean#L91)

```lean
theorem greedy_half_of_cofinal_upper_carry (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 (greedyMersenneSupport (1/2 : ℝ)) = (1 : ℝ)/2
```

<a id="prop-collapse-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `half_of_cofinal_absolute_carry` | [E257_03/Challenge.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L106) | [PaperStatementsE.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsE.lean#L43) | [E257_03](../evidence/comparator/replay-35882032091/receipt-E257_03.json) |
| `greedy_half_of_cofinal_upper_carry` | [E257_03/Challenge.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L122) | [PaperStatementsD.lean, line 178](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsD.lean#L178) | [E257_03](../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-sqrt-witness"></a>

## Lemma (The terminal bound at square depths)

> *Suppose $`x_A = 1/2`$ and $`1 \notin A`$. Then for every $`k \ge 1`$,
> ``` math
> \operatorname{ihc}(A, k^2 - 1) \;=\; \mathrm{T}(k^2) \;\le\; 2k + 4 \;=\; \ensuremath{B}(k^2).
> ```
> *half-carry recurrence* <span class="sans-serif">(cofinal)</span> <span class="sans-serif">\[Math\]</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.square_depth_witness`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/CarryCollapseCorrespondence.lean#L8)

```lean
theorem square_depth_witness (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k^2-1) : ℝ) = binaryCoeffTail (supportCoeff A) (k^2) ∧
    binaryCoeffTail (supportCoeff A) (k^2) ≤ 2*(k : ℝ)+4 ∧
    (halfStripBound (k^2) : ℝ) = 2*(k : ℝ)+4
```

<a id="lem-sqrt-witness-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `square_depth_witness` | [E257_03/Challenge.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L136) | [PaperStatementsL.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsL.lean#L28) | [E257_03](../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-collapsed-list"></a>

## Proposition (Six equivalent membership conditions)

> *Each of the following is logically *equivalent* to $`1/2 \in \mathcal{A}`$, not strictly weaker:*
> 
> 1.  *$`C_G(N)\le2\sqrt N+4`$ for every $`N\ge0`$ ([`greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L834); [`greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L953));*
> 
> 2.  *there are arbitrarily large positive exponents outside $`G`$ ([`CofinalPositiveHalfGreedySkips`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L22));*
> 
> 3.  *at arbitrarily large depths $`n`$, some $`D\subseteq\{2,\ldots,n\}`$ satisfies $`Q(D,n)=2^{n-1}-1`$ ([`CofinalExactLocalMersenneHalfRows`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCofinalExactRows.lean#L38)); no agreement between the sets $`D`$ at different depths is required;*
> 
> 4.  *at arbitrarily large $`M`$, $`\operatorname{ihc}(G,M)\le B(M+1)`$ ([`GreedyHalfCarryCofinalStripReturn`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CofinalStripReturn.lean#L76));*
> 
> 5.  *at arbitrarily large positive depths $`M`$, some $`D\subseteq\{2,\ldots,M\}`$ satisfies $`|\operatorname{ihc}(D,M-1)|\le B(M)`$ ([`HalfCarryCofinalTerminalOnlyStrip`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TerminalOnlyCofinal.lean#L34));*
> 
> 6.  *the half-target greedy remainder never exceeds the full remaining tail, so no finite fatal gap exists ([`ExistsFatalHalfGap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L526)); the seven equivalent forms in the later classification express this same condition.*
> 
> *Forward directions are supplied formal (e.g. [`half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L2583), [`half_mem_mersenneAchievementSet_of_cofinalExactLocalRows`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCofinalExactRows.lean#L71), [`existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L643)). For (d) and (e), the reverse directions use the square depths in Lemma <a href="#lem:sqrt-witness" data-reference-type="ref" data-reference="lem:sqrt-witness">17</a>. All six equivalences, including these reverse directions, are now Lean-checked in [`six_membership_conditions`](https://github.com/wcook04/plectis-erdos/blob/168bf6727758f918a430ef056a1c93d3160b53a6/lean/ErdosProblems/Erdos257/PaperCompleteR20/SixMembershipConditions.lean#L123). For (a), membership gives $`C_G(N)\le2\sqrt{N+1}+3\le2\sqrt N+4`$ when $`N\ge1`$, and $`C_G(0)=0`$. The forward implication still needs the greedy inequality $`x_G\le1/2`$. *half-carry recurrence ; exact-row* <span class="sans-serif">(cofinal)</span> <span class="sans-serif">\[Lean\]</span><span class="sans-serif">\[Math\]</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.six_membership_conditions`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/SixMembershipConditions.lean#L123)

```lean
theorem six_membership_conditions :
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ N : ℕ, (mobiusCenteredHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        2*Real.sqrt (N : ℝ)+4) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ 0 < n ∧ n ∉ greedyMersenneSupport (1/2 : ℝ)) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ GreedyHalfCarryCofinalStripReturn) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      (∀ n : ℕ, greedyMersenneRemainder (1/2 : ℝ) n ≤ mersenneTail n) ∧
        ¬ ExistsFatalHalfGap)
```

<a id="prop-collapsed-list-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `six_membership_conditions` | [E257_03/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L207) | [PaperStatementsK.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsK.lean#L56) | [E257_03](../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-local-void"></a>

## Proposition (Limits of the specified local summaries)

> *(i) After $`L`$ common steps the endpoint residue mod $`2^L`$ of an affine binary orbit is *independent* of the initial carry: $`u(L) - v(L) = 2^L(u_0 - v_0)`$ ([`affineBinaryOrbit_mod_twoPow_eq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L307)). (ii) Fix $`m\ge2`$ and put $`h=\lfloor(m+1)/2\rfloor`$. Consider the coefficient sequences
> ``` math
> c_r(m)=h-r,\qquad c_r(m+1)=2r,\qquad
>  c_r(j)=0\ (j\ne m,m+1),\qquad 0\le r\le h.
> ```
> Their binary sums are all $`h2^{-m}`$, and their scaled tails before position $`m`$ agree, but their scaled tails immediately after $`m`$ are $`r`$. Thus any exact label-and-decoder system recovering those latter tails must have at least $`h+1=\lfloor(m+1)/2\rfloor+1`$ labels. A state determined only by the common preceding history, with no new input, cannot distinguish them ([`balancedPulse_no_autonomous_decoder`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L247)). (iii) For any starting carry and any finite list of prescribed valuations and odd unit residues modulo $`2^u`$, with $`u\ge1`$, there are integer input coefficients with those data whose successor carries lie in their prescribed centred intervals. The unrestricted higher bits of the input coefficients may be chosen separately at each step, as in Proposition <a href="#prop:2adic-nogo" data-reference-type="ref" data-reference="prop:2adic-nogo">256</a> ([`fixedPrecisionTropicalNoGo`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TropicalCurvatureCarry.lean#L137)), so these fixed-precision symbols alone do not exclude a completion in that specified family. This says nothing about extra constraints imposed by divisor counts from one common support. *carry* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.affineBinaryOrbit_mod_twoPow_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L307)

```lean
theorem affineBinaryOrbit_mod_twoPow_eq (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L]
```

2. [`Erdos249257.balancedPulse_weighted_pair`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L200)

```lean
theorem balancedPulse_weighted_pair
    {m r : ℕ} (hr : r ≤ balancedPulseRadius m) :
    2 * balancedPulseCoeff m r m + balancedPulseCoeff m r (m + 1) =
      2 * balancedPulseRadius m
```

3. [`Erdos249257.balancedPulse_endpoint_fanout`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L209)

```lean
theorem balancedPulse_endpoint_fanout (m r : ℕ) :
    balancedPulseCoeff m r (m + 1) / 2 = r
```

4. [`Erdos249257.balancedPulse_label_card_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L228)

```lean
theorem balancedPulse_label_card_lower_bound
    {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ)
    (decode : Λ → ℕ) (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ
```

5. [`Erdos249257.balancedPulse_no_autonomous_decoder`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L247)

```lean
theorem balancedPulse_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_centred_completion_of_fixed_precision`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/CentredCompletionAndDecisionBoundary.lean#L34)

```lean
theorem paper_centred_completion_of_fixed_precision
    (u : ℕ) (hu : 1 ≤ u) (m : ℕ) (v : ℕ → ℕ) (a : ℕ → ℤ)
    (hodd : ∀ i, i < m → Odd (a i)) (e₀ : ℤ) :
    ∃ e z : ℕ → ℤ, e 0 = e₀ ∧
      ∀ i, i < m →
        e (i + 1) = 2 * e i + 2 ^ (v i) * (a i + 2 ^ u * z i) ∧
          |e (i + 1)| ≤ 2 ^ (v i + u - 1)
```

<a id="prop-local-void-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `affineBinaryOrbit_mod_twoPow_eq` | [E257_04/Challenge.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L47) | [PaperStatementsA.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsA.lean#L17) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `balancedPulse_weighted_pair` | [E257_04/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L111) | [PaperStatementsAE.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAE.lean#L47) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `balancedPulse_endpoint_fanout` | [E257_04/Challenge.lean, line 93](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L93) | [PaperStatementsAE.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAE.lean#L31) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `balancedPulse_label_card_lower_bound` | [E257_04/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L97) | [PaperStatementsAE.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAE.lean#L34) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `balancedPulse_no_autonomous_decoder` | [E257_04/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L104) | [PaperStatementsAE.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAE.lean#L41) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `paper_centred_completion_of_fixed_precision` | [E257_04/Challenge.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L56) | [PaperStatementsAA.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAA.lean#L181) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-exponent-gap"></a>

## Proposition (Weighted denominator budget)

> *Let $`n\ge2`$, let $`\mathrm{Skip}_n\subseteq\{2,\ldots,n-1\}`$, and let $`D_n`$ be the reduced denominator of the associated finite sum. Since $`D_n`$ divides the product of its Mersenne denominators,
> ``` math
> \log_2D_n\le\sum_{d\in\mathrm{Skip}_n}\log_2(2^d-1)
>  \le\sum_{d\in\mathrm{Skip}_n}d\le\frac{n(n-1)}2-1.
> ```
> The middle inequality is strict when the skip set is nonempty; for an empty skip set both sums are zero. This is an upper bound, not a quadratic asymptotic for $`D_n`$. Combined with the cited fixed irrationality-measure exponent, it does not supply the required $`2^{-3n/2}`$-scale estimate. Even an asymptotic for the exponent sum would need additional information about the skip distribution. *diophantine* <span class="sans-serif">(cofinal)</span> <span class="sans-serif">\[Math\]</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.skipSum_den_dvd_prod`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/DenominatorBudget.lean#L43)

```lean
theorem skipSum_den_dvd_prod (S : Finset ℕ) (hS : ∀ d ∈ S, 1 ≤ d) :
    ((skipSum S).den : ℤ) ∣ ∏ d ∈ S, ((2 : ℤ) ^ d - 1)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.weighted_denominator_budget`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/DenominatorBudget.lean#L78)

```lean
theorem weighted_denominator_budget (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico 2 n) :
    Real.logb 2 (((skipSum S).den : ℕ) : ℝ)
        ≤ ∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1) ∧
      (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) ≤ ∑ d ∈ S, (d : ℝ) ∧
      (∑ d ∈ S, (d : ℝ)) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 - 1 ∧
      (S.Nonempty →
        (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) < ∑ d ∈ S, (d : ℝ)) ∧
      (S = ∅ → (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) = 0 ∧
        (∑ d ∈ S, (d : ℝ)) = 0)
```

<a id="prop-exponent-gap-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `skipSum_den_dvd_prod` | [E257_04/Challenge.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L65) | [PaperStatementsAA.lean, line 352](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAA.lean#L352) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `weighted_denominator_budget` | [E257_04/Challenge.lean, line 69](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L69) | [PaperStatementsAA.lean, line 355](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAA.lean#L355) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-one-sided"></a>

## Theorem (One-sidedness)

> *Non-membership of $`1/2`$ in $`\mathcal A`$ has an effectively checkable finite-certificate formulation, hence a $`\Sigma^0_1`$ formulation. Membership has the complementary $`\Pi^0_1`$ formulation. Survival through a tested finite depth alone does not establish membership; a uniform theorem or inductive invariant could. The arithmetical-hierarchy form by itself proves neither undecidability nor the absence of finite proofs. *meta* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span><span class="sans-serif">\[Math\]</span> The linked declarations establish the fatal-gap equivalences. The arithmetical-hierarchy classification also uses the effective tail estimate explained below; it is an ordinary computability deduction, not a separately replayed Lean theorem.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sidedness`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L492)

```lean
theorem paper_one_sidedness :
    (∃ P : ℕ → Prop, ComputablePred P ∧
        ((1 / 2 : ℝ) ∉ mersenneAchievementSet ↔ ∃ n : ℕ, P n) ∧
        ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ∀ n : ℕ, ¬ P n)) ∧
      (∀ d : ℕ, ∃ x : ℝ, IsStraddlePrefix x ∅ d ∧ x ∉ mersenneAchievementSet)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_iff_exists_certificate`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L291)

```lean
theorem existsFatalHalfGap_iff_exists_certificate :
    ExistsFatalHalfGap ↔ ∃ p : List Bool × ℕ, FatalHalfGapCertificate p
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_of_certificate`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L174)

```lean
theorem existsFatalHalfGap_of_certificate {L : List Bool} {N : ℕ}
    (h : FatalHalfGapCertificate (L, N)) : ExistsFatalHalfGap
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.certificate_of_existsFatalHalfGap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L243)

```lean
theorem certificate_of_existsFatalHalfGap (h : ExistsFatalHalfGap) :
    ∃ p : List Bool × ℕ, FatalHalfGapCertificate p
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.scaledMersenneWeight_cast`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L103)

```lean
theorem scaledMersenneWeight_cast {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (scaledMersenneWeight N n : ℝ) = 2 * (mersenneDen N : ℝ) * mersenneWeight n
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.certifiedWordValue_cast`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L133)

```lean
theorem certifiedWordValue_cast {L : List Bool} {N : ℕ} (hLN : L.length ≤ N) :
    (certifiedWordValue L N : ℝ)
      = 2 * (mersenneDen N : ℝ) * ∑ n ∈ certWord L, mersenneWeight n
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.certifiedTailBound_cast`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L144)

```lean
theorem certifiedTailBound_cast {d N : ℕ} (hdN : d + 1 ≤ N) :
    (certifiedTailBound d N : ℝ)
      = 2 * (mersenneDen N : ℝ) *
          ((∑ j ∈ Finset.range (N - (d + 1)), mersenneWeight (d + 1 + 1 + j))
            + mersenneWeight N)
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.mersenneTail_eq_sum_add`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L160)

```lean
theorem mersenneTail_eq_sum_add (m K : ℕ) :
    mersenneTail m
      = (∑ j ∈ Finset.range K, mersenneWeight (m + 1 + j)) + mersenneTail (m + K)
```

<a id="thm-one-sided-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_one_sidedness` | [E257_04/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L205) | [PaperStructuresS.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStructuresS.lean#L32) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `existsFatalHalfGap_iff_exists_certificate` | [E257_04/Challenge.lean, line 170](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L170) | [PaperStatementsAM.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L141) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `existsFatalHalfGap_of_certificate` | [E257_04/Challenge.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L174) | [PaperStatementsAM.lean, line 144](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L144) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `certificate_of_existsFatalHalfGap` | [E257_04/Challenge.lean, line 154](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L154) | [PaperStatementsAM.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L120) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `scaledMersenneWeight_cast` | [E257_04/Challenge.lean, line 183](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L183) | [PaperStatementsAM.lean, line 226](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L226) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `certifiedWordValue_cast` | [E257_04/Challenge.lean, line 165](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L165) | [PaperStatementsAM.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L129) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `certifiedTailBound_cast` | [E257_04/Challenge.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L158) | [PaperStatementsAM.lean, line 123](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L123) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `mersenneTail_eq_sum_add` | [E257_04/Challenge.lean, line 178](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L178) | [PaperStatementsAM.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L171) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-full-support"></a>

## Theorem (Full-support irrationality, unconditional, every base $`b \ge 2`$)

> *For every integer $`b \ge 2`$,
> ``` math
> \sum_{k=0}^{\infty} \frac{1}{b^{k+1}-1} \quad \text{is irrational.}
> ```
> **Hypotheses:** $`b \in \mathbb{N}`$, $`b \ge 2`$. **Conclusion:** unconditional irrationality of the full-support Erdős–Borwein-type series at every base, not merely base $`2`$. *full-support* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>\
> *Source:* [`irrational_erdosSum_full_support`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L8328) (‘$`b : \mathbb{N}`$, hb : $`2 \le b`$’), recorded via a certificate machine (bounded Bertrand/CRT first-block frame, middle-window divisor-pair average with pigeonhole selection, explicit parameter closure). The base-$`2`$ instance recovering the classical Erdős–Borwein constant’s irrationality is [`irrational_erdosBorwein_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L8335), a one-line corollary.*

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSum_full_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L8328)

```lean
theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1))
```

<a id="thm-full-support-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSum_full_support` | [E257_05/Challenge.lean, line 48](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L48) | [PaperStatementsAG.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L52) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-purely-periodic-support"></a>

## Theorem

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSupportSeries_periodic`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L11590)

```lean
theorem irrational_erdosSupportSeries_periodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, n + m ∈ A ↔ n ∈ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A)
```

<a id="thm-purely-periodic-support-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSupportSeries_periodic` | [E257_05/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L63) | [PaperStatementsAG.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L86) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-eventually-periodic-support"></a>

## Theorem

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSupportSeries_eventuallyPeriodic`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L11604)

```lean
theorem irrational_erdosSupportSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → (n + m ∈ A ↔ n ∈ A))
    (hinf : A.Infinite) :
    Irrational (erdosSupportSeries b A)
```

<a id="thm-eventually-periodic-support-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSupportSeries_eventuallyPeriodic` | [E257_05/Challenge.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L52) | [PaperStatementsAG.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L64) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-residue-class-support"></a>

## Theorem

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.irrational_residueClass_positive_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResidueClassSupport.lean#L21)

```lean
theorem irrational_residueClass_positive_support
    (b m : ℕ) (c : ℤ) (hb : 2 ≤ b) (hm : 1 ≤ m) :
    Irrational (erdosSupportSeries b
      {n : ℕ | 0 < n ∧ (n : ℤ) % (m : ℤ) = c % (m : ℤ)})
```

<a id="thm-residue-class-support-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_residueClass_positive_support` | [E257_05/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L76) | [PaperStatementsBC.lean, line 53](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsBC.lean#L53) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-odd-support"></a>

## Theorem

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSupportSeries_odd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L11686)

```lean
theorem irrational_erdosSupportSeries_odd (b : ℕ) (hb : 2 ≤ b) :
    Irrational (erdosSupportSeries b {n : ℕ | Odd n})
```

<a id="thm-odd-support-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSupportSeries_odd` | [E257_05/Challenge.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L59) | [PaperStatementsAG.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L74) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-topology"></a>

## Theorem (Achievement-set topology and measure)

> *$`\mathcal{A}`$ (Definition <a href="#defn:half-question" data-reference-type="ref" data-reference="defn:half-question">26</a>) is compact, closed, perfect, totally disconnected, and nowhere dense; its Lebesgue measure is exactly $`1`$: $`\operatorname{volume}(\mathcal{A}) = 1`$. **Hypotheses:** none. **Conclusion:** $`\mathcal A`$ is a Cantor set of positive measure, often called a fat Cantor set. Its measure is $`1`$, not the length of its ambient interval $`[0,E]`$, where $`E\approx1.6067`$. *achievement-set-topology* <span class="sans-serif">(n/a)</span> <span class="sans-serif">\[Lean\]</span>\
> *Source:* [`isCompact_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L656), [`isClosed_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L660), [`perfect_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1656), [`isTotallyDisconnected_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1672), [`isNowhereDense_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1681), [`volume_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L996). Strict separation and summability give the compactness, unique coding, and Cantor topology, and Hornich’s strict-tail theorem, as proved by Nitecki \[nitecki2013, Theorem 4(1), p. 9\], gives the measure as $`\lim_N2^NR_N`$ with $`R_N=\sum_{n>N}x_n`$: each level-$`N`$ cylinder has length $`R_N`$, and the $`2^N`$ disjoint cylinders have total length $`2^NR_N`$. The Mersenne-specific input is $`2^NR_N\to1`$. Other weight sequences require their own tail asymptotic.\
> *Use:* Theorem <a href="#thm:greedy-survival-record" data-reference-type="ref" data-reference="thm:greedy-survival-record">34</a> below (compactness is exactly what powers every “limit of achieved points is achieved” argument used downstream, including the seam-limit route of Part 2).*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR20.paper_achievement_geometry`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/AchievementGeometry.lean#L40)

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

2. [`ErdosProblems.Erdos257.PaperCompleteR20.mersenne_topology_quantitative`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/MersenneConstantDecimal.lean#L21)

```lean
theorem mersenne_topology_quantitative :
    |erdosBorweinMersenneConstant-(16067 : ℝ)/10000| < 1/20000 ∧
    1 < erdosBorweinMersenneConstant ∧
    Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ)^n*mersenneTail n) Filter.atTop (nhds 1)
```

<a id="thm-topology-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_achievement_geometry` | [E257_02/Challenge.lean, line 70](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_02/Challenge.lean#L70) | [PaperStatementsAM.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L109) | [E257_02](../evidence/comparator/replay-35882032091/receipt-E257_02.json) |
| `mersenne_topology_quantitative` | [E257_05/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L96) | [PaperStatementsAM.lean, line 126](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAM.lean#L126) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-greedy-survival-record"></a>

## Theorem (Membership equals greedy survival at every level)

> *For a real $`x`$, let $`r_n(x)`$ be its greedy remainder after rank $`n`$, and let $`R_n=\sum_{j>n}w_j`$, as in the initial notation. Then
> ``` math
> x\in\mathcal A\quad\Longleftrightarrow\quad
>  x\ge0\ \text{and}\ r_n(x)\le R_n\text{ for every }n\ge0.
> ```
> The inequality says that the unselected tail has enough total mass at every rank. A failure at any one rank excludes membership; the inequalities at all ranks give a representation. *greedy-survival* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>\
> *Source:* [`mem_mersenneAchievementSet_iff_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1458) (forward direction [`greedy_survives_of_mem_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1375), reverse [`mem_mersenneAchievementSet_of_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1394)).*

The Lean declarations below together state this result.

1. [`Erdos249257.mem_mersenneAchievementSet_iff_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L1458)

```lean
theorem mem_mersenneAchievementSet_iff_greedy_survival (x : ℝ) :
    x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n
```

2. [`Erdos249257.greedy_survives_of_mem_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L1375)

```lean
theorem greedy_survives_of_mem_mersenneAchievementSet {x : ℝ}
    (hx : x ∈ mersenneAchievementSet) :
    0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n
```

3. [`Erdos249257.mem_mersenneAchievementSet_of_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L1394)

```lean
theorem mem_mersenneAchievementSet_of_greedy_survival {x : ℝ} (hx : 0 ≤ x)
    (hsurvive : ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) :
    x ∈ mersenneAchievementSet
```

<a id="thm-greedy-survival-record-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mem_mersenneAchievementSet_iff_greedy_survival` | [E257_05/Challenge.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L134) | [PaperStatementsB.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsB.lean#L106) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |
| `greedy_survives_of_mem_mersenneAchievementSet` | [E257_05/Challenge.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L129) | [PaperStatementsB.lean, line 60](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsB.lean#L60) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |
| `mem_mersenneAchievementSet_of_greedy_survival` | [E257_05/Challenge.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L139) | [PaperStatementsB.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsB.lean#L119) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-master-identity"></a>

## Theorem (Decomposition of the integer remainder)

> *For every quotient row $`n \ge 6`$,
> ``` math
> \begin{equation*}
> \Delta_n \;=\; K(2n) \;+\; \sum_{d \in \mathrm{Skip}_n} \left\lfloor \frac{4^n}{2^d-1} \right\rfloor.
> \tag{I}
> \end{equation*}
> ```
> Here the take and skip sets, capacity and remainder are those defined at the start of this subsection. The identity separates the contribution of the full exponent range from that of the omitted ranks. It makes no claim that there are few omitted ranks; controlling their sum is a separate part of any application. *quotient-row ; integer-greedy (Mersenne weights, binary digits of $`K`$)* <span class="sans-serif">(fixed)</span> <span class="sans-serif">\[Math\]</span><span class="sans-serif">\[Cert\]</span>\
> **Proof.** For $`d=n`$ the quotient is $`2^n+1`$, and for $`n<d\le2n`$ it is $`2^{2n-d}`$. Hence
> ``` math
> \sum_{d=n}^{2n}\left\lfloor\frac{4^n}{2^d-1}\right\rfloor
>  =2^n+1+\sum_{j=0}^{n-1}2^j=2^{n+1}.
> ```
> Substitute this in the definition of $`K(2n)`$, split $`\{2,\ldots,n-1\}=D_n\sqcup\mathrm{Skip}_n`$, and use $`\Delta_n=2^{2n-1}-2^{n+1}-\sum_{d\in D_n}w(n,d)`$. This gives (I). **Certification:** verified rows $`6\le n\le200`$, zero mismatches, reported as reproduced in two separate computations (§<a href="#ssec:anchors" data-reference-type="ref" data-reference="ssec:anchors">5.7</a>).\
> *Use:* (I) permits substitution of information about $`K(2n)`$. A resulting estimate for $`\Delta_n`$ must also retain or bound the skip-set sum; information about $`K`$ alone need not control their cancellation.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.paper_master_identity_floors`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/QuotientRowIdentity.lean#L89)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_master_identity_floors` | [E257_05/Challenge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L147) | [PaperStatementsAA.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAA.lean#L97) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-real-form"></a>

## Theorem (Real (non-integer) form of the quotient identity)

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
> ***Use of the error bound.** For $`H>2n+2`$, the condition $`|\sum_{d\in\mathrm{Skip}_n}x_d-C|>(H+2n+2)/4^n`$ is sufficient for $`|\Delta_n|>H`$. Conversely, $`|\Delta_n|>H`$ implies $`|\sum_{d\in\mathrm{Skip}_n}x_d-C|>(H-2n-2)/4^n`$. Thus a square-root-exponential deviation corresponds to a separation of order $`2^{-3n/2}`$, with the displayed additive error retained. This is not an exact equivalence after simply discarding that error. *real approximation and integer remainder* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Math\]</span>\
> **Note:** $`C = E - 3/2`$ is Mersenne-specific, but the shape “scaled deviation $`=`$ $`4^n \cdot`$(finite skip-sum $`-`$ target constant) $`+ O(n)`$” is a template, not yet matched to any analogous constant on the \#249 side.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_core`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/QuotientRowReal.lean#L84)

```lean
theorem paper_real_quotient_core {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    ∃ eta : ℝ,
      (rowDeviation n D : ℝ) = (4 : ℝ)^n *
        ((∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) -
          (erdosBorweinMersenneConstant-3/2)) + eta ∧
      0 < eta ∧ eta < (n : ℝ)+2/3 ∧ |eta| < 2*(n : ℝ)+2
```

2. [`ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_margins`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/QuotientRowReal.lean#L103)

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

3. [`ErdosProblems.Erdos257.PaperCompleteR20.row_constant_eq_tail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/QuotientRowReal.lean#L94)

```lean
theorem row_constant_eq_tail :
    erdosBorweinMersenneConstant-3/2 = mersenneTail 1-1/2
```

4. [`ErdosProblems.Erdos257.PaperCompleteR20.mersenne_constant_decimal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/MersenneConstantDecimal.lean#L8)

```lean
theorem mersenne_constant_decimal :
    (1066951524152917 : ℝ)/10^16 < erdosBorweinMersenneConstant-3/2 ∧
      erdosBorweinMersenneConstant-3/2 < (1066951524152918 : ℝ)/10^16
```

<a id="thm-real-form-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_real_quotient_core` | [E257_05/Challenge.lean, line 172](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L172) | [PaperStatementsAR.lean, line 211](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAR.lean#L211) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |
| `paper_real_quotient_margins` | [E257_05/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L181) | [PaperStatementsAR.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAR.lean#L219) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |
| `row_constant_eq_tail` | [E257_05/Challenge.lean, line 102](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L102) | [PaperStatementsAM.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAM.lean#L140) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |
| `mersenne_constant_decimal` | [E257_05/Challenge.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L91) | [PaperStatementsAM.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAM.lean#L122) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-dynamics"></a>

## Theorem (Exact recurrences for the three branches)

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
> ```
> *integer quotient recurrences*<span class="sans-serif">(uniform)</span><span class="sans-serif">\[Math\]</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_dynamics`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L424)

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

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowLower_existsUnique`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L398)

```lean
theorem paper_rowLower_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! D : Finset ℕ, IsRowLower n D
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowUpper_existsUnique`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L404)

```lean
theorem paper_rowUpper_existsUnique {n : ℕ} (hn : 5 ≤ n) :
    ∃! B : Finset ℕ, IsRowUpper n B
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_isRowLower`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L279)

```lean
theorem paper_greedySupport_isRowLower {n : ℕ} (hn : 5 ≤ n) :
    IsRowLower n (greedySupport n)
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_upperSupport_isRowUpper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L364)

```lean
theorem paper_upperSupport_isRowUpper {n : ℕ} (hn : 5 ≤ n) :
    IsRowUpper n (rowSupport n (seamAboveWord n hn))
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowLower_unique`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L379)

```lean
theorem paper_isRowLower_unique {n : ℕ} (hn : 5 ≤ n) {D D₀ : Finset ℕ}
    (hD : IsRowLower n D) (hD₀ : IsRowLower n D₀) : D = D₀
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_isRowUpper_unique`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L388)

```lean
theorem paper_isRowUpper_unique {n : ℕ} (hn : 5 ≤ n) {B B₀ : Finset ℕ}
    (hB : IsRowUpper n B) (hB₀ : IsRowUpper n B₀) : B = B₀
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_greedy_rule`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L301)

```lean
theorem paper_greedySupport_greedy_rule {n : ℕ} (hn : 5 ≤ n) {d : ℕ}
    (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔
      truncatedMersenneWeight n d +
          ∑ e ∈ (greedySupport n).filter (fun e => e < d),
            truncatedMersenneWeight n e ≤ seamSubsetTarget n
```

9. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_mem`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L254)

```lean
theorem paper_greedySupport_mem {n d : ℕ} (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔ seamGreedyWord n ⟨d - 2, by omega⟩ = true
```

10. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_greedy_step`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L244)

```lean
theorem paper_greedy_step {n d : ℕ} (hd : d < n) (C : ℕ) :
    integerGreedyBits (seamWeightsFrom n d) C =
      (decide (truncatedMersenneWeight n d ≤ C)) ::
        integerGreedyBits (seamWeightsFrom n (d + 1))
          (if truncatedMersenneWeight n d ≤ C then
            C - truncatedMersenneWeight n d else C)
```

11. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_consecutive_not_both_divisible`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L69)

```lean
theorem paper_consecutive_not_both_divisible {d m : ℕ} (hd : 2 ≤ d) :
    ¬ (d ∣ m + 1 ∧ d ∣ m + 2)
```

12. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowPulse_eq_indicators`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L50)

```lean
theorem paper_rowPulse_eq_indicators (n d : ℕ) :
    rowPulse n d =
      2 * (if d ∣ 2 * n + 1 then 1 else 0) +
        (if d ∣ 2 * n + 2 then 1 else 0)
```

13. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowQuotient_eq_weightSum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L58)

```lean
theorem paper_rowQuotient_eq_weightSum (n : ℕ) (S : Finset ℕ) :
    localPrefixQuotient S (2 * n) = ∑ d ∈ S, truncatedMersenneWeight n d
```

14. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowWeight_eq_floor`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L41)

```lean
theorem paper_rowWeight_eq_floor (n d : ℕ) :
    truncatedMersenneWeight n d = 4 ^ n / (2 ^ d - 1)
```

15. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_rowTarget_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ThreeBranchRowDynamics.lean#L45)

```lean
theorem paper_rowTarget_eq (n : ℕ) :
    seamSubsetTarget n = 2 ^ (2 * n - 1) - 2 ^ n
```

<a id="thm-dynamics-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-fatal-absorbing"></a>

## Theorem (Infinitely many greedy skips force membership)

> *Fix $`x\ge0`$. If $`r_n(x)>R_n`$ at some rank $`n`$, every later rank is selected and $`r_{n+k}(x)>R_{n+k}`$ for every $`k\ge0`$. Consequently, infinitely many omitted positive ranks imply $`x\in\mathcal A`$.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(cofinal)</span>*greedy recurrence* [`mem_mersenneAchievementSet_of_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1528)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.fatal_absorbing`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L27)

```lean
theorem fatal_absorbing {x : ℝ} (hx : 0 ≤ x) :
    (∀ n : ℕ, mersenneTail n < greedyMersenneRemainder x n →
        (∀ k : ℕ, n + k + 1 ∈ greedyMersenneSupport x) ∧
          ∀ k : ℕ, mersenneTail (n + k) < greedyMersenneRemainder x (n + k)) ∧
      ((greedyMersenneSkippedSupport x).Infinite → x ∈ mersenneAchievementSet)
```

<a id="thm-fatal-absorbing-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `fatal_absorbing` | [E257_07/Challenge.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_07/Challenge.lean#L65) | [PaperStatementsN.lean, line 135](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_07/PaperStatementsN.lean#L135) | [E257_07](../evidence/comparator/replay-35882032091/receipt-E257_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-seam-limit"></a>

## Theorem (The quotient remainders converge to the greedy deficit)

> *Let $`G`$ be the real greedy support for $`1/2`$, and let $`D_s`$ be the integer-greedy support at row $`s`$. Then
> ``` math
> X_{D_s}(2)\longrightarrow X_G(2),\qquad
>  \frac{\mathrm{rem}(s)}{4^s}\longrightarrow
>  \delta:=\frac12-X_G(2)\ge0.
> ```
> In particular, the following conditions are equivalent: $`1/2\in\mathcal A`$; the full sequence $`\mathrm{rem}(s)/4^s`$ tends to zero; and there exist $`s_j\to\infty`$ with $`\mathrm{rem}(s_j)/4^{s_j}\to0`$.*
> 
> *<span class="sans-serif">\[Math\]</span><span class="sans-serif">(cofinal)</span>*integer quotients**

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_limit_unconditional`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L560)

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

2. [`ErdosProblems.Erdos257.PaperCompleteR21.tendsto_seamGreedyFiniteValue_greedyHalfTargetValue`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L438)

```lean
theorem tendsto_seamGreedyFiniteValue_greedyHalfTargetValue :
    Tendsto seamGreedyFiniteValue atTop (nhds greedyHalfTargetValue)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.tendsto_seamGreedyNormalizedRemainder`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L537)

```lean
theorem tendsto_seamGreedyNormalizedRemainder :
    Tendsto seamGreedyNormalizedRemainder atTop (nhds seamGreedyLimitDeficit)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.eventually_seamSupport_agrees`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L370)

```lean
theorem eventually_seamSupport_agrees (K : ℕ) :
    ∀ᶠ s in atTop, ∀ d : ℕ, 1 ≤ d → d ≤ K →
      (d ∈ seamWordSupport (seamGreedyWord s)
        ↔ d ∈ greedyMersenneSupport (1 / 2 : ℝ))
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.seamScaledRem_eq_tailGreedyRemainder`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L259)

```lean
theorem seamScaledRem_eq_tailGreedyRemainder {s : ℕ} (hs : 2 ≤ s) :
    ∀ m : ℕ, m ≤ s - 2 →
      ((seamIntRem s m : ℕ) : ℝ) / (4 : ℝ) ^ s
        = tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) m
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.mem_seamGreedySupport_iff_scaled`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L332)

```lean
theorem mem_seamGreedySupport_iff_scaled {s d : ℕ} (hs : 2 ≤ s) (h2 : 2 ≤ d)
    (hd : d < s) :
    d ∈ seamWordSupport (seamGreedyWord s)
      ↔ seamScaledWeight s d
          ≤ tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) (d - 2)
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.abs_supportValue_sub_le_mersenneTail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamPrefixStabilityLimit.lean#L398)

```lean
theorem abs_supportValue_sub_le_mersenneTail {A B : Set ℕ} {K : ℕ}
    (h : ∀ d : ℕ, 1 ≤ d → d ≤ K → (d ∈ A ↔ d ∈ B)) :
    |positiveMersenneSupportValue A - positiveMersenneSupportValue B|
      ≤ mersenneTail K
```

<a id="thm-seam-limit-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_seam_limit_unconditional` | [E257_10/Challenge.lean, line 301](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_10/Challenge.lean#L301) | [PaperStructuresBL.lean, line 84](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_10/PaperStructuresBL.lean#L84) | [E257_10](../evidence/comparator/replay-35882032091/receipt-E257_10.json) |
| `tendsto_seamGreedyFiniteValue_greedyHalfTargetValue` | [E257_10/Challenge.lean, line 321](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_10/Challenge.lean#L321) | [PaperStructuresBL.lean, line 105](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_10/PaperStructuresBL.lean#L105) | [E257_10](../evidence/comparator/replay-35882032091/receipt-E257_10.json) |
| `tendsto_seamGreedyNormalizedRemainder` | [E257_10/Challenge.lean, line 325](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_10/Challenge.lean#L325) | [PaperStructuresBL.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_10/PaperStructuresBL.lean#L110) | [E257_10](../evidence/comparator/replay-35882032091/receipt-E257_10.json) |
| `eventually_seamSupport_agrees` | [E257_09/Challenge.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_09/Challenge.lean#L128) | [PaperStructuresBJ.lean, line 1379](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_09/PaperStructuresBJ.lean#L1379) | [E257_09](../evidence/comparator/replay-35882032091/receipt-E257_09.json) |
| `seamScaledRem_eq_tailGreedyRemainder` | [E257_11/Challenge.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_11/Challenge.lean#L83) | [PaperStructuresBV.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_11/PaperStructuresBV.lean#L219) | [E257_11](../evidence/comparator/replay-35882032091/receipt-E257_11.json) |
| `mem_seamGreedySupport_iff_scaled` | [E257_08/Challenge.lean, line 328](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_08/Challenge.lean#L328) | [PaperStructuresBB.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_08/PaperStructuresBB.lean#L103) | [E257_08](../evidence/comparator/replay-35882032091/receipt-E257_08.json) |
| `abs_supportValue_sub_le_mersenneTail` | [E257_07/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_07/Challenge.lean#L81) | [PaperStatementsAM.lean, line 143](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_07/PaperStatementsAM.lean#L143) | [E257_07](../evidence/comparator/replay-35882032091/receipt-E257_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-two-channel-cap"></a>

## Theorem (Two-channel and dyadic cap sufficiency)

> *Suppose that for every $`n\ge0`$ at which the next weight is skipped,
> ``` math
> w_{n+1}>r_n(1/2)\quad\Longrightarrow\quad
>  r_n(1/2)\le 2^{-(n+1)}+\frac13\,4^{-(n+1)}.
> ```
> Then $`1/2\in\mathcal A`$. The stronger bound $`r_n(1/2)\le2^{-(n+1)}`$ at the same skipped ranks also suffices. The first bound retains two positive geometric terms of the full tail; it is larger, and hence less restrictive, than the second. Both are sufficient tests on the specified greedy orbit. The result does not assert that either bound holds at all its skipped ranks.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*two-channel-dyadic-cap* [`half_mem_mersenneAchievementSet_of_skipped_twoChannelCap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1425) [`half_mem_mersenneAchievementSet_of_skipped_dyadicCap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1444)*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_skipped_twoChannelCap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L1425)

```lean
theorem half_mem_mersenneAchievementSet_of_skipped_twoChannelCap
    (hskip : ∀ n : ℕ,
      ¬ mersenneWeight (n + 1)
          ≤ greedyMersenneRemainder (1 / 2 : ℝ) n →
      greedyMersenneRemainder (1 / 2 : ℝ) n
          ≤ halfTwoChannelCap (n + 1)) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_of_skipped_dyadicCap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L1444)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `half_mem_mersenneAchievementSet_of_skipped_twoChannelCap` | [E257_11/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_11/Challenge.lean#L159) | [PaperStatementsB.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_11/PaperStatementsB.lean#L67) | [E257_11](../evidence/comparator/replay-35882032091/receipt-E257_11.json) |
| `half_mem_mersenneAchievementSet_of_skipped_dyadicCap` | [E257_11/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_11/Challenge.lean#L150) | [PaperStatementsB.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_11/PaperStatementsB.lean#L57) | [E257_11](../evidence/comparator/replay-35882032091/receipt-E257_11.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-second-channel"></a>

## Theorem (Second-channel phase separation sufficiency)

> *Define $`P_n=4^n\bigl(2r_n(1/2)-2^{-n}\bigr)`$. If
> ``` math
> \frac16+\frac{37}{56}\,2^{-n}\le
>  \left|P_n-\frac13\right|\qquad\text{for every }n\ge1,
> ```
> then $`1/2\in\mathcal A`$. These are exact rational inequalities because the target and every finite greedy remainder are rational. The cited finite calculation establishes them for $`1\le n\le6`$; it therefore suffices to prove them for every $`n\ge7`$.*
> 
> *Unlike Theorem <a href="#thm:two-channel-cap" data-reference-type="ref" data-reference="thm:two-channel-cap">46</a>, this hypothesis concerns every positive rank, not only skipped ranks. It excludes an explicit interval around $`1/3`$. For example, $`P_n\notin(0,1)`$ implies the displayed inequality when $`n\ge2`$, but no such avoidance theorem for the whole orbit is proved here.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*second-channel-phase* [`half_mem_mersenneAchievementSet_of_secondChannelSeparation`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L3118) [`half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L3151)*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L3118)

```lean
theorem half_mem_mersenneAchievementSet_of_secondChannelSeparation
    (hseparate : ∀ n : ℕ, 0 < n →
      (1 / 6 : ℝ) + (37 / 56 : ℝ) * ((1 : ℝ) / 2) ^ n
        ≤ |greedyMersenneSecondChannelPhase n - 1 / 3|) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L3151)

```lean
theorem half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven
    (hseparate : ∀ n : ℕ, 7 ≤ n → HalfSecondChannelSeparatedRat n) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="thm-second-channel-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `half_mem_mersenneAchievementSet_of_secondChannelSeparation` | [E257_11/Challenge.lean, line 138](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_11/Challenge.lean#L138) | [PaperStatementsB.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_11/PaperStatementsB.lean#L43) | [E257_11](../evidence/comparator/replay-35882032091/receipt-E257_11.json) |
| `half_mem_mersenneAchievementSet_of_secondChannelSeparationRat_from_seven` | [E257_11/Challenge.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_11/Challenge.lean#L145) | [PaperStatementsB.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_11/PaperStatementsB.lean#L51) | [E257_11](../evidence/comparator/replay-35882032091/receipt-E257_11.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-straddle-closed-set"></a>

## Theorem (Straddle-prefix closed-set criterion)

> *Suppose that for every $`d\ge0`$ there is a finite support $`D_d\subseteq\{1,\ldots,d\}`$ such that
> ``` math
> X_{D_d}(2)\le t\le X_{D_d}(2)+R_d.
> ```
> Then $`t\in\mathcal A`$. The supports need not agree at different depths: compactness, together with $`R_d\to0`$, supplies a limiting support. Conversely, truncating a support representing $`t`$ supplies such finite supports. Thus this condition is an exact finite-approximation formulation of membership, not a criterion already known to hold for an unresolved target.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*dedekind-cut* [`mem_mersenneAchievementSet_of_straddle_all_depths`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L173)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.straddle_all_depths_iff_mem`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L42)

```lean
theorem straddle_all_depths_iff_mem (t : ℝ) :
    (∀ d : ℕ, ∃ D : Finset ℕ, (∀ n ∈ D, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑D : Set ℕ) ≤ t ∧
        t ≤ positiveMersenneSupportValue (↑D : Set ℕ) + mersenneTail d) ↔
      t ∈ mersenneAchievementSet
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.straddle_limiting_support_inputs`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L103)

```lean
theorem straddle_limiting_support_inputs :
    IsCompact mersenneAchievementSet ∧
      Filter.Tendsto mersenneTail Filter.atTop (nhds 0)
```

<a id="thm-straddle-closed-set-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `straddle_all_depths_iff_mem` | [E257_11/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_11/Challenge.lean#L180) | [PaperStatementsAM.lean, line 254](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_11/PaperStatementsAM.lean#L254) | [E257_11](../evidence/comparator/replay-35882032091/receipt-E257_11.json) |
| `straddle_limiting_support_inputs` | [E257_11/Challenge.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_11/Challenge.lean#L187) | [PaperStatementsAM.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_11/PaperStatementsAM.lean#L260) | [E257_11](../evidence/comparator/replay-35882032091/receipt-E257_11.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-largest-skip-late"></a>

## Theorem (Keeping the largest skipped rank beyond two thirds)

> *Let $`D_s\subseteq\{2,\ldots,s-1\}`$ be the support of the integer-greedy row defined in Section <a href="#ssec:seam-model" data-reference-type="ref" data-reference="ssec:seam-model">5.4</a>. Assume the following implication for every $`s\ge14`$ and every largest omitted rank $`d=\max(\{2,\ldots,s-1\}\smallsetminus D_s)`$:
> ``` math
> 2s<3d\quad\Longrightarrow\quad
>  2(s+1)<3d\quad\text{or}\quad s\notin D_{s+1}.
> ```
> Then $`1/2\in\mathcal A`$. The hypothesis says that either the same omitted rank remains beyond two thirds of the next row, or the next row omits its terminal rank. The latter alternative is exactly an upper or middle transition in the preceding classification.*
> 
> *The cited finite calculation establishes the initial inequality at row $`14`$. The displayed implication then preserves the inequality by induction and supplies omitted ranks tending to infinity. It is an unproved condition on every later row; the verified base case alone does not establish it.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*integer quotients* [`half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderLargestSkipInduction.lean#L167) [`largestSkipLateAt_fourteen`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderLargestSkipInduction.lean#L73)*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderLargestSkipInduction.lean#L167)

```lean
theorem half_mem_mersenneAchievementSet_of_largestSkipLateStepSocket
    (hstep : LargestSkipLateStepSocket) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.largestSkipLateAt_fourteen`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderLargestSkipInduction.lean#L73)

```lean
theorem largestSkipLateAt_fourteen : LargestSkipLateAt 14
```

where [`LargestSkipLateAt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderLargestSkipInduction.lean#L27) is

```lean
def LargestSkipLateAt (s : ℕ) : Prop :=
  ∃ d : ℕ,
    IsLargestFalseRank (seamGreedyWord s) d ∧ 2 * s < 3 * d
```

3. [`Erdos249257.seamGreedy_terminal_false_iff_upperOrMiddle`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L57)

```lean
theorem seamGreedy_terminal_false_iff_upperOrMiddle
    (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = false ↔
      SeamGreedyUpperOrMiddleAt s hs
```

<a id="thm-largest-skip-late-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-middle-producer-escape"></a>

## Theorem (Two sufficient bounds at middle transitions)

> *Suppose that at every middle transition with row $`s\ge13`$,
> ``` math
> |D_s|+p_s^-+5<4\,\mathrm{rem}(s).
> ```
> Then $`1/2\in\mathcal A`$. The stronger condition $`\mathrm{rem}(s)\ge s`$ at all such rows also suffices.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*integer quotients* [`half_mem_mersenneAchievementSet_of_middleProducerCardEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2364) [`half_mem_mersenneAchievementSet_of_middleProducerRowEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2371)*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerCardEscape`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2364)

```lean
theorem half_mem_mersenneAchievementSet_of_middleProducerCardEscape
    (hcard : SeamMiddleProducerCardEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_of_middleProducerRowEscape`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2371)

```lean
theorem half_mem_mersenneAchievementSet_of_middleProducerRowEscape
    (hrow : SeamMiddleProducerRowEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="thm-middle-producer-escape-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-middle-allright-defect"></a>

## Theorem (The tail inequality at a final middle transition)

> *Suppose row $`D\ge13`$ is middle and all rows after it are right. Let $`F_D=D_D\cup\{D\}`$ and put
> ``` math
> C_D=4\,\mathrm{rem}(D)-p_D^--4,\qquad
>  \Theta_D=\sum_{j\ge1}c_{F_D}(2D+2+j)2^{-j}.
> ```
> Then $`C_D<\Theta_D`$. Since $`0\le\Theta_D\le|F_D|`$, an estimate in the opposite direction would exclude this scenario. No such reverse estimate is assumed or proved here. Remark <a href="#rem:tail-dominance-open" data-reference-type="ref" data-reference="rem:tail-dominance-open">260</a> states the corresponding sufficient hypothesis with the value $`-3`$ excepted.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*integer quotients* [`middleProducer_allRight_forces_carry_lt_tail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1814) [`middleProducer_allRight_forces_rational_skip`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1888)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.middleProducer_allRight_forces_carry_lt_tail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1814)

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

2. [`Erdos249257.middleProducer_allRight_forces_rational_skip`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1888)

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

3. [`Erdos249257.producerCarry_insert_seamBelowSupport_eq_middleCoordinate`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderProducerLowerBound.lean#L150)

```lean
theorem producerCarry_insert_seamBelowSupport_eq_middleCoordinate
    (s : ℕ) (hs : 5 ≤ s) :
    producerCarry
        (insert s
          (↑(seamWordSupport (seamAdjacentCut s hs).below) : Set ℕ)) s =
      4 * ((seamAdjacentCut s hs).remainder : ℤ) -
        ((seamAdjacentCut s hs).belowPulse : ℤ) - 4
```

4. [`Erdos249257.binaryCoeffTail_nonneg`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L78)

```lean
theorem binaryCoeffTail_nonneg (c : ℕ → ℕ) (N : ℕ) :
    0 ≤ binaryCoeffTail c N
```

5. [`Erdos249257.binaryCoeffTail_supportCoeff_coe_finset_le_card`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L222)

```lean
theorem binaryCoeffTail_supportCoeff_coe_finset_le_card
    (F : Finset ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff (↑F : Set ℕ)) N ≤ (F.card : ℝ)
```

<a id="thm-middle-allright-defect-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-two-sided-dyadic"></a>

## Theorem (A conditional two-sided dyadic bound)

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
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*integer quotients* [`SeamTwoSidedDyadicCellEscape.twoSided`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4448) [`seamTwoSidedDyadicAt_five`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4431)*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.SeamTwoSidedDyadicCellEscape.twoSided`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4448)

```lean
theorem SeamTwoSidedDyadicCellEscape.twoSided
    (hescape : SeamTwoSidedDyadicCellEscape)
    (s : ℕ) (hs : 5 ≤ s) :
    seamIntegerGreedyRemainder s ≤ 2 ^ s ∨
      (seamAdjacentCut s hs).overshoot ≤ 2 ^ s
```

<a id="thm-two-sided-dyadic-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `twoSided` | [E257_08/Challenge.lean, line 302](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_08/Challenge.lean#L302) | [PaperStructuresBB.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_08/PaperStructuresBB.lean#L81) | [E257_08](../evidence/comparator/replay-35882032091/receipt-E257_08.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-upper-reset-band"></a>

## Theorem (Upper-reset dyadic-band escape, checked for $`13\le d\le30`$)

> **SeamUpperResetDyadicBandEscape* requires the following at every actual upper reset $`d\ge13`$: for every $`0\le j\le d`$, the reset charge avoids a linear-width band immediately below the dyadic power $`2^{d-j+1}`$ ($`2^{d-j+1}<\mathrm{resetCharge}`$ or $`\mathrm{resetCharge}+2(d+j)\le 2^{d-j+1}`$). Granted this, $`1/2\in
> \ensuremath{\mathcal A}`$. The linked proof verifies this condition for $`13\le d\le30`$, using exact successor remainders at rows $`14`$–$`31`$ (for example, $`\mathrm{rem}(14)=392`$ and $`\mathrm{rem}(31)=4187487147`$). This finite verification does not supply the hypothesis for every $`d\ge13`$.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*dyadic-boundary* [`half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4790) [`seamUpperResetDyadicBandEscape_through_thirty`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderUpperResetBandCertificates.lean#L78)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4790)

```lean
theorem half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape
    (hband : SeamUpperResetDyadicBandEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.seamUpperResetDyadicBandEscape_through_thirty`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderUpperResetBandCertificates.lean#L78)

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

<a id="thm-upper-reset-band-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-mobius-centred-nonneg"></a>

## Theorem (Möbius-centred carry nonnegativity below $`1/2`$)

> *If $`1\notin A`$ and $`X_A(2)<1/2`$, then $`C_A(N)\ge0`$ for every $`N`$. Indeed,
> ``` math
> \operatorname{ihc}(A,N)=2^{N+1}(1/2-X_A(2))+
>  \sum_{j>N+1}c_A(j)2^{N+1-j}>0.
> ```
> The carry is an integer, so it is at least $`1`$; subtracting $`1`$ gives the asserted nonnegativity of the centred carry. The strict inequality and integrality are both needed in this argument. The statement is about the divisor counts $`c_A`$, not a new irrationality criterion.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*divisor counts and finite sums* [`mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L94) [`integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L871)*

The Lean declarations below together state this result.

1. [`Erdos249257.mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L94)

```lean
theorem mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
    (A : Set ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry A N
```

2. [`Erdos249257.HalfCarryReachability.integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCarryReachability.lean#L871)

```lean
theorem integerHalfCarry_eq_scaled_residual_add_tail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (integerHalfCarry A N : ℝ) =
      (2 : ℝ) ^ (N + 1) * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) +
        binaryCoeffTail (supportCoeff A) (N + 1)
```

<a id="thm-mobius-centred-nonneg-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half` | [E257_13/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L111) | [PaperStatementsI.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsI.lean#L34) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |
| `integerHalfCarry_eq_scaled_residual_add_tail` | [E257_03/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L99) | [PaperStatementsE.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsE.lean#L35) | [E257_03](../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-sqrt-bound-route"></a>

## Theorem (A square-root bound on the greedy carry)

> *For the greedy support $`G=G_{1/2}`$, the centred carry is nonnegative. If in addition
> ``` math
> C_G(N)\le2\sqrt N+4\qquad\text{for every }N\ge0,
> ```
> then $`G`$ has infinitely many skipped indices and $`X_G(2)=1/2`$. The unresolved part is the upper bound along this particular orbit. The carry identity explains its strength: a positive gap $`1/2-X_G(2)`$ would contribute a term of order $`2^N`$, which cannot satisfy a square-root bound. This is distinct from the reset-deviation hypothesis of Theorem <a href="#thm:upper-reset-band" data-reference-type="ref" data-reference="thm:upper-reset-band">53</a>; no equivalence between the two hypotheses is asserted.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*greedy recurrence* [`greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L834) [`infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L817)*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfCarryReachability.greedy_mobiusCenteredHalfCarry_nonneg`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCarryReachability.lean#L919)

```lean
theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N
```

2. [`Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCarryReachability.lean#L834)

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

3. [`Erdos249257.HalfCarryReachability.infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCarryReachability.lean#L817)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `greedy_mobiusCenteredHalfCarry_nonneg` | [E257_13/Challenge.lean, line 144](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L144) | [PaperStatementsD.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsD.lean#L139) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |
| `greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound` | [E257_13/Challenge.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L131) | [PaperStatementsD.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsD.lean#L114) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |
| `infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound` | [E257_13/Challenge.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L155) | [PaperStatementsE.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsE.lean#L25) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-frozen-margin"></a>

## Theorem (Equivalent sign and vanishing conditions)

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
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*integer quotients* [`half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L633) [`skippedSeamAlignmentZero_iff_skippedFullShellNonnegative`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L671) [`half_mem_mersenneAchievementSet_of_skippedSeamEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L722)*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L633)

```lean
theorem half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative
    (hsign : HalfGreedySkippedFullShellNonnegative) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`Erdos249257.skippedSeamAlignmentZero_iff_skippedFullShellNonnegative`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L671)

```lean
theorem skippedSeamAlignmentZero_iff_skippedFullShellNonnegative :
    HalfGreedySkippedSeamAlignmentZero ↔
      HalfGreedySkippedFullShellNonnegative
```

3. [`Erdos249257.half_mem_mersenneAchievementSet_of_skippedSeamEscape`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L722)

```lean
theorem half_mem_mersenneAchievementSet_of_skippedSeamEscape
    (hescape : HalfGreedySkippedSeamEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="thm-frozen-margin-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `half_mem_mersenneAchievementSet_of_skippedFullShellNonnegative` | [E257_13/Challenge.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L174) | [PaperStatementsF.lean, line 185](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsF.lean#L185) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |
| `skippedSeamAlignmentZero_iff_skippedFullShellNonnegative` | [E257_13/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L260) | [PaperStructuresBJ.lean, line 1313](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStructuresBJ.lean#L1313) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |
| `half_mem_mersenneAchievementSet_of_skippedSeamEscape` | [E257_13/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L255) | [PaperStructuresBJ.lean, line 1294](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStructuresBJ.lean#L1294) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-full-support-catalogue"></a>

## Theorem (Erdős–Borwein full-support irrationality, unconditional)

> *For every integer $`b\ge2`$, the sum $`\sum_{n\ge1}(b^n-1)^{-1}`$ is irrational. This is Erdős’s theorem \[erdos1948\]; at base $`2`$ the sum is the Erdős–Borwein constant. The result concerns full support, not all its infinite subsets.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*divisor counts and finite sums* [`irrational_erdosSum_full_support`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L8328) [`irrational_erdosBorwein_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L8335)*

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSum_full_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L8328)

```lean
theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1))
```

<a id="thm-full-support-catalogue-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSum_full_support` | [E257_05/Challenge.lean, line 48](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L48) | [PaperStatementsAG.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L52) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-pairwise-coprime"></a>

## Theorem (Pairwise-coprime support irrationality, Erdős 1968)

> *For every integer $`b\ge2`$ and every infinite pairwise-coprime support $`A\subseteq\mathbb{N}_{>0}`$ with summable reciprocals, $`\sum_{a\in A} 1/(b^a-1)`$ is irrational.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*divisor counts and finite sums* [`irrational_erdosSupportSeries_pairwise_coprime`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L10776)*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.irrational_erdosSupportSeries_pairwise_coprime`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L10776)

```lean
theorem irrational_erdosSupportSeries_pairwise_coprime (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (hA : A.Infinite) (hpair : A.Pairwise Nat.Coprime)
    (hsum : Summable (Set.indicator A fun a : ℕ => (1 : ℝ) / a)) :
    Irrational (erdosSupportSeries b A)
```

<a id="thm-pairwise-coprime-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSupportSeries_pairwise_coprime` | [E257_13/Challenge.lean, line 292](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L292) | [PaperStatementsAG.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsAG.lean#L81) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-weighted-coeff-engine"></a>

## Theorem (Irrationality from divisible coefficient blocks)

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
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*binary digits* [`irrational_coeff_series_of_weighted_coeff_block_certificates`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L8665)*

The Lean declaration below states this result.

[`Erdos249257.irrational_coeff_series_of_weighted_coeff_block_certificates`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L8665)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_coeff_series_of_weighted_coeff_block_certificates` | [E257_13/Challenge.lean, line 271](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L271) | [PaperStatementsAG.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsAG.lean#L40) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-lcm-gap-engine"></a>

## Theorem (Irrationality from a gap beyond the preceding least common multiple)

> *For an integer base $`b\ge2`$ and strictly increasing support $`a:\mathbb N\to\mathbb N`$ with $`a(0)\ge
> 1`$: if $`a(k)-\mathrm{lcm}(a(0),\dots,a(k-1))\to\infty`$, then $`\sum'_k 1/(b^{a(k)}-1)`$ is irrational. The base may vary over the integers, but the denominators remain $`b^{a(k)}-1`$. Applying the argument to another denominator sequence would require its own divisibility and tail estimates.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*lcm-gap* [`irrational_erdosSum_of_lcm_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5883)*

The Lean declaration below states this result.

[`Erdos249257.irrational_erdosSum_of_lcm_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L5883)

```lean
theorem irrational_erdosSum_of_lcm_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (hgap : Tendsto (fun k => a k - ((Finset.range k).image a).lcm id)
      atTop atTop) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1))
```

<a id="thm-lcm-gap-engine-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSum_of_lcm_gap` | [E257_13/Challenge.lean, line 285](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L285) | [PaperStatementsAG.lean, line 55](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsAG.lean#L55) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-factorial-twopow-support"></a>

## Theorem (Factorial-support and $`2^k`$-support instances)

> *For every integer $`b\ge2`$, both
> ``` math
> \sum_{k\ge0}\frac1{b^{(k+1)!}-1}
>  \quad\text{and}\quad
>  \sum_{k\ge0}\frac1{b^{2^k}-1}
> ```
> are irrational. These are instances of the preceding theorem. For the factorial support the preceding least common multiple is $`k!`$ when $`k\ge1`$, so the gap is $`k\,k!`$. For the powers of two it is $`2^{k-1}`$, so the gap is $`2^{k-1}`$. Both tend to infinity. The conclusion concerns these two supports, not every infinite support.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*lcm-gap* [`irrational_erdosSum_factorial_support`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6035) [`irrational_erdosSum_two_pow_support`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6059)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.irrational_erdosSum_factorial_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L6035)

```lean
theorem irrational_erdosSum_factorial_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (Nat.factorial (k + 1)) - 1))
```

2. [`Erdos249257.irrational_erdosSum_two_pow_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L6059)

```lean
theorem irrational_erdosSum_two_pow_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (2 ^ k) - 1))
```

<a id="thm-factorial-twopow-support-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSum_factorial_support` | [E257_13/Challenge.lean, line 281](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L281) | [PaperStatementsAG.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsAG.lean#L49) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |
| `irrational_erdosSum_two_pow_support` | [E257_14/Challenge.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L44) | [PaperStatementsAG.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAG.lean#L54) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-multiples-support"></a>

## Theorem (Multiples-support irrationality via dilation)

> *For integers $`b\ge2`$ and $`d\ge1`$,
> ``` math
> X_{d\mathbb{N}_{>0}}(b)=\sum_{k\ge1}\frac1{(b^d)^k-1}
> ```
> is irrational. This is the full-support result (Theorem <a href="#thm:full-support-catalogue" data-reference-type="ref" data-reference="thm:full-support-catalogue">57</a>) at the integer base $`b^d`$; no new support argument is required.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*dilation* [`irrational_erdosSupportSeries_multiples`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L9103) [`erdosSupportSeries_multiples_eq_pow_base_full_support`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L9054)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.erdosSupportSeries_multiples_eq_pow_base_full_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L9054)

```lean
theorem erdosSupportSeries_multiples_eq_pow_base_full_support
    (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    erdosSupportSeries b {n : ℕ | d ∣ n}
      = ∑' k : ℕ, (1 : ℝ) / (((b : ℝ) ^ d) ^ (k + 1) - 1)
```

2. [`Erdos249257.irrational_erdosSupportSeries_multiples`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L9103)

```lean
theorem irrational_erdosSupportSeries_multiples (b d : ℕ) (hb : 2 ≤ b) (hd : 1 ≤ d) :
    Irrational (erdosSupportSeries b {n : ℕ | d ∣ n})
```

<a id="thm-multiples-support-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `erdosSupportSeries_multiples_eq_pow_base_full_support` | [E257_14/Challenge.lean, line 38](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L38) | [PaperStatementsAG.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAG.lean#L28) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `irrational_erdosSupportSeries_multiples` | [E257_14/Challenge.lean, line 48](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L48) | [PaperStatementsAG.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAG.lean#L64) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-periodic-support"></a>

## Theorem (Periodic-support irrationality)

> *Let $`b\ge2`$ and $`m\ge1`$ be integers. Suppose $`A\subseteq\mathbb{N}_{>0}`$ is nonempty and satisfies $`n\in A`$ if and only if $`n+m\in A`$ for every $`n\ge1`$. Then $`X_A(b)`$ is irrational.*
> 
> *The indicator of $`A`$ is a nonzero purely periodic integer weight, so this follows from Luca and Tachiya’s theorem stated above. The linked declaration supplies a separate formal proof. At $`m=1`$ the only nonempty periodic support is full support; residue classes and unions of residue classes give the other immediate examples.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*periodic-sieve* [`irrational_erdosSupportSeries_periodic`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L11590)*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.irrational_erdosSupportSeries_periodic`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L11590)

```lean
theorem irrational_erdosSupportSeries_periodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, n + m ∈ A ↔ n ∈ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A)
```

<a id="thm-periodic-support-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSupportSeries_periodic` | [E257_05/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L63) | [PaperStatementsAG.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L86) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-eventually-periodic"></a>

## Theorem (Eventually-periodic support irrationality)

> *Let $`b\ge2`$ and $`m\ge1`$ be integers. An infinite support whose membership is $`m`$-periodic from some threshold $`N_0`$ onward has irrational $`X_A(b)`$.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*periodic-sieve* [`irrational_erdosSupportSeries_eventuallyPeriodic`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L11604)*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.irrational_erdosSupportSeries_eventuallyPeriodic`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L11604)

```lean
theorem irrational_erdosSupportSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → (n + m ∈ A ↔ n ∈ A))
    (hinf : A.Infinite) :
    Irrational (erdosSupportSeries b A)
```

<a id="thm-eventually-periodic-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSupportSeries_eventuallyPeriodic` | [E257_05/Challenge.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L52) | [PaperStatementsAG.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L64) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-residue-odd"></a>

## Theorem (Residue-class and odd-support irrationality)

> *For integers $`b\ge2`$, $`m\ge1`$ and a residue $`c`$, $`\sum_{\substack{n\ge1\\n\equiv c\pmod m}}(b^n-1)^{-1}`$ is irrational. Specializing $`m=2,c=1`$: $`\sum_{n\text{ odd}} 1/(b^n-1)`$ is irrational for every $`b\ge 2`$, the case treated explicitly in \[lucatachiya2017, Example 2, p. 140\].*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*periodic-sieve* [`irrational_erdosSupportSeries_residueClass`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L11672) [`irrational_erdosSupportSeries_odd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L11686)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.irrational_erdosSupportSeries_residueClass`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L11672)

```lean
theorem irrational_erdosSupportSeries_residueClass
    (b m c : ℕ) (hb : 2 ≤ b) (hm : 0 < m) :
    Irrational (erdosSupportSeries b {n : ℕ | n % m = c % m})
```

2. [`Erdos249257.irrational_erdosSupportSeries_odd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L11686)

```lean
theorem irrational_erdosSupportSeries_odd (b : ℕ) (hb : 2 ≤ b) :
    Irrational (erdosSupportSeries b {n : ℕ | Odd n})
```

<a id="thm-residue-odd-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSupportSeries_residueClass` | [E257_14/Challenge.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L52) | [PaperStatementsAG.lean, line 85](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAG.lean#L85) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `irrational_erdosSupportSeries_odd` | [E257_05/Challenge.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L59) | [PaperStatementsAG.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsAG.lean#L74) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-signed-periodic"></a>

## Theorem (A formal dichotomy for signed periodic weights)

> *Let $`b\ge2`$ and $`m\ge1`$ be integers, and let $`w:\mathbb{N}_{>0}\to\mathbb{Z}`$ be $`m`$-periodic. Put
> ``` math
> x=\sum_{a\ge1}\frac{w(a)}{b^a-1},\qquad
>  c_w(n)=\sum_{d\mid n}w(d).
> ```
> The cited formal argument gives the dichotomy that $`x`$ is irrational or $`b^kx\in\mathbb{Z}`$ for some integer $`k\ge0`$. It excludes the latter alternative if $`c_w`$ has one sign throughout and is nonzero at arbitrarily large indices. These sign assumptions concern $`c_w`$, not $`w`$. As noted above, Luca and Tachiya’s theorem already excludes the terminating alternative for every nonzero periodic $`w`$, without either sign restriction. The zero weight gives $`x=0`$.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*signed-divisor-calculus* [`irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L14175) [`irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L14583) [`irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L14643)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L14175)

```lean
theorem irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n) :
    Irrational (intWeightedErdosSeries b w)
      ∨ ∃ (k : ℕ) (z : ℤ), (b : ℝ) ^ k * intWeightedErdosSeries b w = (z : ℝ)
```

2. [`Erdos249257.irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L14583)

```lean
theorem irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hc0 : ∀ n : ℕ, 0 < n → 0 ≤ intWeightedCoeff w n)
    (hne : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) :
    Irrational (intWeightedErdosSeries b w)
```

3. [`Erdos249257.irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L14643)

```lean
theorem irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero
    (b m : ℕ) (w : ℕ → ℤ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, w (n + m) = w n)
    (hc0 : ∀ n : ℕ, 0 < n → intWeightedCoeff w n ≤ 0)
    (hne : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ intWeightedCoeff w n ≠ 0) :
    Irrational (intWeightedErdosSeries b w)
```

<a id="thm-signed-periodic-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_or_bpow_mul_eq_intCast_intWeightedErdosSeries_periodic` | [E257_14/Challenge.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L73) | [PaperStatementsAG.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAG.lean#L107) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `irrational_intWeightedErdosSeries_periodic_of_coeff_nonneg_of_frequently_ne_zero` | [E257_14/Challenge.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L57) | [PaperStatementsAG.lean, line 93](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAG.lean#L93) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `irrational_intWeightedErdosSeries_periodic_of_coeff_nonpos_of_frequently_ne_zero` | [E257_14/Challenge.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L65) | [PaperStatementsAG.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAG.lean#L100) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-mersenne-channel-survival"></a>

## Theorem (Denominators of finite Mersenne sums)

> *Let $`t\ge1`$ and $`h\ge1`$ be integers, and let $`r\ge1`$ be squarefree with every prime factor at most $`t`$. Let $`P`$ be a set of prime divisors of $`r`$ such that $`t<2p`$ for each $`p\in P`$, and put $`C=\prod_{p\in P}(2^p-1)`$. Then
> ``` math
> \frac{C}{\gcd(C,h)}\ \bigm|\ \operatorname{den}\bigl(hB(r)\bigr).
> ```
> In particular, $`C`$ divides this reduced denominator when $`\gcd(C,h)=1`$. The factors in $`C`$ are pairwise coprime, since $`\gcd(2^p-1,2^q-1)=2^{\gcd(p,q)}-1=1`$ for distinct primes. The assertion concerns this finite signed sum; it does not replace the approximation hypotheses in Theorem <a href="#thm:full-support-catalogue" data-reference-type="ref" data-reference="thm:full-support-catalogue">57</a>.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*cyclotomic* [`upperHalfChannel_survivorProduct_dvd_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L766) [`upperHalfChannel_product_dvd_den_of_coprime_scale`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L795)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L210)

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

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_channel_survival_of_coprime_scale`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L234)

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

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factor_gcd_eq_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L248)

```lean
theorem paper_channel_factor_gcd_eq_one
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 2 ^ Nat.gcd p q - 1 ∧
      Nat.gcd (2 ^ p - 1) (2 ^ q - 1) = 1
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_channel_factors_pairwise_coprime`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L260)

```lean
theorem paper_channel_factors_pairwise_coprime
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) :
    (P : Set ℕ).Pairwise fun p q => Nat.Coprime (2 ^ p - 1) (2 ^ q - 1)
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paperB_eq_divInt_paperA`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L118)

```lean
theorem paperB_eq_divInt_paperA {r : ℕ} (hr : Squarefree r) :
    paperB r = Rat.divInt (paperA r) (RadicalMobiusShadow.mersenne r : ℤ)
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paperB_eq_baseMobiusShadow`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L100)

```lean
theorem paperB_eq_baseMobiusShadow {r : ℕ} (hr : Squarefree r) :
    paperB r = RadicalMobiusShadow.baseMobiusShadow r
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.paperA_eq_mobiusNumerator`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L83)

```lean
theorem paperA_eq_mobiusNumerator {r : ℕ} (hr : Squarefree r) :
    paperA r = RadicalMobiusShadow.mobiusNumerator r
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.channelProduct_coprime_mobiusNumerator_of_one_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L163)

```lean
theorem channelProduct_coprime_mobiusNumerator_of_one_le
    {P : Finset ℕ} {t r : ℕ} (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t) :
    Nat.Coprime (∏ p ∈ P, RadicalMobiusShadow.mersenne p)
      (RadicalMobiusShadow.mobiusNumerator r).natAbs
```

9. [`ErdosProblems.Erdos257.PaperCompleteR21.upperHalfChannel_survivorProduct_dvd_den_of_one_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneChannelSurvivalAllHeights.lean#L187)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_mersenne_channel_survival` | [E257_14/Challenge.lean, line 161](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L161) | [PaperStatementsAD.lean, line 148](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L148) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `paper_mersenne_channel_survival_of_coprime_scale` | [E257_14/Challenge.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L171) | [PaperStatementsAD.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L157) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `paper_channel_factor_gcd_eq_one` | [E257_14/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L150) | [PaperStatementsAD.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L118) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `paper_channel_factors_pairwise_coprime` | [E257_14/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L156) | [PaperStatementsAD.lean, line 123](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L123) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `paperB_eq_divInt_paperA` | [E257_14/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L146) | [PaperStatementsAD.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L115) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `paperB_eq_baseMobiusShadow` | [E257_14/Challenge.lean, line 142](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L142) | [PaperStatementsAD.lean, line 112](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L112) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `paperA_eq_mobiusNumerator` | [E257_14/Challenge.lean, line 138](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L138) | [PaperStatementsAD.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L109) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `channelProduct_coprime_mobiusNumerator_of_one_le` | [E257_14/Challenge.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L129) | [PaperStatementsAD.lean, line 101](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L101) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `upperHalfChannel_survivorProduct_dvd_den_of_one_le` | [E257_14/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L181) | [PaperStatementsAD.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L186) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |

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

## Theorem (Exponential growth of the reduced denominators)

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
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">\[Math\]</span><span class="sans-serif">(uniform)</span>*cyclotomic* [`upperHalfMersenneProduct_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowDenominatorGrowth.lean#L60) [`lcmHeight_scaledMobiusShadow_den_exact`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowDenominatorGrowth.lean#L147)*

The Lean declarations below together state this result.

1. [`Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MersenneShadowDenominatorGrowth.lean#L85)

```lean
theorem lcmHeight_scaledMobiusShadow_den_lower_bound
    {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den
```

2. [`Erdos249257.MersenneShadowDenominatorGrowth.upperHalfMersenneProduct_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MersenneShadowDenominatorGrowth.lean#L60)

```lean
theorem upperHalfMersenneProduct_lower_bound {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤
      ∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p
```

3. [`Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_exact`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MersenneShadowDenominatorGrowth.lean#L147)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lcmHeight_scaledMobiusShadow_den_lower_bound` | [E257_14/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L117) | [PaperStatementsAD.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L62) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `upperHalfMersenneProduct_lower_bound` | [E257_14/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_14/Challenge.lean#L124) | [PaperStatementsAD.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_14/PaperStatementsAD.lean#L68) | [E257_14](../evidence/comparator/replay-35882032091/receipt-E257_14.json) |
| `lcmHeight_scaledMobiusShadow_den_exact` | [E249_05/Challenge.lean, line 292](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L292) | [PaperStatementsAR.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAR.lean#L21) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

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

## Theorem (The Lambert-series identity for the Möbius function)

> *The absolutely convergent signed series satisfies
> ``` math
> \sum_{d\ge1}\frac{\mu(d)}{2^d-1}=\frac12.
> ```
> This classical identity is also recorded in \[duverneytachiya, Example 1.1, p. 4\]. Expand each denominator geometrically and interchange the absolutely convergent sums. The coefficient of $`2^{-n}`$ is $`\sum_{d\mid n}\mu(d)`$, equal to $`1`$ for $`n=1`$ and $`0`$ otherwise. This proves the identity. Its coefficients are $`-1,0,1`$, not indicators of a support; the identity therefore does not represent $`1/2`$ as a subseries with all coefficients in $`\{0,1\}`$.*
> 
> *<span class="sans-serif">\[Cited\]</span><span class="sans-serif">(fixed)</span>*divisor counts and finite sums* [`tsum_moebius_div_two_pow_sub_one_eq_half`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneLambertLadder.lean#L587)*

The Lean declaration below states a result at least as strong as this one.

[`MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MersenneLambertLadder.lean#L587)

```lean
theorem tsum_moebius_div_two_pow_sub_one_eq_half :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 1 / 2
```

<a id="thm-mobius-lambert-identity-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_moebius_div_two_pow_sub_one_eq_half` | [E257_15/Challenge.lean, line 60](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_15/Challenge.lean#L60) | [PaperStatementsAJ.lean, line 16](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_15/PaperStatementsAJ.lean#L16) | [E257_15](../evidence/comparator/replay-35882032091/receipt-E257_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-negative-mobius-overshoot"></a>

## Corollary (Negative-Möbius Boolean support overshoots $`1/2`$)

> *Let $`N=\{d\ge2:\mu(d)=-1\}`$. Isolating the $`d=1`$ term in Theorem <a href="#thm:mobius-lambert-identity" data-reference-type="ref" data-reference="thm:mobius-lambert-identity">71</a> gives
> ``` math
> X_N(2)=\frac12+
>        \sum_{\substack{d\ge2\\\mu(d)=1}}\frac1{2^d-1}
>        \ge\frac12+\frac1{63}>\frac12,
> ```
> since $`\mu(6)=1`$. This rules out the particular candidate $`N`$. It does not rule out other infinite supports representing $`1/2`$.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(fixed)</span>*divisor counts and finite sums* [`half_lt_tsum_negativeMobius`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MobiusSignSupportNoGo.lean#L164) [`tsum_negativeMobius_eq_half_add_positiveMobiusTail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MobiusSignSupportNoGo.lean#L111)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.MobiusSignSupportNoGo.tsum_negativeMobius_eq_half_add_positiveMobiusTail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MobiusSignSupportNoGo.lean#L111)

```lean
theorem tsum_negativeMobius_eq_half_add_positiveMobiusTail :
    (∑' d : ℕ+, negativeMobiusTerm d) =
      1 / 2 + ∑' d : ℕ+, positiveMobiusTailTerm d
```

2. [`Erdos249257.MobiusSignSupportNoGo.half_lt_tsum_negativeMobius`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MobiusSignSupportNoGo.lean#L164)

```lean
theorem half_lt_tsum_negativeMobius :
    (1 : ℝ) / 2 < ∑' d : ℕ+, negativeMobiusTerm d
```

<a id="cor-negative-mobius-overshoot-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_negativeMobius_eq_half_add_positiveMobiusTail` | [E257_15/Challenge.lean, line 84](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_15/Challenge.lean#L84) | [PaperStatementsAQ.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_15/PaperStatementsAQ.lean#L27) | [E257_15](../evidence/comparator/replay-35882032091/receipt-E257_15.json) |
| `half_lt_tsum_negativeMobius` | [E257_15/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_15/Challenge.lean#L80) | [PaperStatementsAQ.lean, line 24](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_15/PaperStatementsAQ.lean#L24) | [E257_15](../evidence/comparator/replay-35882032091/receipt-E257_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-half-skip-dichotomy"></a>

## Theorem (The half-skip dichotomy via Erdős–Borwein irrationality)

> *The half target satisfies
> ``` math
> \frac12\in\mathcal A\quad\Longleftrightarrow\quad
>  \mathbb N_{>0}\smallsetminus G\text{ is infinite},
> ```
> where $`G`$ is the greedy support for $`1/2`$. In the forward direction, finitely many skipped exponents would express the full Mersenne sum as $`1/2`$ plus a finite rational sum, contradicting Erdős’s full-support irrationality theorem. The reverse implication uses the greedy tail criterion: once a remainder exceeds the whole available tail, every later exponent is selected. Infinitely many skips exclude that failure. The equivalence does not establish that infinitely many skips actually occur.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(cofinal)</span>*greedy recurrence* [`half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L2583) [`irrational_erdosBorweinMersenneConstant`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L2469)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L2583)

```lean
theorem half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite
```

2. [`Erdos249257.irrational_erdosBorweinMersenneConstant`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L2469)

```lean
theorem irrational_erdosBorweinMersenneConstant :
    Irrational erdosBorweinMersenneConstant
```

<a id="thm-half-skip-dichotomy-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite` | [E257_15/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_15/Challenge.lean#L117) | [PaperStatementsB.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_15/PaperStatementsB.lean#L62) | [E257_15](../evidence/comparator/replay-35882032091/receipt-E257_15.json) |
| `irrational_erdosBorweinMersenneConstant` | [E257_15/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_15/Challenge.lean#L104) | [PaperStatementsAH.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_15/PaperStatementsAH.lean#L31) | [E257_15](../evidence/comparator/replay-35882032091/receipt-E257_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-nine-way-hub"></a>

## Theorem (Equivalent descriptions of half-membership)

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
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(cofinal)</span>*integer quotients* [`half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L112) [`half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L213) [`half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L235)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L112)

```lean
theorem half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ SeamGreedyEventuallyRight
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L126)

```lean
theorem half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedTerminalFalse
```

3. [`Erdos249257.half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L156)

```lean
theorem half_mem_mersenneAchievementSet_iff_unboundedUpperOrMiddle :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedUpperOrMiddle
```

4. [`Erdos249257.half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L203)

```lean
theorem half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyCofinalTerminalFalse
```

5. [`Erdos249257.half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L213)

```lean
theorem half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∃ rows : ℕ → ℕ, SeamGreedyUnboundedSkippedRanksAlong rows
```

6. [`Erdos249257.unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L228)

```lean
theorem unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite :
    SeamGreedyUnboundedTerminalFalse ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite
```

7. [`Erdos249257.half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L235)

```lean
theorem half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ ∃ M : ℕ, IsLastHalfGreedySkip M
```

<a id="thm-nine-way-hub-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-eventually-right-impossible"></a>

## Lemma (The values on either side of an eventual right continuation)

> *If the seam eventually always extends “true” (right branch) from some row $`S`$ on with a fixed lower prefix $`u`$, the resulting cofinite-support value stays strictly below $`1/2`$ (*prefix_add_mersenneTail_lt_half_of_eventually_right*); the matching alternative “upper competitor” word gives a strict excess *above* $`1/2`$ (*half_lt_upper_competitor_of_eventually_right*). Neither of these two cofinite continuations represents $`1/2`$. This does not rule out an eventually-right integer orbit; it describes the two values in that case. The inequalities are used in Theorem <a href="#thm:final-middle-cell" data-reference-type="ref" data-reference="thm:final-middle-cell">87</a>.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(cofinal)</span>*integer quotients* [`prefix_add_mersenneTail_lt_half_of_eventually_right`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFatalGapRightTail.lean#L402) [`half_lt_upper_competitor_of_eventually_right`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFatalGapRightTail.lean#L627)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.prefix_add_mersenneTail_lt_half_of_eventually_right`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFatalGapRightTail.lean#L402)

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

2. [`Erdos249257.half_lt_upper_competitor_of_eventually_right`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFatalGapRightTail.lean#L627)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `prefix_add_mersenneTail_lt_half_of_eventually_right` | [E257_17/Challenge.lean, line 130](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L130) | [PaperStructuresBJ.lean, line 1346](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStructuresBJ.lean#L1346) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |
| `half_lt_upper_competitor_of_eventually_right` | [E257_16/Challenge.lean, line 334](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_16/Challenge.lean#L334) | [PaperStructuresBI.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_16/PaperStructuresBI.lean#L283) | [E257_16](../evidence/comparator/replay-35882032091/receipt-E257_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-mersenne-tail-weight"></a>

## Lemma (Each Mersenne weight exceeds its remaining tail)

> *For $`n\ge1`$, let $`w_n=(2^n-1)^{-1}`$ and $`R_n=\sum_{j>n}w_j`$. Then
> ``` math
> R_n=w_{n+1}+R_{n+1},\qquad
>  2^{-n}<R_n\le2w_{n+1}<w_n.
> ```
> For the upper bound, compare each tail term with $`2^{1-j}w_{n+1}`$ at index $`n+j`$, $`j\ge1`$, and sum the geometric series. The last inequality follows by comparing $`2/(2^{n+1}-1)`$ with $`1/(2^n-1)`$. This strict term-versus-tail inequality is the separation hypothesis used in the greedy arguments.*
> 
> *It is not available for the totient weights $`\varphi(n)/2^n`$: the terms at indices $`4`$ and $`5`$ already sum to $`2/16+4/32=1/4=\varphi(3)/2^3`$, and the remaining tail is positive. A general strict-tail argument therefore cannot be transferred to that sequence without a different hypothesis or proof.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*divisor counts and finite sums* [`mersenneTail_lt_weight`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L180) [`mersenneTail_le_two_mul_weight`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L155)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.mersenneTail_eq_weight_add`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L114)

```lean
theorem mersenneTail_eq_weight_add (n : ℕ) :
    mersenneTail n = mersenneWeight (n + 1) + mersenneTail (n + 1)
```

2. [`Erdos249257.halfTwoChannelCap_lt_mersenneTail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L1226)

```lean
theorem halfTwoChannelCap_lt_mersenneTail (n : ℕ) :
    halfTwoChannelCap n < mersenneTail n
```

3. [`Erdos249257.mersenneTail_le_two_mul_weight`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L155)

```lean
theorem mersenneTail_le_two_mul_weight (n : ℕ) :
    mersenneTail n ≤ 2 * mersenneWeight (n + 1)
```

4. [`Erdos249257.two_mul_mersenneWeight_succ_lt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L125)

```lean
theorem two_mul_mersenneWeight_succ_lt {n : ℕ} (hn : 0 < n) :
    2 * mersenneWeight (n + 1) < mersenneWeight n
```

5. [`Erdos249257.mersenneTail_lt_weight`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L180)

```lean
theorem mersenneTail_lt_weight {n : ℕ} (hn : 0 < n) :
    mersenneTail n < mersenneWeight n
```

<a id="lem-mersenne-tail-weight-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mersenneTail_eq_weight_add` | [E257_17/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L159) | [PaperStatementsAH.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAH.lean#L36) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |
| `halfTwoChannelCap_lt_mersenneTail` | [E257_17/Challenge.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L155) | [PaperStatementsAH.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAH.lean#L27) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |
| `mersenneTail_le_two_mul_weight` | [E257_17/Challenge.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L163) | [PaperStatementsAH.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAH.lean#L39) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |
| `two_mul_mersenneWeight_succ_lt` | [E257_17/Challenge.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L171) | [PaperStatementsAH.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAH.lean#L45) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |
| `mersenneTail_lt_weight` | [E257_17/Challenge.lean, line 167](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L167) | [PaperStatementsAH.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAH.lean#L42) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-greedy-survival-catalogue"></a>

## Theorem (Greedy survival and membership)

> *With the greedy remainder $`r_n(x)`$ and complete tail $`R_n`$,
> ``` math
> x\in\mathcal A\quad\Longleftrightarrow\quad
>  x\ge0\ \text{and}\ r_n(x)\le R_n\text{ for every }n\ge0.
> ```
> If all inequalities hold, the nonnegative remainders tend to zero because $`R_n\to0`$, so the greedy partial sums converge to $`x`$. Conversely, strict tail domination $`w_n>R_n`$ forces the greedy choices in any representation and therefore gives every inequality. The argument applies to positive summable weights satisfying that separation hypothesis; it is not a consequence of summability alone.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*greedy recurrence* [`mem_mersenneAchievementSet_iff_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1458)*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.mem_mersenneAchievementSet_iff_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L1458)

```lean
theorem mem_mersenneAchievementSet_iff_greedy_survival (x : ℝ) :
    x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n
```

<a id="thm-greedy-survival-catalogue-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mem_mersenneAchievementSet_iff_greedy_survival` | [E257_05/Challenge.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_05/Challenge.lean#L134) | [PaperStatementsB.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_05/PaperStatementsB.lean#L106) | [E257_05](../evidence/comparator/replay-35882032091/receipt-E257_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-rank-step-trichotomy"></a>

## Lemma (The two next-prefix intervals and their gap)

> *Let $`d\ge0`$ be an integer, let $`u\subseteq\{1,\ldots,d\}`$, and suppose the target $`t`$ lies in the interval $`[X_u(2),X_u(2)+R_d]`$. At depth $`d+1`$, either $`t`$ lies in the lower interval
> ``` math
> [X_u(2),X_u(2)+R_{d+1}],
> ```
> or in the upper interval
> ``` math
> [X_u(2)+w_{d+1},X_u(2)+w_{d+1}+R_{d+1}],
> ```
> or in the open gap between them. These alternatives are disjoint because $`R_{d+1}<w_{d+1}`$, and exhaustive because $`R_d=w_{d+1}+R_{d+1}`$. For $`t=1/2`$, Lemma <a href="#lem:half-endpoint-kills" data-reference-type="ref" data-reference="lem:half-endpoint-kills">81</a> also excludes the interval endpoints, so all relevant comparisons are strict. Endpoint exclusion is not what makes the two child intervals disjoint; the strict-tail inequality does that.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*dedekind-cut* [`isStraddlePrefix_step_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L205) [`IsStraddlePrefix.half_step_forced`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L301)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.isStraddlePrefix_step_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCutLocator.lean#L205)

```lean
theorem isStraddlePrefix_step_trichotomy {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix t u d) :
    IsStraddlePrefix t u (d + 1) ∨
      IsStraddlePrefix t (insert (d + 1) u) (d + 1) ∨
        (positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t ∧
          t < positiveMersenneSupportValue (↑u : Set ℕ)
              + mersenneWeight (d + 1))
```

2. [`Erdos249257.IsStraddlePrefix.half_step_forced`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCutLocator.lean#L301)

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

<a id="lem-rank-step-trichotomy-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `isStraddlePrefix_step_trichotomy` | [E257_17/Challenge.lean, line 202](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L202) | [PaperStructuresU.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStructuresU.lean#L43) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |
| `half_step_forced` | [E257_17/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L190) | [PaperStructuresU.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStructuresU.lean#L31) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-fatal-gap-exclusion"></a>

## Lemma (A greedy gap excludes every representation)

> *Let $`d\ge0`$ be an integer and $`u\subseteq\{1,\ldots,d\}`$ a finite prefix. If
> ``` math
> X_u(2)+R_{d+1}<t<X_u(2)+w_{d+1},
> ```
> then no support agreeing with $`u`$ through rank $`d`$ represents $`t`$: omitting $`d+1`$ leaves value at most the lower endpoint, while including it gives value at least the upper endpoint. Other length-$`d`$ prefixes have disjoint containing intervals by the first-difference argument using $`w_n>R_n`$. Since the displayed gap lies inside the interval for $`u`$, none of those prefixes can represent $`t`$ either. Thus a certified strict gap excludes every representation, not just one proposed continuation.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*dedekind-cut* [`positiveMersenneSupportValue_ne_of_rank_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L380)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_excludes_every_representation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L174)

```lean
theorem fatal_gap_excludes_every_representation {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    ∀ A : Set ℕ, 0 ∉ A → positiveMersenneSupportValue A ≠ t
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_endpoint_bounds`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L114)

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

3. [`ErdosProblems.Erdos257.PaperCompleteR21.depth_prefix_interval_disjoint`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L144)

```lean
theorem depth_prefix_interval_disjoint {t : ℝ} {u v : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d) (hv : ∀ n ∈ v, 0 < n ∧ n ≤ d)
    (hut : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d)
    (hvt : positiveMersenneSupportValue (↑v : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑v : Set ℕ) + mersenneTail d) :
    u = v
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_within_prefix_interval`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L162)

```lean
theorem fatal_gap_within_prefix_interval {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
```

<a id="lem-fatal-gap-exclusion-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `fatal_gap_excludes_every_representation` | [E257_17/Challenge.lean, line 251](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L251) | [PaperStatementsAM.lean, line 185](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L185) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |
| `fatal_gap_endpoint_bounds` | [E257_17/Challenge.lean, line 240](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L240) | [PaperStatementsAM.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L175) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |
| `depth_prefix_interval_disjoint` | [E257_17/Challenge.lean, line 231](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L231) | [PaperStatementsAM.lean, line 161](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L161) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |
| `fatal_gap_within_prefix_interval` | [E257_17/Challenge.lean, line 258](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L258) | [PaperStatementsAM.lean, line 191](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L191) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-half-endpoint-kills"></a>

## Lemma (No finite Mersenne sum equals one half)

> *For every finite $`u\subseteq\mathbb N_{>0}`$, $`X_u(2)\ne1/2`$: its reduced denominator is odd. Also $`X_u(2)+R_d\ne1/2`$ for every $`d\ge0`$, since $`R_d`$ is the irrational full Mersenne sum minus a finite rational sum. These observations exclude equality at the finite-prefix and complete-tail endpoints of Lemma <a href="#lem:rank-step-trichotomy" data-reference-type="ref" data-reference="lem:rank-step-trichotomy">79</a>.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*parity-irrationality* [`positiveMersenneSupportValue_coe_finset_ne_half`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L243) [`half_ne_coe_finset_add_mersenneTail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L263)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.positiveMersenneSupportValue_coe_finset_ne_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCutLocator.lean#L243)

```lean
theorem positiveMersenneSupportValue_coe_finset_ne_half
    {u : Finset ℕ} (h0 : 0 ∉ u) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≠ (1 / 2 : ℝ)
```

2. [`Erdos249257.half_ne_coe_finset_add_mersenneTail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCutLocator.lean#L263)

```lean
theorem half_ne_coe_finset_add_mersenneTail
    (u : Finset ℕ) (d : ℕ) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
      ≠ (1 / 2 : ℝ)
```

<a id="lem-half-endpoint-kills-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `positiveMersenneSupportValue_coe_finset_ne_half` | [E257_17/Challenge.lean, line 226](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L226) | [PaperStatementsAM.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L110) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |
| `half_ne_coe_finset_add_mersenneTail` | [E257_17/Challenge.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L220) | [PaperStatementsAM.lean, line 98](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsAM.lean#L98) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-straddle-agrees-greedy"></a>

## Lemma (Straddle words are canonical: they agree with the greedy prefix)

> *Let $`u\subseteq\{1,\ldots,d\}`$ satisfy $`X_u(2)\le1/2\le X_u(2)+R_d`$. Then
> ``` math
> u=G\cap\{1,\ldots,d\},
> ```
> where $`G`$ is the real greedy support for $`1/2`$. At the first disagreement, if $`u`$ takes rank $`k`$ and the greedy rule skips it, then $`X_u(2)>1/2`$. In the opposite case, the greedy remainder before $`k`$ is at least $`w_k`$, whereas the remaining contribution allowed by $`u`$, including $`R_d`$, is at most $`R_k<w_k`$. Both cases contradict the displayed interval. Thus there is at most one such word at each depth; the lemma does not assert its existence at every depth.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*greedy recurrence* [`IsStraddlePrefix.half_agrees_greedy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L442) [`IsStraddlePrefix.erase_top`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L334)*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.IsStraddlePrefix.half_agrees_greedy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCutLocator.lean#L442)

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

## Theorem (Last-skip iff local fatality: a pointwise criterion)

> *Keep $`G`$ for the selected half-greedy support, $`r_M(1/2)`$ for its remainder and $`R_M`$ for the complete tail after rank $`M`$. A positive rank $`M`$ is the last omitted rank if and only if $`M\notin G`$ and $`r_M(1/2)>R_M`$. Consequently,
> ``` math
> \frac12\in\mathcal A
>  \quad\Longleftrightarrow\quad
>  r_M(1/2)\le R_M\quad\text{for every positive }M\notin G.
> ```
> Thus it suffices to check the tail inequality at the ranks actually omitted by the greedy rule. This is an equivalence on that fixed orbit; it does not establish the inequality at its unboundedly many possible omitted ranks.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*greedy recurrence* [`half_mem_iff_every_actual_skip_survives`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFixedTailSocket.lean#L73) [`isLastHalfGreedySkip_iff_skip_and_fatal`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFixedTailSocket.lean#L22)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.isLastHalfGreedySkip_iff_skip_and_fatal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFixedTailSocket.lean#L22)

```lean
theorem isLastHalfGreedySkip_iff_skip_and_fatal
    {M : ℕ} :
    IsLastHalfGreedySkip M ↔
      M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) ∧
        GreedyMersenneFatalAt (1 / 2 : ℝ) M
```

2. [`Erdos249257.half_mem_iff_every_actual_skip_survives`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFixedTailSocket.lean#L73)

```lean
theorem half_mem_iff_every_actual_skip_survives :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ M : ℕ,
        M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) →
          greedyMersenneRemainder (1 / 2 : ℝ) M ≤ mersenneTail M
```

<a id="thm-last-skip-iff-fatal-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `isLastHalfGreedySkip_iff_skip_and_fatal` | [E257_18/Challenge.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_18/Challenge.lean#L64) | [PaperStatementsG.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_18/PaperStatementsG.lean#L36) | [E257_18](../evidence/comparator/replay-35882032091/receipt-E257_18.json) |
| `half_mem_iff_every_actual_skip_survives` | [E257_17/Challenge.lean, line 292](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_17/Challenge.lean#L292) | [PaperStatementsD.lean, line 166](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_17/PaperStatementsD.lean#L166) | [E257_17](../evidence/comparator/replay-35882032091/receipt-E257_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-seam-upper-or-middle"></a>

## Lemma (Seam upper-or-middle classification)

> *At a row $`s\ge5`$, the terminal rank is omitted in the next row, $`s\notin D_{s+1}`$, if and only if either
> ``` math
> 4o_s+p_s^+\le2^{s+1},
> ```
> or this inequality fails and
> ``` math
> 4\,\mathrm{rem}(s)+2^{s+1}-p_s^-<2^{s+2}+4.
> ```
> These are exactly branches $`\mathrm U`$ and $`\mathrm M`$ of Theorem <a href="#thm:dynamics" data-reference-type="ref" data-reference="thm:dynamics">40</a>. On either branch the new terminal weight does not fit; on $`\mathrm R`$ it does. This is an exact classification, not a conjecture inferred from observed branch labels.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*integer quotients* [`seamGreedy_terminal_false_iff_upperOrMiddle`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L57)*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.seamGreedy_terminal_false_iff_upperOrMiddle`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderHalfMembershipClassification.lean#L57)

```lean
theorem seamGreedy_terminal_false_iff_upperOrMiddle
    (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord.terminal (by omega)
        (seamGreedyWord (s + 1)) = false ↔
      SeamGreedyUpperOrMiddleAt s hs
```

<a id="lem-seam-upper-or-middle-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `seamGreedy_terminal_false_iff_upperOrMiddle` | [E257_08/Challenge.lean, line 312](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_08/Challenge.lean#L312) | [Statement.lean, line 312](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_08/Statement.lean#L312) | [E257_08](../evidence/comparator/replay-35882032091/receipt-E257_08.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-largest-false-rank-algebra"></a>

## Lemma (The exact gap at the largest omitted rank)

> *Let $`2\le d<s`$ and $`2s<3d`$. Write $`W_s(E)=\sum_{e\in E}\lfloor4^s/(2^e-1)\rfloor`$ for a finite set $`E\subseteq\{2,\ldots,s-1\}`$. For $`u\subseteq\{2,\ldots,d-1\}`$, put $`E_-=u\cup\{d+1,\ldots,s-1\}`$ and $`E_+=u\cup\{d\}`$. Then
> ``` math
> 3W_s(E_-)+3\cdot2^{s+1}+2\cdot4^{s-d}+4=3W_s(E_+).
> ```
> The correction is independent of the common prefix $`u`$. For the integer-greedy rows $`s\ge5`$, a right transition preserves the largest omitted rank, whereas an upper or middle transition makes $`s`$ the largest omitted rank in the next row.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*integer quotients* [`three_mul_largestSkipLowerWeight_add_exactLateGap_eq_upperWeight`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderLargestSkipGap.lean#L259) [`IsLargestFalseRank.seamGreedyWord_succ_of_rightBranch`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderLargestSkipGap.lean#L339)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.largest_false_rank_algebra`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamRowGapAndCarry.lean#L39)

```lean
theorem largest_false_rank_algebra {s d : ℕ} {u : Finset ℕ}
    (hd2 : 2 ≤ d) (hds : d < s) (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d)
    (hlate : 2 * s < 3 * d) :
    3 * rowWeightSum s (u ∪ Finset.Ico (d + 1) s)
        + (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4)
      = 3 * rowWeightSum s (insert d u)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_largest_false_rank_algebra`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamRowGapAndCarry.lean#L98)

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

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `largest_false_rank_algebra` | [E257_18/Challenge.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_18/Challenge.lean#L77) | [PaperStatementsAA.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_18/PaperStatementsAA.lean#L163) | [E257_18](../evidence/comparator/replay-35882032091/receipt-E257_18.json) |
| `paper_largest_false_rank_algebra` | [E257_19/Challenge.lean, line 319](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_19/Challenge.lean#L319) | [PaperStructuresBH.lean, line 204](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_19/PaperStructuresBH.lean#L204) | [E257_19](../evidence/comparator/replay-35882032091/receipt-E257_19.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-critical-dyadic-band"></a>

## Theorem (Reduction to the nearest dyadic boundary)

> *Let $`d,E`$ be nonnegative integers with $`E\le2^{d+1}`$, and let $`j_*`$ be the largest $`j\in\{0,\ldots,d\}`$ for which $`E\le2^{d-j+1}`$. The set is nonempty, so $`j_*`$ is well defined, including when $`E=0`$. Then
> ``` math
> \begin{aligned}
>  &\forall j\in\{0,\ldots,d\},\quad
>   2^{d-j+1}<E\ \text{or}\ E+2(d+j)\le2^{d-j+1}\\
>  &\hspace{35mm}\Longleftrightarrow\quad
>  E+2(d+j_*)\le2^{d-j_*+1}.
>  \end{aligned}
> ```
> For $`j>j_*`$ the first alternative holds by maximality. For $`j\le j_*`$, the left side of the required inequality increases with $`j`$ and its right side decreases, so the condition at $`j_*`$ implies all the others. This is an elementary reduction from $`d+1`$ inequalities to one. Specialized to the seam reset charge (where the actual upper-reset condition gives $`E\le2^{d+1}`$, as explained in Proposition <a href="#record:257bm-c12" data-reference-type="ref" data-reference="record:257bm-c12">123</a>), the reduced hypothesis *SeamUpperResetCriticalBandEscape* is proved logically equivalent to Theorem <a href="#thm:upper-reset-band" data-reference-type="ref" data-reference="thm:upper-reset-band">53</a>’s band-avoidance hypothesis.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*dyadic-boundary* [`dyadicBandEscape_iff_exists_critical`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L108) [`seamUpperResetCriticalBandEscape_iff`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L883)*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfUpperResetCriticalBand.exists_criticalDyadicBandIndex`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfUpperResetCriticalBand.lean#L46)

```lean
theorem exists_criticalDyadicBandIndex
    {d E : ℕ} (hE : E ≤ 2 ^ (d + 1)) :
    ∃ j : ℕ, CriticalDyadicBandIndex d E j
```

2. [`Erdos249257.HalfUpperResetCriticalBand.dyadicBandEscape_iff_exists_critical`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfUpperResetCriticalBand.lean#L108)

```lean
theorem dyadicBandEscape_iff_exists_critical
    {d E : ℕ} (hE : E ≤ 2 ^ (d + 1)) :
    DyadicBandEscape d E ↔
      ∃ j : ℕ, CriticalDyadicBandIndex d E j ∧
        E + 2 * (d + j) ≤ 2 ^ (d - j + 1)
```

3. [`Erdos249257.HalfUpperResetCriticalBand.seamUpperResetCriticalBandEscape_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfUpperResetCriticalBand.lean#L883)

```lean
theorem seamUpperResetCriticalBandEscape_iff :
    SeamUpperResetCriticalBandEscape ↔ SeamUpperResetDyadicBandEscape
```

<a id="thm-critical-dyadic-band-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-final-middle-cell"></a>

## Theorem (Excluding minus three at a final middle transition)

> *Suppose that row $`D\ge13`$ is a middle transition in Theorem <a href="#thm:dynamics" data-reference-type="ref" data-reference="thm:dynamics">40</a> and every transition at a row $`s\ge D+1`$ is right. Then
> ``` math
> C_D:=4\,\mathrm{rem}(D)-p_D^--4\ne-3.
> ```
> This excludes one particular value under the stated tail assumption; it neither excludes every final middle transition nor proves the all-middle-row hypothesis of Theorem <a href="#thm:two-sided-dyadic" data-reference-type="ref" data-reference="thm:two-sided-dyadic">52</a>.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*integer quotients* [`finalMiddleCell_neg_three_not_last`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L587) [`mobiusCenteredHalfCarry_add_two`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L39)*

The Lean declarations below together state this result.

1. [`Erdos249257.finalMiddleCell_neg_three_not_last`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L587)

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

2. [`Erdos249257.mobiusCenteredHalfCarry_add_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L39)

```lean
theorem mobiusCenteredHalfCarry_add_two
    (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N
```

<a id="thm-final-middle-cell-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-skipped-endpoint-trichotomy"></a>

## Lemma (The signed position of a skipped greedy prefix)

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
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*integer quotients* [`halfGreedy_skipped_endpoint_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L246)*

The Lean declaration below states this result.

[`Erdos249257.halfGreedy_skipped_endpoint_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L246)

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

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `halfGreedy_skipped_endpoint_trichotomy` | [E257_16/Challenge.lean, line 316](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_16/Challenge.lean#L316) | [PaperStructuresBI.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_16/PaperStructuresBI.lean#L264) | [E257_16](../evidence/comparator/replay-35882032091/receipt-E257_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-reverse-carry-word"></a>

## Lemma (Spacing of reverse-carry words)

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
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*binary digits* [`overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L124) [`overlappingReverseCarryWords_twoPow_le_realBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L191)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_reverse_carry_word`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamRowGapAndCarry.lean#L240)

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

2. [`ErdosProblems.Erdos257.PaperCompleteR21.reverse_carry_word_common_bound_sharp`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamRowGapAndCarry.lean#L209)

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

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_reverse_carry_word` | [E257_20/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L110) | [PaperStatementsAA.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAA.lean#L238) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |
| `reverse_carry_word_common_bound_sharp` | [E257_20/Challenge.lean, line 169](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L169) | [PaperStatementsAA.lean, line 344](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAA.lean#L344) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-linear-channel-nogo"></a>

## Lemma (Linear functionals factoring through one value)

> *Let $`V`$ be a vector space over $`\mathbb Q`$, let $`\mathrm{ev}:V\to\mathbb Q`$ be linear, and choose $`e\in V`$ with $`\mathrm{ev}(e)=1`$. Suppose that each linear functional $`\ell_j:V\to\mathbb Q`$ vanishes on $`\ker(\mathrm{ev})`$. Then $`v-\mathrm{ev}(v)e\in\ker(\mathrm{ev})`$ gives $`\ell_j(v)=\ell_j(e)\mathrm{ev}(v)`$. Consequently any finite evaluation matrix $`(\ell_j(v_i))_{i,j}`$ is an outer product and has rank at most one. Every square minor of order at least two therefore vanishes. This excludes determinant arguments formed from these particular functionals, not determinant methods with additional independent information.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*linear-algebra* [`relationInvariantLinearChannels_det_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L42)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.AdelicHeightObstruction.linearDescender_eq_smul_eval`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/AdelicHeightObstruction.lean#L120)

```lean
theorem linearDescender_eq_smul_eval
    {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (ev : V →ₗ[ℚ] ℚ) (Λ : V →ₗ[ℚ] W)
    (hker : LinearMap.ker ev ≤ LinearMap.ker Λ)
    (he : ∃ e : V, ev e = 1) :
    ∃ w₀ : W, ∀ v : V, Λ v = ev v • w₀
```

2. [`Erdos249257.HalfTrappingReturnCarry.relationInvariantLinearChannels_det_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfTrappingReturnCarry.lean#L42)

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

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `linearDescender_eq_smul_eval` | [E257_20/Challenge.lean, line 101](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L101) | [PaperStatementsAA.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAA.lean#L68) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |
| `relationInvariantLinearChannels_det_eq_zero` | [E257_20/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L184) | [PaperStatementsAB.lean, line 16](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAB.lean#L16) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-two-thirds-band"></a>

## Theorem (Two-thirds band: exact localisation of post-take skip-unsafety)

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
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*rational-band* [`postTakeUnsafeAt_iff_band`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyTwoThirdsBand.lean#L88) [`seven_le_of_intBand_odd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyTwoThirdsBand.lean#L231) [`not_twoThirdsBand_of_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyTwoThirdsBand.lean#L185)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_two_thirds_band`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/PostTakeBandLocalisation.lean#L96)

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

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_two_thirds_band` | [E257_20/Challenge.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L139) | [PaperStatementsAA.lean, line 308](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAA.lean#L308) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-sharp-fatal-gap"></a>

## Theorem (A weaker sufficient test against the remaining tail)

> *Let $`k,u,L`$ be positive integers, and put $`a=2L-(2^k-1)u`$. Suppose $`a>0`$, equivalently that $`\rho=u/(2L)<w_k`$ and the greedy rule skips weight $`w_k`$. The dyadic sufficient test $`\rho\le2^{-k}`$ is equivalent to $`u\le a`$. The weaker sufficient condition
> ``` math
> 2u\le3a
> ```
> ensures $`\rho<R_k`$, by comparison with $`2^{-k}+(3\cdot4^k)^{-1}+(7\cdot8^k)^{-1}<R_k`$. This conclusion excludes a fatal tail-mass deficit at the current step; it does not assert that $`\rho`$ is representable by the remaining weights, or that all future greedy steps survive.*
> 
> *The containment of these sufficient conditions is strict even for valid rational data: $`(k,u,L,a)=(2,7,13,5)`$ gives $`1/4<7/26<R_2`$. In contrast, the scalar pair $`(u,a)=(3,2)`$ in the linked inequality lemma does not arise from integral $`L`$ under the present parity relation. Unit numerators are nonfatal at such a skipped step, since then $`a\ge1`$. Conversely, a fatal step requires $`3a<2u`$, hence $`u\ge2`$, or $`u\ge3`$ when $`u`$ is odd.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*divisor counts and finite sums* [`skipSafe_of_two_mul_le_three_mul`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L107) [`sharp_strictly_stronger`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L200) [`three_le_of_fatal_of_odd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L173)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_fatal_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyGapCriteria.lean#L299)

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

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_sharp_fatal_gap` | [E257_20/Challenge.lean, line 214](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L214) | [PaperStatementsAM.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L221) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-gap-mass-summability"></a>

## Lemma (Summability of one gap length per level)

> *For $`n\ge1`$, put $`g_n=w_n-R_n>0`$. The sum of one gap length per level satisfies, for $`N\ge0`$,
> ``` math
> \sum_{n>N}g_n\le\frac29\,4^{-N}+\frac37\,8^{-N}.
> ```
> This follows by summing the per-level upper bounds geometrically. It is not the measure of the union of all gaps: level $`n`$ has $`2^{n-1}`$ translated gaps of length $`g_n`$. The corresponding weighted sum and its geometric interpretation are given after Theorem <a href="#record:257hg-i2" data-reference-type="ref" data-reference="record:257hg-i2">161</a>. Neither estimate decides membership of a specified point such as $`1/2`$.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*divisor counts and finite sums* [`mersenneGap_tail_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGapMass.lean#L83) [`tendsto_mersenneGap_tail_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGapMass.lean#L104)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.mersenneGap_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L2346)

```lean
theorem mersenneGap_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneGap n
```

2. [`Erdos249257.summable_mersenneGap_succ`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGapMass.lean#L77)

```lean
theorem summable_mersenneGap_succ : Summable (fun k : ℕ => mersenneGap (k + 1))
```

3. [`Erdos249257.mersenneGap_tail_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGapMass.lean#L83)

```lean
theorem mersenneGap_tail_le (N : ℕ) :
    ∑' k : ℕ, mersenneGap (N + k + 1)
      ≤ (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N
```

4. [`Erdos249257.tendsto_mersenneGap_tail_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGapMass.lean#L104)

```lean
theorem tendsto_mersenneGap_tail_zero :
    Tendsto (fun N : ℕ => ∑' k : ℕ, mersenneGap (N + k + 1)) atTop (nhds 0)
```

<a id="lem-gap-mass-summability-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mersenneGap_pos` | [E257_20/Challenge.lean, line 244](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L244) | [PaperStatementsAH.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAH.lean#L34) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |
| `summable_mersenneGap_succ` | [E257_20/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L207) | [PaperStatementsAM.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L117) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |
| `mersenneGap_tail_le` | [E257_20/Challenge.lean, line 202](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L202) | [PaperStatementsAM.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L106) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |
| `tendsto_mersenneGap_tail_zero` | [E257_20/Challenge.lean, line 210](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L210) | [PaperStatementsAM.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L119) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-half-divisor-unit-drop"></a>

## Lemma (The effect of adding one divisor)

> *Let $`N\ge0`$ and let finite supports $`D_0,D_1`$ differ only by $`D_1=D_0\cup\{N+1\}`$, with $`N+1\notin D_0`$. For every positive integer $`m`$,
> ``` math
> c_{D_1}(m)-c_{D_0}(m)=\mathbf1_{N+1\mid m}.
> ```
> In particular, the difference is $`1`$ at $`m=2(N+1)`$. This follows directly from the definition of a divisor count. Its use in another coefficient sequence requires proving that sequence has the same support-incidence description.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*divisor-incidence* [`supportCoeff_extend_true_eq_false_add_one_at_double`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfDivisorUnitDrop.lean#L20)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.HalfCylinderIntegerGreedy.supportCoeff_insert_eq_add_indicator`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderIntegerGreedy.lean#L882)

```lean
theorem supportCoeff_insert_eq_add_indicator
    (A : Set ℕ) {d n : ℕ} (hdA : d ∉ A) :
    supportCoeff (insert d A) n =
      supportCoeff A n + if d ∈ n.divisors then 1 else 0
```

2. [`Erdos249257.HalfDivisorUnitDrop.supportCoeff_extend_true_eq_false_add_one_at_double`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfDivisorUnitDrop.lean#L20)

```lean
theorem supportCoeff_extend_true_eq_false_add_one_at_double
    {N : ℕ} (a : HalfWord N) :
    supportCoeff (wordSupport (extendHalfWord a true)) (2 * (N + 1)) =
      supportCoeff (wordSupport (extendHalfWord a false)) (2 * (N + 1)) + 1
```

<a id="lem-half-divisor-unit-drop-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `supportCoeff_insert_eq_add_indicator` | [E257_20/Challenge.lean, line 276](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L276) | [PaperStatementsAN.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAN.lean#L32) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |
| `supportCoeff_extend_true_eq_false_add_one_at_double` | [E257_20/Challenge.lean, line 263](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L263) | [PaperStatementsAL.lean, line 55](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAL.lean#L55) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-tempered-orbit-rigidity"></a>

## Theorem (Uniqueness of an integer recurrence with a vanishing scaled limit)

> *For any nonnegative-integer coefficient sequence $`c:\mathbb N\to\mathbb N`$ with $`c(n)\le
> n`$: the binary coefficient series $`X_c = \sum'_{n\ge 1} c(n)/2^n`$ is rational iff there exists a positive integer multiplier $`v`$ and an integer orbit $`u:\mathbb N\to\mathbb Z`$ satisfying the exact carry recurrence $`u(N{+}1)=2u(N)-v\cdot c(N{+}1)`$ together with the condition $`u(N)/2^N\to0`$. Every integer sequence satisfying both conditions obeys $`u(N) = v\cdot T_c(N)`$ exactly, where $`T_c(N)=\sum_{j\ge 1} c(N{+}j)/2^j`$ is the scaled tail. For each fixed $`v`$ there is at most one such sequence. Positivity of the orbit alone is deliberately *not* used as an equivalent criterion: a homogeneous $`2^N`$-scaled perturbation can be added to any orbit without breaking the recurrence, so the limit condition cannot be dropped. The choices $`c=c_A`$ for Problem 257 and $`c=\varphi`$ for Problem 249 both satisfy $`0\le c(n)\le n`$. The telescoping argument is given again, with an example, in Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a>.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*binary digits* [`binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L426) [`temperedBinaryOrbit_eq_scaledTail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L339)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L426)

```lean
theorem binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u
```

2. [`Erdos249257.temperedBinaryOrbit_eq_scaledTail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L339)

```lean
theorem temperedBinaryOrbit_eq_scaledTail
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    {v : ℕ} {u : ℕ → ℤ} (horbit : IsTemperedBinaryOrbit c v u) :
    ∀ N : ℕ, (u N : ℝ) = (v : ℝ) * binaryCoeffTail c N
```

<a id="thm-tempered-orbit-rigidity-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit` | [E257_21/Challenge.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L58) | [PaperStatementsAE.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAE.lean#L45) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `temperedBinaryOrbit_eq_scaledTail` | [E257_21/Challenge.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L64) | [PaperStatementsAE.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAE.lean#L65) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-tail-transfer"></a>

## Lemma (Changing finitely many support elements)

> *Let $`b\ge2`$ be an integer, and let $`A,B\subseteq\mathbb N_{\ge1}`$. If $`X_A(b)`$ is irrational and $`A,B`$ have finite symmetric difference, then $`X_B(b)`$ is irrational too: the two sums differ by a finite sum of rational numbers. This observation supplies the finite modifications in Theorem <a href="#thm:eventually-periodic" data-reference-type="ref" data-reference="thm:eventually-periodic">64</a>.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*tail-transfer* [`irrational_erdosSupportSeries_tail_of_irrational`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L9476)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.irrational_erdosSupportSeries_of_tail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L9467)

```lean
theorem irrational_erdosSupportSeries_of_tail (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b)
    (B : ℕ) (h : Irrational (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n})) :
    Irrational (erdosSupportSeries b A)
```

2. [`Erdos249257.irrational_erdosSupportSeries_tail_of_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L9476)

```lean
theorem irrational_erdosSupportSeries_tail_of_irrational (b : ℕ) (A : Set ℕ)
    (hb : 2 ≤ b) (B : ℕ) (h : Irrational (erdosSupportSeries b A)) :
    Irrational (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n})
```

<a id="lem-tail-transfer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_erdosSupportSeries_of_tail` | [E257_21/Challenge.lean, line 78](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L78) | [PaperStatementsAG.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAG.lean#L76) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `irrational_erdosSupportSeries_tail_of_irrational` | [E257_21/Challenge.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L83) | [PaperStatementsAG.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAG.lean#L95) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-dyadic-excess-reformulation"></a>

## Lemma (An integer test for the interval between the dyadic and Mersenne weights)

> *For positive integers $`p,L`$ and $`n\ge0`$, write the residual as $`p/(2L)`$ and put $`E=2^np-L`$. Clearing positive denominators gives
> ``` math
> \frac{p}{2L}\le\frac1{2^{n+1}}\quad\Longleftrightarrow\quad E\le0,
>  \qquad
>  \frac1{2^{n+1}}<\frac{p}{2L}<\frac1{2^{n+1}-1}
>  \quad\Longleftrightarrow\quad 0<E<\frac p2.
> ```
> The first test concerns the dyadic bound, not the greedy selection threshold itself. The second identifies precisely the interval in which a Mersenne weight is skipped but the dyadic safety test fails.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*integer quotients* [`divInt_le_nextDyadic_iff_excess_nonpos`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/DyadicPrefixCompression.lean#L198) [`greedyHalf_mem_nextMersenneDyadicSliver_iff_excess`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/DyadicPrefixCompression.lean#L1044)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.divInt_le_nextDyadic_iff_excess_nonpos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/DyadicPrefixCompression.lean#L198)

```lean
theorem divInt_le_nextDyadic_iff_excess_nonpos
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    Rat.divInt p ((2 * L : ℕ) : ℤ) ≤ 1 / (2 : ℚ) ^ (n + 1) ↔
      nextDyadicExcessIntNumerator p n L ≤ 0
```

2. [`Erdos249257.greedyHalf_mem_nextMersenneDyadicSliver_iff_excess`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/DyadicPrefixCompression.lean#L1044)

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

<a id="lem-dyadic-excess-reformulation-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `divInt_le_nextDyadic_iff_excess_nonpos` | [E257_21/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L99) | [PaperStatementsAF.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAF.lean#L30) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `greedyHalf_mem_nextMersenneDyadicSliver_iff_excess` | [E257_21/Challenge.lean, line 166](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L166) | [PaperStatementsD.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsD.lean#L131) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-denominator-sandwich"></a>

## Lemma (The odd denominator survives dyadic subtraction)

> *Let $`r/D`$ be a reduced fraction with $`D>0`$ odd, let $`p\in\mathbb Z`$, and let $`c\ge0`$ be an integer. The reduced denominator of $`p/2^c-r/D`$ is divisible by $`D`$ and divides $`2^cD`$. Indeed, its unreduced numerator $`pD-2^cr`$ is coprime to $`D`$, since $`\gcd(r,D)=\gcd(2^c,D)=1`$. Reduction can therefore remove only powers of $`2`$ from the displayed denominator. No property of Mersenne weights is used.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*denominator-algebra* [`dyadicResidual_denominator_sandwich`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/DyadicPrefixCompression.lean#L118)*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.dyadicResidual_denominator_sandwich`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/DyadicPrefixCompression.lean#L118)

```lean
theorem dyadicResidual_denominator_sandwich
    (p r c D : ℕ) (hDpos : 0 < D) (hDodd : Odd D)
    (hrD : r.Coprime D) (hle : 2 ^ c * r ≤ p * D) :
    D ∣ (dyadicResidualRat p r c D).den ∧
      (dyadicResidualRat p r c D).den ∣ 2 ^ c * D
```

<a id="lem-denominator-sandwich-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `dyadicResidual_denominator_sandwich` | [E257_21/Challenge.lean, line 105](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L105) | [PaperStatementsAF.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAF.lean#L35) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-denominator-survival"></a>

## Lemma (A guaranteed divisor of a reduced denominator)

> *Let $`a\in\mathbb Z`$, $`D\in\mathbb N_{>0}`$ and $`m,C,h\in\mathbb N`$. Write $`\operatorname{den}(x)`$ for the positive reduced denominator of a rational number $`x`$. If $`m\mid D`$ and $`\gcd(m,|a|)=1`$, then $`m\mid\operatorname{den}(a/D)`$. If $`C\mid D`$ and $`\gcd(C,|a|)=1`$, then
> ``` math
> \frac{C}{\gcd(C,h)}\mid\operatorname{den}(ha/D).
> ```
> Thus scaling may remove part of the guaranteed divisor. Indeed, reduction divides $`D`$ by $`\gcd(D,|a|)`$, so no prime power in $`m`$ can be lost. After scaling, a prime $`p\mid C`$ can lose at most $`v_p(h)`$ powers from the guaranteed divisor. This is a lower bound on the reduced denominator, not an equality: for $`D=12`$, $`C=6`$, $`a=1`$, $`h=2`$, it guarantees the divisor $`3`$, while the reduced denominator is $`6`$. The lemma feeds Theorem <a href="#thm:mersenne-channel-survival" data-reference-type="ref" data-reference="thm:mersenne-channel-survival">67</a> directly.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*denominator-algebra* [`divisor_dvd_divInt_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalDenominatorSurvival.lean#L17) [`survivingDivisor_dvd_scaled_divInt_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalDenominatorSurvival.lean#L38)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.RationalDenominatorSurvival.divisor_dvd_divInt_den`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RationalDenominatorSurvival.lean#L17)

```lean
theorem divisor_dvd_divInt_den
    {a : ℤ} {D m : ℕ} (hD : 0 < D) (hmD : m ∣ D)
    (hcop : Nat.Coprime m a.natAbs) :
    m ∣ (Rat.divInt a (D : ℤ)).den
```

2. [`Erdos249257.RationalDenominatorSurvival.survivingDivisor_dvd_scaled_divInt_den`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RationalDenominatorSurvival.lean#L38)

```lean
theorem survivingDivisor_dvd_scaled_divInt_den
    {a : ℤ} {D C h : ℕ} (hD : 0 < D) (hCD : C ∣ D)
    (hcop : Nat.Coprime C a.natAbs) :
    C / Nat.gcd C h ∣
      (Rat.divInt ((h : ℤ) * a) (D : ℤ)).den
```

<a id="lem-denominator-survival-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `divisor_dvd_divInt_den` | [E257_21/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L186) | [PaperStatementsAA.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAA.lean#L80) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `survivingDivisor_dvd_scaled_divInt_den` | [E257_21/Challenge.lean, line 192](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L192) | [PaperStatementsAA.lean, line 85](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAA.lean#L85) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-mixed-prime-power-layer"></a>

## Lemma (Commuting prime-power differences)

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
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(uniform)</span>*p-adic* [`mixedPrimePowerLayerTwo_supportCoeffInt`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MaximalOmegaLayer.lean#L39) [`primePowerLayer_comm`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MaximalOmegaLayer.lean#L29)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.MaximalOmegaLayer.primePowerLayer_comm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MaximalOmegaLayer.lean#L29)

```lean
theorem primePowerLayer_comm
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) :
    primePowerLayer q f (primePowerLayer p e g) n =
      primePowerLayer p e (primePowerLayer q f g) n
```

2. [`Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_supportCoeffInt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MaximalOmegaLayer.lean#L39)

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

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `primePowerLayer_comm` | [E257_21/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L180) | [PaperStatementsAA.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAA.lean#L75) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `mixedPrimePowerLayerTwo_supportCoeffInt` | [E257_21/Challenge.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L220) | [PaperStatementsAO.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAO.lean#L22) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-achievement-set-topology"></a>

## Proposition (Achievement-set topology: compact, closed, perfect, measure exactly one)

> *$`\ensuremath{\mathcal A}`$ is compact (continuous image of the binary-sequence Cantor space $`\mathbb N\to\mathrm{Fin}\,2`$ under the product topology, via $`\mathrm{positiveMersenneDigitValue}`$), hence closed; it is also perfect, totally disconnected, and nowhere dense, with Lebesgue measure exactly $`1`$. The compactness/closedness argument (binary coding $`\to`$ Cantor space $`\to`$ continuous image) is a fully generic technique for characterizing the achievement set of *any* absolutely convergent digit-weighted series, not specific to Mersenne denominators ; reusable for a $`\varphi(n)/2^n`$ subsum set after checking summability. No separation of successive weights is needed for compactness or closedness; the stronger topological conclusions require their own hypotheses. Closedness alone is what powers every “limit of a sequence of achieved points is achieved” argument in this catalogue (e.g. Theorem <a href="#thm:seam-limit" data-reference-type="ref" data-reference="thm:seam-limit">45</a>, Theorem <a href="#thm:straddle-closed-set" data-reference-type="ref" data-reference="thm:straddle-closed-set">48</a>).*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*binary digits* [`isCompact_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L656) [`isClosed_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L660) [`volume_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L996)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_achievement_set_topology`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/AchievementSetTopologyAndFiniteHalf.lean#L27)

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

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_achievement_set_topology` | [E257_21/Challenge.lean, line 273](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L273) | [PaperStatementsAM.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAM.lean#L187) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-master-dichotomy"></a>

## Theorem (Nonmembership of one half and a finite fatal gap)

> *The value $`1/2`$ is not in $`\mathcal A`$ if and only if there are an integer $`d\ge0`$ and a finite set $`u\subseteq\{1,\ldots,d\}`$ such that
> ``` math
> X_u(2)+R_{d+1}<\frac12<X_u(2)+w_{d+1}.
> ```
> One implication is Lemma <a href="#lem:fatal-gap-exclusion" data-reference-type="ref" data-reference="lem:fatal-gap-exclusion">80</a>. For the other, follow the greedy prefixes: nonmembership forces a first failure of the tail inequality, hence one of these gaps. The endpoint equalities are excluded by Lemma <a href="#lem:half-endpoint-kills" data-reference-type="ref" data-reference="lem:half-endpoint-kills">81</a>.*
> 
> *A finite prefix and strict gap provide a nonmembership witness. The tail inequality can be certified by rational truncation bounds as in Theorem <a href="#thm:one-sided" data-reference-type="ref" data-reference="thm:one-sided">22</a>. Membership, in contrast, asserts that no such witness exists; failure to find one in a finite search is not a proof. The reduction uses $`w_n>R_n`$, not compactness alone. The totient weights fail this hypothesis, as the example after Lemma <a href="#lem:mersenne-tail-weight" data-reference-type="ref" data-reference="lem:mersenne-tail-weight">77</a> shows.*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*dedekind-cut* [`half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L654) [`half_mem_mersenneAchievementSet_or_exists_fatal_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L623)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCutLocator.lean#L654)

```lean
theorem half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ¬ ExistsFatalHalfGap
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_or_exists_fatal_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCutLocator.lean#L623)

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

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap` | [E257_21/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L260) | [PaperStatementsAM.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAM.lean#L71) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `half_mem_mersenneAchievementSet_or_exists_fatal_gap` | [E257_21/Challenge.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L264) | [PaperStatementsAM.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAM.lean#L74) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-perturbed-family-maximality"></a>

## Theorem (Perturbed-family maximality and the three-branch recurrence)

> *Use the family and adjacent pair of Definition <a href="#defn:perturbed-family" data-reference-type="ref" data-reference="defn:perturbed-family">104</a>, and assume in addition that $`B<g`$. At capacity $`C'=4C+g`$, the largest admissible updated value is $`t(x_+)`$ if $`4o+p_+\le g`$, and $`t(x_-)`$ otherwise. After this choice, apply the take-if-possible rule to an additional weight $`W=2g+4`$. The resulting remainder is
> ``` math
> \begin{cases}
>  g-4o-p_+,&4o+p_+\le g,\\
>  4r+g-p_-,&4o+p_+>g\ \text{and}\ 4r+g-p_-<W,\\
>  4r-g-p_--4,&4o+p_+>g\ \text{and}\ 4r+g-p_-\ge W.
>  \end{cases}
> ```*
> 
> *<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*abstract-perturbed-greedy* [`prefixChoice_maximal`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderIntegerGreedy.lean#L1390) [`nextRemainder_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderIntegerGreedy.lean#L1463)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.prefixChoice_maximal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderIntegerGreedy.lean#L1390)

```lean
theorem prefixChoice_maximal
    (hcap : F.pulseCap < F.gap)
    [Decidable K.successorCarries]
    {x : α} (hx : F.newSum x ≤ K.newCapacity) :
    F.newSum x ≤ F.newSum K.prefixChoice
```

2. [`Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.nextRemainder_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderIntegerGreedy.lean#L1463)

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

<a id="thm-perturbed-family-maximality-comparator"></a>

**Comparator:** not yet compared.

<a id="record-257bm-c1"></a>

## Theorem (Compactness from exact finite sums)

> *Suppose the cofinal exact-row condition in Definition <a href="#record:257bm-d4" data-reference-type="ref" data-reference="record:257bm-d4">109</a> holds. Then $`1/2\in\mathcal A`$. For each $`N`$, choose an exact row $`D_N`$ at depth $`n_N\ge\max\{N,1\}`$. Proposition <a href="#record:257bm-i9" data-reference-type="ref" data-reference="record:257bm-i9">141</a> gives
> ``` math
> \left|X_{D_N}(2)-\frac12\right|
>        \le\frac{n_N+1}{2^{n_N}}\longrightarrow0.
> ```
> Every $`X_{D_N}(2)`$ belongs to the closed set $`\mathcal A`$, so its limit does too. No finite support represents $`1/2`$; the representing support is therefore infinite. The proof does not require the chosen rows to be nested. The unproved input is their existence at unbounded depths.*
> 
> *<span class="sans-serif">(cofinal)</span> *topological-achievement-set* [`half_mem_mersenneAchievementSet_of_cofinalExactLocalRows`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCofinalExactRows.lean#L71)*

The Lean declarations below together state this result.

1. [`Erdos249257.abs_exactLocalMersenneRowValue_sub_half_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCofinalExactRows.lean#L58)

```lean
theorem abs_exactLocalMersenneRowValue_sub_half_le
    {D : Finset ℕ} {n : ℕ} (hn : 2 ≤ n)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d ≤ n)
    (hquot : localPrefixQuotient D n = 2 ^ (n - 1) - 1) :
    |exactLocalMersenneRowValue D - (1 : ℝ) / 2| ≤
      ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_of_cofinalExactLocalRows`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCofinalExactRows.lean#L71)

```lean
theorem half_mem_mersenneAchievementSet_of_cofinalExactLocalRows
    (hcofinal : CofinalExactLocalMersenneHalfRows) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

3. [`Erdos249257.HalfCarryReachability.finite_boolSupport_ne_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCarryReachability.lean#L589)

```lean
theorem finite_boolSupport_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2
```

<a id="record-257bm-c1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `abs_exactLocalMersenneRowValue_sub_half_le` | [E257_22/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L117) | [PaperStatementsAR.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAR.lean#L63) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |
| `half_mem_mersenneAchievementSet_of_cofinalExactLocalRows` | [E257_22/Challenge.lean, line 130](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L130) | [PaperStatementsAR.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAR.lean#L128) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |
| `finite_boolSupport_ne_half` | [E257_22/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L99) | [PaperStatementsAL.lean, line 48](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAL.lean#L48) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c2"></a>

## Theorem (Infinitely many greedy skips suffice)

> *Suppose that the greedy remainder for $`1/2`$ satisfies
> ``` math
> \forall N\ \exists c\ge\max\{N,4\}:\qquad
>  0<r_{c-1}(1/2)<w_c.
> ```
> Then exact quotient rows exist at unbounded depths, and $`1/2\in\mathcal A`$. A single such skip at $`c`$ gives an exact row at depth $`2c-2`$ without an additional capacity hypothesis. Taking arbitrarily large $`c`$ therefore supplies the rows needed for the compactness implication in Theorem <a href="#record:257bm-c1" data-reference-type="ref" data-reference="record:257bm-c1">110</a>. The existence of arbitrarily late positive skips is the hypothesis, not an established property of the greedy sequence. It is equivalent to half-membership and remains unproved here.*
> 
> *<span class="sans-serif">(cofinal)</span> *greedy recurrence* [`cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L84) [`half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L97) [`exactLocalMersenneHalfRow_of_positiveHalfGreedySkip`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L55)*

The Lean declarations below together state this result.

1. [`Erdos249257.exactLocalMersenneHalfRow_of_positiveHalfGreedySkip`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L55)

```lean
theorem exactLocalMersenneHalfRow_of_positiveHalfGreedySkip
    {c : ℕ} (hc : 4 ≤ c)
    (hpos : 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1))
    (hskip : greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c) :
    ExactLocalMersenneHalfRow (2 * c - 2)
```

2. [`Erdos249257.cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L84)

```lean
theorem cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    CofinalExactLocalMersenneHalfRows
```

3. [`Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L97)

```lean
theorem half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

4. [`Erdos249257.cofinalPositiveHalfGreedySkips_iff_half_mem`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L110)

```lean
theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="record-257bm-c2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exactLocalMersenneHalfRow_of_positiveHalfGreedySkip` | [E257_22/Challenge.lean, line 191](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L191) | [PaperStatementsF.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsF.lean#L134) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |
| `cofinalExactLocalMersenneHalfRows_of_positiveHalfGreedySkips` | [E257_22/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L186) | [PaperStatementsF.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsF.lean#L117) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |
| `half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips` | [E257_22/Challenge.lean, line 154](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L154) | [PaperStatementsD.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsD.lean#L174) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |
| `cofinalPositiveHalfGreedySkips_iff_half_mem` | [E257_22/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L149) | [PaperStatementsD.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsD.lean#L149) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c3"></a>

## Theorem (A compatible family of finite supports)

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
> *These are the finite hypotheses of the compatible-limit construction. The bit condition fixes coordinate $`d`$ from row $`2d`$ onward. Unlike the independent finite supports in Definition <a href="#record:257bm-d4" data-reference-type="ref" data-reference="record:257bm-d4">109</a>, the rows therefore have a prescribed common limit. This extra structure is not, by itself, a proof of strictness between the corresponding existence statements.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`GlobalBooleanMobiusRepairFeasible`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGlobalRepair.lean#L174) [`GlobalEndpointExponentialBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGlobalRepair.lean#L139) [`bit_stable`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGlobalRepair.lean#L82)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_bit_stable`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/CompatibleFiniteRowFamily.lean#L95)

```lean
theorem paper_compatible_bit_stable
    (T : BooleanMobiusGlobalRepairTrajectory) {d n : ℕ} (hdn : 2 * d ≤ n) :
    T.bit n d = T.bit (2 * d) d
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_finite_row_conditions`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/CompatibleFiniteRowFamily.lean#L111)

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

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_first_condition_gives_nonneg`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/CompatibleFiniteRowFamily.lean#L146)

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

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_rows_agree_with_limit`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/CompatibleFiniteRowFamily.lean#L158)

```lean
theorem paper_compatible_rows_agree_with_limit
    (T : BooleanMobiusGlobalRepairTrajectory) {n d : ℕ} (hd : d ≤ n / 2) :
    d ∈ globalRepairStageSupport T.bit n ↔ d ∈ globalRepairLimitSupport T
```

<a id="record-257bm-c3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_compatible_bit_stable` | [E257_22/Challenge.lean, line 261](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L261) | [PaperStructuresW.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStructuresW.lean#L37) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |
| `paper_compatible_finite_row_conditions` | [E257_19/Challenge.lean, line 300](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_19/Challenge.lean#L300) | [PaperStructuresBH.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_19/PaperStructuresBH.lean#L184) | [E257_19](../evidence/comparator/replay-35882032091/receipt-E257_19.json) |
| `paper_compatible_first_condition_gives_nonneg` | [E257_22/Challenge.lean, line 224](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L224) | [PaperStructuresAW.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStructuresAW.lean#L40) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |
| `paper_compatible_rows_agree_with_limit` | [E257_22/Challenge.lean, line 249](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L249) | [PaperStructuresT.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStructuresT.lean#L37) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c4"></a>

## Theorem (A sufficient quotient bound at a crossing)

> *Consider the following condition on finite sets $`D`$ and integers $`c\ge4`$:
> ``` math
> \begin{gathered}
>  D\subseteq\{2,\ldots,c-1\},\qquad
>  X_D(2)<\frac12<X_D(2)+w_c\\[2pt]
>  \Longrightarrow\qquad Q(D\cup\{c\},2c-2)\ge2^{2c-3}.
>  \end{gathered}
> ```
> It requires the quotient inequality at every strict crossing of one half by an added weight. Theorem <a href="#record:257bm-i5" data-reference-type="ref" data-reference="record:257bm-i5">136</a> identifies this inequality with the binary bound needed in the finite construction. If the condition holds for all such $`D,c`$, the induction below produces exact sums at unbounded depths and hence an infinite support of value $`1/2`$. The universal crossing condition itself is unproved.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`SkippedCoreCriticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L30)*

The Lean declarations below together state this result.

1. [`Erdos249257.cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1309)

```lean
theorem cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    CofinalExactLocalMersenneHalfRows
```

2. [`Erdos249257.half_mem_mersenneAchievementSet_of_criticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1321)

```lean
theorem half_mem_mersenneAchievementSet_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

3. [`Erdos249257.HalfCarryReachability.finite_boolSupport_ne_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCarryReachability.lean#L589)

```lean
theorem finite_boolSupport_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2
```

<a id="record-257bm-c4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply` | [E257_22/Challenge.lean, line 125](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L125) | [PaperStatementsAR.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAR.lean#L77) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |
| `half_mem_mersenneAchievementSet_of_criticalQuotientSupply` | [E257_22/Challenge.lean, line 135](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L135) | [PaperStatementsAR.lean, line 132](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAR.lean#L132) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |
| `finite_boolSupport_ne_half` | [E257_22/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L99) | [PaperStatementsAL.lean, line 48](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsAL.lean#L48) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c5"></a>

## Theorem (Induction from the depth-six example)

> *An already-formalised induction from the endpoint-six seed (Definition <a href="#record:257bm-i-seed" data-reference-type="ref" data-reference="record:257bm-i-seed">140</a>) consumes Theorem <a href="#record:257bm-c4" data-reference-type="ref" data-reference="record:257bm-c4">113</a> at every step: each `ProtectedExactLocalMersenneRow` either doubles below half (unconditional) or recycles at its first crossing rank $`e >`$ cutoff, giving endpoint $`2e-2 >`$ previous endpoint; `protection` (endpoint $`< 2\cdot`$cutoff, new ranks $`>`$ cutoff) is exactly what converts the non-growing recycle endpoint of the bare dichotomy (Theorem <a href="#record:257bm-k1" data-reference-type="ref" data-reference="record:257bm-k1">170</a>) into strict progress. The below-half branch never fires twice from the seed arithmetic, so the supply is needed at essentially every step. Ends literally at $`\mathrm{CofinalExactLocalMersenneHalfRows}`$.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1309) [`ProtectedExactLocalMersenneRow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1087) [`exists_laterProtectedExactLocalMersenneRow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1139)*

The Lean declarations below together state this result.

1. [`Erdos249257.ProtectedExactLocalMersenneRow`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1087)

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

2. [`Erdos249257.exists_laterProtectedExactLocalMersenneRow`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1139)

```lean
theorem exists_laterProtectedExactLocalMersenneRow
    (hcap : SkippedCoreCriticalQuotientSupply)
    (s : ProtectedExactLocalMersenneRow) :
    ∃ t : ProtectedExactLocalMersenneRow, s.endpoint < t.endpoint
```

3. [`Erdos249257.cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1309)

```lean
theorem cofinalExactLocalMersenneHalfRows_of_criticalQuotientSupply
    (hcap : SkippedCoreCriticalQuotientSupply) :
    CofinalExactLocalMersenneHalfRows
```

<a id="record-257bm-c5-comparator"></a>

**Comparator:** not yet compared.

<a id="record-257bm-c6"></a>

## Theorem (The quotient condition on greedy prefixes)

> *Let $`D_c=G\cap\{2,\ldots,c-1\}`$. The condition on the actual greedy prefixes is
> ``` math
> \begin{gathered}
>  c\ge4,\quad c\notin G\\
>  \Longrightarrow\qquad Q(D_c\cup\{c\},2c-2)\ge2^{2c-3}.
>  \end{gathered}
> ```
> It asks for the quotient bound at every skipped rank of the specified half-greedy orbit. This restricts the crossing test of Theorem <a href="#record:257bm-c4" data-reference-type="ref" data-reference="record:257bm-c4">113</a> to its actual greedy prefixes. The finite uniqueness results justify that restriction where the cited induction uses it; they do not prove the displayed inequality.*
> 
> *<span class="sans-serif">(uniform)</span> *greedy recurrence* [`HalfGreedySkippedCriticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L178)*

The Lean declaration below states this result.

[`Erdos249257.skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1068)

```lean
theorem skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped :
    SkippedCoreCriticalQuotientSupply ↔
      HalfGreedySkippedCriticalQuotientSupply
```

<a id="record-257bm-c6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `skippedCoreCriticalQuotientSupply_iff_halfGreedySkipped` | [E257_22/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_22/Challenge.lean#L199) | [PaperStatementsF.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_22/PaperStatementsF.lean#L200) | [E257_22](../evidence/comparator/replay-35882032091/receipt-E257_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c6a"></a>

## Theorem (Two consecutive skips)

> *If $`c\ge6`$ and the real half-greedy rule skips both $`c`$ and $`c+1`$, put $`D=G\cap\{2,\ldots,c-1\}`$. Then
> ``` math
> S(D,1,2c-3)<2^{c-3}.
> ```
> The one-step quotient recurrence gives $`S(D,1,2c-2)<2^{c-2}`$, so Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a> supplies an exact row at depth $`2c-2`$ whose new ranks are all greater than $`c`$. The hypothesis concerns this pair of skipped ranks; no unbounded sequence of such pairs is proved here. For the stated precritical-suffix condition at every skipped rank, the remaining tests are the skip-then-take cases, with ranks $`4`$ and $`5`$ handled separately in the cited proof.*
> 
> *<span class="sans-serif">(uniform)</span> *greedy recurrence* [`halfGreedy_precriticalSuffix_lt_of_next_skip`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L682) [`halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1001) [`halfGreedySkippedPrecriticalSuffixSupply_iff_preTake`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L838)*

The Lean declarations below together state this result.

1. [`Erdos249257.halfGreedy_precriticalSuffix_lt_of_next_skip`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L682)

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

2. [`Erdos249257.halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L1001)

```lean
theorem halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix
    (hpre : HalfGreedySkippedPrecriticalSuffixSupply) :
    HalfGreedySkippedCriticalQuotientSupply
```

where [`HalfGreedySkippedCriticalQuotientSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L178) is

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

3. [`Erdos249257.halfGreedySkippedPrecriticalSuffixSupply_iff_preTake`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L838)

```lean
theorem halfGreedySkippedPrecriticalSuffixSupply_iff_preTake :
    HalfGreedySkippedPrecriticalSuffixSupply ↔
      HalfGreedyPreTakePrecriticalSuffixSupply
```

<a id="record-257bm-c6a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `halfGreedy_precriticalSuffix_lt_of_next_skip` | [E257_23/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L120) | [PaperStatementsF.lean, line 189](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsF.lean#L189) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `halfGreedySkippedCriticalQuotientSupply_of_precriticalSuffix` | [E257_23/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L96) | [PaperStatementsF.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsF.lean#L149) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `halfGreedySkippedPrecriticalSuffixSupply_iff_preTake` | [E257_23/Challenge.lean, line 101](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L101) | [PaperStatementsF.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsF.lean#L155) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c6b"></a>

## Theorem (A later skip after a selected block)

> *Suppose the real half-greedy rule skips rank $`c`$, takes $`c+1,\ldots,c+t-1`$, and skips $`c+t`$. If
> ``` math
> 0<t\le c-3,\qquad c-2\le2^{c-t-3},
> ```
> then the precritical suffix bound at $`c`$ holds. It yields sharp capacity and hence an exact row at depth $`2c-2`$. The case $`t=1`$ includes Theorem <a href="#record:257bm-c6a" data-reference-type="ref" data-reference="record:257bm-c6a">116</a>; the proof also permits longer selected blocks. The arithmetic condition is precisely $`t\le c-3-\lceil\log_2(c-2)\rceil`$. Its role in the proof is to make the dyadic allowance $`2^{c-t-3}`$ cover the bound $`|D|\le c-2`$ for the earlier selected support.*
> 
> *To obtain cofinal exact rows by this result, the stated gap condition must hold at cofinally many skipped ranks $`c`$, not just at one rank or throughout a finite sample. A finite empirical skip frequency alone gives no such pointwise gap bound.*
> 
> *<span class="sans-serif">(uniform)</span> *greedy recurrence* [`halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L603) [`precriticalCrossingTax_of_futureThreshold`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L472) [`sub_two_le_two_pow_sub_four`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L432)*

The Lean declarations below together state this result.

1. [`Erdos249257.halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L603)

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

2. [`Erdos249257.precriticalCrossingTax_of_futureThreshold`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L472)

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

3. [`Erdos249257.sub_two_le_two_pow_sub_four`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L432)

```lean
theorem sub_two_le_two_pow_sub_four
    {c : ℕ} (hc : 6 ≤ c) :
    c - 2 ≤ 2 ^ (c - 4)
```

<a id="record-257bm-c6b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `halfGreedy_precriticalSuffix_lt_of_future_skip_after_takenBlock` | [E257_23/Challenge.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L106) | [PaperStatementsF.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsF.lean#L174) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `precriticalCrossingTax_of_futureThreshold` | [E257_23/Challenge.lean, line 185](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L185) | [PaperStatementsAR.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAR.lean#L187) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `sub_two_le_two_pow_sub_four` | [E257_23/Challenge.lean, line 133](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L133) | [PaperStatementsAA.lean, line 93](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAA.lean#L93) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c7"></a>

## Theorem (Filling the remaining binary positions)

> *For any $`c\ge4`$ and any finite $`D\subseteq[2,c)`$ with $`\mathrm{value}(D)<1/2`$ and the sharp capacity
> ``` math
> \ensuremath{S}(D,1,2c-2) < 2^{c-2},
> ```
> there is an exact row $`E`$ at endpoint $`2c-2`$ with $`D\subseteq E`$ and every new rank strictly above $`c`$. The implication requires the displayed capacity bound, but neither a crossing condition nor a specified real greedy prefix. The crossing hypothesis used in Theorem <a href="#record:257bm-c4" data-reference-type="ref" data-reference="record:257bm-c4">113</a> is one way to seek that input, not an additional premise of this filling result. No strict comparison between the corresponding cofinal existence statements is asserted.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRow.lean#L238)*

The Lean declaration below states this result.

[`Erdos249257.exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusSkipRow.lean#L238)

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
| `exists_exactRowStrictUpperFill_of_skippedCoreSharpCapacity` | [E257_23/Challenge.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L171) | [PaperStatementsAR.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAR.lean#L119) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c8"></a>

## Theorem (An exact sum at depth $`2c-2`$)

> *Under the hypotheses of Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a>, there is a set $`E\subseteq\{2,\ldots,2c-2\}`$ with
> ``` math
> Q(E,2c-2)=2^{2c-3}-1.
> ```
> This conclusion forgets the additional support-extension information in that theorem. It is the form used when only the existence of an exact row is needed.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRow.lean#L332)*

The Lean declaration below states this result.

[`Erdos249257.exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusSkipRow.lean#L332)

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
| `exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCoreSharpCapacity` | [E257_23/Challenge.lean, line 162](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L162) | [PaperStatementsAR.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAR.lean#L96) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c9"></a>

## Proposition (Quotients in the upper half of the index range)

> *For integers $`d\ge2`$ and $`d\le M<2d`$,
> ``` math
> q(M,d)=\left\lfloor\frac{2^M}{2^d-1}\right\rfloor=2^{M-d}.
> ```
> Indeed, the quotient is $`2^{M-d}+2^{M-d}/(2^d-1)`$, whose second term is strictly between zero and one. In Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a>, the available ranks $`d=c+1,\ldots,2c-2`$ therefore supply the binary weights $`2^{c-3},\ldots,1`$. They represent every integer from $`0`$ to $`2^{c-2}-1`$, which explains both the capacity bound and the choice of terminal depth.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`localMersenneQuotient_eq_two_pow_sub_of_half_lt`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusLocalRepair.lean#L26)*

The Lean declarations below together state this result.

1. [`Erdos249257.localMersenneQuotient_eq_two_pow_sub_of_half_lt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusLocalRepair.lean#L26)

```lean
theorem localMersenneQuotient_eq_two_pow_sub_of_half_lt
    {M d : ℕ} (hd2 : 2 ≤ d) (hhalf : M / 2 < d) (hdM : d ≤ M) :
    localMersenneQuotient M d = 2 ^ (M - d)
```

2. [`Erdos249257.exists_boolean_word_of_lt_two_pow`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusLocalRepair.lean#L525)

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
| `localMersenneQuotient_eq_two_pow_sub_of_half_lt` | [E257_23/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L223) | [PaperStatementsAD.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAD.lean#L114) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `exists_boolean_word_of_lt_two_pow` | [E257_23/Challenge.lean, line 215](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L215) | [PaperStatementsAD.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAD.lean#L103) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c10"></a>

## Theorem (A finite sum from a skipped prefix)

> *Let $`c\ge4`$ and $`D\subseteq\{2,\ldots,c-1\}`$ satisfy
> ``` math
> 0<\frac12-X_D(2)<\frac1{2^c-1}.
> ```
> Then there is $`E`$ with $`D\subseteq E\subseteq\{2,\ldots,2c-2\}`$ and $`Q(E,2c-2)=2^{2c-3}-1`$. No separate sharp-capacity assumption is required. The binary completion in the linked proof uses ranks $`c,\ldots,2c-2`$; it may therefore insert $`c`$. Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a> instead assumes the sharper $`(c-2)`$-bit bound so that every added rank is strictly greater than $`c`$.*
> 
> *<span class="sans-serif">(bounded)</span> *binary digits* [`exactLocalMersenneHalfRow_two_mul_sub_two_of_skippedCore`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRow.lean#L149)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_from_skipped_prefix`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L264)

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
| `paper_exact_row_from_skipped_prefix` | [E257_23/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L199) | [PaperStatementsAR.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsAR.lean#L228) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c11"></a>

## Theorem (Testing one nearest dyadic boundary)

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
> ```
> The first condition is $`\mathrm{DyadicBandEscape}(d,E)`$ and $`j_*`$ satisfies $`\mathrm{CriticalDyadicBandIndex}(d,E,j_*)`$.*
> 
> *<span class="sans-serif">(uniform)</span> *dyadic-boundary* [`CriticalDyadicBandIndex`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L33) [`dyadicBandEscape_iff_exists_critical`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L108) [`seamUpperResetCriticalBandEscape_iff`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L883) [`half_mem_mersenneAchievementSet_of_upperResetCriticalBandEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L896)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_band_index_unique`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/DyadicBandAndTwoSidedBounds.lean#L26)

```lean
theorem paper_critical_dyadic_band_index_unique {d E : ℕ}
    (hE : E ≤ 2 ^ (d + 1)) :
    ∃! j : ℕ, CriticalDyadicBandIndex d E j
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_boundary_is_smallest`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/DyadicBandAndTwoSidedBounds.lean#L52)

```lean
theorem paper_critical_dyadic_boundary_is_smallest {d E j : ℕ}
    (hj : CriticalDyadicBandIndex d E j) :
    E ≤ 2 ^ (d - j + 1) ∧
      ∀ i : ℕ, i ≤ d → E ≤ 2 ^ (d - i + 1) →
        (2 : ℕ) ^ (d - j + 1) ≤ 2 ^ (d - i + 1)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_dyadic_band_index_eq_top_of_le_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/DyadicBandAndTwoSidedBounds.lean#L71)

```lean
theorem paper_critical_dyadic_band_index_eq_top_of_le_two {d E j : ℕ}
    (hE : E ≤ 2) (hj : CriticalDyadicBandIndex d E j) :
    j = d
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_dyadic_band_escape_iff_single_test`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/DyadicBandAndTwoSidedBounds.lean#L89)

```lean
theorem paper_dyadic_band_escape_iff_single_test {d E j : ℕ}
    (hj : CriticalDyadicBandIndex d E j) :
    DyadicBandEscape d E ↔ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)
```

<a id="record-257bm-c11-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_critical_dyadic_band_index_unique` | [E257_23/Challenge.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L246) | [PaperStatementsBE.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsBE.lean#L21) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `paper_critical_dyadic_boundary_is_smallest` | [E257_23/Challenge.lean, line 251](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L251) | [PaperStatementsBE.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsBE.lean#L25) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `paper_critical_dyadic_band_index_eq_top_of_le_two` | [E257_23/Challenge.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L241) | [PaperStatementsBE.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsBE.lean#L17) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |
| `paper_dyadic_band_escape_iff_single_test` | [E257_23/Challenge.lean, line 258](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_23/Challenge.lean#L258) | [PaperStatementsBE.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_23/PaperStatementsBE.lean#L31) | [E257_23](../evidence/comparator/replay-35882032091/receipt-E257_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c12"></a>

## Proposition (An upper bound for the reset expression)

> *Let $`d\ge5`$ be an actual upper-reset row. Write $`E_d`$ for its reset charge, the sum of four times the adjacent upper overshoot and the corresponding nonnegative correction term. The upper-reset identity is
> ``` math
> \mathrm{rem}(d+1)+E_d=2^{d+1}.
> ```
> The nonnegativity of the successor remainder therefore gives $`E_d\le2^{d+1}`$, the side condition needed for Theorem <a href="#record:257bm-c11" data-reference-type="ref" data-reference="record:257bm-c11">122</a>. This argument uses the upper-reset branch assumption. It does not require the separate, conditional two-sided bound of Theorem <a href="#thm:two-sided-dyadic" data-reference-type="ref" data-reference="thm:two-sided-dyadic">52</a>, and does not assert the charge bound at arbitrary rows.*
> 
> *<span class="sans-serif">(uniform)</span> *dyadic-boundary* [`seamUpperResetCharge_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L131)*

The Lean declarations below together state this result.

1. [`Erdos249257.seamUpperBranch_remainder_add_resetCharge_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3542)

```lean
theorem seamUpperBranch_remainder_add_resetCharge_eq
    {d : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    seamIntegerGreedyRemainder (d + 1) +
        (4 * (seamAdjacentCut d hd5).overshoot +
          (seamAdjacentCut d hd5).abovePulse) =
      2 ^ (d + 1)
```

2. [`Erdos249257.HalfUpperResetCriticalBand.seamUpperResetCharge_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfUpperResetCriticalBand.lean#L131)

```lean
theorem seamUpperResetCharge_le
    {d : ℕ} (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    seamUpperResetCharge d hd5 ≤ 2 ^ (d + 1)
```

<a id="record-257bm-c12-comparator"></a>

**Comparator:** not yet compared.

<a id="record-257bm-c14"></a>

## Theorem (An equivalent vanishing condition)

> *``` math
> \begin{gathered}
>  \forall\ \text{skipped rank }n\ge3\text{ whose actual word equals the seam-greedy word},\\
>  \text{the integer remainder at }n\text{ is zero}.
> \end{gathered}
> ```
> This condition is equivalent to Definition <a href="#record:257bm-c13" data-reference-type="ref" data-reference="record:257bm-c13">124</a>. At an actual skipped rank, the source proves that $`F(n-1,n)<0`$ holds exactly when the real prefix agrees with the integer greedy word and its integer remainder is positive. On agreement, $`F(n-1,n)`$ is the negative of that nonnegative remainder. Thus nonnegativity of the margin at every skip is equivalent to vanishing of the remainder at every aligned skip. The equivalence is proved; neither condition is established for all required ranks. Its formal statement is `skippedSeamAlignmentZero_iff_skippedFullShellNonnegative`.*
> 
> *<span class="sans-serif">(uniform)</span> *frozen-margin* [`HalfGreedySkippedSeamAlignmentZero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L593) [`skippedSeamAlignmentZero_iff_skippedFullShellNonnegative`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L671)*

The Lean declarations below together state this result.

1. [`Erdos249257.skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L569)

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

2. [`Erdos249257.greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L531)

```lean
theorem greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment
    (n : ℕ) (hn : 3 ≤ n)
    (halign :
      stemBits n (halfGreedyPrefixSupport (n - 1)) =
        integerGreedyBits (seamWeights n) (seamSubsetTarget n)) :
    greedyHalfFrozenMargin (n - 1) n =
      -(seamIntegerGreedyRemainder n : ℤ)
```

3. [`Erdos249257.skippedSeamAlignmentZero_iff_skippedFullShellNonnegative`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L671)

```lean
theorem skippedSeamAlignmentZero_iff_skippedFullShellNonnegative :
    HalfGreedySkippedSeamAlignmentZero ↔
      HalfGreedySkippedFullShellNonnegative
```

<a id="record-257bm-c14-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `skipped_fullShell_neg_iff_alignment_and_seamRemainder_pos` | [E257_24/Challenge.lean, line 143](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_24/Challenge.lean#L143) | [PaperStructuresBJ.lean, line 1347](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_24/PaperStructuresBJ.lean#L1347) | [E257_24](../evidence/comparator/replay-35882032091/receipt-E257_24.json) |
| `greedyHalfFrozenMargin_fullShell_eq_neg_seamRemainder_of_alignment` | [E257_16/Challenge.lean, line 307](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_16/Challenge.lean#L307) | [PaperStructuresBI.lean, line 254](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_16/PaperStructuresBI.lean#L254) | [E257_16](../evidence/comparator/replay-35882032091/receipt-E257_16.json) |
| `skippedSeamAlignmentZero_iff_skippedFullShellNonnegative` | [E257_13/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L260) | [PaperStructuresBJ.lean, line 1313](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStructuresBJ.lean#L1313) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c15"></a>

## Theorem (A sufficient lower bound for the integer remainder)

> *``` math
> \forall\ \text{skipped rank }n\ge3,\quad B(2n) < \mathrm{rem}(n),
> ```
> a sufficient condition for the nonnegativity condition above. Indeed, a negative margin at an actual skip would force $`1\le\mathrm{rem}(n)\le B(2n)`$, contradicting this bound. This proves the implication, not a converse or strict separation of the conditions.*
> 
> *<span class="sans-serif">(uniform)</span> *frozen-margin* [`HalfGreedySkippedSeamEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L687) [`governedFrozenMarginProducer_of_skippedSeamEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFullShellSeamBridge.lean#L695)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_forces_remainder_band`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamEscapeAndTerminalStrip.lean#L36)

```lean
theorem paper_seam_escape_forces_remainder_band
    {n : ℕ} (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))
    (hneg : greedyHalfFrozenMargin (n - 1) n < 0) :
    1 ≤ seamIntegerGreedyRemainder n ∧
      seamIntegerGreedyRemainder n ≤ halfStripBound (2 * n)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_full_shell_nonnegative`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamEscapeAndTerminalStrip.lean#L47)

```lean
theorem paper_seam_escape_implies_full_shell_nonnegative
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    HalfGreedySkippedFullShellNonnegative
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_half_membership`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamEscapeAndTerminalStrip.lean#L61)

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
| `paper_seam_escape_forces_remainder_band` | [E257_25/Challenge.lean, line 329](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_25/Challenge.lean#L329) | [PaperStructuresBK.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_25/PaperStructuresBK.lean#L260) | [E257_25](../evidence/comparator/replay-35882032091/receipt-E257_25.json) |
| `paper_seam_escape_implies_full_shell_nonnegative` | [E257_25/Challenge.lean, line 337](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_25/Challenge.lean#L337) | [PaperStructuresBK.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_25/PaperStructuresBK.lean#L269) | [E257_25](../evidence/comparator/replay-35882032091/receipt-E257_25.json) |
| `paper_seam_escape_implies_half_membership` | [E257_26/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L117) | [PaperStructuresBW.lean, line 304](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStructuresBW.lean#L304) | [E257_26](../evidence/comparator/replay-35882032091/receipt-E257_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-c16"></a>

## Theorem (A square-root carry bound implies half-membership)

> *Write $`G`$ for the greedy support and $`C_G(N)`$ for its centred carry. If
> ``` math
> \forall N,\qquad C_G(N) \le 2\sqrt N + 4,
> ```
> then the greedy selected support $`G`$ is infinite and $`X_G(2)=1/2`$. Nonnegativity of $`C_G`$ is unconditional (see Theorem <a href="#thm:mobius-centred-nonneg" data-reference-type="ref" data-reference="thm:mobius-centred-nonneg">54</a> and the greedy case above); only the upper $`2\sqrt N+4`$ bound remains open. This is a different hypothesis from the dyadic-band condition and the largest-skip condition; logical independence is not asserted.*
> 
> *<span class="sans-serif">(cofinal)</span> *sqrt-carry-growth* [`infinite_support_half_of_mobiusCenteredHalfCarry_sqrtBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L817) [`greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L834)*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfCarryReachability.greedy_mobiusCenteredHalfCarry_nonneg`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCarryReachability.lean#L919)

```lean
theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N
```

2. [`Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCarryReachability.lean#L953)

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
| `greedy_mobiusCenteredHalfCarry_nonneg` | [E257_13/Challenge.lean, line 144](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L144) | [PaperStatementsD.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsD.lean#L139) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |
| `greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound` | [E257_26/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L152) | [PaperStatementsD.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsD.lean#L120) | [E257_26](../evidence/comparator/replay-35882032091/receipt-E257_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-c17"></a>

## Theorem (Terminal bounds at unbounded depths)

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
> 
> *<span class="sans-serif">(cofinal)</span> *sqrt-carry-growth* [`HalfCarryCofinalTerminalOnlyStrip`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TerminalOnlyCofinal.lean#L34) [`exists_infinite_support_half_of_cofinalTerminalOnlyStrip`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TerminalOnlyCofinal.lean#L192)*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_forces_half_membership`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TerminalStripExactRowGap.lean#L44)

```lean
theorem paper_terminal_strip_forces_half_membership
    (hcofinal : ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ ∃ D : Finset ℕ,
      (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧
      |(integerHalfCarry (↑D : Set ℕ) (M - 1) : ℝ)| ≤ (halfStripBound M : ℝ)) :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ erdosSupportSeries 2 A = (1 : ℝ) / 2
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TerminalStripExactRowGap.lean#L88)

```lean
theorem paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) =
      (2 : ℤ) ^ (M - 1) - (localPrefixQuotient D M : ℤ)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_integerHalfCarry_eq_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TerminalStripExactRowGap.lean#L106)

```lean
theorem paper_exact_row_integerHalfCarry_eq_one
    {D : Finset ℕ} {M : ℕ} (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hexact : localPrefixQuotient D M = 2 ^ (M - 1) - 1) :
    integerHalfCarry (↑D : Set ℕ) (M - 1) = 1
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_witness_six`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TerminalStripExactRowGap.lean#L122)

```lean
theorem paper_terminal_strip_witness_six :
    (∀ d ∈ ({2, 3} : Finset ℕ), 2 ≤ d ∧ d ≤ 6) ∧
      localPrefixQuotient ({2, 3} : Finset ℕ) 6 = 30 ∧
      integerHalfCarry (↑({2, 3} : Finset ℕ) : Set ℕ) (6 - 1) = 2 ∧
      |(integerHalfCarry (↑({2, 3} : Finset ℕ) : Set ℕ) (6 - 1) : ℝ)| ≤
        (halfStripBound 6 : ℝ) ∧
      localPrefixQuotient ({2, 3} : Finset ℕ) 6 ≠ 2 ^ (6 - 1) - 1
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_both_cofinal_statements_iff_half_membership`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TerminalStripExactRowGap.lean#L160)

```lean
theorem paper_both_cofinal_statements_iff_half_membership :
    ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows) ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip)
```

<a id="record-257rig-c17-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_terminal_strip_forces_half_membership` | [E257_26/Challenge.lean, line 224](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L224) | [PaperStatementsL.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsL.lean#L63) | [E257_26](../evidence/comparator/replay-35882032091/receipt-E257_26.json) |
| `paper_integerHalfCarry_eq_two_pow_sub_localPrefixQuotient` | [E257_26/Challenge.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L245) | [PaperStatementsQ.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsQ.lean#L40) | [E257_26](../evidence/comparator/replay-35882032091/receipt-E257_26.json) |
| `paper_exact_row_integerHalfCarry_eq_one` | [E257_26/Challenge.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L239) | [PaperStatementsQ.lean, line 33](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsQ.lean#L33) | [E257_26](../evidence/comparator/replay-35882032091/receipt-E257_26.json) |
| `paper_terminal_strip_witness_six` | [E257_26/Challenge.lean, line 170](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L170) | [PaperStatementsAT.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsAT.lean#L32) | [E257_26](../evidence/comparator/replay-35882032091/receipt-E257_26.json) |
| `paper_both_cofinal_statements_iff_half_membership` | [E257_26/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L212) | [PaperStatementsK.lean, line 101](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsK.lean#L101) | [E257_26](../evidence/comparator/replay-35882032091/receipt-E257_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-c18"></a>

## Theorem (Cofinal returns of the greedy carry)

> *Suppose that for every $`N\ge0`$ there is $`M\ge N`$ such that
> ``` math
> \operatorname{ihc}(G,M)\le B(M+1)
>        =2\lfloor\sqrt{M+1}\rfloor+4.
> ```
> Then $`G`$ is infinite and $`X_G(2)=1/2`$. Unlike Theorem <a href="#record:257rig-c16" data-reference-type="ref" data-reference="record:257rig-c16">127</a>, this hypothesis bounds the actual greedy carry only at unboundedly many indices. It still concerns the same fixed support $`G`$, not independently chosen finite supports. The last source below compares this carry with the carry obtained by fixing a finite prefix. Its comparison includes a contribution from later omitted ranks. No equivalence with the finite-support hypothesis of Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a> follows without controlling that additional contribution.*
> 
> *<span class="sans-serif">(cofinal)</span> *sqrt-carry-growth* [`GreedyHalfCarryCofinalStripReturn`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CofinalStripReturn.lean#L76) [`greedy_half_infinite_of_cofinalStripReturn`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CofinalStripReturn.lean#L130) [`halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L949)*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CofinalStripReturn.lean#L130)

```lean
theorem greedy_half_infinite_of_cofinalStripReturn
    (hreturn : GreedyHalfCarryCofinalStripReturn) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2
```

2. [`Erdos249257.halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L949)

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
| `greedy_half_infinite_of_cofinalStripReturn` | [E257_26/Challenge.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_26/Challenge.lean#L145) | [PaperStatementsD.lean, line 98](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_26/PaperStatementsD.lean#L98) | [E257_26](../evidence/comparator/replay-35882032091/receipt-E257_26.json) |
| `halfGreedy_precriticalSuffix_lt_iff_futureSkipCoverage` | [E257_27/Challenge.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L109) | [PaperStatementsF.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsF.lean#L150) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c19"></a>

## Theorem (An eventual nonnegative margin suffices)

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
> 
> *<span class="sans-serif">(uniform)</span> *frozen-margin* [`exists_greedyHalfFrozenMargin_nonneg_of_excess_neg`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFiniteShadow.lean#L1198) [`exists_greedyHalfFrozenMargin_nonneg_iff_excess_neg`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFiniteShadow.lean#L1229)*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L56)

```lean
theorem paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc (k : ℕ) :
    (↑(halfGreedyPrefixSupport k) : Set ℕ) =
      greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Icc 2 k
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_eventual_nonnegative_margin_equivalence`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L131)

```lean
theorem paper_eventual_nonnegative_margin_equivalence {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) ↔
      ∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_value`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L165)

```lean
theorem paper_frozen_margin_normalised_value (k J : ℕ) :
    (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J =
      (∑ i ∈ Finset.Icc 1 J,
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + i) : ℝ) /
            (2 : ℝ) ^ i) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_monotone`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L180)

```lean
theorem paper_frozen_margin_normalised_monotone (k : ℕ) :
    Monotone (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J)
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_eq_coeffTail_sub_carry`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L200)

```lean
theorem paper_eta_eq_coeffTail_sub_carry (k : ℕ) :
    1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k =
      binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ)
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_tendsto`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L221)

```lean
theorem paper_frozen_margin_normalised_tendsto (k : ℕ) :
    Tendsto (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J)
      atTop
      (nhds (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k))
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_limit_pos_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L239)

```lean
theorem paper_frozen_margin_limit_pos_iff (k : ℕ) :
    0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k ↔
      greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1)
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_greedyHalfRemainder_ne_dyadicCap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L92)

```lean
theorem paper_greedyHalfRemainder_ne_dyadicCap {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k ≠ halfDyadicCap (k + 1)
```

9. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_coeffTail_le_index_add_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L258)

```lean
theorem paper_coeffTail_le_index_add_two (A : Set ℕ) (m : ℕ) :
    binaryCoeffTail (supportCoeff A) m ≤ (m : ℝ) + 2
```

10. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_effective_horizon_test`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L266)

```lean
theorem paper_effective_horizon_test (k J : ℕ)
    (heta : 0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)
    (htest : ((k + J + 3 : ℕ) : ℝ) / (2 : ℝ) ^ J <
      1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) :
    0 < greedyHalfFrozenMargin k J
```

11. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_hasRationalValue`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/EventualNonnegativeMargin.lean#L311)

```lean
theorem paper_eta_hasRationalValue (k : ℕ) :
    HasRationalValue
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)
```

<a id="record-257bm-c19-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc` | [E257_27/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L212) | [PaperStatementsN.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L180) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_eventual_nonnegative_margin_equivalence` | [E257_27/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L180) | [PaperStatementsN.lean, line 142](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L142) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_frozen_margin_normalised_value` | [E257_27/Challenge.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L200) | [PaperStatementsN.lean, line 166](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L166) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_frozen_margin_normalised_monotone` | [E257_27/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L190) | [PaperStatementsN.lean, line 154](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L154) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_eta_eq_coeffTail_sub_carry` | [E257_27/Challenge.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L168) | [PaperStatementsN.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L128) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_frozen_margin_normalised_tendsto` | [E257_27/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L194) | [PaperStatementsN.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L159) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_frozen_margin_limit_pos_iff` | [E257_27/Challenge.lean, line 185](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L185) | [PaperStatementsN.lean, line 148](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L148) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_greedyHalfRemainder_ne_dyadicCap` | [E257_27/Challenge.lean, line 208](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L208) | [PaperStatementsN.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L175) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_coeffTail_le_index_add_two` | [E257_27/Challenge.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L128) | [PaperStatementsAL.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsAL.lean#L65) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_effective_horizon_test` | [E257_27/Challenge.lean, line 161](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L161) | [PaperStatementsN.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L120) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |
| `paper_eta_hasRationalValue` | [E257_27/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L175) | [PaperStatementsN.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsN.lean#L136) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-c20"></a>

## Theorem (Half-membership and infinitely many skips)

> *``` math
> (1/2:\mathbb{R})\in\ensuremath{\mathcal A} \;\Longleftrightarrow\; (\mathrm{greedyMersenneSkippedSupport}(1/2)).\mathrm{Infinite}.
> ```
> Odd-denominator parity supplies the positivity clause in Theorem <a href="#record:257bm-c2" data-reference-type="ref" data-reference="record:257bm-c2">111</a> automatically. Thus its cofinal-positive-skip hypothesis is exactly the assertion that the greedy skipped support is infinite, which the displayed theorem identifies with half-membership. See Observation <a href="#record:257bm-k5" data-reference-type="ref" data-reference="record:257bm-k5">175</a> for the reason this restatement does not itself prove membership.*
> 
> *<span class="sans-serif">(cofinal)</span> *topological-achievement-set* [`half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L2583) [`mem_mersenneAchievementSet_of_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1528)*

The Lean declarations below together state this result.

1. [`Erdos249257.half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L2583)

```lean
theorem half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite
```

2. [`Erdos249257.mem_mersenneAchievementSet_of_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GreedyAchievementSet.lean#L1528)

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
| `half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite` | [E257_15/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_15/Challenge.lean#L117) | [PaperStatementsB.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_15/PaperStatementsB.lean#L62) | [E257_15](../evidence/comparator/replay-35882032091/receipt-E257_15.json) |
| `mem_mersenneAchievementSet_of_greedySkippedSupport_infinite` | [E257_27/Challenge.lean, line 235](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_27/Challenge.lean#L235) | [PaperStatementsB.lean, line 108](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_27/PaperStatementsB.lean#L108) | [E257_27](../evidence/comparator/replay-35882032091/receipt-E257_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i1a"></a>

## Theorem (The next floor quotient)

> *For $`d\ge2`$ and $`M\ge0`$, the floor quotient satisfies
> ``` math
> q(M+1,d)=2q(M,d)+\mathbf1_{d\mid M+1}.
> ```
> Indeed, $`q(M,d)=\sum_{j=1}^{\lfloor M/d\rfloor}2^{M-jd}`$. Increasing $`M`$ doubles each existing term and adds $`1`$ exactly when $`M+1`$ is divisible by $`d`$. Thus a quotient doubles or doubles plus one; it does not remain unchanged except when both values are zero. Summing over a fixed finite support gives the corresponding update with added term $`c_D(M+1)`$.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`localMersenneQuotient_endpoint_succ`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactTransition.lean#L29)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L37)

```lean
theorem paper_next_floor_quotient {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient (M + 1) d =
      2 * localMersenneQuotient M d + (if d ∣ M + 1 then 1 else 0)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient_no_fixed_point`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L74)

```lean
theorem paper_next_floor_quotient_no_fixed_point {M d : ℕ} (hd : 2 ≤ d)
    (hfix : localMersenneQuotient (M + 1) d = localMersenneQuotient M d) :
    localMersenneQuotient M d = 0 ∧ localMersenneQuotient (M + 1) d = 0
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_next_quotient_sum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L82)

```lean
theorem paper_next_quotient_sum {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M + endpointDivisorContribution D (M + 1)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_floor_quotient_geometric_sum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L44)

```lean
theorem paper_floor_quotient_geometric_sum {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = ∑ j ∈ Finset.Icc 1 (M / d), 2 ^ (M - j * d)
```

<a id="record-257bm-i1a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_next_floor_quotient` | [E257_28/Challenge.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L67) | [PaperStatementsAK.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L22) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_next_floor_quotient_no_fixed_point` | [E257_28/Challenge.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L72) | [PaperStatementsAK.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L26) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_next_quotient_sum` | [E257_28/Challenge.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L77) | [PaperStatementsAK.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L30) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_floor_quotient_geometric_sum` | [E257_28/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L63) | [PaperStatementsAK.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L19) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i1b"></a>

## Theorem (The next quotient sum)

> *For a fixed finite set $`D\subseteq\{2,3,\ldots\}`$ and $`M\ge0`$,
> ``` math
> Q(D,M+1)=2Q(D,M)+c_D(M+1).
> ```
> This is the sum of Theorem <a href="#record:257bm-i1a" data-reference-type="ref" data-reference="record:257bm-i1a">132</a> over $`d\in D`$. Keeping $`D`$ fixed is essential: changing the support between steps adds a separate difference of quotient sums. The exclusion of $`d=1`$ is also essential for the displayed correction term, since $`q(M,1)=2^M`$ doubles without an added unit.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`localPrefixQuotient_succ`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactTransition.lean#L131)*

The Lean declaration below states this result.

[`Erdos249257.localPrefixQuotient_succ`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusExactTransition.lean#L131)

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
| `localPrefixQuotient_succ` | [E257_28/Challenge.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L107) | [PaperStatementsAD.lean, line 112](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAD.lean#L112) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i1c"></a>

## Theorem (The signed endpoint recurrence)

> *The signed next-step expression is $`H(D,k,n)=2S(D,k,n-1)+1-c_D(n)`$. The last term counts the selected exponents dividing the new endpoint. This is the same recurrence shape as the generic tempered-orbit recurrence $`u(N+1)=2u(N)-v\cdot c(N+1)`$ from the public `GenericTailOrbitRigidity.lean` T7 criterion (Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a> below), specialised to Mersenne local repair. A matching recurrence alone does not imply rationality: Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a> also requires one fixed coefficient sequence, integer states and a vanishing scaled limit. Those additional conditions must be checked before that criterion can be applied to these finite-row quantities.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`localEndpointDefect_succ`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactTransition.lean#L189) [`localRepairInteger_eq_localEndpointDefect_succ`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactTransition.lean#L203)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_recurrence`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L92)

```lean
theorem paper_signed_endpoint_recurrence (D : Finset ℕ) (k n : ℕ) :
    localRepairInteger D k n =
      2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
        (endpointDivisorContribution D n : ℤ)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_endpoint_term_counts_divisors`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L99)

```lean
theorem paper_endpoint_term_counts_divisors {D : Finset ℕ} {n : ℕ}
    (hn : 0 < n) :
    endpointDivisorContribution D n = (D.filter fun d ↦ d ∣ n).card ∧
      endpointDivisorContribution D n = supportCoeff (↑D : Set ℕ) n
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_defect_succ`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L106)

```lean
theorem paper_signed_endpoint_defect_succ {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    localEndpointDefect D (M + 1) =
      2 * localEndpointDefect D M + 1 -
        (endpointDivisorContribution D (M + 1) : ℤ)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_repair_integer_eq_endpoint_defect`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L114)

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
| `paper_signed_endpoint_recurrence` | [E257_28/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L96) | [PaperStatementsAK.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L46) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_endpoint_term_counts_divisors` | [E257_28/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L150) | [PaperStatementsAN.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAN.lean#L28) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_signed_endpoint_defect_succ` | [E257_28/Challenge.lean, line 89](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L89) | [PaperStatementsAK.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L40) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_repair_integer_eq_endpoint_defect` | [E257_28/Challenge.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L83) | [PaperStatementsAK.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAK.lean#L35) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i5"></a>

## Theorem (Equivalent forms of the sharper bound)

> *Under the hypotheses of Definition <a href="#record:257bm-i-cap" data-reference-type="ref" data-reference="record:257bm-i-cap">135</a>:
> ``` math
> \ensuremath{S}(D,1,2c-2) < 2^{c-2} \;\Longleftrightarrow\; 2^{(2c-2)-1} \le \ensuremath{Q}(\mathrm{insert}\ c\ D,\ 2c-2).
> ```
> The threshold on the right is one greater than the exact-row target $`2^{2c-3}-1`$. Thus this is a test for omitting rank $`c`$, not for including it in the completed row.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkippedCoreCriticalCapacity.lean#L22)*

The Lean declaration below states this result.

[`Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusSkippedCoreCriticalCapacity.lean#L22)

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
| `localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff` | [E257_28/Challenge.lean, line 215](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L215) | [PaperStatementsAR.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAR.lean#L171) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i6"></a>

## Theorem (An unconditional bound with one extra bit)

> *Unconditionally, for every $`c\ge4`$ and every below-half core $`D\subseteq[2,c)`$ with deficit $`<\ensuremath{w}(c)`$:
> ``` math
> \ensuremath{S}(D,1,2c-2) < 2^{c-1}.
> ```
> The bound holds uniformly in $`c`$, but is twice the threshold needed in Theorem <a href="#record:257bm-i5" data-reference-type="ref" data-reference="record:257bm-i5">136</a> to apply Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a>. Before using $`|D|\le c-2\le2^{c-2}`$, the proof gives the sharper additive estimate $`\ensuremath{S}(D,1,2c-2)<2^{c-2}+|D|`$. Thus the critical-capacity inequality would follow by excluding the integer band $`[2^{c-2},\,2^{c-2}+c-3]`$, which contains $`c-2`$ integers. This is the same band shape as Theorem <a href="#record:257bm-c11" data-reference-type="ref" data-reference="record:257bm-c11">122</a>’s dyadic-band condition. Its width is linear in $`c`$, whereas the square-root reset condition discussed in Section <a href="#sec:o4" data-reference-type="ref" data-reference="sec:o4">12.5</a> has width $`2^{(r+5)/2}`$ in a different parameter $`r`$. Comparing these widths alone proves no implication between the two hypotheses.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`localBinarySuffix_two_mul_sub_two_lt_upperHalfCapacity`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkippedCoreExactRow.lean#L123) [`exists_upperHalfBooleanWord_of_skippedCore`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkippedCoreExactRow.lean#L228)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_unconditional_bound_one_extra_bit`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L126)

```lean
theorem paper_unconditional_bound_one_extra_bit {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 1) ∧ D.card ≤ c - 2
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharper_additive_estimate`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L141)

```lean
theorem paper_sharper_additive_estimate {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hskip : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) + D.card
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_capacity_band_exclusion`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MersenneQuotientRowRecurrences.lean#L236)

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
| `paper_unconditional_bound_one_extra_bit` | [E257_28/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L255) | [PaperStatementsAS.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAS.lean#L43) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_sharper_additive_estimate` | [E257_28/Challenge.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L247) | [PaperStatementsAS.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAS.lean#L31) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_capacity_band_exclusion` | [E257_28/Challenge.lean, line 225](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L225) | [PaperStatementsAR.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAR.lean#L228) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i7"></a>

## Theorem (The binary bound after doubling)

> *Let $`n\ge6`$ and $`D\subseteq\{2,\ldots,n\}`$ satisfy $`2\in D`$, $`Q(D,n)=2^{n-1}-1`$, and $`X_D(2)<1/2`$. Then
> ``` math
> S(D,1,2n-1)<2^{n-1}.
> ```
> The missing quotient can therefore be filled using only the ranks $`n+1,\ldots,2n-1`$, without changing $`D`$.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDoubling.lean#L44)*

The Lean declarations below together state this result.

1. [`Erdos249257.localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusExactRowDoubling.lean#L44)

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

2. [`Erdos249257.exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusExactRowDoubling.lean#L185)

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
| `localBinarySuffix_two_mul_sub_one_lt_upperWindow_of_exact_below` | [E257_28/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L205) | [PaperStatementsAR.lean, line 162](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAR.lean#L162) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `exists_exactRowStrictUpperExtension_two_mul_sub_one_of_exact_below` | [E257_28/Challenge.lean, line 189](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L189) | [PaperStatementsAR.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAR.lean#L115) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i-rank2"></a>

## Proposition (Every exact sum contains exponent two)

> *Let $`n\ge3`$ and let $`D\subseteq\{2,\ldots,n\}`$ satisfy $`Q(D,n)=2^{n-1}-1`$. Then $`2\in D`$. Thus the rank-two hypothesis in Theorem <a href="#record:257bm-i7" data-reference-type="ref" data-reference="record:257bm-i7">138</a> is automatic for its exact rows. The interval restriction on $`D`$ is part of the assertion, not an assumption about arbitrary finite quotient sums.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`two_mem_of_exact_localMersenneQuotient`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowRankTwo.lean#L23)*

The Lean declaration below states this result.

[`Erdos249257.two_mem_of_exact_localMersenneQuotient`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusExactRowRankTwo.lean#L23)

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
| `two_mem_of_exact_localMersenneQuotient` | [E257_28/Challenge.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L115) | [PaperStatementsAD.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAD.lean#L119) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i9"></a>

## Proposition (Error in the finite subseries value)

> *An exact row at endpoint $`n`$ has real value within $`O(n/2^n)`$ of $`1/2`$: the quantitative bound $`|y_n-1/2|\le(n+1)/2^n`$ consumed by Theorem <a href="#record:257bm-c1" data-reference-type="ref" data-reference="record:257bm-c1">110</a> to turn a sequence of exact rows tending to depth infinity into a sequence of values tending to $`1/2`$.*
> 
> *<span class="sans-serif">(uniform)</span> *divisor counts and finite sums* [`abs_localMersennePrefixValue_sub_half_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGlobalRepair.lean#L243)*

The Lean declaration below states this result.

[`Erdos249257.abs_localMersennePrefixValue_sub_half_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusGlobalRepair.lean#L243)

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
| `abs_localMersennePrefixValue_sub_half_le` | [E257_28/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L181) | [PaperStatementsAR.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAR.lean#L96) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i10"></a>

## Proposition (No finite support has value one half)

> *A finite sum of reciprocals of odd integers has odd denominator in lowest terms, so it cannot equal $`1/2`$. Applied to the denominators $`2^a-1`$, this proves that a support representing $`1/2`$ must be infinite, as used in Theorem <a href="#record:257bm-c1" data-reference-type="ref" data-reference="record:257bm-c1">110</a>.*
> 
> *<span class="sans-serif">(uniform)</span> *p-adic* [`finite_boolSupport_ne_half`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L589)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_den_odd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OddReciprocalDenominators.lean#L54)

```lean
theorem paper_finite_sum_inv_odd_den_odd {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    Odd (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)).den
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_sum_inv_odd_ne_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OddReciprocalDenominators.lean#L73)

```lean
theorem paper_finite_sum_inv_odd_ne_half {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hodd : ∀ i ∈ s, Odd (f i)) :
    (∑ i ∈ s, (1 : ℚ) / ((f i : ℤ) : ℚ)) ≠ (1 : ℚ) / 2
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finiteErdosSum_den_odd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OddReciprocalDenominators.lean#L94)

```lean
theorem paper_finiteErdosSum_den_odd (F : Finset ℕ) (h0 : 0 ∉ F) :
    Odd (finiteErdosSum F 2).den
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_support_series_ne_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OddReciprocalDenominators.lean#L114)

```lean
theorem paper_finite_support_series_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_half_representing_support_is_infinite`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/OddReciprocalDenominators.lean#L142)

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
| `paper_finite_sum_inv_odd_den_odd` | [E257_28/Challenge.lean, line 123](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L123) | [PaperStatementsAD.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAD.lean#L155) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_finite_sum_inv_odd_ne_half` | [E257_28/Challenge.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L128) | [PaperStatementsAD.lean, line 160](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAD.lean#L160) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_finiteErdosSum_den_odd` | [E257_28/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L156) | [PaperStatementsAN.lean, line 33](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAN.lean#L33) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_finite_support_series_ne_half` | [E257_28/Challenge.lean, line 160](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L160) | [PaperStatementsAN.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAN.lean#L36) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `paper_half_representing_support_is_infinite` | [E257_28/Challenge.lean, line 165](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L165) | [PaperStatementsAN.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStatementsAN.lean#L40) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i11a"></a>

## Theorem (Small remainder forces the greedy word)

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
> 
> *<span class="sans-serif">(uniform)</span> *greedy recurrence* [`remainder_lt_gap_iff_eq_integerGreedyBits`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGreedyReduction.lean#L918)*

The Lean declaration below states this result.

[`Erdos249257.BooleanMobiusGreedyReduction.remainder_lt_gap_iff_eq_integerGreedyBits`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L918)

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
| `remainder_lt_gap_iff_eq_integerGreedyBits` | [E257_02/Challenge.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_02/Challenge.lean#L157) | [PaperStatementsC.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_02/PaperStatementsC.lean#L17) | [E257_02](../evidence/comparator/replay-35882032091/receipt-E257_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i11b"></a>

## Proposition (Gap domination of the integer weights)

> *For integers $`1\le d\le R\le M`$, the quotient weights satisfy
> ``` math
> \left\lfloor\frac{2^M}{2^d-1}\right\rfloor
>  \ge 2^{M-R}+
>  \sum_{j=d+1}^{R}\left\lfloor\frac{2^M}{2^j-1}\right\rfloor.
> ```
> Thus the finite weight list at ranks $`2,\ldots,R`$ satisfies the hypothesis of Theorem <a href="#record:257bm-i11a" data-reference-type="ref" data-reference="record:257bm-i11a">143</a> with $`g=2^{M-R}`$. At $`M=2R-1`$ this gap is $`2^{R-1}`$, and at $`M=2R`$ it is $`2^R`$. The inequality is unconditional; it does not assert that the greedy remainder is smaller than the gap.*
> 
> *<span class="sans-serif">(uniform)</span> *greedy recurrence* [`localMersenneWeightsFrom_gapDominates`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGreedyReduction.lean#L684) [`localMersenneWeights_gapDominates_even`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGreedyReduction.lean#L846) [`localMersenneWeights_gapDominates_odd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGreedyReduction.lean#L855)*

The Lean declarations below together state this result.

1. [`Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom_gapDominates`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L684)

```lean
theorem localMersenneWeightsFrom_gapDominates
    {M R d : ℕ} (hRM : R ≤ M) (hd : 1 ≤ d) :
    GapDominates (lowerBinaryWindow M R)
      (localMersenneWeightsFrom M R d)
```

2. [`Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_even`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L846)

```lean
theorem localMersenneWeights_gapDominates_even
    (R : ℕ) (hR : 1 ≤ R) :
    GapDominates (2 ^ (R - 1)) (localMersenneWeights (2 * R - 1) R)
```

3. [`Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_odd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L855)

```lean
theorem localMersenneWeights_gapDominates_odd (R : ℕ) :
    GapDominates (2 ^ R) (localMersenneWeights (2 * R) R)
```

<a id="record-257bm-i11b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `localMersenneWeightsFrom_gapDominates` | [E257_28/Challenge.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L287) | [PaperStructuresAY.lean, line 284](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStructuresAY.lean#L284) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `localMersenneWeights_gapDominates_even` | [E257_28/Challenge.lean, line 293](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_28/Challenge.lean#L293) | [PaperStructuresAY.lean, line 291](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_28/PaperStructuresAY.lean#L291) | [E257_28](../evidence/comparator/replay-35882032091/receipt-E257_28.json) |
| `localMersenneWeights_gapDominates_odd` | [E257_29/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L110) | [PaperStructuresAY.lean, line 281](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStructuresAY.lean#L281) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i11c"></a>

## Proposition (Uniqueness of the finite greedy representation)

> *Let $`1\le M`$, $`0\le R\le M`$, and $`0\le a<2^{M-R}`$. If
> ``` math
> \sum_{d=2}^{R}\varepsilon_d
>        \left\lfloor\frac{2^M}{2^d-1}\right\rfloor+a
>        =2^{M-1}-1,\qquad \varepsilon_d\in\{0,1\},
> ```
> then $`\varepsilon`$ is the greedy word for capacity $`2^{M-1}-1`$ and $`a`$ is its remainder. This follows by applying Theorem <a href="#record:257bm-i11a" data-reference-type="ref" data-reference="record:257bm-i11a">143</a> with the preceding gap inequality. The statement identifies any such representation; it does not prove that a representation with $`a<2^{M-R}`$ exists. The degenerate formal case $`M=0`$ has empty word and zero target, using truncated natural-number subtraction.*
> 
> *<span class="sans-serif">(uniform)</span> *greedy recurrence* [`localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGreedyReduction.lean#L997)*

The Lean declaration below states this result.

[`Erdos249257.BooleanMobiusGreedyReduction.localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L997)

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
| `localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq` | [E257_29/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L96) | [PaperStructuresAY.lean, line 253](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStructuresAY.lean#L253) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i12"></a>

## Theorem (A division-free form of the binary bound)

> *For $`M\ge0`$ and $`d\ge2`$,
> ``` math
> \left\lfloor\frac{2^M}{2^d-1}\right\rfloor
>    =\sum_{j=1}^{\lfloor M/d\rfloor}2^{M-jd},
> ```
> where an empty sum is zero. To see this, write $`M=qd+r`$ with $`0\le r<d`$ and expand the finite geometric sum. The remaining fraction is $`2^r/(2^d-1)`$, which lies strictly between $`0`$ and $`1`$. Substitution in Theorem <a href="#record:257bm-i5" data-reference-type="ref" data-reference="record:257bm-i5">136</a> expresses its quotient condition as a finite sum of powers of $`2`$. This is an exact rewriting, not a weaker hypothesis or a new existence result.*
> 
> *<span class="sans-serif">(uniform)</span> *geometric-series* [`localMersenneQuotient_eq_geometric`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L27) [`localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L196) [`localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L208)*

The Lean declarations below together state this result.

1. [`Erdos249257.localMersenneQuotient_eq_geometric`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L27)

```lean
theorem localMersenneQuotient_eq_geometric
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = localMersenneGeometricQuotient M d
```

2. [`Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L196)

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

3. [`Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCriticalCapacityGeometric.lean#L208)

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
| `localMersenneQuotient_eq_geometric` | [E257_29/Challenge.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L119) | [PaperStatementsAD.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAD.lean#L107) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric` | [E257_29/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L149) | [PaperStatementsAR.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAR.lean#L174) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore` | [E257_29/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L159) | [PaperStatementsAR.lean, line 183](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAR.lean#L183) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i2"></a>

## Theorem (An upper bound for a binary coefficient tail)

> *Let $`c:\mathbb{N}\to\mathbb{N}`$ satisfy $`c(n)\le n`$ for every $`n`$. Then
> ``` math
> \sum_{r\ge1}c(N+r)2^{-r}\le N+2\qquad(N\ge0).
> ```
> Indeed, $`c(N+r)\le N+r`$, while $`\sum_{r\ge1}2^{-r}=1`$ and $`\sum_{r\ge1}r2^{-r}=2`$. Thus the scaled tail is $`O(N)`$, and in particular $`o(2^N)`$, as required in Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a>. The coefficient bound also holds for Euler’s totient function.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`binaryCoeffTail_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L85)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.binaryCoeffTail_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L85)

```lean
theorem binaryCoeffTail_le (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (N : ℕ) :
    binaryCoeffTail c N ≤ (N : ℝ) + 2
```

2. [`Erdos249257.binaryCoeffTail_div_pow_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L91)

```lean
theorem binaryCoeffTail_div_pow_tendsto_zero
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    Tendsto (fun N : ℕ ↦ binaryCoeffTail c N / (2 : ℝ) ^ N) atTop (nhds 0)
```

<a id="record-257bm-i2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `binaryCoeffTail_le` | [E257_29/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L180) | [PaperStatementsAE.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAE.lean#L58) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `binaryCoeffTail_div_pow_tendsto_zero` | [E257_29/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L175) | [PaperStatementsAE.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAE.lean#L54) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i-t7"></a>

## Theorem (Rationality through an integer recurrence)

> *Let $`c:\mathbb{N}\to\mathbb{N}`$ satisfy $`c(n)\le n`$ for every $`n`$. Then $`\sum_{n\ge1}c(n)2^{-n}`$ is rational if and only if there exist a positive integer $`v`$ and a sequence $`u:\mathbb{N}\to\mathbb{Z}`$ such that
> ``` math
> u(N+1)=2u(N)-v c(N+1)\quad(N\ge0),\qquad
>  \frac{u(N)}{2^N}\longrightarrow0.
> ```
> The limit condition is $`u(N)=o(2^N)`$; it does not assume that $`u`$ is bounded. No divisor-count hypothesis is imposed on $`c`$. Thus the ordinary statement also applies to $`c=\varphi`$; the identification with the separate formal \#249 development, including its indexing conventions, is not asserted here.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`IsTemperedBinaryOrbit`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L67) [`binaryCoeffSeries`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L37) [`binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L426)*

The Lean declaration below states a result at least as strong as this one.

[`Erdos249257.not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L435)

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
| `not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit` | [E257_29/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L184) | [PaperStatementsAE.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAE.lean#L64) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i-mob"></a>

## Theorem (Möbius inversion of the divisor counts)

> *For a set $`A\subseteq\mathbb{N}`$ and each positive integer $`n`$,
> ``` math
> \sum_{d\mid n}\mu(d)c_A(n/d)=\mathbf1_A(n),
> ```
> where $`\mu`$ is the Möbius function and $`c_A(n)`$ counts the positive elements of $`A`$ dividing $`n`$. Thus the divisor counts determine the positive support exactly. In particular their Möbius transform takes only the values $`0`$ and $`1`$. The identity does not depend on a base.*
> 
> *<span class="sans-serif">(uniform)</span> *mobius-inversion* [`moebius_mul_supportCoeffAF`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L95) [`mobius_supportCoeff_boolean`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L118) [`card_divisors_le_two_mul_sqrt`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L209)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.moebius_mul_supportCoeffAF`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCarry.lean#L95)

```lean
theorem moebius_mul_supportCoeffAF (A : Set ℕ) :
    ArithmeticFunction.moebius * supportCoeffAF A = positiveSupportBitAF A
```

2. [`Erdos249257.mobius_supportCoeff_eq_one_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCarry.lean#L112)

```lean
theorem mobius_supportCoeff_eq_one_iff (A : Set ℕ) {n : ℕ} (hn : 0 < n) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 ↔ n ∈ A
```

3. [`Erdos249257.mobius_supportCoeff_boolean`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCarry.lean#L118)

```lean
theorem mobius_supportCoeff_boolean (A : Set ℕ) (n : ℕ) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 0 ∨
      (ArithmeticFunction.moebius * supportCoeffAF A) n = 1
```

<a id="record-257bm-i-mob-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `moebius_mul_supportCoeffAF` | [E257_29/Challenge.lean, line 231](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L231) | [PaperStatementsAU.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAU.lean#L46) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `mobius_supportCoeff_eq_one_iff` | [E257_29/Challenge.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L227) | [PaperStatementsAU.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAU.lean#L43) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `mobius_supportCoeff_boolean` | [E257_29/Challenge.lean, line 222](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L222) | [PaperStatementsAU.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAU.lean#L39) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i-bridge"></a>

## Theorem (The support series as a coefficient series)

> *For $`A\subseteq\mathbb{N}_{>0}`$,
> ``` math
> X_A(2)=\sum_{a\in A}\frac1{2^a-1}
>        =\sum_{n\ge1}\frac{c_A(n)}{2^n}.
> ```
> Expanding each denominator as a geometric series and interchanging nonnegative sums gives the identity. Since $`c_A(n)\le\tau(n)\le n`$, Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a> applies. Together with Theorem <a href="#record:257bm-i-mob" data-reference-type="ref" data-reference="record:257bm-i-mob">149</a>, it expresses rationality through an integer recurrence whose coefficients all come from the same support.*
> 
> *<span class="sans-serif">(uniform)</span> *divisor counts and finite sums* [`erdosSupportSeries_two_eq_binaryCoeffSeries`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L377) [`erdosSupportSeries_rational_iff_exists_temperedCarry`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L384)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.erdosSupportSeries_two_eq_binaryCoeffSeries`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCarry.lean#L377)

```lean
theorem erdosSupportSeries_two_eq_binaryCoeffSeries (A : Set ℕ) :
    erdosSupportSeries 2 A = binaryCoeffSeries (supportCoeff A)
```

2. [`Erdos249257.supportCoeff_le_card_divisors`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L8860)

```lean
theorem supportCoeff_le_card_divisors (A : Set ℕ) (n : ℕ) :
    supportCoeff A n ≤ n.divisors.card
```

3. [`Erdos249257.supportCoeff_le_self`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L8868)

```lean
theorem supportCoeff_le_self (A : Set ℕ) (n : ℕ) : supportCoeff A n ≤ n
```

4. [`Erdos249257.erdosSupportSeries_rational_iff_exists_temperedCarry`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusCarry.lean#L384)

```lean
theorem erdosSupportSeries_rational_iff_exists_temperedCarry (A : Set ℕ) :
    HasRationalValue (erdosSupportSeries 2 A) ↔
      ∃ q : ℕ, 0 < q ∧ ∃ U : ℕ → ℤ,
        IsTemperedBinaryOrbit (supportCoeff A) q U
```

<a id="record-257bm-i-bridge-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `erdosSupportSeries_two_eq_binaryCoeffSeries` | [E257_29/Challenge.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L218) | [PaperStatementsAU.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAU.lean#L36) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `supportCoeff_le_card_divisors` | [E257_29/Challenge.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L241) | [PaperStatementsAG.lean, line 125](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAG.lean#L125) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `supportCoeff_le_self` | [E257_29/Challenge.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L245) | [PaperStatementsAG.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAG.lean#L128) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `erdosSupportSeries_rational_iff_exists_temperedCarry` | [E257_29/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L212) | [PaperStatementsAU.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAU.lean#L31) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-i2"></a>

## Theorem (A restriction on dyadic rational values)

> *If an infinite support $`A\subseteq\mathbb{N}_{>0}`$ has $`X_A(2)=p/2^c`$ for integers $`p`$ and $`c\ge0`$, then $`\sum_{a\in A}1/a`$ either diverges or converges to a value greater than $`1`$. The cited proof averages the shifted integer recurrence and uses a common multiple of two distinct support elements. Thus a convergent reciprocal sum of at most $`1`$ is excluded. This is a separate necessary condition: the reciprocal-summable criterion proved earlier already excludes every support with a convergent reciprocal sum, not just those whose sum is at most $`1`$.*
> 
> *<span class="sans-serif">(uniform)</span> *cesaro-tail* [`dyadic_support_fraction_reciprocalMass_diverges_or_gt_one`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2210) [`one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2124)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RationalSupportCarrySkeleton.lean#L2124)

```lean
theorem one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    1 < reciprocalMass A
```

2. [`Erdos249257.dyadic_support_fraction_reciprocalMass_diverges_or_gt_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RationalSupportCarrySkeleton.lean#L2210)

```lean
theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A
```

<a id="record-257rig-i2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem` | [E257_29/Challenge.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L283) | [PaperStatementsAV.lean, line 55](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAV.lean#L55) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `dyadic_support_fraction_reciprocalMass_diverges_or_gt_one` | [E257_29/Challenge.lean, line 262](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L262) | [PaperStatementsAV.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAV.lean#L23) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-i3"></a>

## Theorem (Unboundedness of a positive shifted recurrence)

> *Let $`A\subseteq\mathbb{N}_{>0}`$ be infinite, fix a shift $`c\ge0`$ and a positive integer $`v`$, and let $`u`$ be a positive integer sequence satisfying
> ``` math
> u(n+1)+v c_A(c+n+1)=2u(n)\qquad(n\ge0).
> ```
> Then $`u`$ is unbounded. Indeed, under a proposed bound $`u(n)\le B`$, choose $`2B+1`$ distinct support elements and a common multiple larger than $`c`$. At the corresponding index the divisor count is at least $`2B+1`$, contradicting the recurrence. This does not conflict with Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a>, whose condition is $`u(n)/2^n\to0`$, not boundedness. An unbounded sequence can still satisfy that limit.*
> 
> *<span class="sans-serif">(uniform)</span> *common-multiple-forcing* [`shifted_state_unbounded_of_infinite_support`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2327) [`exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2383) [`one_add_mul_card_le_two_mul_shifted_state`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2237)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.one_add_mul_card_le_two_mul_shifted_state`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RationalSupportCarrySkeleton.lean#L2237)

```lean
theorem one_add_mul_card_le_two_mul_shifted_state
    (A : Set ℕ) (F : Finset ℕ) (c v L : ℕ) (u : ℕ → ℕ)
    (hcL : c < L) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ L) :
    1 + v * F.card ≤ 2 * u (L - c - 1)
```

2. [`Erdos249257.shifted_state_unbounded_of_infinite_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RationalSupportCarrySkeleton.lean#L2327)

```lean
theorem shifted_state_unbounded_of_infinite_support
    (A : Set ℕ) (hAinf : A.Infinite) (c v : ℕ) (hv : 0 < v)
    (u : ℕ → ℕ) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n) :
    ∀ B : ℕ, ∃ n : ℕ, B < u n
```

3. [`Erdos249257.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RationalSupportCarrySkeleton.lean#L2383)

```lean
theorem exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      (∀ B : ℕ, ∃ n : ℕ, B < u n)
```

<a id="record-257rig-i3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `one_add_mul_card_le_two_mul_shifted_state` | [E257_30/Challenge.lean, line 53](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L53) | [PaperStatementsAV.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAV.lean#L59) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `shifted_state_unbounded_of_infinite_support` | [E257_30/Challenge.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L62) | [PaperStatementsAV.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAV.lean#L76) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction` | [E257_29/Challenge.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L269) | [PaperStatementsAV.lean, line 29](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAV.lean#L29) | [E257_29](../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-i4a"></a>

## Theorem (Bounds for intervals with zero divisor counts)

> *Suppose that $`X_A(2)=p/(2^cv)`$ for an infinite positive support $`A`$ and an odd positive integer $`v`$. For every $`\varepsilon>0`$ there is $`B`$ such that, for $`N\ge1`$, a run of $`h`$ zero divisor counts starting after $`c+N`$ satisfies $`h\le\varepsilon\log_2N+B`$. In fact this conclusion holds without rationality: fix any $`a\in A`$. Every $`a`$ consecutive positive integers include a multiple of $`a`$, where $`c_A`$ is positive. Hence $`h\le a-1`$, so one can take $`B=a-1`$. The zero-run conclusion therefore imposes no additional restriction on a fixed nonempty support, regardless of the tail estimates used in the linked proof.*
> 
> *<span class="sans-serif">(uniform)</span> *divisor-envelope* [`supportCoeffZeroWindow_length_le_eps_logb`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SublogDivisorCoverage.lean#L435)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_eps_logb`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L219)

```lean
theorem paper_zero_run_le_eps_logb
    (A : Set ℕ) (hinf : A.Infinite) (hzero : 0 ∉ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v) (_hvodd : Odd v)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ, 1 ≤ N →
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N : ℝ) + B
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_of_mem`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L237)

```lean
theorem paper_zero_run_le_of_mem
    (A : Set ℕ) {a : ℕ} (hapos : 0 < a) (haA : a ∈ A) {N h : ℕ}
    (hwindow : SupportCoeffZeroWindow A N h) :
    h ≤ a - 1
```

<a id="record-257rig-i4a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_zero_run_le_eps_logb` | [E257_30/Challenge.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L86) | [PaperStatementsAL.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAL.lean#L62) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_zero_run_le_of_mem` | [E257_30/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L97) | [PaperStatementsAL.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAL.lean#L73) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-i4b"></a>

## Proposition (A subpower bound for divisor counts)

> *For positive integers $`n,k`$, $`\tau(n)^k \le (k^{2^k})^k\cdot n`$, or equivalently $`\tau(n)\le k^{2^k}n^{1/k}`$. The constant absorbs the finitely many primes below $`2^k`$; for larger primes, $`(\nu+1)^k\le p^\nu`$ controls each factor of the divisor product. This estimate is independent of the support problem. The elementary zero-run bound above already follows from a single positive support element, without this estimate or a recurrence.*
> 
> *<span class="sans-serif">(uniform)</span> *divisor-envelope* [`card_divisors_pow_le_divisorSubpowerConst_pow_mul`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SublogDivisorCoverage.lean#L107)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.card_divisors_pow_le_divisorSubpowerConst_pow_mul`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/SublogDivisorCoverage.lean#L107)

```lean
theorem card_divisors_pow_le_divisorSubpowerConst_pow_mul
    (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    n.divisors.card ^ k ≤ divisorSubpowerConst k ^ k * n
```

2. [`Erdos249257.card_divisors_le_divisorSubpowerConst_mul_rpow`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/SublogDivisorCoverage.lean#L142)

```lean
theorem card_divisors_le_divisorSubpowerConst_mul_rpow
    (n k : ℕ) (hk : 1 ≤ k) :
    (n.divisors.card : ℝ) ≤
      (divisorSubpowerConst k : ℝ) *
        (n : ℝ) ^ ((k : ℝ)⁻¹)
```

<a id="record-257rig-i4b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `card_divisors_pow_le_divisorSubpowerConst_pow_mul` | [E257_30/Challenge.lean, line 116](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L116) | [PaperStatementsAF.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAF.lean#L32) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `card_divisors_le_divisorSubpowerConst_mul_rpow` | [E257_30/Challenge.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L109) | [PaperStatementsAF.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAF.lean#L26) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-i5"></a>

## Proposition (Two distinct prime-power differences commute)

> *Lemma <a href="#lem:mixed-prime-power-layer" data-reference-type="ref" data-reference="lem:mixed-prime-power-layer">100</a> gives the four-term expansion and its divisor-count interpretation. Commutation is elementary for arbitrary positive multipliers. The extraction formula uses distinct primes, *positive* exponents $`e,f`$ and $`\gcd(n,pq)=1`$. The example $`A=\{12\}`$ shows the extracted coefficient explicitly. No rationality statement about multiplicative subsequences follows from commutation alone.*
> 
> *<span class="sans-serif">(uniform)</span> *mobius-inversion* [`mixedPrimePowerLayerTwo_supportCoeffInt`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MaximalOmegaLayer.lean#L39) [`primePowerLayer_comm`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MaximalOmegaLayer.lean#L29)*

The Lean declarations below together state this result.

1. [`Erdos249257.MaximalOmegaLayer.primePowerLayer_comm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MaximalOmegaLayer.lean#L29)

```lean
theorem primePowerLayer_comm
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) :
    primePowerLayer q f (primePowerLayer p e g) n =
      primePowerLayer p e (primePowerLayer q f g) n
```

2. [`Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_supportCoeffInt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MaximalOmegaLayer.lean#L39)

```lean
theorem mixedPrimePowerLayerTwo_supportCoeffInt
    (A : Set ℕ) {p e q f n : ℕ}
    (hp : p.Prime) (he : 0 < e) (hq : q.Prime) (hf : 0 < f)
    (hpq : p ≠ q) (hn : n.Coprime (p * q)) :
    mixedPrimePowerLayerTwo p e q f (supportCoeffInt A) n =
      supportCoeffInt
        (exactPrimePowerPullback q f (exactPrimePowerPullback p e A)) n
```

3. [`Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_twelve_fixture`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MaximalOmegaLayer.lean#L65)

```lean
theorem mixedPrimePowerLayerTwo_twelve_fixture :
    mixedPrimePowerLayerTwo 2 2 3 1
      (supportCoeffInt ({12} : Set ℕ)) 1 = 1
```

<a id="record-257rig-i5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `primePowerLayer_comm` | [E257_21/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L180) | [PaperStatementsAA.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAA.lean#L75) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `mixedPrimePowerLayerTwo_supportCoeffInt` | [E257_21/Challenge.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L220) | [PaperStatementsAO.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAO.lean#L22) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `mixedPrimePowerLayerTwo_twelve_fixture` | [E257_30/Challenge.lean, line 138](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L138) | [PaperStatementsAO.lean, line 33](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAO.lean#L33) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i-cross2"></a>

## Theorem (Existence of a first crossing)

> *Let $`E\subseteq\{2,3,\ldots\}`$ be finite and suppose $`X_E(2)>1/2`$. There is a least $`c\in E`$ such that
> ``` math
> X_{E\cap[2,c)}(2)<\frac12
>        <X_{E\cap[2,c]}(2),\qquad c\ge4.
> ```
> Positivity of the summands makes the partial sums increasing. Their odd reduced denominators exclude equality with $`1/2`$, so the first crossing is strict on both sides. Finally $`w_2+w_3=10/21<1/2`$, which excludes a crossing before rank $`4`$. This is the finite crossing data used in the later exact-row constructions; the lower bound on $`c`$ and strictness are specific to these weights.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`exists_first_localMersenne_crossing`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowCrossing.lean#L31)*

The Lean declaration below states this result.

[`Erdos249257.exists_first_localMersenne_crossing`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/BooleanMobiusExactRowCrossing.lean#L31)

```lean
theorem exists_first_localMersenne_crossing
    {E : Finset ℕ}
    (hE : ∀ d ∈ E, 2 ≤ d)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ,
      c ∈ E ∧
      4 ≤ c ∧
      localMersennePrefixValue (E.filter fun d ↦ d < c) < (1 / 2 : ℚ) ∧
      (1 / 2 : ℚ) <
        localMersennePrefixValue (insert c (E.filter fun d ↦ d < c))
```

<a id="record-257bm-i-cross2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_first_localMersenne_crossing` | [E257_30/Challenge.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L158) | [PaperStatementsAR.lean, line 151](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAR.lean#L151) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-i6"></a>

## Theorem (Nonnegative centred carries below the half-value)

> *If $`1\notin A`$ and $`X_A(2)<1/2`$, then
> ``` math
> C_A(N)=\operatorname{ihc}(A,N)-1\ge0\qquad(N\ge0).
> ```
> Indeed, Lemma <a href="#lem:collapse-mech" data-reference-type="ref" data-reference="lem:collapse-mech">15</a> gives
> ``` math
> \operatorname{ihc}(A,N)
>  =2^{N+1}\bigl(1/2-X_A(2)\bigr)
>      +\sum_{r\ge1}c_A(N+1+r)2^{-r}>0.
> ```
> The first term is strictly positive and the tail is nonnegative. Since the half-carry is an integer, it is at least $`1`$; subtracting $`1`$ proves the centred bound. Nonnegativity alone, without this strictness and integrality step, would only give $`C_A(N)\ge-1`$. The argument supplies the lower bound used with the conditional upper bound in Theorem <a href="#record:257rig-c16" data-reference-type="ref" data-reference="record:257rig-c16">127</a>.*
> 
> *<span class="sans-serif">(uniform)</span> *mobius-centred-carry* [`integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L871) [`mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L94)*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfCarryReachability.integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCarryReachability.lean#L871)

```lean
theorem integerHalfCarry_eq_scaled_residual_add_tail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (integerHalfCarry A N : ℝ) =
      (2 : ℝ) ^ (N + 1) * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) +
        binaryCoeffTail (supportCoeff A) (N + 1)
```

2. [`Erdos249257.mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L94)

```lean
theorem mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
    (A : Set ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry A N
```

<a id="record-257hg-i6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `integerHalfCarry_eq_scaled_residual_add_tail` | [E257_03/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L99) | [PaperStatementsE.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsE.lean#L35) | [E257_03](../evidence/comparator/replay-35882032091/receipt-E257_03.json) |
| `mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half` | [E257_13/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L111) | [PaperStatementsI.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsI.lean#L34) | [E257_13](../evidence/comparator/replay-35882032091/receipt-E257_13.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-i7"></a>

## Theorem (Three possibilities at a skipped endpoint)

> *For a rank $`s\ge5`$ omitted by the real greedy support, let $`H_s`$ and $`f_s`$ be as in Lemma <a href="#lem:skipped-endpoint-trichotomy" data-reference-type="ref" data-reference="lem:skipped-endpoint-trichotomy">88</a>. That lemma identifies the actual prefix as $`D_s`$ when $`f_s\le0`$ and as $`B_s`$ when $`f_s>0`$, with the exact remainder or overshoot in each case. To obtain the nonnegative-margin condition in Definition <a href="#record:257bm-c13" data-reference-type="ref" data-reference="record:257bm-c13">124</a>, the negative case would still have to be excluded at every required skipped rank. The trichotomy itself does not exclude it. In particular, the value $`-3`$ excluded for $`C_D`$ under the all-right-tail hypothesis of Theorem <a href="#thm:final-middle-cell" data-reference-type="ref" data-reference="thm:final-middle-cell">87</a> is not an exclusion for $`f_s`$: the coordinates and the hypotheses are different.*
> 
> *<span class="sans-serif">(uniform)</span> *frozen-margin* [`halfGreedy_skipped_endpoint_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L246)*

The Lean declaration below states this result.

[`Erdos249257.halfGreedy_skipped_endpoint_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L246)

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

<a id="record-257hg-i7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `halfGreedy_skipped_endpoint_trichotomy` | [E257_16/Challenge.lean, line 316](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_16/Challenge.lean#L316) | [PaperStructuresBI.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_16/PaperStructuresBI.lean#L264) | [E257_16](../evidence/comparator/replay-35882032091/receipt-E257_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-i2"></a>

## Theorem (The unweighted sum of remaining gap lengths)

> *For every $`N\ge0`$, the unweighted sum of gap lengths satisfies
> ``` math
> \sum_{n>N}g_n\le\frac29\,4^{-N}+\frac37\,8^{-N},
> ```
> which tends to zero. The estimate follows by summing the per-level bound; it counts one length per level. It does not, by itself, bound the measure of the union of all gaps, because there are $`2^{n-1}`$ disjoint translated gaps at level $`n`$.*
> 
> *<span class="sans-serif">(uniform)</span> *summed-gap-mass* [`summable_mersenneGap_shift`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGapMass.lean#L69) [`mersenneGap_tail_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGapMass.lean#L83) [`tendsto_mersenneGap_tail_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGapMass.lean#L104) [`mersenneGap_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGapMass.lean#L40)*

The Lean declarations below together state this result.

1. [`Erdos249257.mersenneGap_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGapMass.lean#L40)

```lean
theorem mersenneGap_le {n : ℕ} (hn : 0 < n) :
    mersenneGap n ≤ (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n + 3 * ((1 : ℝ) / 8) ^ n
```

2. [`Erdos249257.summable_mersenneGap_shift`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGapMass.lean#L69)

```lean
theorem summable_mersenneGap_shift (N : ℕ) :
    Summable (fun k : ℕ => mersenneGap (N + k + 1))
```

3. [`Erdos249257.mersenneGap_tail_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGapMass.lean#L83)

```lean
theorem mersenneGap_tail_le (N : ℕ) :
    ∑' k : ℕ, mersenneGap (N + k + 1)
      ≤ (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N
```

4. [`Erdos249257.tendsto_mersenneGap_tail_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGapMass.lean#L104)

```lean
theorem tendsto_mersenneGap_tail_zero :
    Tendsto (fun N : ℕ => ∑' k : ℕ, mersenneGap (N + k + 1)) atTop (nhds 0)
```

<a id="record-257hg-i2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mersenneGap_le` | [E257_30/Challenge.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L182) | [PaperStatementsAM.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAM.lean#L103) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `summable_mersenneGap_shift` | [E257_30/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L186) | [PaperStatementsAM.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAM.lean#L114) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `mersenneGap_tail_le` | [E257_20/Challenge.lean, line 202](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L202) | [PaperStatementsAM.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L106) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |
| `tendsto_mersenneGap_tail_zero` | [E257_20/Challenge.lean, line 210](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L210) | [PaperStatementsAM.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L119) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-i4"></a>

## Theorem (A sufficient inequality for a safe skip)

> *Let $`k,u,L\ge1`$ be integers, set $`a=2L-(2^k-1)u`$, and suppose $`a>0`$. For the skipped rational remainder $`\rho=u/(2L)`$, $`\rho\le2^{-k}`$ is equivalent to $`u\le a`$, whereas
> ``` math
> 2u\le3a\quad\Longrightarrow\quad\rho<R_k.
> ```
> The latter implication uses the three-term lower bound above. More explicitly, with $`t=2^k\ge2`$,
> ``` math
> \left(\frac1t+\frac1{3t^2}+\frac1{7t^3}\right)
>        -\frac3{3t-1}
>  =\frac{2t-3}{21t^3(3t-1)}>0.
> ```
> The inequality $`2u\le3a`$ gives $`\rho\le3/(3t-1)`$, proving the claim. The first two terms alone would not prove this comparison. This is a sufficient exclusion of the current tail-mass deficit, not an exact test for membership in the remaining achievement set.*
> 
> *The sufficient condition is weaker than $`u\le a`$. A realizable example is $`(k,u,L,a)=(2,7,13,5)`$; it passes $`2u\le3a`$ but not $`u\le a`$. The linked scalar example $`(u,a)=(3,2)`$ proves strict containment of the inequalities, but is not integral rational data for this substitution. For comparison, the exact mass threshold is $`a/u\ge R_k^{-1}-(2^k-1)`$; its right-hand side lies strictly between $`0`$ and $`2/3`$. None of these comparisons asserts that the half-greedy orbit satisfies the sufficient inequality at every skipped rank.*
> 
> *<span class="sans-serif">(uniform)</span> *lambert-bound* [`skipSafe_of_two_mul_le_three_mul`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L107) [`sharp_of_dyadic`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L197) [`sharp_strictly_stronger`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L200) [`skipSafe_actualTail_of_two_mul_le_three_mul`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L235)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_dyadic_skip_test_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L30)

```lean
theorem paper_dyadic_skip_test_iff {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k) ↔ u ≤ a
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_skip_safe_lb3`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L54)

```lean
theorem paper_sharp_skip_safe_lb3 {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTailLB3 k
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_skip_safe_actual_tail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L62)

```lean
theorem paper_sharp_skip_safe_actual_tail {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTail k
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_three_channel_margin_identity`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L71)

```lean
theorem paper_three_channel_margin_identity {t : ℝ} (ht : 2 ≤ t) :
    (1 / t + 1 / (3 * t ^ 2) + 1 / (7 * t ^ 3)) - 3 / (3 * t - 1) =
        (2 * t - 3) / (21 * t ^ 3 * (3 * t - 1)) ∧
      0 < (2 * t - 3) / (21 * t ^ 3 * (3 * t - 1))
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_weaker_than_dyadic`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L92)

```lean
theorem paper_sharp_weaker_than_dyadic {u a : ℕ} (h : u ≤ a) : 2 * u ≤ 3 * a
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_strictly_weaker_realizable`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L97)

```lean
theorem paper_sharp_strictly_weaker_realizable :
    ∃ k u L a : ℕ, 1 ≤ k ∧ 0 < u ∧ 0 < a ∧
      2 ^ k * u + a = 2 * L + u ∧ 2 * u ≤ 3 * a ∧ ¬ u ≤ a
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_gives_three_over_three_t_sub_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L104)

```lean
theorem paper_sharp_gives_three_over_three_t_sub_one {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) ≤ 3 / (3 * (2 : ℝ) ^ k - 1)
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_two_channels_insufficient`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L131)

```lean
theorem paper_two_channels_insufficient :
    1 / (2 : ℝ) + 1 / (3 * (2 : ℝ) ^ 2) < 3 / (3 * (2 : ℝ) - 1)
```

9. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_mass_threshold`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L138)

```lean
theorem paper_exact_mass_threshold {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ mersenneTail k ↔
        (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ≤ (a : ℝ) / u) ∧
      0 < (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ∧
      (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) < 2 / 3
```

<a id="record-257hg-i4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_dyadic_skip_test_iff` | [E257_30/Challenge.lean, line 210](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L210) | [PaperStatementsAA.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L190) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_sharp_skip_safe_lb3` | [E257_30/Challenge.lean, line 222](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L222) | [PaperStatementsAA.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L283) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_sharp_skip_safe_actual_tail` | [E257_30/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L199) | [PaperStatementsAM.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAM.lean#L241) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_three_channel_margin_identity` | [E257_30/Challenge.lean, line 237](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L237) | [PaperStatementsAA.lean, line 298](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L298) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_sharp_weaker_than_dyadic` | [E257_30/Challenge.lean, line 234](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L234) | [PaperStatementsAA.lean, line 293](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L293) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_sharp_strictly_weaker_realizable` | [E257_30/Challenge.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L229) | [PaperStatementsAA.lean, line 289](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L289) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_sharp_gives_three_over_three_t_sub_one` | [E257_30/Challenge.lean, line 216](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L216) | [PaperStatementsAA.lean, line 278](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L278) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_two_channels_insufficient` | [E257_30/Challenge.lean, line 243](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L243) | [PaperStatementsAA.lean, line 303](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L303) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_exact_mass_threshold` | [E257_30/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L190) | [PaperStatementsAM.lean, line 213](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAM.lean#L213) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-i5"></a>

## Proposition (Two unconditional safety cases)

> *Under the positive-integer and skipped-step hypotheses of Theorem <a href="#record:257hg-i4" data-reference-type="ref" data-reference="record:257hg-i4">163</a>, $`u=1`$ implies $`a\ge1`$, so the current remainder is less than $`R_k`$. Conversely, a fatal tail-mass deficit forces $`3a<2u`$, hence $`u\ge2`$, or $`u\ge3`$ when $`u`$ is odd. These are statements about the current step, not infinite survival. The exact declaration names are linked below.*
> 
> *<span class="sans-serif">(uniform)</span> *lambert-bound* [`unitNumerator_skipSafe`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L135) [`two_le_of_fatal`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L161) [`three_le_of_fatal_of_odd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L173) [`unitNumerator_skipSafe_actualTail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L246)*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGreedyFatalGap.lean#L135)

```lean
theorem unitNumerator_skipSafe
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTailLB3 k
```

2. [`Erdos249257.HalfGreedyFatalGap.two_le_of_fatal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGreedyFatalGap.lean#L161)

```lean
theorem two_le_of_fatal
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    2 ≤ u
```

3. [`Erdos249257.HalfGreedyFatalGap.three_le_of_fatal_of_odd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGreedyFatalGap.lean#L173)

```lean
theorem three_le_of_fatal_of_odd
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a) (hodd : Odd u)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    3 ≤ u
```

4. [`Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe_actualTail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfGreedyFatalGap.lean#L246)

```lean
theorem unitNumerator_skipSafe_actualTail
    {k L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTail k
```

<a id="record-257hg-i5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `unitNumerator_skipSafe` | [E257_30/Challenge.lean, line 267](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L267) | [PaperStructuresH.lean, line 29](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStructuresH.lean#L29) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `two_le_of_fatal` | [E257_30/Challenge.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L259) | [PaperStructuresH.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStructuresH.lean#L22) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `three_le_of_fatal_of_odd` | [E257_30/Challenge.lean, line 251](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L251) | [PaperStructuresH.lean, line 15](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStructuresH.lean#L15) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `unitNumerator_skipSafe_actualTail` | [E257_30/Challenge.lean, line 282](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L282) | [PaperStructuresV.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStructuresV.lean#L22) | [E257_30](../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Challenge for `unitNumerator_skipSafe`:

```lean
theorem unitNumerator_skipSafe {k u L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTailLB3 k := by sorry
```

Challenge for `two_le_of_fatal`:

```lean
theorem two_le_of_fatal {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    2 ≤ u := by sorry
```

Challenge for `three_le_of_fatal_of_odd`:

```lean
theorem three_le_of_fatal_of_odd {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a) (hodd : Odd u)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    3 ≤ u := by sorry
```

Challenge for `unitNumerator_skipSafe_actualTail`:

```lean
theorem unitNumerator_skipSafe_actualTail {k u L a : ℕ}
    {k L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTail k := by sorry
```

<a id="record-257bm-i13"></a>

## Theorem (Two-sided dyadic bounds)

> *Under the local hypothesis excluding the specified three middle cells and imposing the right-pulse bound, induction (base case at row 5 verified by `decide`) propagates it to the universal two-sided bound
> ``` math
> \forall s\ge5,\quad \min(\mathrm{rem}(s),\ \mathrm{overshoot}(s)) \;\le\; 2^s.
> ```
> This conditional bound says that at least one of the remainder and the adjacent overshoot is at most $`2^s`$. It does not assert that both are at most $`2^s`$; that stronger assertion would replace the minimum by a maximum. It is not needed for the charge bound at an actual upper reset: Proposition <a href="#record:257bm-c12" data-reference-type="ref" data-reference="record:257bm-c12">123</a> obtains that bound directly from the upper-reset identity. Applying the inductive argument to another recurrence would require its own transition and separation estimates.*
> 
> *<span class="sans-serif">(uniform)</span> *dyadic-scale* [`SeamTwoSidedDyadicCellEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4374) [`SeamTwoSidedDyadicCellEscape.step`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4398) [`SeamTwoSidedDyadicCellEscape.twoSided`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4448)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_two_sided_dyadic_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/DyadicBandAndTwoSidedBounds.lean#L105)

```lean
theorem paper_two_sided_dyadic_bound
    (hescape : SeamTwoSidedDyadicCellEscape) (s : ℕ) (hs : 5 ≤ s) :
    min (seamIntegerGreedyRemainder s) ((seamAdjacentCut s hs).overshoot) ≤
      2 ^ s
```

<a id="record-257bm-i13-comparator"></a>

**Comparator:** not yet compared.

<a id="record-257bm-i14"></a>

## Proposition (A finite band check for $`13\le d\le30`$)

> *For every actual upper-reset index $`13\le d\le30`$ and every $`0\le j\le d`$, the linked certificate verifies
> ``` math
> 2^{d-j+1}<\mathrm{resetCharge}
> \quad\text{or}\quad
> \mathrm{resetCharge}+2(d+j)\le2^{d-j+1}.
> ```
> It computes the successor remainder at each row $`d+1`$, from $`\mathrm{rem}(14)=392`$ through $`\mathrm{rem}(31)=4187487147`$. This proves the required condition on a finite range, not the universal condition for all $`d\ge13`$. A proof for unbounded reset indices must supply a further argument; repeatedly extending the table alone does not establish that statement.*
> 
> *<span class="sans-serif">(fixed)</span> *dyadic-boundary* [`SeamUpperResetDyadicBandEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4566) [`seamUpperResetDyadicBandEscape_through_thirty`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderUpperResetBandCertificates.lean#L78) [`half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4790)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_band_check_thirteen_to_thirty`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L29)

```lean
theorem paper_finite_band_check_thirteen_to_thirty
    (d : ℕ) (hd13 : 13 ≤ d) (hd30 : d ≤ 30) (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    ∀ j : ℕ, j ≤ d →
      2 ^ (d - j + 1) <
          4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse ∨
        4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
          2 ^ (d - j + 1)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_successor_remainders_fourteen_through_thirtyone`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L44)

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

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_universal_band_condition_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L77)

```lean
theorem paper_universal_band_condition_unfolded :
    SeamUpperResetDyadicBandEscape ↔
      ∀ (d : ℕ) (hd5 : 5 ≤ d), 13 ≤ d →
        (seamAdjacentCut d hd5).successorCarries →
          ∀ j : ℕ, j ≤ d →
            2 ^ (d - j + 1) <
                4 * (seamAdjacentCut d hd5).overshoot +
                  (seamAdjacentCut d hd5).abovePulse ∨
              4 * (seamAdjacentCut d hd5).overshoot +
                    (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
                2 ^ (d - j + 1)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_universal_band_condition_would_close_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L70)

```lean
theorem paper_universal_band_condition_would_close_half
    (hband : SeamUpperResetDyadicBandEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="record-257bm-i14-comparator"></a>

**Comparator:** not yet compared.

<a id="record-257bm-i15"></a>

## Theorem (A general perturbed greedy recurrence)

> *Let the old integer values be separated by at least $`g\ge1`$, and let the update be $`t(x)=4s(x)+p(x)`$ with $`0\le p(x)\le B<g`$. Suppose $`x_-`$ and $`x_+`$ are the adjacent old values on either side of capacity $`C`$. Theorem <a href="#thm:perturbed-family-maximality" data-reference-type="ref" data-reference="thm:perturbed-family-maximality">105</a> gives the largest admissible updated value at capacity $`4C+g`$ and the exact three-branch remainder after testing the extra weight $`2g+4`$.*
> 
> *The underlying structure in Definition <a href="#defn:perturbed-family" data-reference-type="ref" data-reference="defn:perturbed-family">104</a> assumes only $`B<3g`$; that suffices for order preservation, but the cited maximality application has the additional hypothesis $`B<g`$. The counterexample after Theorem <a href="#thm:perturbed-family-maximality" data-reference-type="ref" data-reference="thm:perturbed-family-maximality">105</a> shows what can fail without it. For a maximum over both choices of the extra weight, rather than the stated two-stage rule, one also needs a separation argument; $`4g-B\ge2g+4`$ suffices, as shown after that theorem.*
> 
> *<span class="sans-serif">(uniform)</span> *abstract-perturbed-greedy* [`PerturbedFamily`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderIntegerGreedy.lean#L1286) [`prefixChoice_maximal`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderIntegerGreedy.lean#L1390) [`nextRemainder_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderIntegerGreedy.lean#L1463)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_order_preservation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L97)

```lean
theorem paper_perturbed_order_preservation (F : PerturbedFamily α)
    {x y : α} (hxy : F.oldSum x < F.oldSum y) :
    F.newSum x < F.newSum y
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_prefixChoice_maximal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L106)

```lean
theorem paper_perturbed_prefixChoice_maximal (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap) :
    K.newCapacity = 4 * C + F.gap ∧
      K.successorCarries = (4 * K.overshoot + K.abovePulse ≤ F.gap) ∧
      K.prefixChoice = (if K.successorCarries then K.above else K.below) ∧
      F.newSum K.prefixChoice ≤ K.newCapacity ∧
      ∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤ F.newSum K.prefixChoice
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_nextRemainder_three_branches`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L124)

```lean
theorem paper_perturbed_nextRemainder_three_branches (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] :
    K.terminalWeight = 2 * F.gap + 4 ∧
      K.nextRemainder =
        if K.successorCarries then
          F.gap - (4 * K.overshoot + K.abovePulse)
        else if 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight then
          4 * K.remainder + F.gap - K.belowPulse
        else
          4 * K.remainder - F.gap - K.belowPulse - 4
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_separation_global_maximality`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L140)

```lean
theorem paper_perturbed_separation_global_maximality (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap)
    {x : α} (hx : F.oldSum x < F.oldSum K.prefixChoice) :
    F.newSum x + K.terminalWeight ≤ F.newSum K.prefixChoice
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_two_stage_is_global_maximum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L158)

```lean
theorem paper_perturbed_two_stage_is_global_maximum (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap)
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap) :
    F.newSum K.prefixChoice +
          (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
            else 0) ≤ K.newCapacity ∧
      (∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0)) ∧
      (∀ x : α, F.newSum x + K.terminalWeight ≤ K.newCapacity →
        F.newSum x + K.terminalWeight ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0))
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_weak_cap_counterexample`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L245)

```lean
theorem paper_perturbed_weak_cap_counterexample :
    ¬ weakCapFamily.pulseCap < weakCapFamily.gap ∧
      weakCapFamily.pulseCap < 3 * weakCapFamily.gap ∧
      ¬ weakCapCut.successorCarries ∧
      weakCapCut.newCapacity = 10 ∧
      weakCapFamily.newSum weakCapCut.below = 11 ∧
      ¬ weakCapFamily.newSum weakCapCut.below ≤ weakCapCut.newCapacity ∧
      weakCapFamily.newSum (0 : Fin 3) ≤ weakCapCut.newCapacity
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.prefixChoice_eq_below`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L259)

```lean
theorem prefixChoice_eq_below (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (h : ¬ K.successorCarries) :
    K.prefixChoice = K.below
```

<a id="record-257bm-i15-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_perturbed_order_preservation` | [E257_12/Challenge.lean, line 316](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_12/Challenge.lean#L316) | [PaperStructuresBN.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_12/PaperStructuresBN.lean#L99) | [E257_12](../evidence/comparator/replay-35882032091/receipt-E257_12.json) |
| `paper_perturbed_prefixChoice_maximal` | [E257_12/Challenge.lean, line 321](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_12/Challenge.lean#L321) | [PaperStructuresBN.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_12/PaperStructuresBN.lean#L104) | [E257_12](../evidence/comparator/replay-35882032091/receipt-E257_12.json) |
| `paper_perturbed_nextRemainder_three_branches` | [E257_12/Challenge.lean, line 304](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_12/Challenge.lean#L304) | [PaperStructuresBN.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_12/PaperStructuresBN.lean#L87) | [E257_12](../evidence/comparator/replay-35882032091/receipt-E257_12.json) |
| `paper_perturbed_separation_global_maximality` | [E257_31/Challenge.lean, line 316](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_31/Challenge.lean#L316) | [PaperStructuresBP.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_31/PaperStructuresBP.lean#L74) | [E257_31](../evidence/comparator/replay-35882032091/receipt-E257_31.json) |
| `paper_perturbed_two_stage_is_global_maximum` | [E257_31/Challenge.lean, line 323](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_31/Challenge.lean#L323) | [PaperStructuresBP.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_31/PaperStructuresBP.lean#L81) | [E257_31](../evidence/comparator/replay-35882032091/receipt-E257_31.json) |
| `paper_perturbed_weak_cap_counterexample` | [E257_31/Challenge.lean, line 342](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_31/Challenge.lean#L342) | [PaperStructuresBP.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_31/PaperStructuresBP.lean#L100) | [E257_31](../evidence/comparator/replay-35882032091/receipt-E257_31.json) |
| `prefixChoice_eq_below` | [E257_32/Challenge.lean, line 60](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L60) | [PaperStructuresBU.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStructuresBU.lean#L71) | [E257_32](../evidence/comparator/replay-35882032091/receipt-E257_32.json) |

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `paper_perturbed_order_preservation`:

```lean
theorem paper_perturbed_order_preservation {α : Type*} (F : PerturbedFamily α)
    {x y : α} (hxy : F.oldSum x < F.oldSum y) :
    F.newSum x < F.newSum y := by sorry
```

Challenge for `paper_perturbed_prefixChoice_maximal`:

```lean
theorem paper_perturbed_prefixChoice_maximal {α : Type*} (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap) :
    K.newCapacity = 4 * C + F.gap ∧
      K.successorCarries = (4 * K.overshoot + K.abovePulse ≤ F.gap) ∧
      K.prefixChoice = (if K.successorCarries then K.above else K.below) ∧
      F.newSum K.prefixChoice ≤ K.newCapacity ∧
      ∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤ F.newSum K.prefixChoice := by sorry
```

Challenge for `paper_perturbed_nextRemainder_three_branches`:

```lean
theorem paper_perturbed_nextRemainder_three_branches {α : Type*} (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] :
    K.terminalWeight = 2 * F.gap + 4 ∧
      K.nextRemainder =
        if K.successorCarries then
          F.gap - (4 * K.overshoot + K.abovePulse)
        else if 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight then
          4 * K.remainder + F.gap - K.belowPulse
        else
          4 * K.remainder - F.gap - K.belowPulse - 4 := by sorry
```

Challenge for `paper_perturbed_separation_global_maximality`:

```lean
theorem paper_perturbed_separation_global_maximality {α : Type*} (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap)
    {x : α} (hx : F.oldSum x < F.oldSum K.prefixChoice) :
    F.newSum x + K.terminalWeight ≤ F.newSum K.prefixChoice := by sorry
```

Challenge for `paper_perturbed_two_stage_is_global_maximum`:

```lean
theorem paper_perturbed_two_stage_is_global_maximum {α : Type*} (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap)
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap) :
    F.newSum K.prefixChoice +
          (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
            else 0) ≤ K.newCapacity ∧
      (∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0)) ∧
      (∀ x : α, F.newSum x + K.terminalWeight ≤ K.newCapacity →
        F.newSum x + K.terminalWeight ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0)) := by sorry
```

Challenge for `prefixChoice_eq_below`:

```lean
theorem prefixChoice_eq_below {α : Type*} (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (h : ¬ K.successorCarries) :
    K.prefixChoice = K.below := by sorry
```

<a id="record-257bm-i16"></a>

## Theorem (Spacing of compatible reverse-carry words)

> *Consider two integer carry recurrences $`b_i(m)+2u_i(m)=a_i(m)+u_i(m+1)`$, $`i=1,2`$. If $`a_1(k)=a_2(k)`$ and the output bits at $`k`$ are $`1`$ and $`0`$, then the carry difference at $`k+1`$ is odd. If the coefficients and bits agree for the following $`L`$ positions, the difference at $`k+L+1`$ is $`2^L`$ times that odd integer. Consequently absolute terminal bounds $`B_1,B_2`$ give $`2^L\le B_1+B_2`$. Lemma <a href="#lem:reverse-carry-word" data-reference-type="ref" data-reference="lem:reverse-carry-word">89</a> states the exact identity and proves it by subtraction. The linked formal statements encode these agreements; they do not supply terminal bounds for an unrelated digit system.*
> 
> *<span class="sans-serif">(uniform)</span> *reverse-carry-word* [`ReverseCarryWord`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L70) [`overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L124) [`overlappingReverseCarryWords_twoPow_le_realBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L191) [`overlappingMidpointReturns_twoPow_le_realBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L244)*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfTrappingReturnCarry.lean#L124)

```lean
theorem overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd
    (left right : ReverseCarryWord) (seam length : ℕ)
    (hcoeffSeam : left.coeff seam = right.coeff seam)
    (hleftSeam : left.bit seam = 1)
    (hrightSeam : right.bit seam = 0)
    (hcoeffOverlap : ∀ j < length,
      left.coeff (seam + 1 + j) = right.coeff (seam + 1 + j))
    (hbitOverlap : ∀ j < length,
      left.bit (seam + 1 + j) = right.bit (seam + 1 + j)) :
    ∃ z : ℤ, Odd z ∧
      carryDifference left right (seam + 1 + length) =
        (2 : ℤ) ^ length * z
```

2. [`Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_twoPow_le_realBound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfTrappingReturnCarry.lean#L191)

```lean
theorem overlappingReverseCarryWords_twoPow_le_realBound
    (left right : ReverseCarryWord) (seam length : ℕ) (bound : ℝ)
    (hcoeffSeam : left.coeff seam = right.coeff seam)
    (hleftSeam : left.bit seam = 1)
    (hrightSeam : right.bit seam = 0)
    (hcoeffOverlap : ∀ j < length,
      left.coeff (seam + 1 + j) = right.coeff (seam + 1 + j))
    (hbitOverlap : ∀ j < length,
      left.bit (seam + 1 + j) = right.bit (seam + 1 + j))
    (hleftNonneg : 0 ≤ left.carry (seam + 1 + length))
    (hrightNonneg : 0 ≤ right.carry (seam + 1 + length))
    (hleftBound : (left.carry (seam + 1 + length) : ℝ) ≤ bound)
    (hrightBound : (right.carry (seam + 1 + length) : ℝ) ≤ bound) :
    (2 : ℝ) ^ length ≤ bound
```

3. [`Erdos249257.HalfTrappingReturnCarry.overlappingMidpointReturns_twoPow_le_realBound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfTrappingReturnCarry.lean#L244)

```lean
theorem overlappingMidpointReturns_twoPow_le_realBound
    (left right : ReverseCarryWord) (N M : ℕ) (bound : ℝ) (hN : 1 ≤ N)
    (hNM : M ≤ 2 * N - 2)
    (hcoeffSeam : left.coeff (M + 1) = right.coeff (M + 1))
    (hleftSeam : left.bit (M + 1) = 1)
    (hrightSeam : right.bit (M + 1) = 0)
    (hcoeffOverlap : ∀ j < 2 * N - M - 1,
      left.coeff (M + 2 + j) = right.coeff (M + 2 + j))
    (hbitOverlap : ∀ j < 2 * N - M - 1,
      left.bit (M + 2 + j) = right.bit (M + 2 + j))
    (hleftNonneg : 0 ≤ left.carry (2 * N + 1))
    (hrightNonneg : 0 ≤ right.carry (2 * N + 1))
    (hleftBound : (left.carry (2 * N + 1) : ℝ) ≤ bound)
    (hrightBound : (right.carry (2 * N + 1) : ℝ) ≤ bound) :
    (2 : ℝ) ^ (2 * N - M - 1) ≤ bound
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_reverse_carry_word`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamRowGapAndCarry.lean#L240)

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

<a id="record-257bm-i16-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd` | [E257_32/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L97) | [PaperStructuresO.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStructuresO.lean#L67) | [E257_32](../evidence/comparator/replay-35882032091/receipt-E257_32.json) |
| `overlappingReverseCarryWords_twoPow_le_realBound` | [E257_32/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L111) | [PaperStructuresO.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStructuresO.lean#L80) | [E257_32](../evidence/comparator/replay-35882032091/receipt-E257_32.json) |
| `overlappingMidpointReturns_twoPow_le_realBound` | [E257_32/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L80) | [PaperStructuresO.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStructuresO.lean#L51) | [E257_32](../evidence/comparator/replay-35882032091/receipt-E257_32.json) |
| `paper_reverse_carry_word` | [E257_20/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L110) | [PaperStatementsAA.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAA.lean#L238) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i17"></a>

## Proposition (Changing one support bit at a doubled rank)

> *Let two supports agree except that the second includes $`N+1`$ while the first does not. At the argument $`2(N+1)`$ their divisor counts differ by exactly $`1`$, because $`N+1`$ divides $`2(N+1)`$. More generally the difference at a positive argument $`m`$ is $`\mathbf1_{N+1\mid m}`$. The linked statements apply this identity to the finite supports in their hypotheses. No conclusion about a different coefficient sequence follows without identifying its own support change.*
> 
> *<span class="sans-serif">(uniform)</span> *half-divisor* [`supportCoeff_extend_true_eq_false_add_one_at_double`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfDivisorUnitDrop.lean#L20) [`supportCoeff_boundaryPair_unitDrop_at_double`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfDivisorUnitDrop.lean#L35)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.HalfCylinderFiniteShadow.supportCoeff_insert_divisor`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfCylinderFiniteShadow.lean#L642)

```lean
theorem supportCoeff_insert_divisor
    (A : Set ℕ) {d n : ℕ} (hd : d ∈ n.divisors) (hdA : d ∉ A) :
    supportCoeff (insert d A) n = supportCoeff A n + 1
```

2. [`Erdos249257.HalfDivisorUnitDrop.supportCoeff_extend_true_eq_false_add_one_at_double`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfDivisorUnitDrop.lean#L20)

```lean
theorem supportCoeff_extend_true_eq_false_add_one_at_double
    {N : ℕ} (a : HalfWord N) :
    supportCoeff (wordSupport (extendHalfWord a true)) (2 * (N + 1)) =
      supportCoeff (wordSupport (extendHalfWord a false)) (2 * (N + 1)) + 1
```

3. [`Erdos249257.HalfDivisorUnitDrop.supportCoeff_boundaryPair_unitDrop_at_double`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/HalfDivisorUnitDrop.lean#L35)

```lean
theorem supportCoeff_boundaryPair_unitDrop_at_double
    {N : ℕ} (a : HalfWord N) (left right : HalfWord (N + 1))
    (hleft : left = extendHalfWord a true)
    (hright : right = extendHalfWord a false) :
    supportCoeff (wordSupport left) (2 * (N + 1)) =
      supportCoeff (wordSupport right) (2 * (N + 1)) + 1
```

<a id="record-257bm-i17-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `supportCoeff_insert_divisor` | [E257_32/Challenge.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L145) | [PaperStatementsAL.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStatementsAL.lean#L43) | [E257_32](../evidence/comparator/replay-35882032091/receipt-E257_32.json) |
| `supportCoeff_extend_true_eq_false_add_one_at_double` | [E257_20/Challenge.lean, line 263](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L263) | [PaperStatementsAL.lean, line 55](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAL.lean#L55) | [E257_20](../evidence/comparator/replay-35882032091/receipt-E257_20.json) |
| `supportCoeff_boundaryPair_unitDrop_at_double` | [E257_32/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L150) | [PaperStatementsAL.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStatementsAL.lean#L47) | [E257_32](../evidence/comparator/replay-35882032091/receipt-E257_32.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-k1"></a>

## Theorem (A bounded model of the doubling-or-return alternative)

> *The dichotomy $`\mathrm{ExactLocalMersenneHalfRow}(2n{-}1) \vee \exists c,\,4\le c\le n\wedge
> \mathrm{ExactLocalMersenneHalfRow}(2c{-}2)`$ (proved for $`n\ge6`$ at Theorem <a href="#record:257bm-k-dich" data-reference-type="ref" data-reference="record:257bm-k-dich">171</a> below) is not by itself enough for cofinality. Countermodel: $`\mathrm{boundedDoubleOrRecycleModel}(n) := (n=6)`$ satisfies exactly the same two-branch transition shape (seed at 6, and `boundedDoubleOrRecycleModel_transition` reproduces the $`\vee`$ shape by always taking the recycle branch with $`c=4`$, conclusion back at $`2\cdot4-2=6`$), yet
> ``` math
> \neg\big(\forall N,\ \exists n\ge N,\ \mathrm{boundedDoubleOrRecycleModel}(n)\big) \qquad \text{(not cofinal ;  only ever true at } n=6\text{)}.
> ```
> Packaged existentially as `exists_seeded_bounded_double_or_recycle_model`. The double-or-recycle transition shape, even together with an endpoint-six seed, is logically insufficient to conclude cofinal exact rows. A genuinely new progress input (strict endpoint growth, or an independent cofinality argument) is required. The countermodel retains only the seed and this transition rule. It therefore tests those premises, not additional arithmetic information that a more structured induction may use.*
> 
> *<span class="sans-serif">(fixed)</span> *meta-logical* [`boundedDoubleOrRecycleModel`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDichotomy.lean#L58) [`boundedDoubleOrRecycleModel_transition`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDichotomy.lean#L64) [`boundedDoubleOrRecycleModel_not_cofinal`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDichotomy.lean#L79) [`exists_seeded_bounded_double_or_recycle_model`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDichotomy.lean#L91)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_bounded_double_or_recycle_countermodel`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L84)

```lean
theorem paper_bounded_double_or_recycle_countermodel :
    (∀ n : ℕ, boundedDoubleOrRecycleModel n ↔ n = 6) ∧
      boundedDoubleOrRecycleModel 6 ∧
      (∀ n : ℕ, 6 ≤ n → boundedDoubleOrRecycleModel n →
        boundedDoubleOrRecycleModel (2 * n - 1) ∨
          ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ boundedDoubleOrRecycleModel (2 * c - 2)) ∧
      (∀ n : ℕ, 6 ≤ n → boundedDoubleOrRecycleModel n →
        4 ≤ 4 ∧ 4 ≤ n ∧ boundedDoubleOrRecycleModel (2 * 4 - 2)) ∧
      ¬ (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ boundedDoubleOrRecycleModel n)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exists_seeded_bounded_double_or_recycle_model`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L102)

```lean
theorem paper_exists_seeded_bounded_double_or_recycle_model :
    ∃ P : ℕ → Prop,
      P 6 ∧
        (∀ n : ℕ, 6 ≤ n → P n →
          P (2 * n - 1) ∨ ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ P (2 * c - 2)) ∧
        ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n
```

<a id="record-257bm-k1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_bounded_double_or_recycle_countermodel` | [E257_33/Challenge.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L52) | [PaperStatementsAA.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L171) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_exists_seeded_bounded_double_or_recycle_model` | [E257_33/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L63) | [PaperStatementsAA.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L195) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-k-dich"></a>

## Theorem (Doubling or returning to an earlier depth)

> *For $`n\ge6`$, $`\mathrm{ExactLocalMersenneHalfRow}(n)`$:
> ``` math
> \mathrm{ExactLocalMersenneHalfRow}(2n-1) \;\vee\; \exists c,\ 4\le c\le n \wedge \mathrm{ExactLocalMersenneHalfRow}(2c-2).
> ```
> Every exact row of depth at least $`6`$ has at least one of the two asserted continuations. The proof separates the below-half case from the above-half case, but the two existential conclusions need not be exclusive. The returned depth $`2c-2`$ is not claimed to exceed $`n`$. The finite Mersenne value cannot equal $`1/2`$, by Observation <a href="#record:257bm-k11" data-reference-type="ref" data-reference="record:257bm-k11">181</a> (`finiteErdosSum_den_odd`); this says nothing about equality of the returned and original depths. For example, at $`n=6`$, the support $`\{2,3,6\}`$ is an exact row, and so is $`\{2,3,6,7,11\}`$ at depth $`11`$. The second conclusion also holds with $`c=4`$, since $`2c-2=6`$. Thus both conclusions hold in this example, and the second allows no depth increase. What is missing, per Theorem <a href="#record:257bm-k1" data-reference-type="ref" data-reference="record:257bm-k1">170</a>, is not another dichotomy but strict endpoint progress in the recycle branch, or a proof the below-half branch recurs ; re-deriving this disjunction without an additional progress argument would not establish cofinality.*
> 
> *<span class="sans-serif">(bounded)</span> *divisor counts and finite sums* [`exactLocalMersenneHalfRow_double_or_recycle`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDichotomy.lean#L26)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_double_or_recycle`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L33)

```lean
theorem paper_exact_row_double_or_recycle {n : ℕ} (hn : 6 ≤ n)
    (hrow : ExactLocalMersenneHalfRow n) :
    ExactLocalMersenneHalfRow (2 * n - 1) ∨
      ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_row_value_ne_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L41)

```lean
theorem paper_finite_row_value_ne_half {D : Finset ℕ} (h0 : 0 ∉ D) :
    localMersennePrefixValue D ≠ (1 / 2 : ℚ)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_example_six_and_eleven`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L55)

```lean
theorem paper_exact_row_example_six_and_eleven :
    localPrefixQuotient ({2, 3, 6} : Finset ℕ) 6 = 2 ^ (6 - 1) - 1 ∧
      ExactLocalMersenneHalfRow 6 ∧
      localPrefixQuotient ({2, 3, 6, 7, 11} : Finset ℕ) 11 = 2 ^ (11 - 1) - 1 ∧
      ExactLocalMersenneHalfRow (2 * 6 - 1) ∧
      (4 ≤ 4 ∧ 4 ≤ 6 ∧ ExactLocalMersenneHalfRow (2 * 4 - 2)) ∧
      2 * 4 - 2 = 6
```

<a id="record-257bm-k-dich-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_exact_row_double_or_recycle` | [E257_33/Challenge.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L140) | [PaperStatementsAX.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAX.lean#L21) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_finite_row_value_ne_half` | [E257_33/Challenge.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L107) | [PaperStatementsAR.lean, line 243](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAR.lean#L243) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_exact_row_example_six_and_eleven` | [E257_33/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L146) | [PaperStatementsAX.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAX.lean#L26) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-k2"></a>

## Proposition (A sufficient fractional-mass bound need not hold)

> *Take $`D=\{2,3\}`$ and $`c=5`$. Direct calculation gives
> ``` math
> X_D(2)=\frac{10}{21}<\frac12
>  <\frac{331}{651}=X_{D\cup\{5\}}(2),\qquad S(D,1,8)=6<8.
> ```
> However, the combined fractional mass is
> ``` math
> \sum_{d\in D\cup\{5\}}\frac{2^8\bmod(2^d-1)}{2^d-1}
>  =\frac{757}{651}>1.
> ```
> The linked `norm_num` proof checks this example. Thus the combined fractional-mass bound by $`1`$, which suffices for the sharp capacity estimate, is not necessary for that estimate. Thus the fractional-mass bound cannot hold at every real crossing core. A proof using it would need to handle the exceptional cores separately; the example does not rule out all uses of fractional-mass estimates. Theorem <a href="#record:257rig-k6" data-reference-type="ref" data-reference="record:257rig-k6">176</a> identifies the support at a critical crossing with a real greedy prefix, but does not prove the missing bound on those prefixes.*
> 
> *<span class="sans-serif">(fixed)</span> *divisor counts and finite sums* [`splitFractionMass_one_bound_not_necessary_fixture`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkippedCoreCriticalCapacity.lean#L183)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_fractional_mass_bound_not_necessary`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L118)

```lean
theorem paper_fractional_mass_bound_not_necessary :
    localMersennePrefixValue ({2, 3} : Finset ℕ) = 10 / 21 ∧
      localMersennePrefixValue ({2, 3} : Finset ℕ) < (1 / 2 : ℚ) ∧
      localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) = 331 / 651 ∧
      (1 / 2 : ℚ) < localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 = 6 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 8 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 2 ^ (5 - 2) ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 = 757 / 651 ∧
      1 < localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 =
        localFractionMass ({2, 3} : Finset ℕ) 8 + localMersenneFraction 8 5
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_fractional_mass_bound_suffices_for_sharp_capacity`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L139)

```lean
theorem paper_fractional_mass_bound_suffices_for_sharp_capacity
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) < localMersennePrefixValue (insert c D))
    (hfrac : localFractionMass (insert c D) (2 * c - 2) ≤ 1) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)
```

<a id="record-257bm-k2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_fractional_mass_bound_not_necessary` | [E257_33/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L111) | [PaperStatementsAR.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAR.lean#L246) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_fractional_mass_bound_suffices_for_sharp_capacity` | [E257_33/Challenge.lean, line 125](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L125) | [PaperStatementsAR.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAR.lean#L259) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-k4"></a>

## Theorem (The returning endpoint need not be larger)

> *Theorem <a href="#record:257bm-c10" data-reference-type="ref" data-reference="record:257bm-c10">121</a> (`exists_skippedCoreExactRow_of_value_above`) is unconditional, but its witness is $`\exists c\le n`$, not $`\exists c`$ large: $`2c-2`$ may be $`\le n`$, so the endpoint need not grow. Theorem <a href="#record:257bm-k1" data-reference-type="ref" data-reference="record:257bm-k1">170</a>’s `exists_seeded_bounded_double_or_recycle_model` is the explicit falsifier of the naive hope that growth comes for free: $`\mathrm{boundedDoubleOrRecycleModel}(n):=(n=6)`$ satisfies the same transition schema plus a seed and is not cofinal. Growth is recovered only inside $`\mathrm{ProtectedExactLocalMersenneRow}`$ (Theorem <a href="#record:257bm-c5" data-reference-type="ref" data-reference="record:257bm-c5">114</a>), whose invariants $`\mathrm{endpoint}<2\cdot\mathrm{cutoff}`$ and $`\mathrm{new\_above\_cutoff}`$ force $`c>\mathrm{cutoff}`$ hence $`2c-2>\mathrm{endpoint}`$ ; and maintaining those invariants is precisely what needs the strict-upper (sharp capacity) fill of Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a> rather than this general recycling theorem.*
> 
> *<span class="sans-serif">(bounded)</span> *binary digits* [`exists_skippedCoreExactRow_of_value_above`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowCrossing.lean#L155)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_skipped_core_recycling_witness_bounded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L163)

```lean
theorem paper_skipped_core_recycling_witness_bounded
    {E : Finset ℕ} {n : ℕ} (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_returning_endpoint_may_fail_to_grow`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L172)

```lean
theorem paper_returning_endpoint_may_fail_to_grow :
    ∃ n c : ℕ, 4 ≤ c ∧ c ≤ n ∧ 2 * c - 2 ≤ n ∧
      ExactLocalMersenneHalfRow (2 * c - 2)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exists_seeded_bounded_double_or_recycle_model`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L102)

```lean
theorem paper_exists_seeded_bounded_double_or_recycle_model :
    ∃ P : ℕ → Prop,
      P 6 ∧
        (∀ n : ℕ, 6 ≤ n → P n →
          P (2 * n - 1) ∨ ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ P (2 * c - 2)) ∧
        ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_protected_row_crossing_beyond_cutoff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L184)

```lean
theorem paper_protected_row_crossing_beyond_cutoff
    (s : ProtectedExactLocalMersenneRow) {e : ℕ} (heSupport : e ∈ s.support)
    (heCross : (1 / 2 : ℚ) <
      localMersennePrefixValue (insert e (s.support.filter fun d => d < e))) :
    s.cutoff < e
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_protected_row_endpoint_growth`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L218)

```lean
theorem paper_protected_row_endpoint_growth
    (s : ProtectedExactLocalMersenneRow) {c : ℕ} (hc : s.cutoff < c) :
    s.endpoint < 2 * c - 2
```

<a id="record-257bm-k4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_skipped_core_recycling_witness_bounded` | [E257_33/Challenge.lean, line 170](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L170) | [PaperStatementsAS.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAS.lean#L36) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_returning_endpoint_may_fail_to_grow` | [E257_33/Challenge.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L155) | [PaperStatementsAX.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAX.lean#L34) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_exists_seeded_bounded_double_or_recycle_model` | [E257_33/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L63) | [PaperStatementsAA.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L195) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_protected_row_crossing_beyond_cutoff` | [E257_33/Challenge.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L203) | [PaperStructuresBG.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStructuresBG.lean#L68) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_protected_row_endpoint_growth` | [E257_33/Challenge.lean, line 210](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L210) | [PaperStructuresBG.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStructuresBG.lean#L74) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-k6"></a>

## Theorem (Uniqueness at a critical crossing)

> *For $`c\ge4`$, $`D`$ bounded $`[2,c)`$, below-half, with genuine crossing deficit $`\tfrac12-\mathrm{value}(D) < \ensuremath{w}(c)`$:
> ``` math
> D \;=\; \mathrm{halfGreedyPrefixSupport}(c-1).
> ```
> Thus $`D=G\cap\{1,\ldots,c-1\}`$: at a critical crossing the support is fixed by $`c`$. The proof uses the strict inequality between each Mersenne weight and the sum of all later weights, as in Theorem <a href="#record:257bm-i11a" data-reference-type="ref" data-reference="record:257bm-i11a">143</a>. Consequently, the support quantifier in Theorem <a href="#record:257bm-c4" data-reference-type="ref" data-reference="record:257bm-c4">113</a> does not allow arbitrary choices of $`D`$. This reduces that hypothesis to a statement about the actual greedy sequence. It does not rule out proving a new bound for that sequence.*
> 
> *<span class="sans-serif">(uniform)</span> *greedy recurrence* [`eq_halfGreedyPrefixSupport_of_critical_crossing`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L50)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_crossing_support_is_greedy_prefix`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L231)

```lean
theorem paper_critical_crossing_support_is_greedy_prefix
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1) ∧
      (↑D : Set ℕ) = greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Iic (c - 1)
```

<a id="record-257rig-k6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_critical_crossing_support_is_greedy_prefix` | [E257_33/Challenge.lean, line 256](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L256) | [PaperStatementsK.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsK.lean#L122) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-k9"></a>

## Theorem (Vanishing of the specified linear-channel determinant)

> *Let $`V`$ be a vector space over $`\mathbb{Q}`$, let $`e:V\to\mathbb{Q}`$ be linear, and let $`(\ell_j)_{j\in\iota}`$ be a finite family of linear functionals vanishing on $`\ker e`$. For any vectors $`(v_i)_{i\in\iota}`$, the matrix $`(\ell_j(v_i))_{i,j\in\iota}`$ has rank at most one, so every square minor of size at least two vanishes. Indeed, the functionals descend to $`V/\ker e`$, which has dimension at most one. This elementary linear-algebra argument applies at every matrix size. It does not cover additional functionals that fail to vanish on $`\ker e`$.*
> 
> *<span class="sans-serif">(uniform)</span> *linear-algebra* [`relationInvariantLinearChannels_det_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L42)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_rank_le_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L37)

```lean
theorem paper_relationInvariant_channels_rank_le_one
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    ∃ u w : ι → ℚ, ∀ i j : ι, channel j (row i) = u i * w j
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_det_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L63)

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
| `paper_relationInvariant_channels_rank_le_one` | [E257_33/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L80) | [PaperStatementsAA.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L228) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_relationInvariant_channels_det_eq_zero` | [E257_33/Challenge.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L71) | [PaperStatementsAA.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L219) | [E257_33](../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-k12"></a>

## Theorem (Excluding the cell with value minus three)

> *At a middle row $`D\ge13`$ followed only by right transitions, $`4\,\mathrm{rem}(D)-p_D^--4\ne-3`$, by Theorem <a href="#thm:final-middle-cell" data-reference-type="ref" data-reference="thm:final-middle-cell">87</a>. Its proof uses the nonnegative centred carry for the completed support, not a finite search. The values $`-2,-1`$ remain among the three exceptional negative cells. Excluding them under this extra tail assumption would still not exclude nonnegative values of the coordinate, or establish the all-middle-row and right-branch hypotheses in Theorem <a href="#thm:two-sided-dyadic" data-reference-type="ref" data-reference="thm:two-sided-dyadic">52</a>. The complete remaining tail inequality is stated in Remark <a href="#rem:tail-dominance-open" data-reference-type="ref" data-reference="rem:tail-dominance-open">260</a>.*
> 
> *<span class="sans-serif">(uniform)</span> *mobius-centred-carry* [`finalMiddleCell_neg_three_not_last`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L587) [`mobiusCenteredHalfCarry_add_two`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L39) [`cofiniteRightTail_ne_zero_centeredEndpoint`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L547)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_ne_neg_three`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L100)

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

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_remaining_negative_values`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L118)

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

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_mobiusCenteredHalfCarry_add_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L155)

```lean
theorem paper_mobiusCenteredHalfCarry_add_two (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_cofiniteRightTail_ne_zero_centeredEndpoint`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L163)

```lean
theorem paper_cofiniteRightTail_ne_zero_centeredEndpoint
    (A : Set ℕ) (D : ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (hcofinite : Set.Ioi D ⊆ A) :
    mobiusCenteredHalfCarry A (2 * D + 1) ≠ 0
```

<a id="record-257hg-k12-comparator"></a>

**Comparator:** not yet compared.

<a id="prop-unsafe-middle-range-exactly-three"></a>

## Proposition

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_unsafe_middle_range_is_three_integers`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L83)

```lean
theorem paper_unsafe_middle_range_is_three_integers {s : ℕ} (hs : 5 ≤ s) :
    ¬ (4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≤ -4 ∨
          0 ≤ 4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4) ↔
      4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -3 ∨
        4 * ((seamAdjacentCut s hs).remainder : ℤ) -
              ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -2 ∨
          4 * ((seamAdjacentCut s hs).remainder : ℤ) -
              ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -1
```

<a id="prop-unsafe-middle-range-exactly-three-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_unsafe_middle_range_is_three_integers` | [E257_31/Challenge.lean, line 373](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_31/Challenge.lean#L373) | [PaperStructuresBP.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_31/PaperStructuresBP.lean#L131) | [E257_31](../evidence/comparator/replay-35882032091/receipt-E257_31.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-approximations-without-compatibility"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_contains_strip_witness`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SharedPrefixFamiliesAndMeasureDichotomy.lean#L37)

```lean
theorem paper_shared_prefix_family_contains_strip_witness
    {K N : ℕ} (S : CylinderStage K N) :
    ∃ a : Erdos249257.HalfCarryReachability.HalfWord N,
      a ⟨0, Nat.zero_lt_succ N⟩ = false ∧
        (∀ h : 1 < N + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N - 1) : ℝ)| ≤
          (halfStripBound N : ℝ)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_strip_witness_after_feedback_all_depths`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L104)

```lean
theorem paper_shared_prefix_family_strip_witness_after_feedback_all_depths
    {K N : ℕ} (S : CylinderStage K N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) :
    ∃ a : Erdos249257.HalfCarryReachability.HalfWord (N + 1),
      a ⟨0, Nat.zero_lt_succ (N + 1)⟩ = false ∧
        (∀ h : 1 < N + 1 + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N + 1 - 1) : ℝ)| ≤
          (halfStripBound (N + 1) : ℝ)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_feedback_row_total_dichotomy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L84)

```lean
theorem paper_feedback_row_total_dichotomy
    {K N : ℕ} (S : CylinderStage K N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) :
    Nonempty (CylinderStage (K + 1) (N + 1)) ∨
      Nonempty (InStripTwoSheetStage K (N + 1))
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.halfTerminalOnlyStripWitness_of_feedbackAdvance`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L74)

```lean
theorem halfTerminalOnlyStripWitness_of_feedbackAdvance
    {K M : ℕ} (S : CylinderStage K M) :
    Erdos249257.HalfCarryReachability.HalfTerminalOnlyStripWitness M
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.halfTerminalOnlyStripWitness_of_inStripTwoSheetStage_via_carries_three_four`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L53)

```lean
theorem halfTerminalOnlyStripWitness_of_inStripTwoSheetStage_via_carries_three_four
    {K M : ℕ} (T : InStripTwoSheetStage K M) :
    Erdos249257.HalfCarryReachability.HalfTerminalOnlyStripWitness M
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.four_le_halfStripBound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L42)

```lean
theorem four_le_halfStripBound (m : ℕ) : 4 ≤ halfStripBound m
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_strip_witness_after_feedback_of_all_depths`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L121)

```lean
theorem paper_shared_prefix_family_strip_witness_after_feedback_of_all_depths
    {K N : ℕ} (S : CylinderStage K N) (_hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) (_h27 : 27 ≤ halfStripBound (N + 1)) :
    ∃ a : Erdos249257.HalfCarryReachability.HalfWord (N + 1),
      a ⟨0, Nat.zero_lt_succ (N + 1)⟩ = false ∧
        (∀ h : 1 < N + 1 + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N + 1 - 1) : ℝ)| ≤
          (halfStripBound (N + 1) : ℝ)
```

<a id="prop-finite-approximations-without-compatibility-comparator"></a>

**Comparator:** not yet compared.

<a id="prop-exact-lebesgue-measure-dichotomy"></a>

## Proposition

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_volume_supportedMersenneAchievementSet_dichotomy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SharedPrefixFamiliesAndMeasureDichotomy.lean#L68)

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
| `paper_volume_supportedMersenneAchievementSet_dichotomy` | [E257_34/Challenge.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_34/Challenge.lean#L229) | [PaperStatementsAM.lean, line 236](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_34/PaperStatementsAM.lean#L236) | [E257_34](../evidence/comparator/replay-35882032091/receipt-E257_34.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-one-orbit"></a>

## Proposition (Stability of each fixed greedy prefix)

> *Let $`t_j\to1/2`$ and, for each fixed $`n\ge2`$, let $`v_n^{(j)}\to x_n=(2^n-1)^{-1}`$, with $`v_n^{(j)}>0`$. Apply the greedy rule with target $`t_j`$ and weights $`v_n^{(j)}`$ in increasing order of $`n`$, through depths $`m_j\to\infty`$. For every fixed depth $`K`$, the decisions at ranks $`2,\ldots,K`$ eventually agree with those of the real half-greedy rule. This assertion concerns finite prefixes, not survival at all ranks.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_one_orbit_stability`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L272)

```lean
theorem paper_one_orbit_stability
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (dep : ℕ → ℕ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n)))
    (hvpos : ∀ j n : ℕ, 0 < v j n)
    (hdep : Filter.Tendsto dep Filter.atTop Filter.atTop)
    (K : ℕ) :
    ∀ᶠ j in Filter.atTop, K ≤ dep j ∧
      ∀ n : ℕ, 2 ≤ n → n ≤ K →
        ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
          (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)))
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.approx_orbit_induction`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L182)

```lean
theorem approx_orbit_induction
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n))) :
    ∀ r : ℕ,
      Filter.Tendsto (fun j => tailGreedyRemainder (t j) (v j) r) Filter.atTop
          (nhds (greedyMersenneRemainder (1 / 2 : ℝ) (r + 1))) ∧
        ∀ᶠ j in Filter.atTop, ∀ n : ℕ, 2 ≤ n → n ≤ r + 1 →
          ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
            (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)))
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder_mersenne`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L166)

```lean
theorem tailGreedyRemainder_mersenne (m : ℕ) :
    tailGreedyRemainder (1 / 2 : ℝ) mersenneWeight m
      = greedyMersenneRemainder (1 / 2 : ℝ) (m + 1)
```

<a id="prop-one-orbit-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_one_orbit_stability` | [E257_35/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L104) | [PaperStatementsN.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsN.lean#L246) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |
| `approx_orbit_induction` | [E257_35/Challenge.lean, line 78](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L78) | [PaperStatementsN.lean, line 121](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsN.lean#L121) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |
| `tailGreedyRemainder_mersenne` | [E257_35/Challenge.lean, line 127](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L127) | [PaperStatementsN.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsN.lean#L283) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-no-ties"></a>

## Lemma (No-ties lemma)

> *At every rank $`k`$ of the full greedy orbit for target $`1/2`$, both defining comparisons are strict: $`\rho\ne x_k`$ and $`\rho\ne T_{k+1}`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L126)

```lean
theorem paper_no_ties (k : ℕ) (hk : 2 ≤ k) :
    greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneWeight k ∧
      greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneTail k
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_take`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L71)

```lean
theorem paper_no_ties_take (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneWeight (n + 1)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_skip`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L114)

```lean
theorem paper_no_ties_skip (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneTail (n + 1)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.irrational_mersenneTail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L44)

```lean
theorem irrational_mersenneTail : ∀ n : ℕ, Irrational (mersenneTail n)
```

<a id="lem-no-ties-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_no_ties` | [E257_35/Challenge.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L91) | [PaperStatementsN.lean, line 230](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsN.lean#L230) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |
| `paper_no_ties_take` | [E257_35/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L100) | [PaperStatementsN.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsN.lean#L241) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |
| `paper_no_ties_skip` | [E257_35/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L96) | [PaperStatementsN.lean, line 236](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsN.lean#L236) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |
| `irrational_mersenneTail` | [E257_35/Challenge.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L141) | [PaperStatementsAM.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsAM.lean#L200) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-tr-forced-greedy"></a>

## Lemma (Forced greedy)

> *For every $`J\ge2`$: $`w_n^{(J)}>T_{n+1}^{(J)}`$ for all $`n`$ (the $`q=1`$ terms agree exactly, and every $`q\ge2`$ tail term is strictly smaller than the corresponding weight term). Consequently the greedy support is the unique candidate support, and $`\mathrm{HalfRung}(J)`$ holds iff the greedy orbit for $`1/2`$ under weights $`w_n^{(J)}`$ never lands in a fatal interval $`(T_{n+1}^{(J)},w_n^{(J)})`$. Rank $`1`$ is always a safe skip; ranks $`2`$ and $`3`$ are always takes.*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_unique_support_and_criterion`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungGreedyDecision.lean#L486)

```lean
theorem paper_forced_greedy_unique_support_and_criterion {J : ℕ} (hJ : 2 ≤ J) :
    (∀ A : Set ℕ, ∑' n : ℕ, rungSupportWeight J A n = 1 / 2 → A = rungGreedySupport J) ∧
      (HalfRung J ↔ ∀ n : ℕ, ¬ RungFatal J n)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_low_ranks`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungGreedyDecision.lean#L567)

```lean
theorem paper_forced_greedy_low_ranks {J : ℕ} (hJ : 2 ≤ J) :
    (1 ∉ rungGreedySupport J ∧ rungRem J 1 ≤ rungTail J 1) ∧
      2 ∈ rungGreedySupport J ∧ 3 ∈ rungGreedySupport J
```

<a id="lem-tr-forced-greedy-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_forced_greedy_unique_support_and_criterion` | [E257_35/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L186) | [PaperStatementsJ.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsJ.lean#L19) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |
| `paper_forced_greedy_low_ranks` | [E257_35/Challenge.lean, line 151](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L151) | [PaperStatementsAI.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsAI.lean#L19) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-tr-parity"></a>

## Lemma (Parity forces infinite support)

> *For every $`J\ge2`$, no finite $`A\subseteq\{2,3,\ldots\}`$ attains $`\mathrm{HalfRung}(J)`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_parity_excludes_finite_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungWitnessHorizon.lean#L176)

```lean
theorem paper_parity_excludes_finite_support {J : ℕ} (hJ : 2 ≤ J)
    (A : Finset ℕ) (hA : ∀ n ∈ A, 2 ≤ n) :
    ∑ n ∈ A, truncWeight J n ≠ 1 / 2
```

<a id="lem-tr-parity-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_parity_excludes_finite_support` | [E257_35/Challenge.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L221) | [PaperStatementsAA.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsAA.lean#L203) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-tr-witness-exclusion"></a>

## Theorem (Witness exclusion)

> *Define the misalignment mass
> ``` math
> \mu_J(M):=\sum_{q=2}^{J}\frac{2^{M\bmod q}}{2^q-1}.
> ```
> Let $`J\ge3`$, $`n\ge4`$, and suppose some $`M\in[n,2n-2]`$ has $`\mu_J(M)\le\tfrac{11}{15}`$. Then no Boolean prefix $`D\subseteq\{2,\ldots,n-1\}`$ satisfies
> ``` math
> T_{n+1}^{(J)}<\tfrac12-\sum_{d\in D}w_d^{(J)}<w_n^{(J)};
> ```
> This excludes the specified gap for every Boolean prefix, not only the greedy prefix.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_witness_exclusion`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungWitnessHorizon.lean#L250)

```lean
theorem paper_witness_exclusion {J n M : ℕ} (hJ : 3 ≤ J) (hn : 4 ≤ n)
    (hMlow : n ≤ M) (hMhigh : M + 2 ≤ 2 * n)
    (hmu : misalignMass J M ≤ 11 / 15)
    (D : Finset ℕ) (hD : ∀ d ∈ D, 2 ≤ d ∧ d + 1 ≤ n) :
    ¬ (truncTail J n < 1 / 2 - ∑ d ∈ D, truncWeight J d ∧
        1 / 2 - ∑ d ∈ D, truncWeight J d < truncWeight J n)
```

<a id="thm-tr-witness-exclusion-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_witness_exclusion` | [E257_35/Challenge.lean, line 230](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L230) | [PaperStatementsAA.lean, line 323](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsAA.lean#L323) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-tr-half-lcm"></a>

## Corollary (Half-LCM horizon)

> *Let $`J\ge2`$ and $`L_J:=\mathrm{lcm}(2,3,\ldots,J)`$. For every $`n\ge\max\{4,L_J/2+1\}`$ there is an $`M\in[n,2n-2]`$ with $`\mu_J(M)<11/15`$. Thus witness exclusion leaves only the finite window $`[4,L_J/2]`$ to check.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_half_lcm_horizon`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungWitnessHorizon.lean#L467)

```lean
theorem paper_half_lcm_horizon {J n : ℕ} (hJ : 2 ≤ J) (hn4 : 4 ≤ n)
    (hn : truncLcm J / 2 + 1 ≤ n) :
    ∃ M : ℕ, n ≤ M ∧ M + 2 ≤ 2 * n ∧ misalignMass J M < 11 / 15
```

<a id="cor-tr-half-lcm-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_half_lcm_horizon` | [E257_35/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L212) | [PaperStatementsAA.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsAA.lean#L190) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-tr-mod12"></a>

## Lemma (Mod-12 filter, $`J\ge7`$)

> *For $`J\ge7`$, the inequality $`\mu_J(M)\le11/15`$ implies $`12\mid M`$. Thus only multiples of $`12`$ need be tested as witnesses in each interval $`[n,2n-2]`$; no potentially uncovered rank is discarded.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_mod_twelve_filter`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungWitnessHorizon.lean#L544)

```lean
theorem paper_mod_twelve_filter {J M : ℕ} (hJ : 7 ≤ J)
    (hmu : misalignMass J M ≤ 11 / 15) : 12 ∣ M
```

<a id="lem-tr-mod12-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_mod_twelve_filter` | [E257_35/Challenge.lean, line 217](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L217) | [PaperStatementsAA.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsAA.lean#L200) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-tr-finite-decision"></a>

## Theorem (Finite decision procedure)

> *Call $`n\in[4,L_J/2]`$ **bad** if no $`M\in[n,2n-2]`$ has $`\mu_J(M)\le\tfrac{11}{15}`$, and set $`B(J):=\max(\mathrm{bad}\cup\{3\})`$. Then $`\mathrm{HalfRung}(J)`$ holds iff the greedy orbit for $`1/2`$ under weights $`w_n^{(J)}`$ survives every rank from $`2`$ through $`B(J)`$. This is a finite exact decision procedure.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_rung_finite_decision`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungGreedyDecision.lean#L896)

```lean
theorem paper_rung_finite_decision {J : ℕ} (hJ : 2 ≤ J) :
    HalfRung J ↔ ∀ n : ℕ, 2 ≤ n → n ≤ rungDecisionHorizon J → ¬ RungFatal J n
```

<a id="thm-tr-finite-decision-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_rung_finite_decision` | [E257_35/Challenge.lean, line 191](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L191) | [PaperStatementsJ.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsJ.lean#L25) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-lower-bound-every-reset"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_half_membership`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L595)

```lean
theorem paper_theoremA_half_membership (h : PaperResetSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paperResetSqrtEscape_iff_square`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L545)

```lean
theorem paperResetSqrtEscape_iff_square :
    PaperResetSqrtEscape ↔ SeamResetSqrtEscape
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_crossing_bound_square_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L121)

```lean
theorem paper_theoremA_crossing_bound_square_le (r : ℕ) (hr : 10 ≤ r) :
    resetCrossingBound r ^ 2 ≤ 2 ^ (r + 5)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_right_branch_forces_small_deviation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L261)

```lean
theorem paper_theoremA_right_branch_forces_small_deviation
    {s d : ℕ} (hs14 : 14 ≤ s)
    (hd : IsLargestFalseRank (seamGreedyWord s) d)
    (hlate : 2 * s < 3 * d) (hcross : 3 * d ≤ 2 * (s + 1))
    (hR : ¬ SeamGreedyUpperOrMiddleAt s (by omega)) :
    (seamResetDeviation d).natAbs ≤ resetCrossingBound d
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.half_mem_mersenneAchievementSet_of_resetSqrtEscape`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ResetSqrtEscapeHalfMembership.lean#L526)

```lean
theorem half_mem_mersenneAchievementSet_of_resetSqrtEscape
    (hsqrt : SeamResetSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="thm-lower-bound-every-reset-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-one-sided-finite-decision-boundary"></a>

## Theorem

The Lean declaration below states a result at least as strong as this one.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sided_finite_decision_boundary`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/CentredCompletionAndDecisionBoundary.lean#L77)

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
| `paper_one_sided_finite_decision_boundary` | [E257_35/Challenge.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_35/Challenge.lean#L118) | [PaperStatementsN.lean, line 261](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_35/PaperStatementsN.lean#L261) | [E257_35](../evidence/comparator/replay-35882032091/receipt-E257_35.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-2adic-nogo"></a>

## Proposition (Centred completion of fixed-precision 2-adic data)

> *Fix $`u\ge1`$ and a finite list $`(v_i,a_i)_{0\le i<m}`$, where $`v_i\ge0`$ are integers and the integers $`a_i`$ are odd. For every initial integer $`e_0`$, there are integers $`z_i,e_{i+1}`$ such that
> ``` math
> e_{i+1}=2e_i+2^{v_i}(a_i+2^u z_i),\qquad
>  |e_{i+1}|\le2^{v_i+u-1}\qquad(0\le i<m).
> ```
> Thus one may prescribe the valuation and $`u`$ bits of the odd unit of each input coefficient while keeping every *successor* state in its stated centred interval. The initial state is arbitrary. *2-adic-valuation-unit*<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(finite words)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_centred_completion_of_fixed_precision`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/CentredCompletionAndDecisionBoundary.lean#L34)

```lean
theorem paper_centred_completion_of_fixed_precision
    (u : ℕ) (hu : 1 ≤ u) (m : ℕ) (v : ℕ → ℕ) (a : ℕ → ℤ)
    (hodd : ∀ i, i < m → Odd (a i)) (e₀ : ℤ) :
    ∃ e z : ℕ → ℤ, e 0 = e₀ ∧
      ∀ i, i < m →
        e (i + 1) = 2 * e i + 2 ^ (v i) * (a i + 2 ^ u * z i) ∧
          |e (i + 1)| ≤ 2 ^ (v i + u - 1)
```

<a id="prop-2adic-nogo-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_centred_completion_of_fixed_precision` | [E257_04/Challenge.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L56) | [PaperStatementsAA.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAA.lean#L181) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-upper-unconditional"></a>

## Proposition (The upper (carries) successor needs no exceptional-cell exclusion)

> *Let $`s\ge5`$ and suppose the upper branch occurs at row $`s`$, that is, $`(\mathrm{seamAdjacentCut}\ s\ hs).\mathrm{successorCarries}`$ holds. Then
> ``` math
> \mathrm{rem}(s+1)\le2^{s+1}.
> ```
> [`Erdos249257.seamUpperBranch_nextRemainder_le_pow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3924) Indeed, the reset identity expresses $`2^{s+1}`$ as $`\mathrm{rem}(s+1)`$ plus a nonnegative reset charge: [`Erdos249257.seamUpperBranch_remainder_add_resetCharge_eq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3542). Thus the upper branch needs no exceptional-value exclusion for the next-row two-sided invariant. This conclusion concerns that induction step, not the absence of upper transitions on the orbit. *quotient-branch-classification* <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_upper_branch_needs_no_exceptional_cell`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/BranchCellHorizonExclusions.lean#L31)

```lean
theorem paper_upper_branch_needs_no_exceptional_cell {s : ℕ} (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    seamIntegerGreedyRemainder (s + 1) ≤ 2 ^ (s + 1) ∧
      0 ≤ 4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse ∧
      seamIntegerGreedyRemainder (s + 1) +
          (4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse) =
        2 ^ (s + 1)
```

<a id="prop-upper-unconditional-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_upper_branch_needs_no_exceptional_cell` | [E257_31/Challenge.lean, line 386](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_31/Challenge.lean#L386) | [PaperStructuresBP.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_31/PaperStructuresBP.lean#L145) | [E257_31](../evidence/comparator/replay-35882032091/receipt-E257_31.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-cd-neg3-impossible"></a>

## Theorem ($`C_D=-3`$ is impossible at the final middle transition, $`D\ge 13`$)

> *Consider a hypothetical *final middle transition*: a middle transition at row $`D\ge 13`$ ($`\lnot\mathrm{carries}`$, and the middle-branch inequality $`4\mathrm{rem}(D)+\mathrm{gap}-\mathrm{belowPulse} < \mathrm{terminalWeight}`$ holds at $`D`$), followed by an all-right tail forever after ($`\forall s\ge D{+}1`$, $`\mathrm{seamGreedyWord}(s+1) =
> \mathrm{seamGreedyWord}(s).\mathrm{extend}\ \mathrm{true}`$). Under these assumptions,
> ``` math
> \mathrm{belowPulse}(D) + 2 \;\le\; 4\cdot\mathrm{rem}(D),
> ```
> i.e. $`C_D \ge -2`$ ; the cell $`C_D=-3`$ (and every more negative value) is excluded. [`Erdos249257.middleThenAllRight_landingExcess_two_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2319)*
> 
> ***Proof of the bound.** The all-right-tail assumption puts the terminal-augmented finite prefix strictly above $`1/2`$ ([`Erdos249257.half_lt_upper_competitor_of_eventually_right`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFatalGapRightTail.lean#L627)). Consequently the producer carry is below its complete incidence tail ([`Erdos249257.middleProducer_allRight_forces_carry_lt_tail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1814)), or equivalently $`Z_D<1+1/(2^D-1)`$, where $`Z_D=\mathrm{rem}(D)-\mathrm{seamWordFloorError}(D)`$ ([`Erdos249257.middleProducer_allRight_forces_floorZ_lt_takeThreshold`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1869)). The lower bound uses the other endpoint: under the same tail assumption, the finite value at $`D`$ plus the complete Mersenne tail remains below $`1/2`$. The exact scaled remainder identity therefore gives
> ``` math
> Z_D>4^D\sum_{e>D}\frac1{2^e-1}-2^D>\frac13.
> ```
> The last inequality follows by retaining the first two geometric channels of the complete Mersenne tail. Put $`E_D=\mathrm{seamWordFloorError}(D)`$. Pulse absorption gives $`\mathrm{belowPulse}(D)\le4E_D`$, so
> ``` math
> 4\,\mathrm{rem}(D)-\mathrm{belowPulse}(D)
>  \ge4(\mathrm{rem}(D)-E_D)=4Z_D>\frac43.
> ```
> The left side is an integer, hence is at least $`2`$, as required. The upper threshold inequality alone would not give this lower bound.*
> 
> ***Scope.** This excludes $`C_D=-3`$ at a middle row $`D\ge13`$ under the additional all-right-tail assumption. The general induction requires exclusion of all three cells at every middle row, not just under this extra hypothesis, together with its right-branch bound. The two statements share the same coordinate $`C_D`$ but have different hypotheses. Theorem <a href="#thm:cd-neg3-impossible" data-reference-type="ref" data-reference="thm:cd-neg3-impossible">258</a> is universal over rows satisfying the additional all-right-tail assumption; it does not assert that such a row exists. The induction hypothesis concerns every middle row, without that tail assumption. Excluding $`C_D=-3`$ in the former statement therefore does not supply the exclusion required in the latter. *final-required input; conclusion-excess* **Object or representation:** about the *object* under the stated hypothesis ; a genuine arithmetic consequence of the all-right-tail assumption via the fatal-gap orbit, not a coordinate artifact. <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_at_least_neg_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/BranchCellHorizonExclusions.lean#L50)

```lean
theorem paper_final_middle_cell_at_least_neg_two
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (seamAdjacentCut D (by omega)).belowPulse + 2 ≤
        4 * (seamAdjacentCut D (by omega)).remainder ∧
      (-2 : ℤ) ≤ 4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ∧
      ∀ c : ℤ, c ≤ -3 →
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≠ c
```

<a id="thm-cd-neg3-impossible-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_final_middle_cell_at_least_neg_two` | [E257_12/Challenge.lean, line 249](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_12/Challenge.lean#L249) | [Statement.lean, line 242](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_12/Statement.lean#L242) | [E257_12](../evidence/comparator/replay-35882032091/receipt-E257_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-cd-remaining"></a>

## Corollary (Only $`C_D\in\{-2,-1\}`$ remain among the exceptional dyadic cells)

> *At a final middle row $`D\ge13`$, Theorem <a href="#thm:cd-neg3-impossible" data-reference-type="ref" data-reference="thm:cd-neg3-impossible">258</a> removes $`-3`$ from the exceptional set $`\{-3,-2,-1\}`$, leaving $`-2,-1`$ *within that set*. It does not assert $`C_D\in\{-2,-1\}`$: nonnegative values have not been excluded. Proposition <a href="#prop:upper-unconditional" data-reference-type="ref" data-reference="prop:upper-unconditional">257</a> handles upper transitions in the two-sided induction; it supplies no additional restriction on a middle coordinate. For the all-middle-row induction, the exclusion of all three values still needs proof without an all-right-tail assumption, together with the separate right-branch inequality. *final-required input; conclusion-excess* <span class="sans-serif">\[Lean\]</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_remaining_cells`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/BranchCellHorizonExclusions.lean#L81)

```lean
theorem paper_final_middle_cell_remaining_cells
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -3 ∨
          4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
              ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
            4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
                ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1) →
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
              ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1
```

<a id="cor-cd-remaining-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_final_middle_cell_remaining_cells` | [E257_12/Challenge.lean, line 282](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_12/Challenge.lean#L282) | [Statement.lean, line 277](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_12/Statement.lean#L277) | [E257_12](../evidence/comparator/replay-35882032091/receipt-E257_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-state-nogo"></a>

## Proposition (A finite-state restriction for the stated pulse family)

> *For a “balanced pulse” family at location $`m\ge2`$ (radius $`\rho=\lfloor(m{+}1)/2\rfloor`$, parameters $`0\le r\le\rho`$, moving mass between positions $`m`$ and $`m{+}1`$ with the weighted total $`2c(m)+c(m{+}1)=2\rho`$ of the two coefficients fixed), if a predecessor state is constant across the whole family, then no function $`\mathrm{decode}:\mathrm{State}\to\mathbb N`$ can recover the parameter $`r`$ from $`\mathrm{state}(r)`$ for every $`r`$. The family has exactly $`\rho+1=\lfloor(m{+}1)/2\rfloor+1`$ members, so the fan-out is unbounded in $`m`$. More strongly, any finite set of states carrying an exact decoder for the family has at least $`\rho+1`$ elements, unbounded in $`m`$. [`Erdos249257.balancedPulse_no_autonomous_decoder`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L247) (exact family size at [`ErdosProblems.Erdos257.PaperCompleteR21.paper_balanced_pulse_fanout_is_radius_succ`](https://github.com/wcook04/plectis-erdos/blob/168bf6727758f918a430ef056a1c93d3160b53a6/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L61)).*
> 
> ***Scope.** Excludes bounded-state encodings of pre-$`m`$ history that must distinguish every member of the displayed balanced-pulse family, whether the coefficients are $`\varphi`$ or a Möbius-support indicator. Applying it to \#249 or \#257 requires showing that the relevant orbit realises that family, and it does not rule out every finite-state proof strategy. *binary digits, generic* **Object or representation:** about a *representation* class, the encodings of history that separate the balanced-pulse family; it says nothing about $`C`$ or $`\mathcal A`$ directly. <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_no_autonomous_decoder`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L113)

```lean
theorem paper_pulse_family_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_balanced_pulse_fanout_is_radius_succ`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L61)

```lean
theorem paper_balanced_pulse_fanout_is_radius_succ (m : ℕ) :
    (balancedPulseFamily m).ncard = balancedPulseRadius m + 1 ∧
      (balancedPulseFamily m).ncard = (m + 1) / 2 + 1
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_balanced_pulse_fanout_unbounded_corrected`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L95)

```lean
theorem paper_balanced_pulse_fanout_unbounded_corrected :
    (∀ m : ℕ, m / 2 + 1 ≤ (balancedPulseFamily m).ncard) ∧
      ∀ N : ℕ, ∃ m : ℕ, N ≤ (balancedPulseFamily m).ncard
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_finite_state_card`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L123)

```lean
theorem paper_pulse_family_finite_state_card
    {m : ℕ} {State : Type*} [Fintype State]
    (state : Fin (balancedPulseRadius m + 1) → State)
    (decode : State → ℕ) (hdecode : ∀ r, decode (state r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card State ∧
      ∀ N : ℕ, ∃ m' : ℕ, N ≤ balancedPulseRadius m' + 1
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.balancedPulseCoeff_injective`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L52)

```lean
theorem balancedPulseCoeff_injective (m : ℕ) :
    Function.Injective (balancedPulseCoeff m)
```

6. [`Erdos249257.balancedPulse_weighted_pair`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L200)

```lean
theorem balancedPulse_weighted_pair
    {m r : ℕ} (hr : r ≤ balancedPulseRadius m) :
    2 * balancedPulseCoeff m r m + balancedPulseCoeff m r (m + 1) =
      2 * balancedPulseRadius m
```

<a id="prop-finite-state-nogo-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_pulse_family_no_autonomous_decoder` | [E257_36/Challenge.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L71) | [PaperStatementsBD.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsBD.lean#L43) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_balanced_pulse_fanout_is_radius_succ` | [E257_36/Challenge.lean, line 53](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L53) | [PaperStatementsBD.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsBD.lean#L28) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_balanced_pulse_fanout_unbounded_corrected` | [E257_36/Challenge.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L58) | [PaperStatementsBD.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsBD.lean#L32) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_pulse_family_finite_state_card` | [E257_36/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L63) | [PaperStatementsBD.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsBD.lean#L36) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `balancedPulseCoeff_injective` | [E257_36/Challenge.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L49) | [PaperStatementsBD.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsBD.lean#L23) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `balancedPulse_weighted_pair` | [E257_04/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L111) | [PaperStatementsAE.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAE.lean#L47) | [E257_04](../evidence/comparator/replay-35882032091/receipt-E257_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-mobius-nogo"></a>

## Proposition (Möbius-support countermodel: the natural negative-sign candidate overshoots)

> *The signed Lambert identity $`\sum_{d\ge1}\mu(d)/(2^d-1) = 1/2`$ is exact. Writing $`N:=\{d:\mu(d)=-1\}`$: $`\sum_{d\in N}1/(2^d-1) = 1/2 + \sum_{d\in P}1/(2^d-1)`$ where $`P:=\{d\ge2:
> \mu(d)=1\}`$, and quantitatively $`1/2 + 1/63 \le \sum_{d\in N}1/(2^d-1)`$ (using the first positive tail term $`d=6`$, $`\mu(6)=1`$) ; the negative-Möbius support strictly *overshoots* $`1/2`$ by at least $`1/63`$. [`MobiusSignSupportNoGo.half_lt_tsum_negativeMobius`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MobiusSignSupportNoGo.lean#L164) (exact decomposition at [`MobiusSignSupportNoGo.tsum_negativeMobius_eq_half_add_positiveMobiusTail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MobiusSignSupportNoGo.lean#L111)).*
> 
> ***Scope.** Rules out exactly one natural candidate infinite Boolean support (the negative-Möbius set) as a witness for $`1/2\in\mathcal A`$. A route-sufficiency no-go only ; it says nothing about whether *some other* infinite Boolean support sums to $`1/2`$. *divisor counts and finite sums* **Object or representation:** about the *object* ; a genuine value inequality for one specific candidate set, not a coordinate artifact. Margin $`1/63`$ is the concrete number any repair attempt (adding/removing finitely many elements) must close or exceed. <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(fixed)</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_mobius_support_overshoots_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MobiusSignAndFiniteCertificates.lean#L70)

```lean
theorem paper_mobius_support_overshoots_half :
    (∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1)) = 1 / 2 ∧
      (∑' d : ℕ+, negativeMobiusTerm d)
        = 1 / 2 + ∑' d : ℕ+, positiveMobiusTailTerm d ∧
      (1 : ℝ) / 2 + 1 / 63 ≤ ∑' d : ℕ+, negativeMobiusTerm d ∧
      (1 : ℝ) / 2 < ∑' d : ℕ+, negativeMobiusTerm d
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_first_positiveMobius_tail_term`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MobiusSignAndFiniteCertificates.lean#L48)

```lean
theorem paper_first_positiveMobius_tail_term :
    (∀ d : ℕ+, (d : ℕ) < 6 → positiveMobiusTailTerm d = 0) ∧
      moebius 6 = 1 ∧
      positiveMobiusTailTerm (⟨6, by norm_num⟩ : ℕ+) = (1 : ℝ) / 63
```

<a id="prop-mobius-nogo-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_mobius_support_overshoots_half` | [E257_36/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L100) | [PaperStatementsAQ.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAQ.lean#L36) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_first_positiveMobius_tail_term` | [E257_36/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L94) | [PaperStatementsAQ.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAQ.lean#L31) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-boolsupport-and-onesided"></a>

## Proposition (Finite computation and half-membership)

> *No finite positive-index Boolean support has value exactly $`1/2`$: the reduced denominator of any finite Mersenne subset-sum is provably **odd** (each $`2^n-1`$ is odd), while $`1/2`$ needs an even denominator. [`finite_boolSupport_ne_half`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L589). Separately, $`\mathsf{CertifiedGreedyMersenneDeath}`$ is a finite-depth certificate of $`x\notin\mathcal A`$, obtained by decidable tests on rational input. For example, the supplied source excludes $`3/4`$ at level $`1`$ with lookahead $`0`$: [`three_fourths_certifiedGreedyMersenneDeath`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1778). Failure to find such a certificate at a given depth does not establish membership. It records survival of that finite test, not survival at every depth. [`Erdos249257.CertifiedGreedyMersenneDeath`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1756).*
> 
> ***Scope.** Any support representing $`1/2`$, if it exists, must be infinite. This follows from denominator parity, independently of the certificate search. The search supplies a different fact: a successful exclusion certificate proves nonmembership, whereas its absence in a bounded search does not prove membership or rationality. The same distinction must be checked separately for any other certificate family. *denominator parity; finite search* <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(fixed)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_support_and_onesided_certificate`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/MobiusSignAndFiniteCertificates.lean#L101)

```lean
theorem paper_finite_support_and_onesided_certificate :
    (∀ A : Set ℕ, A.Finite → 0 ∉ A → erdosSupportSeries 2 A ≠ (1 : ℝ) / 2) ∧
      (∀ F : Finset ℕ, 0 ∉ F → Odd (finiteErdosSum F 2).den) ∧
      (∀ n : ℕ, 1 ≤ n → Odd (2 ^ n - 1)) ∧
      ((1 : ℚ) / 2).den = 2 ∧ Even ((1 : ℚ) / 2).den ∧
      (∀ (x : ℚ) (level lookahead : ℕ),
        CertifiedGreedyMersenneDeath x level lookahead →
          ((x : ℚ) : ℝ) ∉ mersenneAchievementSet) ∧
      CertifiedGreedyMersenneDeath (3 / 4 : ℚ) 1 0 ∧
      (3 / 4 : ℝ) ∉ mersenneAchievementSet ∧
      (∀ A : Set ℕ, 0 ∉ A → erdosSupportSeries 2 A = (1 : ℝ) / 2 → A.Infinite)
```

<a id="prop-finite-boolsupport-and-onesided-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_finite_support_and_onesided_certificate` | [E257_36/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L150) | [PaperStatementsR.lean, line 24](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsR.lean#L24) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-carry-survivor-extinction"></a>

## Proposition (Period exclusion for the totient series)

> *For $`\sum_n\varphi(n)/2^n`$, the cited finite test proves that $`\mathrm{totientTail}(N+h)-\mathrm{totientTail}(N)`$ is not an integer by excluding every possible integer state in a bounded range within finitely many steps. If the series were rational, some positive period $`h_0`$ would make these tail differences integral for every sufficiently large $`N`$. Telescoping would then give integrality also for every positive multiple $`mh_0`$.*
> 
> *Consequently, the required certificate supply is: for every $`h_0\ge1`$ and every lower bound $`N_0`$, there exist $`m\ge1`$, $`N\ge N_0`$ and a finite test length $`K`$ excluding integrality for $`(mh_0,N)`$. The unbounded choice of $`N`$ is essential; a counterexample before the unknown eventual threshold does not exclude an eventual period. [`Erdos257PeriodNoncollapse.irrational_totient_series_of_multiple_survivor_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L491). It is sufficient instead to obtain such certificates for $`h=\mathrm{lcm}(1,\ldots,t)`$ with both $`t`$ and $`N`$ exceeding arbitrary prescribed lower bounds: [`Erdos257PeriodNoncollapse.irrational_totient_series_of_lcm_survivor_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L540). The supplied finite theorem excludes the tail differences for $`1\le h\le16`$ at $`(N,L)=(14,9)`$, and hence excludes rational values whose reduced denominator divides $`2^{14}(2^h-1)`$ for one of those $`h`$. It does not establish the unbounded certificate supply. [`Erdos257PeriodNoncollapse.totient_series_ne_rat_of_den_dvd_upto_sixteen`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L587).*
> 
> ***Scope.** The declarations in <span class="sans-serif">CarrySurvivorExtinction.lean</span>, <span class="sans-serif">AdjacentCarryTube.lean</span>, <span class="sans-serif">AdjacentPhaseSeparation.lean</span> and <span class="sans-serif">TotientCarryKernelRigidity.lean</span> used in this comparison concern the totient series of Problem 249. Their carry recurrences may suggest constructions for Problem 257, but applying them there requires a new argument for the divisor transform of its chosen support. The totient-specific theorems do not supply that argument. *integer carries; totient series* <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(cofinal)</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_carry_survivor_extinction`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TotientPeriodCertificateSupply.lean#L40)

```lean
theorem paper_carry_survivor_extinction :
    (∀ h N K : ℕ, survivorKill h N K →
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) ∧
      (¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) →
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
          totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ h N₀ : ℕ,
        (∀ N, N₀ ≤ N →
            totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) →
          ∀ m N : ℕ, N₀ ≤ N →
            totientTail (N + m * h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      ((∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
          ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ K, survivorKill (m * h₀) N K) →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      ((∀ t₀ N₀ : ℕ,
          ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ K, survivorKill (periodLcm t) N K) →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9) ∧
      (∀ h : ℕ, 1 ≤ h → h ≤ 16 →
        totientTail (14 + h) - totientTail 14 ∉ Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 16 →
        (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1) →
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ))
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_periodLcm_is_prefix_lcm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/TotientPeriodCertificateSupply.lean#L23)

```lean
theorem paper_periodLcm_is_prefix_lcm (t : ℕ) :
    0 < periodLcm t ∧ ∀ h : ℕ, 1 ≤ h → h ≤ t → h ∣ periodLcm t
```

<a id="prop-carry-survivor-extinction-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_carry_survivor_extinction` | [E257_36/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L194) | [PaperStatementsP.lean, line 18](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsP.lean#L18) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_periodLcm_is_prefix_lcm` | [E257_36/Challenge.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L219) | [PaperStatementsP.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsP.lean#L44) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-scalar-localization"></a>

## Lemma (Denominator complement survives scaling)

> *For $`x:\mathbb Q`$, $`c:\mathbb Z`$, $`H:\mathbb N`$: if $`H\mid x.\mathrm{den}`$ and $`(c\cdot x).\mathrm{den}\mid H`$ ; i.e. multiplying by the integer $`c`$ shrinks the displayed denominator down *into* $`H`$ ; then the **complementary** denominator factor $`x.\mathrm{den}/H`$ divides $`c`$:
> ``` math
> H\mid x.\mathrm{den} \ \land\ (c\cdot x).\mathrm{den}\mid H \implies x.\mathrm{den}/H \mid |c|.
> ```
> [`Erdos249257.AdelicHeightObstruction.scalarLocalization_complement_dvd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/AdelicHeightObstruction.lean#L23). Equivalently, writing $`D=x.\mathrm{den}/H`$, we have $`D\mid c`$, so $`t=c/D`$ is an integer and $`Hcx=t\,x.\mathrm{num}`$. Here $`H>0`$ follows from $`H\mid x.\mathrm{den}`$, since the reduced denominator is positive. [`Erdos249257.AdelicHeightObstruction.scalarLocalization_integer_eq_mul_num`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/AdelicHeightObstruction.lean#L56).*
> 
> ***Scope.** This is elementary rational arithmetic, independent of the problem. If $`c\ne0`$, divisibility gives the size bound $`|c|\ge x.\mathrm{den}/H`$. The nonzero condition is essential: $`c=0`$ clears every denominator and satisfies the divisibility conclusion without any positive lower bound on $`|c|`$. The lemma therefore constrains denominator clearing by a nonzero bounded multiplier, not arbitrary multiplication. *rational-denominator; height* **Object or representation:** about a *representation* ; pure denominator bookkeeping for $`\mathbb Q`$, with zero problem-specific content; the upstream primitive ([`Erdos249257.RationalDenominatorSurvival.divisor_dvd_divInt_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalDenominatorSurvival.lean#L17)) is the domain-neutral extraction this lemma builds on. <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ScalarLocalisationHeightObstruction.lean#L29)

```lean
theorem paper_scalar_localization (x : ℚ) (c : ℤ) {H : ℕ}
    (hH : H ∣ x.den) (hscaled : ((c : ℚ) * x).den ∣ H) :
    0 < H ∧ x.den / H ∣ c.natAbs ∧ ((x.den / H : ℕ) : ℤ) ∣ c ∧
      (H : ℚ) * (c : ℚ) * x
        = ((c / ((x.den / H : ℕ) : ℤ) : ℤ) : ℚ) * (x.num : ℚ)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization_size_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ScalarLocalisationHeightObstruction.lean#L53)

```lean
theorem paper_scalar_localization_size_bound (x : ℚ) {c : ℤ} {H : ℕ}
    (hH : H ∣ x.den) (hscaled : ((c : ℚ) * x).den ∣ H) (hc : c ≠ 0) :
    x.den / H ≤ c.natAbs
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization_zero_degenerate`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ScalarLocalisationHeightObstruction.lean#L62)

```lean
theorem paper_scalar_localization_zero_degenerate (x : ℚ) (H : ℕ) :
    (((0 : ℤ) : ℚ) * x).den = 1 ∧ x.den / H ∣ (0 : ℤ).natAbs ∧
      (0 : ℤ).natAbs = 0
```

<a id="lem-scalar-localization-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_scalar_localization` | [E257_36/Challenge.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L233) | [PaperStatementsAA.lean, line 266](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAA.lean#L266) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_scalar_localization_size_bound` | [E257_36/Challenge.lean, line 240](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L240) | [PaperStatementsAA.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAA.lean#L272) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_scalar_localization_zero_degenerate` | [E257_36/Challenge.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L245) | [PaperStatementsAA.lean, line 276](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAA.lean#L276) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-mersenne-height"></a>

## Corollary (Mersenne specialisation)

> *Let $`x`$ be a positive rational number and let $`r\ge0`$, $`n\ge1`$ be integers. If $`2^r\mid x.\mathrm{num}.\mathrm{natAbs}`$ and $`x<2/(2^n-1)`$, then $`2^r\cdot(2^n-1) < 2\cdot x.\mathrm{den}`$ ; a numerator $`2`$-power lower bound plus a Mersenne-scale upper bound on $`x`$ together force a denominator lower bound, *without* introducing a global prefix LCM. [`Erdos249257.AdelicHeightObstruction.positiveRat_mersenne_height`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/AdelicHeightObstruction.lean#L103) (generic form [`Erdos249257.AdelicHeightObstruction.positiveRat_numDivisor_mul_lt_two_mul_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/AdelicHeightObstruction.lean#L77)). To see the inequality directly, write $`x=a/b`$ in lowest terms with $`a,b>0`$. The hypotheses give $`a\ge2^r`$ and $`a(2^n-1)<2b`$. The conclusion follows by substitution. An application of Lemma <a href="#lem:scalar-localization" data-reference-type="ref" data-reference="lem:scalar-localization">265</a> must in addition supply its denominator-divisibility assumptions. *rational-denominator; height, Mersenne instance* <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_height`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ScalarLocalisationHeightObstruction.lean#L77)

```lean
theorem paper_mersenne_height (x : ℚ) {r n : ℕ} (hx : 0 < x) (hn : 1 ≤ n)
    (hpow : 2 ^ r ∣ x.num.natAbs) (hlt : x < (2 : ℚ) / ((2 ^ n - 1 : ℕ) : ℚ)) :
    2 ^ r ≤ x.num.natAbs ∧
      x.num.natAbs * (2 ^ n - 1) < 2 * x.den ∧
      2 ^ r * (2 ^ n - 1) < 2 * x.den
```

<a id="cor-mersenne-height-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_mersenne_height` | [E257_36/Challenge.lean, line 226](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L226) | [PaperStatementsAA.lean, line 208](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAA.lean#L208) | [E257_36](../evidence/comparator/replay-35882032091/receipt-E257_36.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-critical-band-index"></a>

## Proposition (Quantifier collapse: one critical index suffices, not $`d{+}1`$)

> *Let $`d,E\in\mathbb N`$ and assume $`E\le2^{d+1}`$. Then the purely combinatorial statement $`\mathsf{DyadicBandEscape}(d,E) \iff \exists j,\ \mathsf{CriticalDyadicBandIndex}(d,E,j)\land
> E+2(d+j)\le 2^{d-j+1}`$ collapses the $`\forall j\in[0,d]`$ band-avoidance condition (formally $`d{+}1`$ separate inequalities) to checking exactly *one* nearest-boundary index $`j`$. The range assumption ensures that a dyadic threshold lies at or above $`E`$. Choose the smallest such threshold: smaller thresholds are already below $`E`$, while larger thresholds have narrower forbidden bands. Without the range assumption all bands escape automatically when $`E>2^{d+1}`$, but no critical index exists; $`(d,E)=(0,3)`$ is the smallest example. Specialised to the concrete seam reset charge, $`\mathsf{SeamUpperResetCriticalBandEscape}`$ is proved logically *equivalent* to Definition <a href="#defn:band-escape" data-reference-type="ref" data-reference="defn:band-escape">267</a>’s hypothesis. [`Erdos249257.dyadicBandEscape_iff_exists_critical`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L108) (seam specialisation [`Erdos249257.seamUpperResetCriticalBandEscape_iff`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L883)). Zero Mersenne/seam content in the core lemma ; pure $`(d,E,j)`$ arithmetic over powers of 2. *dyadic-boundary, generic* <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_band_index_collapse`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/CriticalDyadicBandCollapse.lean#L20)

```lean
theorem paper_critical_band_index_collapse :
    (∀ d E : ℕ, DyadicBandEscape d E ↔
        ∀ j : ℕ, j ≤ d →
          2 ^ (d - j + 1) < E ∨ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)) ∧
      (∀ d E : ℕ, E ≤ 2 ^ (d + 1) →
        (DyadicBandEscape d E ↔ ∃ j : ℕ, CriticalDyadicBandIndex d E j ∧
          E + 2 * (d + j) ≤ 2 ^ (d - j + 1))) ∧
      (∀ d E : ℕ, E ≤ 2 ^ (d + 1) → ∃ j : ℕ, CriticalDyadicBandIndex d E j) ∧
      (∀ d E : ℕ, 2 ^ (d + 1) < E → DyadicBandEscape d E) ∧
      (∀ d E : ℕ, 2 ^ (d + 1) < E → ¬ ∃ j : ℕ, CriticalDyadicBandIndex d E j) ∧
      (2 ^ (0 + 1) < 3 ∧ ∀ d E : ℕ, 2 ^ (d + 1) < E → 0 ≤ d ∧ 3 ≤ E) ∧
      (SeamUpperResetCriticalBandEscape ↔ SeamUpperResetDyadicBandEscape)
```

<a id="prop-critical-band-index-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-odometer"></a>

## Lemma (Divisor-residue form of the short-window phase)

> *For all $`M,L\ge 1`$,
> ``` math
> \Theta_L(M)\ =\ \sum_{d\ge 2}\ \sum_{\substack{1\le i\le L\\ i\,\equiv\,-M\ (\mathrm{mod}\ d)}} 2^{-i}
> \ =\ \sum_{d\ge 2}\ 2^{-i_d(M)}\cdot\frac{1-2^{-d\,m_d}}{1-2^{-d}},
> ```
> where $`i_d(M)\in[1,d]`$ is the least $`i\ge1`$ with $`d\mid M+i`$ (so $`i_d(M)`$ depends only on $`M \bmod d`$), $`m_d := \#\{1\le i\le L: d\mid M+i\}`$, and terms with $`i_d(M)>L`$ are empty. In particular, for every integer $`D\ge M+L`$,
> ``` math
> \Theta_L(M)\ =\ \sum_{d=2}^{D}\ \sum_{i=1}^{L} 2^{-i}\,\mathbf 1_{d\mid M+i},
> ```
> and the right-hand side, with an arbitrary integer $`x\ge0`$ in place of $`M`$, depends on $`x`$ only through its residues modulo the integers $`d`$ with $`2\le d\le D`$. The cutoff $`D`$ has to be fixed before the argument varies: at $`(M,L)=(1,1)`$ the cutoff is $`M+L=2`$, the integers $`1`$ and $`3`$ have the same residue modulo every $`d`$ with $`2\le d\le 2`$, and yet $`\Theta_1(1)=1/2`$ while $`\Theta_1(3)=1`$.*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_tsum_divisorResidue`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L417)

```lean
theorem theta_eq_tsum_divisorResidue (M L : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L) :
    Theta L M
      = ∑' d : ℕ,
          ∑ i ∈ (Finset.Icc 1 L).filter (fun i => (d + 2) ∣ M + i), (1 / 2 : ℚ) ^ i
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_tsum_geometricForm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L442)

```lean
theorem theta_eq_tsum_geometricForm (M L : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) :
    Theta L M
      = ∑' d : ℕ,
          (1 / 2 : ℚ) ^ (iLeast (d + 2) M)
            * (1 - (1 / 2 : ℚ) ^ ((d + 2) * mCount (d + 2) M L))
            / (1 - (1 / 2 : ℚ) ^ (d + 2))
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_divisorResidueSum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L368)

```lean
theorem theta_eq_divisorResidueSum (M L D : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (hD : M + L ≤ D) :
    Theta L M
      = ∑ d ∈ Finset.Icc 2 D,
          ∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ M + i), (1 / 2 : ℚ) ^ i
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_geometricForm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L378)

```lean
theorem theta_eq_geometricForm (M L D : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (hD : M + L ≤ D) :
    Theta L M
      = ∑ d ∈ Finset.Icc 2 D,
          (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
            / (1 - (1 / 2 : ℚ) ^ d)
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.residue_condition_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L116)

```lean
theorem residue_condition_iff (d M i : ℕ) :
    ((i : ℤ) ≡ -(M : ℤ) [ZMOD (d : ℤ)]) ↔ d ∣ M + i
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.card_divisors_sub_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L303)

```lean
theorem card_divisors_sub_one (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card - 1 : ℕ) = (n.divisors.filter (fun d => 2 ≤ d)).card
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast_mem_Icc`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L132)

```lean
theorem iLeast_mem_Icc (d M : ℕ) (hd : 1 ≤ d) : 1 ≤ iLeast d M ∧ iLeast d M ≤ d
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.dvd_add_iLeast`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L138)

```lean
theorem dvd_add_iLeast (d M : ℕ) (hd : 1 ≤ d) : d ∣ M + iLeast d M
```

9. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.not_dvd_of_lt_iLeast`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L147)

```lean
theorem not_dvd_of_lt_iLeast (d M i : ℕ) (hd : 1 ≤ d) (hi : 1 ≤ i)
    (hlt : i < iLeast d M) : ¬ d ∣ M + i
```

10. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast_congr`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L160)

```lean
theorem iLeast_congr (d M M' : ℕ) (h : M % d = M' % d) : iLeast d M = iLeast d M'
```

11. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.mCount_eq_zero_of_lt_iLeast`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L278)

```lean
theorem mCount_eq_zero_of_lt_iLeast (d M L : ℕ) (hd : 1 ≤ d) (h : L < iLeast d M) :
    mCount d M L = 0
```

12. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.geometric_term_eq_zero_of_lt_iLeast`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L293)

```lean
theorem geometric_term_eq_zero_of_lt_iLeast (d M L : ℕ) (hd : 1 ≤ d)
    (h : L < iLeast d M) :
    (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
        / (1 - (1 / 2 : ℚ) ^ d) = 0
```

13. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_Psi`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L339)

```lean
theorem theta_eq_Psi (M L D : ℕ) (hM : 1 ≤ M) (hD : M + L ≤ D) :
    Theta L M = Psi L D M
```

14. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.Psi_eq_of_residues_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L467)

```lean
theorem Psi_eq_of_residues_eq (L D x y : ℕ) (h : ∀ d ∈ Finset.Icc 2 D, x % d = y % d) :
    Psi L D x = Psi L D y
```

15. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_one_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L523)

```lean
theorem theta_one_one : Theta 1 1 = 1 / 2
```

16. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_one_three`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L528)

```lean
theorem theta_one_three : Theta 1 3 = 1
```

17. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.residue_cutoff_reading_fails`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L538)

```lean
theorem residue_cutoff_reading_fails :
    (∀ d ∈ Finset.Icc 2 (1 + 1), (1 : ℕ) % d = 3 % d) ∧ Theta 1 1 ≠ Theta 1 3
```

<a id="lem-odometer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `theta_eq_tsum_divisorResidue` | [E257_37/Challenge.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L103) | [PaperStatementsAA.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L140) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `theta_eq_tsum_geometricForm` | [E257_37/Challenge.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L109) | [PaperStatementsAA.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L145) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `theta_eq_divisorResidueSum` | [E257_37/Challenge.lean, line 88](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L88) | [PaperStatementsAA.lean, line 127](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L127) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `theta_eq_geometricForm` | [E257_37/Challenge.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L95) | [PaperStatementsAA.lean, line 133](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L133) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `residue_condition_iff` | [E257_37/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L76) | [PaperStatementsAA.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L118) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `card_divisors_sub_one` | [E257_37/Challenge.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L49) | [PaperStatementsAA.lean, line 98](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L98) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `iLeast_mem_Icc` | [E257_37/Challenge.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L65) | [PaperStatementsAA.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L110) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `dvd_add_iLeast` | [E257_37/Challenge.lean, line 53](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L53) | [PaperStatementsAA.lean, line 101](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L101) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `not_dvd_of_lt_iLeast` | [E257_37/Challenge.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L72) | [PaperStatementsAA.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L115) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `iLeast_congr` | [E257_37/Challenge.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L62) | [PaperStatementsAA.lean, line 108](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L108) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `mCount_eq_zero_of_lt_iLeast` | [E257_37/Challenge.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L68) | [PaperStatementsAA.lean, line 112](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L112) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `geometric_term_eq_zero_of_lt_iLeast` | [E257_37/Challenge.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L56) | [PaperStatementsAA.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L103) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `theta_eq_Psi` | [E257_37/Challenge.lean, line 84](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L84) | [PaperStatementsAA.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L124) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `Psi_eq_of_residues_eq` | [E257_37/Challenge.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L45) | [PaperStatementsAA.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L95) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `theta_one_one` | [E257_37/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L117) | [PaperStatementsAA.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L152) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `theta_one_three` | [E257_37/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L120) | [PaperStatementsAA.lean, line 154](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L154) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `residue_cutoff_reading_fails` | [E257_37/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L80) | [PaperStatementsAA.lean, line 121](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsAA.lean#L121) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-sqwitness"></a>

## Lemma (The terminal bound at square depths)

> *Let $`A\subseteq\mathbb{N}`$ with $`1\notin A`$ and $`X_{A}(2)=1/2`$. Then for every $`k\ge1`$,
> ``` math
> \bigl(\ensuremath{\operatorname{ihc}}\ A\ (k^{2}-1)\ :\ \mathbb{R}\bigr)
> \ =\ \mathtt{binaryCoeffTail}\ (c_{A})\ (k^{2})
> \ \le\ 2k+4\ =\ \ensuremath{B}\ (k^{2}).
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_square_depth_terminal_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquareDepthAndHalfMembershipEquivalences.lean#L27)

```lean
theorem paper_square_depth_terminal_bound (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2) (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k ^ 2 - 1) : ℝ) = binaryCoeffTail (supportCoeff A) (k ^ 2) ∧
      binaryCoeffTail (supportCoeff A) (k ^ 2) ≤ 2 * (k : ℝ) + 4 ∧
      (halfStripBound (k ^ 2) : ℝ) = 2 * (k : ℝ) + 4
```

2. [`ErdosProblems.Erdos257.PaperCompleteR20.square_depth_witness`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR20/CarryCollapseCorrespondence.lean#L8)

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
| `paper_square_depth_terminal_bound` | [E257_37/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L146) | [PaperStatementsL.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsL.lean#L52) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |
| `square_depth_witness` | [E257_03/Challenge.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L136) | [PaperStatementsL.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsL.lean#L28) | [E257_03](../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-squarefree"></a>

## Proposition (Squarefree support: exact engine ceiling, not an open value)

> *Let $`A=\{n\ge2:n\text{ is squarefree}\}`$. Then
> ``` math
> c_{A}(n)=2^{\omega(n)}-1,
> ```
> which is odd for every $`n\ge2`$. Consequently neither the digitwise nor the carry-aware divisibility-first block-certificate schema has an instance at any even base. The two exact no-go theorems are [`ErdosProblems.Erdos257.SquarefreeSupportIncidence.not_exists_carry_certificates_squarefreeSupport`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L274) and [`ErdosProblems.Erdos257.SquarefreeSupportIncidence.not_exists_digitwise_certificates_squarefreeSupport`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos257/SquarefreeSupportIncidence.lean#L292).*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_squarefree_support_engine_ceiling`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquarefreeSupportEngineCeiling.lean#L20)

```lean
theorem paper_squarefree_support_engine_ceiling :
    (squarefreeSupport = {d : ℕ | 2 ≤ d ∧ Squarefree d}) ∧
      (∀ n : ℕ, n ≠ 0 →
        Erdos249257.supportCoeff squarefreeSupport n
          = 2 ^ n.primeFactors.card - 1) ∧
      (∀ n : ℕ, 2 ≤ n → Odd (Erdos249257.supportCoeff squarefreeSupport n)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
              Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (K - r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < Erdos249257.supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (∀ r ∈ Finset.Icc 1 K,
              b ^ r ∣ Erdos249257.supportCoeff squarefreeSupport (N + r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < Erdos249257.supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L))
```

<a id="prop-squarefree-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_squarefree_support_engine_ceiling` | [E257_37/Challenge.lean, line 162](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_37/Challenge.lean#L162) | [PaperStatementsBF.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_37/PaperStatementsBF.lean#L21) | [E257_37](../evidence/comparator/replay-35882032091/receipt-E257_37.json) |

Challenge for `paper_squarefree_support_engine_ceiling`:

```lean
theorem paper_squarefree_support_engine_ceiling :
    (squarefreeSupport = {d : ℕ | 2 ≤ d ∧ Squarefree d}) ∧
      (∀ n : ℕ, n ≠ 0 →
        supportCoeff squarefreeSupport n
          = 2 ^ n.primeFactors.card - 1) ∧
      (∀ n : ℕ, 2 ≤ n → Odd (supportCoeff squarefreeSupport n)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
              supportCoeff squarefreeSupport (N + r) * b ^ (K - r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (∀ r ∈ Finset.Icc 1 K,
              b ^ r ∣ supportCoeff squarefreeSupport (N + r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) := by sorry
```

<a id="prop-cpgs-equiv"></a>

## Proposition (Infinitely many positive skips are equivalent to half-membership)

> *Define
> ``` math
> \mathrm{CPGS}\ :=\ \forall N,\ \exists c\ge N,\ c\ \text{skipped by the rational half-greedy
> orbit}\ \wedge\ 0<\ensuremath{r}(1/2)(c-1)
> ```
> ([`CofinalPositiveHalfGreedySkips`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L22)). The positivity conjunct is unconditionally true for every skipped $`c`$ ([`localMersennePrefixValue_halfGreedy_lt_half`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L138), <span class="sans-serif">\[Lean\]</span>, <span class="sans-serif">(uniform)</span>; an odd-denominator parity fact), hence deletable without changing the Prop’s meaning. What survives, $`\forall N\,\exists c\ge N`$ skipped, is exactly $`(\mathtt{greedyMersenneSkippedSupport}(1/2)).\mathrm{Infinite}`$, so
> ``` math
> \mathrm{CPGS}\ \Longleftrightarrow\ \mathrm{HALF}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_cpgs_equiv`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquareDepthAndHalfMembershipEquivalences.lean#L44)

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
| `paper_cpgs_equiv` | [E257_38/Challenge.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L139) | [PaperStatementsN.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsN.lean#L99) | [E257_38](../evidence/comparator/replay-35882032091/receipt-E257_38.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-strip-equiv"></a>

## Proposition (Terminal carry bounds are equivalent to half-membership)

> *Consider finite sets $`D\subseteq\{2,\ldots,M\}`$ at arbitrarily large depths $`M`$ with
> ``` math
> |\operatorname{ihc}(D,M-1)|\le2\lfloor\sqrt M\rfloor+4.
> ```
> This is the exact terminal-strip condition in [`HalfCarryCofinalTerminalOnlyStrip`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TerminalOnlyCofinal.lean#L34). It is equivalent to $`1/2\in\mathcal A`$: the forward direction follows from the displayed finite-approximation estimate; for the converse, truncate an achieving support at $`M=k^2`$ and apply Lemma <a href="#lem:sqrt-witness" data-reference-type="ref" data-reference="lem:sqrt-witness">17</a>. Thus constant $`4`$ already suffices at cofinally many depths. The relaxed constant $`6`$ gives a bound at every depth, using $`\sqrt M\le\lfloor\sqrt M\rfloor+1`$, but that relaxation is not needed for the cofinal statement.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_equiv`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquareDepthAndHalfMembershipEquivalences.lean#L130)

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

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_relaxed_constant_six_every_depth`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquareDepthAndHalfMembershipEquivalences.lean#L112)

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
| `paper_terminal_strip_equiv` | [E257_38/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L159) | [PaperStatementsN.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsN.lean#L227) | [E257_38](../evidence/comparator/replay-35882032091/receipt-E257_38.json) |
| `paper_relaxed_constant_six_every_depth` | [E257_38/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L180) | [PaperStatementsL.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsL.lean#L51) | [E257_38](../evidence/comparator/replay-35882032091/receipt-E257_38.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-257-logarithmic-counterexample"></a>

## Theorem (arithmetic logarithmic counterexample)

> *For every integer $`H\ge2`$ and every real $`A_0\ge0`$, there are a squarefree positive integer $`L`$ and a finite nonempty set $`F`$ of distinct squarefree positive integers such that
> ``` math
> \min F>\max\{L,A_0\},\qquad
>  \kappa_1(F;1)\le\frac{30\log2}{H},\qquad
>  \mathbb P_L(U_F>1)\ge1-e^{-1}.
> ```
> For these $`F,L`$, some $`R\ge0`$ satisfies $`\mathscr D_{L;R,L}\mathbf1_{\{U_F>1\}}>1/2`$. Consequently, no absolute constant $`C`$ satisfies
> ``` math
> \begin{equation*}
>  \mathscr D_{L;R,M}\mathbf1_{\{U_F>t\}}
>  \le C(1+L/M)\kappa_1(F;t)
>  \tag{E}
> \end{equation*}
> ```
> uniformly in finite $`F`$, positive integers $`L,M`$, integers $`R\ge0`$, and $`0<t\le1`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.arithmetic_logarithmic_counterexample`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCounterexampleAssembly.lean#L1645)

```lean
theorem arithmetic_logarithmic_counterexample (H : ℕ) (hH : 2 ≤ H) (A₀ : ℝ) (hA₀ : 0 ≤ A₀) :
    ∃ (L : ℕ) (F : Finset ℕ),
      0 < L ∧ Squarefree L ∧ F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      (∀ a ∈ F, 0 < a ∧ Squarefree a) ∧
      (∀ a ∈ F, max (L : ℝ) A₀ < (a : ℝ)) ∧
      L ∣ F.lcm id ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ) ∧
      1 - Real.exp (-1) ≤ condExceedProb F L ∧
      ∃ R : ℕ, 1 / 2 < dyadicMean L R L (exceedInd F)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.no_absolute_dyadic_kappaOne_constant`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCounterexampleAssembly.lean#L1859)

```lean
theorem no_absolute_dyadic_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ (F : Finset ℕ), F.Nonempty → (0 : ℕ) ∉ F →
      ∀ (L M : ℕ), 0 < L → 0 < M → ∀ (R : ℕ) (t : ℝ), 0 < t → t ≤ 1 →
        dyadicMean L R M (fun N => if t < framePotential F N then (1 : ℝ) else 0)
          ≤ C * (1 + (L : ℝ) / (M : ℝ)) * kappaOne F t
```

<a id="thm-257-logarithmic-counterexample-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `arithmetic_logarithmic_counterexample` | [E257_38/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L194) | [PaperStatementsAC.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsAC.lean#L42) | [E257_38](../evidence/comparator/replay-35882032091/receipt-E257_38.json) |
| `no_absolute_dyadic_kappaOne_constant` | [E257_38/Challenge.lean, line 211](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L211) | [PaperStatementsAC.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsAC.lean#L58) | [E257_38](../evidence/comparator/replay-35882032091/receipt-E257_38.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-257-logarithmic-separation"></a>

## Corollary (finite-functional separation)

> *For every finite nonempty $`F`$, with $`Q=\operatorname{lcm}(F)`$,
> ``` math
> \begin{equation}
>  K_*(F)\ge\max_{\ell\mid Q}
>    \mathbb P\bigl(U_F(N)>1\mid\ell\mid N\bigr),
>  \label{eq:257-arithmetic-cover-lower}
> \end{equation}
> ```
> where $`N`$ is uniform modulo $`Q`$. The supports of Theorem <a href="#thm:257-logarithmic-counterexample" data-reference-type="ref" data-reference="thm:257-logarithmic-counterexample">285</a> satisfy $`K_*(F)\ge1-e^{-1}`$ and $`\kappa_1(F;1)\le30\log2/H`$. In particular, no absolute $`C`$ gives $`K_*(F)\le C\kappa_1(F;1)`$ for all finite nonempty $`F`$, even after all covering sets, exponents, coefficients and positive weights have been optimised.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.sup_condExceedProb_le_paperCoverCost`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCoverLowerBoundPaperForm.lean#L40)

```lean
theorem sup_condExceedProb_le_paperCoverCost (F : Finset ℕ) (hF : 0 ∉ F)
    (hne : (F.lcm id).divisors.Nonempty) :
    (F.lcm id).divisors.sup' hne (fun ℓ => condExceedProb F ℓ)
      ≤ paperCoverCost (F : Set ℕ)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.exists_support_paperCoverCost_ge`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCounterexampleAssembly.lean#L1900)

```lean
theorem exists_support_paperCoverCost_ge (H : ℕ) (hH : 2 ≤ H) :
    ∃ F : Finset ℕ, F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      1 - Real.exp (-1) ≤ paperCoverCost (F : Set ℕ) ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.no_absolute_paperCoverCost_kappaOne_constant`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCounterexampleAssembly.lean#L1912)

```lean
theorem no_absolute_paperCoverCost_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ F : Finset ℕ, F.Nonempty → (0 : ℕ) ∉ F →
      paperCoverCost (F : Set ℕ) ≤ C * kappaOne F 1
```

<a id="cor-257-logarithmic-separation-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `sup_condExceedProb_le_paperCoverCost` | [E257_38/Challenge.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L283) | [PaperStructuresBS.lean, line 208](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStructuresBS.lean#L208) | [E257_38](../evidence/comparator/replay-35882032091/receipt-E257_38.json) |
| `exists_support_paperCoverCost_ge` | [E257_38/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L272) | [PaperStructuresBS.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStructuresBS.lean#L195) | [E257_38](../evidence/comparator/replay-35882032091/receipt-E257_38.json) |
| `no_absolute_paperCoverCost_kappaOne_constant` | [E257_38/Challenge.lean, line 278](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L278) | [PaperStructuresBS.lean, line 202](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStructuresBS.lean#L202) | [E257_38](../evidence/comparator/replay-35882032091/receipt-E257_38.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-257-logarithmic-initial-interval"></a>

## Proposition (ordinary initial intervals)

> *For every finite nonempty $`F`$, integer $`X\ge1`$, and $`0<t\le1`$,
> ``` math
> \frac1X\#\{1\le N\le X:U_F(N)>t\}
>  \le\frac{2}{\log(4/3)}\kappa_1(F;t).
> ```*

The Lean declaration below states a result at least as strong as this one.

[`ErdosProblems.Erdos257.PaperCompleteR21.logarithmic_initial_interval`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos257/PaperCompleteR21/LogarithmicInitialInterval.lean#L491)

```lean
theorem logarithmic_initial_interval (F : Finset ℕ) (hFne : F.Nonempty) (hF : 0 ∉ F)
    (X : ℕ) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ)) / (X : ℝ)
      ≤ 2 / Real.log (4 / 3 : ℝ) * kappaOne F t
```

<a id="prop-257-logarithmic-initial-interval-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `logarithmic_initial_interval` | [E257_38/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L205) | [PaperStatementsAC.lean, line 53](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsAC.lean#L53) | [E257_38](../evidence/comparator/replay-35882032091/receipt-E257_38.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
