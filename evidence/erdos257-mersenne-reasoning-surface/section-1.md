# Formal evidence: Reciprocal Mersenne Subseries, Section 1

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="thm-257-weighted"></a>

## Theorem 1.1 (A weighted summability criterion), page 8

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

The Lean declarations below together state this result or one that implies it. The first conjunct of the Lean claim and the displacement statement are the printed irrationality of $X_A(b)$ and the cofinal returns $0<\Delta_{b,A}(m)<\varepsilon$; the Lean claim adds a second conjunct, that if a set $H\subseteq\mathbb N_{>0}$ has finite weighted mass at $b=2$, then $X_A(b)$ is irrational for every $b\ge2$ and every infinite $A\subseteq H$.

1. [`ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L120)

```lean
theorem divisibilityWeightedClaim : DivisibilityWeightedClaim
```

where [`DivisibilityWeightedClaim`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean#L61) is

```lean
def DivisibilityWeightedClaim : Prop :=
  (∀ (b : ℕ) (A : Set ℕ), 2 ≤ b → 0 ∉ A → A.Infinite →
    FinitePrimeWeighted b A → Irrational (erdosSupportSeries b A)) ∧
  (∀ H : Set ℕ, 0 ∉ H → FinitePrimeWeighted 2 H →
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A))
```

2. [`ErdosProblems.Erdos257.PaperCompleteR8.weighted_displacement_cofinal_close_return`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L100)

```lean
theorem weighted_displacement_cofinal_close_return
    (b : ℕ) (E : Set ℕ) (hb : 2 ≤ b) (hE0 : 0 ∉ E)
    (hE : FinitePrimeWeighted b E) (hInf : E.Infinite)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < displacement b E m ∧ displacement b E m < ε
```

<a id="thm-257-weighted-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `divisibilityWeightedClaim`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L76) (E257_01, line 76), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/DivisibilityWeightedSupport.lean#L42) (DivisibilityWeightedSupport.lean, line 42), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)
- `weighted_displacement_cofinal_close_return`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L96) (E257_01, line 96), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/WeightedCloseReturn.lean#L19) (WeightedCloseReturn.lean, line 19), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-257-variable-fractional-cover"></a>

## Theorem 1.2 (A summable family of divisor majorants), page 14

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

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one, with $F_j\subseteq\Npos$ written as $0\notin F_j$ and the index $j\ge1$ shifted to start at $0$. Lean assumes each $C_j$ finite, which the printed summability hypothesis already implies.

[`ErdosProblems.Erdos257.PaperCompleteR8.strengthenedPositiveCoverClaim`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR8/PositiveCoverReturn.lean#L241)

```lean
theorem strengthenedPositiveCoverClaim : StrengthenedPositiveCoverClaim
```

where [`StrengthenedPositiveCoverClaim`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean#L53) is

```lean
def StrengthenedPositiveCoverClaim : Prop :=
  ∀ C : PositiveCoverData, C.StrengthenedCostSummable →
    ∀ A : Set ℕ, A ⊆ C.host → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
```

<a id="thm-257-variable-fractional-cover-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `strengthenedPositiveCoverClaim`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L113) (E257_01, line 113), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/VariableExponentCover.lean#L86) (VariableExponentCover.lean, line 86), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-257-mixed-supports"></a>

## Theorem 1.3 (mixed weighted and cover supports), page 15

> *Let $`E,V\subseteq\mathbb{N}_{>0}`$. Suppose $`E`$ has finite weighted mass (1) at $`b=2`$ for a finite nonempty prime set $`\mathcal P`$. Suppose also that $`V\subseteq\bigcup_jF_j`$ for sets and majorants satisfying Theorem 1.2, with (13) or its positive-weight variant. Then $`X_A(b)`$ is irrational for every infinite $`A\subseteq E\cup V`$ and every integer $`b\ge2`$.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusion as the printed theorem, with $E\subseteq\Npos$ written as $0\notin E$. A cover satisfying the summability condition of the cover theorem, with its index $j\ge1$ shifted to start at $0$, is `mixedSupportClaim`; the positive-weight variant, with weights $\eta_j>0$, $\sum_j\eta_j=1$ and $\sum_jC_j\eta_j^{-\alpha_j}/(2^{\alpha_j}-1)<\infty$, is `arbitraryWeightMixedSupport_allBase_hereditary`.

1. [`ErdosProblems.Erdos257.PaperCompleteR8.mixedSupportClaim`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L126)

```lean
theorem mixedSupportClaim : MixedSupportClaim
```

where [`MixedSupportClaim`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean#L71) is

```lean
def MixedSupportClaim : Prop :=
  ∀ E V : Set ℕ, 0 ∉ E → FinitePrimeWeighted 2 E →
    HasStrengthenedPositiveCover V →
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR8.arbitraryWeightMixedSupport_allBase_hereditary`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR8/ArbitraryWeightMixedClaim.lean#L101)

```lean
theorem arbitraryWeightMixedSupport_allBase_hereditary
    (E V : Set ℕ) (hE0 : 0 ∉ E) (hE : FinitePrimeWeighted 2 E)
    (D : LogBudgetCover V) :
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
      Irrational (erdosSupportSeries b A)
```

<a id="thm-257-mixed-supports-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `mixedSupportClaim`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L130) (E257_01, line 130), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/MixedWeightedCover.lean#L109) (MixedWeightedCover.lean, line 109), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)
- `arbitraryWeightMixedSupport_allBase_hereditary`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L159) (E257_01, line 159), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/PaperStructuresBO.lean#L65) (PaperStructuresBO.lean, line 65), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-geometry"></a>

## Theorem 1.7 (Achievement-set geometry), page 20

> *$`\mathcal{A}`$ is compact, closed, perfect, totally disconnected and nowhere dense, and $`\operatorname{volume}(\mathcal{A}) = 1`$. Thus its measure is positive although it contains no interval. Its convex hull is $`[0,E]`$, where $`E=\sum_{n\ge1}w_n`$. The positive-index digit coding onto $`\mathcal{A}`$ is injective: each achievable real has *exactly one* support.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.paper_achievement_geometry`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR20/AchievementGeometry.lean#L40)

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

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_achievement_geometry`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_02/Challenge.lean#L78) (E257_02, line 78), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L109) (PaperStatementsAM.lean, line 109), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_02.json) (E257_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-supported-dichotomy"></a>

## Theorem 1.8 (Support-restricted refinement), page 20

> *Use zero-based indices in this statement: coordinate $`j\in\mathbb{N}`$ carries weight $`w_{j+1}`$. For $`J\subseteq\mathbb{N}`$, consider the sums that use only coordinates in $`J`$. If $`\mathbb{N}\smallsetminus J`$ is finite, this achievement set has measure $`2^{-|\mathbb{N}\smallsetminus J|}`$; if infinitely many coordinates are omitted, its measure is zero. Injectivity survives every restriction; perfectness is proved when $`J`$ is infinite. No perfectness claim is made for finite $`J`$, whose coding range is finite.*

The Lean declarations below together state this result or one that implies it. The four Lean statements give the printed claims with the same zero-based coordinates: measure $2^{-|\N\smallsetminus J|}$ when $\N\smallsetminus J$ is finite, measure $0$ when it is infinite, injectivity of the coding map for every $J$, and perfectness for infinite $J$.

1. [`ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L397)

```lean
theorem volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧
        volume (supportedMersenneAchievementSet J) = 0)
```

2. [`ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L368)

```lean
theorem volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite
    {J : Set ℕ} (hJ : Jᶜ.Infinite) :
    volume (supportedMersenneAchievementSet J) = 0
```

3. [`ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L167)

```lean
theorem perfect_supportedMersenneAchievementSet
    {J : Set ℕ} (hJ : J.Infinite) :
    Perfect (supportedMersenneAchievementSet J)
```

4. [`ErdosProblems.Erdos257.supportedMersenneDigitValue_injective`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/MersenneSubseriesRigidity.lean#L54)

```lean
theorem supportedMersenneDigitValue_injective (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J)
```

<a id="thm-supported-dichotomy-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `volume_supportedMersenneAchievementSet_dichotomy`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_02/Challenge.lean#L97) (E257_02, line 97), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L252) (PaperStatementsAM.lean, line 252), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_02.json) (E257_02)
- `volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_02/Challenge.lean#L106) (E257_02, line 106), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L260) (PaperStatementsAM.lean, line 260), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_02.json) (E257_02)
- `perfect_supportedMersenneAchievementSet`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_02/Challenge.lean#L88) (E257_02, line 88), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L245) (PaperStatementsAM.lean, line 245), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_02.json) (E257_02)
- `supportedMersenneDigitValue_injective`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_02/Challenge.lean#L93) (E257_02, line 93), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_02/PaperStatementsAM.lean#L249) (PaperStatementsAM.lean, line 249), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_02.json) (E257_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-greedy-survival"></a>

## Theorem 1.10 (Membership equals greedy survival; the fatal-gap dichotomy), page 21

> *For a real target $`x\ge0`$, let $`r_n(x)`$ be the remainder after the greedy rule has processed weights $`w_1,\ldots,w_n`$, and let $`R_n=\sum_{j>n}w_j`$, with $`r_0(x)=x`$ and $`R_0=E`$. Then
> ``` math
> x\in\mathcal A\quad\Longleftrightarrow\quad
>  x\ge0\ \text{ and }\ r_n(x)\le R_n\ \text{for every }n\ge0.
> ```
> For every $`x\in[0,E]`$, nonmembership is equivalent to a finite strict gap between the two next-prefix intervals; see Observation 9.44.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.paper_greedy_survival`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR20/GeneralTargetGap.lean#L183)

```lean
theorem paper_greedy_survival :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ erdosBorweinMersenneConstant →
      (x ∉ mersenneAchievementSet ↔ InternalMersenneGap x))
```

<a id="thm-greedy-survival-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_greedy_survival`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_02/Challenge.lean#L126) (E257_02, line 126), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_02/PaperStatementsD.lean#L186) (PaperStatementsD.lean, line 186), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_02.json) (E257_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
