# Formal evidence: Irrationality criteria for Lambert subseries

This record belongs to the paper [erdos-257-mersenne-support-subseries.pdf](../paper/257/erdos-257-mersenne-support-subseries.pdf). For every result it lists the Lean declarations that state it, and the recorded Comparator check where there is one. The paper's verification concordance uses this result mapping.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`436f55ebdafa`](https://github.com/wcook04/plectis-erdos/tree/436f55ebdafa67e4af0fff79f621c13f2ded12bf) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 6 results: 5 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 1 without a Lean proof of the whole statement; 4 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below. Comparator checks separately declared statements, the axiom budget and kernel acceptance; it does not establish novelty, significance or peer review.

<a id="res-weighted-support"></a>

## Theorem 1.2 (a weighted condition on the support), page 2

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

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones, with $A\subseteq\Npos$ written as $0\notin A$ and $W_{b,P}(A)<\infty$ written as summability over $A$ for some finite nonempty set $P$ of primes. The fixed-base statement and, under (W), irrationality at every $b\ge2$ for every infinite subset are the two parts of `divisibilityWeightedClaim`; heredity under the fixed-base condition is `finitePrimeWeighted_fixedBase_hereditary`.

1. [`ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L120)

```lean
theorem divisibilityWeightedClaim : DivisibilityWeightedClaim
```

where [`DivisibilityWeightedClaim`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean#L61) is

```lean
def DivisibilityWeightedClaim : Prop :=
  (∀ (b : ℕ) (A : Set ℕ), 2 ≤ b → 0 ∉ A → A.Infinite →
    FinitePrimeWeighted b A → Irrational (erdosSupportSeries b A)) ∧
  (∀ H : Set ℕ, 0 ∉ H → FinitePrimeWeighted 2 H →
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A))
```

2. [`ErdosProblems.Erdos257.PaperCompleteR8.finitePrimeWeighted_fixedBase_hereditary`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedHereditaryClaim.lean#L31)

```lean
theorem finitePrimeWeighted_fixedBase_hereditary
    (b : ℕ) (H : Set ℕ) (hb : 2 ≤ b) (hH0 : 0 ∉ H)
    (hH : FinitePrimeWeighted b H) :
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      Irrational (erdosSupportSeries b A)
```

<a id="res-weighted-support-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `divisibilityWeightedClaim`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L76) (E257_01, line 76), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/DivisibilityWeightedSupport.lean#L42) (DivisibilityWeightedSupport.lean, line 42), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)
- `finitePrimeWeighted_fixedBase_hereditary`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_47/Challenge.lean#L133) (E257_47, line 133), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_47/PaperStatementsBC.lean#L38) (PaperStatementsBC.lean, line 38), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_47.json) (E257_47)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-variable-fractional-cover"></a>

## Theorem 3.1 (a summable divisor-cover criterion), page 6

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

[`ErdosProblems.Erdos257.PaperCompleteR8.strengthenedPositiveCoverClaim`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR8/PositiveCoverReturn.lean#L241)

```lean
theorem strengthenedPositiveCoverClaim : StrengthenedPositiveCoverClaim
```

where [`StrengthenedPositiveCoverClaim`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean#L53) is

```lean
def StrengthenedPositiveCoverClaim : Prop :=
  ∀ C : PositiveCoverData, C.StrengthenedCostSummable →
    ∀ A : Set ℕ, A ⊆ C.host → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
```

<a id="thm-variable-fractional-cover-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `strengthenedPositiveCoverClaim`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L113) (E257_01, line 113), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/VariableExponentCover.lean#L86) (VariableExponentCover.lean, line 86), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-mixed-supports"></a>

## Theorem 4.1 (mixed weighted and cover supports), page 9

> *Let $`E,V\subseteq\mathbb{N}_{>0}`$. Suppose $`E`$ satisfies ({W}) for a finite nonempty prime set $`P`$, and $`V\subseteq\bigcup_jF_j`$ for finite sets and nonnegative majorants satisfying the hypotheses of Theorem 3.1, with either ({V}) or its positive-weight variant. Then $`X_A(b)`$ is irrational for every infinite $`A\subseteq E\cup V`$ and every integer $`b\ge2`$.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusion as the printed theorem, with $E\subseteq\Npos$ written as $0\notin E$. A cover satisfying (V), with its index $j\ge1$ shifted to start at $0$, is `mixedSupportClaim`; the positive-weight variant, with weights $\eta_j>0$, $\sum_j\eta_j=1$ and $\sum_jC_j\eta_j^{-\alpha_j}/(2^{\alpha_j}-1)<\infty$, is `arbitraryWeightMixedSupport_allBase_hereditary`.

1. [`ErdosProblems.Erdos257.PaperCompleteR8.mixedSupportClaim`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedReturn.lean#L126)

```lean
theorem mixedSupportClaim : MixedSupportClaim
```

where [`MixedSupportClaim`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR7/AnalyticTargets.lean#L71) is

```lean
def MixedSupportClaim : Prop :=
  ∀ E V : Set ℕ, 0 ∉ E → FinitePrimeWeighted 2 E →
    HasStrengthenedPositiveCover V →
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR8.arbitraryWeightMixedSupport_allBase_hereditary`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR8/ArbitraryWeightMixedClaim.lean#L101)

```lean
theorem arbitraryWeightMixedSupport_allBase_hereditary
    (E V : Set ℕ) (hE0 : 0 ∉ E) (hE : FinitePrimeWeighted 2 E)
    (D : LogBudgetCover V) :
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
      Irrational (erdosSupportSeries b A)
```

<a id="res-mixed-supports-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `mixedSupportClaim`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L130) (E257_01, line 130), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/MixedWeightedCover.lean#L109) (MixedWeightedCover.lean, line 109), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)
- `arbitraryWeightMixedSupport_allBase_hereditary`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L159) (E257_01, line 159), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/PaperStructuresBO.lean#L65) (PaperStructuresBO.lean, line 65), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-weighted-cover-incomparability"></a>

## Proposition 5.1 (incomparable support criteria), page 10

> *There are infinite positive supports $`E`$ and $`V`$ such that
> ``` math
> E\in\mathcal W_2,\quad E\notin\mathcal C,\qquad
>  V\in\mathcal C,\quad V\notin\mathcal W_b\ (b\ge2),\qquad
>  \sum_{a\in V}\frac1a=\infty.
> ```*

The Lean declarations below together state this result or one that implies it. The two Lean statements supply the two hosts separately, with a positive support written as $0\notin E$ and a cover satisfying (V) indexed from $0$. `exists_weighted_not_strengthened_host` gives an infinite $E$ with $E\in\mathcal W_2$ and $E\notin\mathcal C$; `exists_strengthened_not_old_or_weighted_host` gives an infinite $V$ with $V\in\mathcal C$, $V\notin\mathcal W_b$ for every integer $b\ge2$, and non-summable reciprocals, which for nonnegative terms is $\sum_{a\in V}1/a=\infty$. Each adds further conclusions. The Lean host $V$ is a squarefree divisor-cube host with its own row schedule; the bounded-mass fresh-prime construction printed in the proof is an ordinary proof.

1. [`ErdosProblems.Erdos257.PaperCompleteR8.exists_weighted_not_strengthened_host`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR8/AnalyticSeparationReturn.lean#L15)

```lean
theorem exists_weighted_not_strengthened_host :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ FinitePrimeWeighted 2 A ∧
      ¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a)) ∧
      ¬ HasStrengthenedPositiveCover A ∧ IsEmpty (LogBudgetCover A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B))
```

2. [`ErdosProblems.Erdos257.PaperCompleteR8.exists_strengthened_not_old_or_weighted_host`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos257/PaperCompleteR8/ReverseStrengthenedHost.lean#L387)

```lean
theorem exists_strengthened_not_old_or_weighted_host :
    ∃ A : Set ℕ, A.Infinite ∧ 0 ∉ A ∧ (∀ a ∈ A, Squarefree a) ∧
      HasStrengthenedPositiveCover A ∧ ¬ HasOldPositiveCover A ∧
      (¬ Summable (Set.indicator A (fun a : ℕ => (1 : ℝ) / a))) ∧
      (∀ b : ℕ, 2 ≤ b → ¬ FinitePrimeWeighted b A) ∧
      (∀ B : Set ℕ, B ⊆ A → B.Infinite → ∀ b : ℕ, 2 ≤ b →
        Irrational (erdosSupportSeries b B))
```

<a id="res-weighted-cover-incomparability-comparator"></a>

**Comparator:** not yet compared.

<a id="res-strict-mixed-supports"></a>

## Corollary 5.2 (a support requiring the mixed criterion), page 12

> *There is an infinite positive support $`U`$ with $`U\notin\mathcal C`$ and $`U\notin\mathcal W_b`$ for every integer $`b\ge2`$, such that $`X_A(b)`$ is irrational for every infinite $`A\subseteq U`$ and every integer $`b\ge2`$.*

**No Lean proof of the whole statement.** In Lean, the new host existence claim has not been formalised; the mixed implication it invokes is already checked.

<a id="res-reciprocal-support"></a>

## Theorem A.1 (reciprocal-summable supports), page 14

> *Let $`A\subseteq\mathbb{N}_{>0}`$ be infinite. If
> ``` math
> \sum_{a\in A}\frac1a<\infty,
> ```
> then $`X_A(b)`$ is irrational for every integer $`b\ge2`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one, except that $A$ may contain $0$; the term at $0$ is $0$ in both $\sum_{a\in A}1/a$ and $X_A(b)$ under the convention $1/0=0$.

[`Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L395)

```lean
theorem irrational_erdosSupportSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (reciprocalSupportTerm A)) :
    Irrational (erdosSupportSeries b A)
```

<a id="res-reciprocal-support-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_erdosSupportSeries_of_summable_reciprocal`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_47/Challenge.lean#L151) (E257_47, line 151), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_47/PaperStatementsAV.lean#L52) (PaperStatementsAV.lean, line 52), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_47.json) (E257_47)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
