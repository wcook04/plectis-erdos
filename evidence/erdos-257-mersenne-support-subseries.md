# Formal evidence: Weighted Support Criteria for Reciprocal Mersenne Subseries

This record belongs to the paper [erdos-257-mersenne-support-subseries.pdf](../paper/257/erdos-257-mersenne-support-subseries.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`7f3dbf0947c3`](https://github.com/wcook04/plectis-erdos/tree/7f3dbf0947c387335ffd392b689eea5721017d84) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 12 results: 10 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 2 without a Lean proof of the whole statement; 9 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="res-weighted-support"></a>

## Theorem 1.1 (a weighted condition on the support), page 1

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

2. [`ErdosProblems.Erdos257.PaperCompleteR8.finitePrimeWeighted_fixedBase_hereditary`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR8/WeightedHereditaryClaim.lean#L31)

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

<a id="res-reciprocal-support"></a>

## Theorem 1.2 (reciprocal-summable supports), page 2

> *Let $`A\subseteq\mathbb{N}_{>0}`$ be infinite. If
> ``` math
> \sum_{a\in A}\frac1a<\infty,
> ```
> then $`X_A(b)`$ is irrational for every integer $`b\ge2`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one, except that $A$ may contain $0$; the term at $0$ is $0$ in both $\sum_{a\in A}1/a$ and $X_A(b)$ under the convention $1/0=0$.

[`Erdos249257.irrational_erdosSupportSeries_of_summable_reciprocal`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/AllBaseReciprocalSupportIrrationality.lean#L395)

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

<a id="res-finite-witness-rule"></a>

## Proposition 3.1 (realising finite monotone witness rules), page 6

> *Let $`E`$ be a finite set of primes, and let $`\mathcal U`$ be an upward-closed family of subsets of $`E`$ with $`E\in\mathcal U`$ and $`\varnothing\notin\mathcal U`$. There is a set $`A_{\mathcal U}\subseteq\mathbb{N}_{>0}`$ with $`\sum_{a\in A_{\mathcal U}}1/a=\infty`$ such that, for every integer $`b\ge2`$ and every finite set $`P`$ of primes (including $`P=\varnothing`$, with $`h(a)=1`$),
> ``` math
> \begin{equation}
> \label{eq:finite-witness-rule}
>  W_{b,P}(A_{\mathcal U})<\infty
>  \quad\Longleftrightarrow\quad P\cap E\in\mathcal U.
> \end{equation}
> ```
> Moreover $`X_B(b)`$ is irrational for every infinite $`B\subseteq A_{\mathcal U}`$ and every integer $`b\ge2`$.*

The Lean declaration below states this result or one that implies it. The Lean statement takes any upward-closed predicate $U$ on finite sets of naturals with $U(E)$ and not $U(\varnothing)$; the printed family $\mathcal U$ on subsets of $E$ is the case $U(S)\iff S\cap E\in\mathcal U$, which is upward closed because intersection with $E$ preserves inclusion, and then $U(P\cap E)$ reads $P\cap E\in\mathcal U$. The host $H$ omits $0$, so it is a set of positive integers; `Summable (Set.indicator H primeWeightedTerm)` is $W_{b,P}(H)<\infty$ for nonnegative terms, and failure of summability of $1/a$ on $H$ is the printed divergence.

[`ErdosProblems.Erdos257.finite_monotone_witness_rule_realised`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/WitnessLogicIrrational.lean#L39)

```lean
theorem finite_monotone_witness_rule_realised
    (E : Finset ℕ) (hE : ∀ p ∈ E, Nat.Prime p)
    (U : Finset ℕ → Prop) (hUp : ∀ S T : Finset ℕ, S ⊆ T → U S → U T)
    (hUE : U E) (hU0 : ¬ U ∅) :
    ∃ H : Set ℕ, 0 ∉ H ∧
      (∀ b : ℕ, 2 ≤ b → ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
        (Summable (Set.indicator H (primeWeightedTerm b P)) ↔ U (P ∩ E))) ∧
      ¬ Summable (Set.indicator H (fun a : ℕ => (1 : ℝ) / a)) ∧
      (∀ A : Set ℕ, A ⊆ H → A.Infinite →
        ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A))
```

<a id="res-finite-witness-rule-comparator"></a>

**Comparator:** not yet compared.

<a id="thm-variable-fractional-cover"></a>

## Theorem 3.2 (a summable divisor-cover criterion), page 8

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

<a id="thm-variable-fractional-cover-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `strengthenedPositiveCoverClaim`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L113) (E257_01, line 113), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/VariableExponentCover.lean#L86) (VariableExponentCover.lean, line 86), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-weighted-cover-incomparability"></a>

## Proposition 3.3 (incomparable support criteria), page 11

> *There are infinite positive supports $`E`$ and $`V`$ such that
> ``` math
> E\in\mathcal W_2,\quad E\notin\mathcal C,\qquad
>  V\in\mathcal C,\quad V\notin\mathcal W_b\ (b\ge2),\qquad
>  \sum_{a\in V}\frac1a=\infty.
> ```*

**No Lean proof of the whole statement.** In Lean, the two explicit separation constructions have not been formalised.

<a id="res-mixed-supports"></a>

## Theorem 3.4 (mixed weighted and cover supports), page 12

> *Let $`E,V\subseteq\mathbb{N}_{>0}`$. Suppose $`E`$ satisfies ({W}) for a finite nonempty prime set $`P`$, and $`V\subseteq\bigcup_jF_j`$ for finite sets and nonnegative majorants satisfying the hypotheses of Theorem 3.2, with either ({V}) or its positive-weight variant. Then $`X_A(b)`$ is irrational for every infinite $`A\subseteq E\cup V`$ and every integer $`b\ge2`$.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusion as the printed theorem, with $E\subseteq\Npos$ written as $0\notin E$. A cover satisfying (V), with its index $j\ge1$ shifted to start at $0$, is `mixedSupportClaim`; the positive-weight variant, with weights $\eta_j>0$, $\sum_j\eta_j=1$ and $\sum_jC_j\eta_j^{-\alpha_j}/(2^{\alpha_j}-1)<\infty$, is `arbitraryWeightMixedSupport_allBase_hereditary`.

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

<a id="res-mixed-supports-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `mixedSupportClaim`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L130) (E257_01, line 130), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/MixedWeightedCover.lean#L109) (MixedWeightedCover.lean, line 109), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)
- `arbitraryWeightMixedSupport_allBase_hereditary`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_01/Challenge.lean#L159) (E257_01, line 159), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_01/PaperStructuresBO.lean#L65) (PaperStructuresBO.lean, line 65), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_01.json) (E257_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-strict-mixed-supports"></a>

## Corollary 3.5 (a host requiring the mixed criterion), page 13

> *There is an infinite positive support $`U`$ with $`U\notin\mathcal C`$ and $`U\notin\mathcal W_b`$ for every integer $`b\ge2`$, such that $`X_A(b)`$ is irrational for every infinite $`A\subseteq U`$ and every integer $`b\ge2`$.*

**No Lean proof of the whole statement.** In Lean, the new host existence claim has not been formalised; the mixed implication it invokes is already checked.

<a id="res-period"></a>

## Theorem 4.1 (the exact denominator period), page 14

> *Let $`F\subseteq\mathbb{N}_{>0}`$ be finite and nonempty, let $`b\ge2`$ be an integer, and let $`D_F>0`$ be the denominator of $`X_F(b)`$ in lowest terms. Then $`D_F`$ is coprime to $`b`$, and
> ``` math
> \operatorname{ord}_{D_F}(b)=\operatorname{lcm}\{n:n\in F\}.
> ```
> If moreover $`\operatorname{lcm}(F)\ge2`$, then $`\operatorname{lcm}(F)<D_F`$. We use $`\operatorname{ord}_1(b)=1`$, so the statement includes $`F=\{1\}`$ at $`b=2`$.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones, with $F\subseteq\Npos$ written as $0\notin F$; coprimality of $D_F$ and $b$ is proved without assuming $F$ nonempty. The order is the multiplicative order of $b$ modulo $D_F$, which is $1$ when $D_F=1$, as in the convention $\operatorname{ord}_1(b)=1$.

1. [`Erdos249257.coprime_base_den_finiteErdosSum`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/CertificateKernel.lean#L5221)

```lean
theorem coprime_base_den_finiteErdosSum
    (F : Finset Nat) (b : Nat) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    Nat.Coprime b (finiteErdosSum F b).den
```

2. [`Erdos249257.finite_period_noncollapse_rat_den`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/CertificateKernel.lean#L5246)

```lean
theorem finite_period_noncollapse_rat_den
    (F : Finset Nat) (b : Nat)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b) :
    orderOf (ZMod.unitOfCoprime b (coprime_base_den_finiteErdosSum F b h0 hb))
      = F.lcm id
```

3. [`Erdos249257.lcm_lt_den_finiteErdosSum`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/CertificateKernel.lean#L5260)

```lean
theorem lcm_lt_den_finiteErdosSum
    (F : Finset Nat) (b : Nat)
    (hF : F.Nonempty) (h0 : 0 ∉ F) (hb : 2 ≤ b)
    (h2 : 2 ≤ F.lcm id) :
    F.lcm id < (finiteErdosSum F b).den
```

<a id="res-period-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `coprime_base_den_finiteErdosSum`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_47/Challenge.lean#L165) (E257_47, line 165), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_47/PaperStatementsAG.lean#L30) (PaperStatementsAG.lean, line 30), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_47.json) (E257_47)
- `finite_period_noncollapse_rat_den`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_50/Challenge.lean#L97) (E257_50, line 97), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_50/FinitePeriodNoncollapse.lean#L12) (FinitePeriodNoncollapse.lean, line 12), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_50.json) (E257_50)
- `lcm_lt_den_finiteErdosSum`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_47/Challenge.lean#L170) (E257_47, line 170), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_47/PaperStatementsAG.lean#L119) (PaperStatementsAG.lean, line 119), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_47.json) (E257_47)

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

## Theorem 8.1 (membership and nonincreasing integer remainders), page 16

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

[`ErdosProblems.Erdos257.PaperCompleteR20.paper_general_repair_criteria`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR20/GeneralRepairCorrespondence.lean#L15)

```lean
theorem paper_general_repair_criteria {x : ℝ} (hx : 0 ≤ x) :
    (x ∈ mersenneAchievementSet ↔ ∀ K : ℕ, ∃ N, K ≤ N ∧
      paperIntegerDefect x (N+1) ≤ paperIntegerDefect x N) ∧
    (x ∈ mersenneAchievementSet ↔ ∀ K : ℕ, ∃ N, K ≤ N ∧
      N < K+2*Nat.sqrt K+12 ∧ paperIntegerDefect x (N+1) ≤ paperIntegerDefect x N)
```

<a id="res-general-repair-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_general_repair_criteria`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_47/Challenge.lean#L207) (E257_47, line 207), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_47/PaperStatementsM.lean#L26) (PaperStatementsM.lean, line 26), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_47.json) (E257_47)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-one-over-twenty-one-frontier"></a>

## Theorem 9.1 (integer-quotient tests for $`1/21`$), page 18

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

The Lean declarations below together state this result or one that implies it. Item 2 follows from a Lean criterion with a weaker hypothesis: $1/21\in\Ach$ whenever $(s_R+2R+1)/2^{2R}\to0$ along some sequence of ranks $R\ge2$ tending to infinity, and ranks $R_k\to\infty$ with $s_{R_k}\le2^{R_k}$ supply such a sequence. Items 1 and 3 are stated as printed; the recurrence for $s_{R+1}$ is written with natural-number subtraction, which agrees with the integer identity because $s_{R+1}>2^{R+1}$ for all large $R$.

1. [`Erdos249257.one_div_twenty_one_mem_iff_not_fatalAlignedBranch`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L3507)

```lean
theorem one_div_twenty_one_mem_iff_not_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ TwentyOneFatalAlignedBranch
```

2. [`Erdos249257.twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L5554)

```lean
theorem twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows
    {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop)
    (hrow : ∀ k : ℕ,
      2 ≤ R k ∧
        twentyOneEvenQuotientGreedyRemainder (R k) ≤ 2 ^ (R k)) :
    TwentyOneCofinalEvenQuotientGreedyDecay
```

where [`TwentyOneCofinalEvenQuotientGreedyDecay`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L5425) is

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

3. [`Erdos249257.one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L5458)

```lean
theorem one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay
    (hcofinal : TwentyOneCofinalEvenQuotientGreedyDecay) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet
```

4. [`Erdos249257.twentyOneFatalAlignedBranch_eventually_strict_supercapacity`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L5625)

```lean
theorem twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      2 ^ R < twentyOneEvenQuotientGreedyRemainder R
```

5. [`Erdos249257.twentyOneFatalAlignedBranch_eventually_affine_supercapacity`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TwentyOneQuotientGreedy.lean#L5658)

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

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `one_div_twenty_one_mem_iff_not_fatalAlignedBranch`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_52/Challenge.lean#L175) (E257_52, line 175), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_52/TwentyOneFatalBranch.lean#L233) (TwentyOneFatalBranch.lean, line 233), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_52.json) (E257_52)
- `twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_47/Challenge.lean#L238) (E257_47, line 238), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_47/PaperStructuresBQ.lean#L299) (PaperStructuresBQ.lean, line 299), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_47.json) (E257_47)
- `one_div_twenty_one_mem_mersenneAchievementSet_of_cofinalGreedyDecay`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_47/Challenge.lean#L225) (E257_47, line 225), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_47/PaperStructuresBM.lean#L302) (PaperStructuresBM.lean, line 302), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_47.json) (E257_47)
- `twentyOneFatalAlignedBranch_eventually_strict_supercapacity`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_52/Challenge.lean#L180) (E257_52, line 180), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_52/TwentyOneFatalBranch.lean#L239) (TwentyOneFatalBranch.lean, line 239), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_52.json) (E257_52)
- `twentyOneFatalAlignedBranch_eventually_affine_supercapacity`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_52/Challenge.lean#L186) (E257_52, line 186), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_52/TwentyOneFatalBranch.lean#L248) (TwentyOneFatalBranch.lean, line 248), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_52.json) (E257_52)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-terminalhalf"></a>

## Theorem 9.2 (finite approximations with vanishing scaled error), page 19

> *Suppose there are integers $`M_j\ge1`$ tending to infinity and sets $`A_j\subseteq\{2,\ldots,M_j\}`$ such that
> ``` math
> \frac{|K_{A_j}(M_j)|}{2^{M_j}}\longrightarrow0.
> ```
> Then $`X_A(2)=1/2`$ for some infinite set $`A\subseteq\mathbb{N}_{>0}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos257/PaperCompleteR20/TerminalSetCorrespondence.lean#L51)

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

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_terminalhalf`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_47/Challenge.lean#L121) (E257_47, line 121), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_47/PaperStatementsBC.lean#L22) (PaperStatementsBC.lean, line 22), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_47.json) (E257_47)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-cylinderhalf"></a>

## Theorem 9.3 (unbounded shared-prefix families imply a half-support), page 20

> *Suppose that for every $`N`$ there are $`M,K`$ with $`\max\{N,1\}\le M`$, $`0\le K\le M`$, and a family satisfying all the conditions in the preceding paragraph. Then $`X_A(2)=1/2`$ for some infinite set $`A\subseteq\mathbb{N}_{>0}`$.*

The Lean declaration below states this result or one that implies it. The Lean hypothesis has the printed content: a stage at depth $M$ with cutoff $K\le M$ consists of sets $A_1,\ldots,A_{B(M)}\subseteq\{2,\ldots,M\}$ with $1\le K_{A_k}(m)\le B(m)$ for $1\le m\le M$ and $K_{A_k}(M)=k$, agreeing on $\{1,\ldots,K\}$, whose suffix values are $E-k$ for one integer $E\ge B(M)$. The conclusion is the printed one, with $A\subseteq\Npos$ written as $0\notin A$.

[`Erdos249257.SuffixCylinderTerminalOnlyBridge.exists_infinite_positive_support_half_of_cofinalCylinderStages`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/SuffixCylinderTerminalOnlyBridge.lean#L287)

```lean
theorem exists_infinite_positive_support_half_of_cofinalCylinderStages
    (hstages : ∀ N : ℕ, ∃ M K : ℕ,
      max N 1 ≤ M ∧ Nonempty (CylinderStage K M)) :
    ∃ A : Set ℕ, 0 ∉ A ∧ A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2
```

<a id="res-cylinderhalf-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exists_infinite_positive_support_half_of_cofinalCylinderStages`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_48/Challenge.lean#L95) (E257_48, line 95), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_48/PaperStructuresCB.lean#L538) (PaperStructuresCB.lean, line 538), [replay report](../evidence/comparator/replay-35935225572/receipt-E257_48.json) (E257_48)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
