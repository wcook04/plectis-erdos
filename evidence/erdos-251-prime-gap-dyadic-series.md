# Formal evidence: Sparse Congruence-Preserving Perturbations\\of Dyadic Series

This record belongs to the paper [erdos-251-prime-gap-dyadic-series.pdf](../paper/251/erdos-251-prime-gap-dyadic-series.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`be89e72217ec`](https://github.com/wcook04/plectis-erdos/tree/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 9 results: 8 with a Lean proof of the whole statement, 1 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 8 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="res-sparserationalisation"></a>

## Proposition 1.1 (sparse changes preserving congruences), page 2

> *Let $`a:\mathbb{N}\to\mathbb{N}`$ satisfy $`A=\sum_{n\ge0}a_n2^{-(n+1)}<\infty`$, let $`K\in\mathbb{N}`$, and let $`f:\mathbb{N}\to\mathbb{R}`$ tend to $`+\infty`$. There exist a set $`S\subseteq[K,\infty)`$ of upper Banach density zero and a nondegenerate interval $`I\subset(A,\infty)`$ such that, for every $`r\in I`$, there is an integer correction $`e:\mathbb{N}\to\mathbb{N}`$ satisfying
> ``` math
> \operatorname{supp}e\subseteq S,\qquad e_n\le f(n)\ \text{eventually},
>  \qquad \sum_{n\ge0}(a_n+e_n)2^{-(n+1)}=r.
> ```
> For each integer $`q\ge1`$ there is a cutoff $`N_q`$, independent of $`r`$, such that $`q\mid e_n`$ and $`q\mid\sum_{i<n}e_i`$ for all $`n\ge N_q`$. For every $`\varepsilon>0`$, the choice $`f(n)=(\log(n+3))^\varepsilon`$ can be made with
> ``` math
> |S\cap[X,2X)|=O_\varepsilon\!\left(\frac{X}{\log\log X}\right),
>  \qquad
>  d_{\rm TV}(\mu_{a,X,m},\mu_{a+e,X,m})
>  \le\frac{m|S\cap[X,2X+m)|}{X}.
> ```
> In particular the distance tends to zero for every integer-valued $`m=m(X)\ge1`$ with $`m(X)=o(\log\log X)`$, uniformly over target values.*

The Lean declarations below together state this result or one that implies it. For a general $f$ the construction holds with $I=[l,u]$, $A<l<u$ and cutoffs $N_q$ chosen before the target $r$ (`arbitrary_word_sparse_rationalisation_uniform`). For $f(n)=(\log(n+3))^\varepsilon$ the construction also satisfies the displayed total-variation bound for all $X$ and $m$, and $|S\cap[X,X+L)|\le CX/\log\log(X+3)$ for all large $X$ and every $L\le2X$, which gives the printed count at $L=X$ (`polylogarithmic_word_interval_uniform`). The same statement proves $d_{\rm TV}\to0$ for every integer-valued $m(X)=o(\log\log X)$, uniformly over all sequences that differ from $a$ only on $S$, a class that contains $a+e$ for every target $r$.

1. [`ErdosProblems.Erdos251.PaperR9.SparseAmbient.arbitrary_word_sparse_rationalisation_uniform`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/SparseAmbientR9.lean#L269)

```lean
theorem arbitrary_word_sparse_rationalisation_uniform (a : ℕ → ℕ) {A : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) :
    ∃ S : Set ℕ, ∃ l u : ℝ, ∃ Nq : ℕ → ℕ,
      S ⊆ Set.Ici K ∧ UpperBanachZero S ∧ A < l ∧ l < u ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r
```

2. [`ErdosProblems.Erdos251.PaperR11.SparsePaper.polylogarithmic_word_interval_uniform`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/SparsePaperR11.lean#L137)

```lean
theorem polylogarithmic_word_interval_uniform (a : ℕ → ℕ) {A ε : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (hε : 0 < ε) (K : ℕ) :
    ∃ start : ℕ, ∃ l u C : ℝ, ∃ Nq : ℕ → ℕ,
      (Set.range (centre (polylog ε) start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre (polylog ε) start)) ∧
      A < l ∧ l < u ∧ 0 < C ∧
      (∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
        ((supportSlice (centre (polylog ε) start) X L).card : ℝ) ≤ C * X / iterlog X) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop,
          ∀ b : ℕ → ℕ,
            (∀ n, a n ≠ b n → n ∈ Set.range (centre (polylog ε) start)) →
            blockTV a b X (m X) < η) ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ Set.range (centre (polylog ε) start)) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        (∀ n < K, a n + e n = a n) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r ∧
        ∀ X m : ℕ, blockTV a (fun n => a n + e n) X m ≤
          (m : ℝ) * (supportSlice (centre (polylog ε) start) X (X + m)).card / X
```

<a id="res-sparserationalisation-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `arbitrary_word_sparse_rationalisation_uniform`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_01/Challenge.lean#L113) (E251_01, line 113), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_01/UniformSparseRationalisation.lean#L50) (UniformSparseRationalisation.lean, line 50), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_01.json) (E251_01)
- `polylogarithmic_word_interval_uniform`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_01/Challenge.lean#L87) (E251_01, line 87), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_01/UniformSparseRationalisation.lean#L20) (UniformSparseRationalisation.lean, line 20), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_01.json) (E251_01)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `polylogarithmic_word_interval_uniform`:

```lean
theorem polylogarithmic_word_interval_uniform (a : ℕ → ℕ) {A ε : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (hε : 0 < ε) (K : ℕ) :
    ∃ S : Set ℕ, ∃ l u C : ℝ, ∃ Nq : ℕ → ℕ,
      (S ⊆ Set.Ici K) ∧
      UpperBanachZero (S) ∧
      A < l ∧ l < u ∧ 0 < C ∧
      (∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
        ((supportSlice S X L).card : ℝ) ≤ C * X / iterlog X) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop,
          ∀ b : ℕ → ℕ,
            (∀ n, a n ≠ b n → n ∈ S) →
            blockTV a b X (m X) < η) ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        (∀ n < K, a n + e n = a n) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r ∧
        ∀ X m : ℕ, blockTV a (fun n => a n + e n) X m ≤
          (m : ℝ) * (supportSlice S X (X + m)).card / X := by sorry
```

<a id="res-jointcountermodel"></a>

## Corollary 1.2 (a rational sum with the stated prime-gap statistics), page 5

> *Let $`p_0=2,p_1=3,\ldots`$ be the primes and $`g_n=p_{n+1}-p_n`$. Given $`K\in\mathbb{N}`$ and $`0<\varepsilon\le1`$, there is $`b:\mathbb{N}\to\mathbb{N}`$ with rational dyadic sum such that $`b_n=g_n`$ for $`n<K`$, $`b_n\ge g_n`$, and $`b_n-g_n\le(\log(n+3))^\varepsilon`$ eventually. For every fixed positive modulus, both the coefficients and the cumulative positions eventually retain their corresponding residues. The empirical distributions of unnormalised blocks have total variation distance tending to zero for lengths $`o(\log\log X)`$, and for every fixed nonzero $`F\in\mathbb{Z}[x_0,\ldots,x_k]`$,
> ``` math
> \bigl|\{n<N:F(b_n,\ldots,b_{n+k})=0\}\bigr|=o(N).
> ```
> Moreover, with $`P_n=2+\sum_{i<n}b_i`$,
> ``` math
> 0\le P_n-p_n=O_\varepsilon\!\left(
>        \frac{n(\log(n+3))^\varepsilon}{\log\log n}\right),
>  \qquad P_n\sim n\log n.
> ```
> These positions are not asserted to be prime.*

The Lean proof assumes Schlage-Puchta's density lemma and the prime number theorem. Lean takes this input as a hypothesis (`PrimeNumberTheorem`, `SchlagePuchtaLemma4`); it is not proved in Lean.

1. [`ErdosProblems.Erdos251.PaperCompleteR21.short_joint_prime_gap_countermodel`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCompleteR21/JointPrimeGapCountermodel.lean#L431)

```lean
theorem short_joint_prime_gap_countermodel
    (hSP : SchlagePuchtaLemma4) (hPNT : PrimeNumberTheorem)
    (K : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ b : ℕ → ℕ, ∃ r : ℚ, ∃ C : ℝ, 0 < C ∧
      HasSum (fun n => (b n : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ n, n < K → b n = primeGap0 n) ∧
      (∀ n, primeGap0 n ≤ b n) ∧
      (∀ᶠ n : ℕ in atTop, ((b n - primeGap0 n : ℕ) : ℝ) ≤ polylog ε n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
        b n ≡ primeGap0 n [MOD q] ∧ cumulative b n ≡ prime0 n [MOD q]) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        Tendsto (fun X => blockTV primeGap0 b X (m X)) atTop (𝓝 0)) ∧
      FixedBlockNonconcentration (fun n => (b n : ℤ)) ∧
      (∀ n, prime0 n ≤ cumulative b n) ∧
      (∀ᶠ n : ℕ in atTop, (cumulative b n : ℝ) - prime0 n
        ≤ C * ((n : ℝ) * polylog ε n / Real.log (Real.log (n : ℝ)))) ∧
      Tendsto (fun n => (cumulative b n : ℝ) / scale n) atTop (𝓝 1)
```

2. [`ErdosProblems.Erdos251.PaperCompleteR21.cut_prefix_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCompleteR21/JointPrimeGapCountermodel.lean#L228)

```lean
theorem cut_prefix_bound {α : ℝ} (hα : 0 < α) (start : ℕ)
    (hc : StrictMono (centre (polylog α) start)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ((cut (centre (polylog α) start) hc n : ℕ) : ℝ) ≤ C * n / iterlog n
```

The assumed input [`PrimeNumberTheorem`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L28) is

```lean
def PrimeNumberTheorem : Prop :=
  Tendsto (fun n => (prime0 n : ℝ) / scale n) atTop (𝓝 1)
```

The assumed input [`SchlagePuchtaLemma4`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L22) is

```lean
def SchlagePuchtaLemma4 : Prop :=
  ∀ k : ℕ, ∀ F : MvPolynomial (Fin (k + 1)) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval
      (fun i : Fin (k + 1) => (primeGap0 (n + i.val) : ℤ)) F = 0}
```

<a id="res-jointcountermodel-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-infinite"></a>

## Theorem 2.1 (prime-to-gap identity), page 6

> *The actual prime and gap series satisfy $`\Pi=2+G`$. Their complete tails
> ``` math
> T_N=\sum_{j\ge1}g_{N+j}2^{-j}
> ```
> satisfy $`T_0=2G-1`$ and $`T_{N+1}=2T_N-g_{N+1}`$. Thus $`\Pi`$, $`G`$ and $`T_0`$ have the same rationality status.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos251.PaperR7.infinite_prime_gap_identity`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L47)

```lean
theorem infinite_prime_gap_identity :
    Summable primeDyadicTerm ∧ Summable primeGapDyadicTerm ∧
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n
```

2. [`ErdosProblems.Erdos251.realPrimeGapTail_eq_tsum_shifted_gaps`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L31)

```lean
theorem realPrimeGapTail_eq_tsum_shifted_gaps (N : ℕ) :
    realPrimeGapTail N =
      ∑' k : ℕ, (primeGap0 (N + k + 1) : ℝ) / 2 ^ (k + 1)
```

3. [`ErdosProblems.Erdos251.realPrimeGapTail_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L57)

```lean
@[simp] theorem realPrimeGapTail_zero :
    realPrimeGapTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1
```

4. [`ErdosProblems.Erdos251.realPrimeGapTail_recurrence`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L48)

```lean
theorem realPrimeGapTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) realPrimeGapTail
```

5. [`ErdosProblems.Erdos251.irrational_tsum_primeDyadicTerm_iff_primeGap`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L435)

```lean
theorem irrational_tsum_primeDyadicTerm_iff_primeGap
    (hprime : Summable primeDyadicTerm) :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)
```

6. [`ErdosProblems.Erdos251.irrational_realPrimeGapTail_zero_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/RealPrimeGapTail.lean#L63)

```lean
theorem irrational_realPrimeGapTail_zero_iff :
    Irrational (realPrimeGapTail 0) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)
```

<a id="res-infinite-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `infinite_prime_gap_identity`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_01/Challenge.lean#L205) (E251_01, line 205), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_01/PaperStatementsG.lean#L44) (PaperStatementsG.lean, line 44), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_01.json) (E251_01)
- `realPrimeGapTail_eq_tsum_shifted_gaps`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_05/Challenge.lean#L126) (E251_05, line 126), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_05/PaperStatementsG.lean#L168) (PaperStatementsG.lean, line 168), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_05.json) (E251_05)
- `realPrimeGapTail_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_05/Challenge.lean#L135) (E251_05, line 135), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_05/PaperStatementsG.lean#L175) (PaperStatementsG.lean, line 175), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_05.json) (E251_05)
- `realPrimeGapTail_recurrence`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_05/Challenge.lean#L131) (E251_05, line 131), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_05/PaperStatementsG.lean#L172) (PaperStatementsG.lean, line 172), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_05.json) (E251_05)
- `irrational_tsum_primeDyadicTerm_iff_primeGap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_05/Challenge.lean#L120) (E251_05, line 120), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_05/PaperStatementsG.lean#L159) (PaperStatementsG.lean, line 159), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_05.json) (E251_05)
- `irrational_realPrimeGapTail_zero_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_05/Challenge.lean#L115) (E251_05, line 115), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_05/PaperStatementsG.lean#L155) (PaperStatementsG.lean, line 155), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_05.json) (E251_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-true-tail"></a>

## Lemma 2.2 (the boundary condition identifying a true tail), page 7

> *Let $`\sum_{j\ge1}|a_j|2^{-j}<\infty`$ and $`U_{N+1}=2U_N-a_{N+1}`$. Then $`U_N=\sum_{j\ge1}a_{N+j}2^{-j}`$ for every $`N`$ if and only if $`2^{-N}U_N\to0`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperCompleteR20.real_dyadic_orbit_eq_true_tail_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCompleteR20/TrueTail.lean#L57)

```lean
theorem real_dyadic_orbit_eq_true_tail_iff (a U : ℕ → ℝ)
    (habs : Summable (fun j : ℕ => |a (j + 1)| / (2 : ℝ) ^ (j + 1)))
    (hrec : ∀ N, U (N + 1) = 2 * U N - a (N + 1)) :
    (∀ N, U N = realDyadicTail a N) ↔
      Tendsto (fun N : ℕ => U N / 2 ^ N) atTop (𝓝 0)
```

<a id="res-true-tail-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `real_dyadic_orbit_eq_true_tail_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_01/Challenge.lean#L268) (E251_01, line 268), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_01/PaperStatementsC.lean#L19) (PaperStatementsC.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_01.json) (E251_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-escape-irrational"></a>

## Theorem 3.1 (exact rationality classification), page 7

> *For a real integer-coefficient recurrence, the following are equivalent: $`U_0\in\mathbb{Q}`$; $`D_h(N)\in\mathbb{Z}`$ for some $`h\ge1,N\ge0`$; and, for some fixed $`h\ge1`$, $`D_h(N)\in\mathbb{Z}`$ at every sufficiently large $`N`$. More precisely, if $`U_0=u/(2^sd)`$ is in lowest terms, with $`d`$ odd, then
> ``` math
> \operatorname{den}(U_N)=2^{\max(s-N,0)}d,\qquad
>  D_h(N)\in\mathbb{Z}\ \Longleftrightarrow\ N\ge s\ \text{and}\ d\mid2^h-1
>  \quad(h\ge1).
> ```
> Consequently $`U_0`$ is irrational exactly when every positive shift is nonintegral at every index, equivalently when for each fixed $`h\ge1`$ there are arbitrarily late nonintegral shifts.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos251.PaperCompleteR20.real_orbit_exact_den_and_shift`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCompleteR20/ExactDenominator.lean#L62)

```lean
theorem real_orbit_exact_den_and_shift
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T)
    (q : ℚ) (hq0 : T 0 = q) (s d : ℕ) (hq : q.den = 2^s*d) (hd : Odd d)
    (N h : ℕ) (hh : 0 < h) :
    (∃ v : ℚ, T N = v ∧ v.den = 2^(s-N)*d) ∧
    (RealIntegral (realTailShift T h N) ↔ s ≤ N ∧ d ∣ 2^h-1)
```

2. [`ErdosProblems.Erdos251.PaperR7.rationality_classification`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L94)

```lean
theorem rationality_classification {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    (¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N)) ∧
    (¬ Irrational (T 0) ↔
      ∃ h N₀ : ℕ, 0 < h ∧
        ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N)) ∧
    (Irrational (T 0) ↔
      ∀ h : ℕ, 0 < h → ∀ N, ¬ RealIntegral (realTailShift T h N)) ∧
    (Irrational (T 0) ↔ CofinalNonintegralTailShifts T)
```

<a id="res-escape-irrational-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `real_orbit_exact_den_and_shift`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_05/Challenge.lean#L150) (E251_05, line 150), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_05/PaperStatementsJ.lean#L18) (PaperStatementsJ.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_05.json) (E251_05)
- `rationality_classification`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_01/Challenge.lean#L220) (E251_01, line 220), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_01/PaperStatementsG.lean#L91) (PaperStatementsG.lean, line 91), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_01.json) (E251_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-signedwindow"></a>

## Proposition 4.1 (two consecutive differences of absolute value less than one), page 8

> *Let $`D,D'\in\mathbb{R}`$, $`\delta\in2\mathbb{Z}`$ and $`D'=2D-\delta`$. The conditions $`|D|<1`$, $`|D'|<1`$ and $`\delta\ne0`$ hold exactly when, for some $`s\in\{-1,1\}`$,
> ``` math
> \delta=2s,\qquad \tfrac12<sD<1.
> ```
> In that case $`sD'\in(-1,0)`$ and both $`D`$ and $`D'`$ are nonintegral.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos251.PaperCompleteR20.signed_two_window_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCompleteR20/SignedWindow.lean#L7)

```lean
theorem signed_two_window_iff (D D' : ℝ) (δ : ℤ)
    (heven : Even δ) (hstep : D' = 2 * D - (δ : ℝ)) :
    (|D| < 1 ∧ |D'| < 1 ∧ δ ≠ 0) ↔
      ∃ s : ℤ, (s = -1 ∨ s = 1) ∧ δ = 2 * s ∧
        (1 / 2 : ℝ) < (s : ℝ) * D ∧ (s : ℝ) * D < 1
```

2. [`ErdosProblems.Erdos251.PaperCompleteR20.signed_two_window_consequences`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCompleteR20/SignedWindow.lean#L47)

```lean
theorem signed_two_window_consequences (D D' : ℝ) (δ s : ℤ)
    (hstep : D' = 2 * D - (δ : ℝ)) (hs : s = -1 ∨ s = 1)
    (hδ : δ = 2 * s) (hlo : (1 / 2 : ℝ) < (s : ℝ) * D)
    (hhi : (s : ℝ) * D < 1) :
    (-1 < (s : ℝ) * D' ∧ (s : ℝ) * D' < 0) ∧
      D ∉ Set.range ((↑) : ℤ → ℝ) ∧ D' ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="res-signedwindow-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `signed_two_window_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_05/Challenge.lean#L169) (E251_05, line 169), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_05/PaperStatementsD.lean#L22) (PaperStatementsD.lean, line 22), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_05.json) (E251_05)
- `signed_two_window_consequences`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_05/Challenge.lean#L161) (E251_05, line 161), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_05/PaperStatementsD.lean#L14) (PaperStatementsD.lean, line 14), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_05.json) (E251_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-truncation"></a>

## Proposition 4.3 (finite separation criterion), page 9

> *If for every $`h\ge1`$ and every cutoff $`N_0`$ there are $`N\ge N_0,L\ge1`$ with
> ``` math
> \begin{equation}
> \label{eq:truncation}
>  \operatorname{dist}(S_{h,N,L},\mathbb{Z})>R_{h,N,L}(M),
> \end{equation}
> ```
> then $`\Pi`$ is irrational.*

The Lean declaration below states this result or one that implies it. The Lean statement assumes only $M(n)\ge g_n$ and convergence of the series $R_{h,N,L}(M)$ at the triples $(h,N,L)$ used; the printed standing assumption $\sum_{n\ge0}M(n)2^{-n}<\infty$ gives that convergence, and the conclusion is irrationality of $\Pi$.

[`ErdosProblems.Erdos251.PaperR7.irrational_prime_series_of_finite_truncation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperTailBoundsR7.lean#L273)

```lean
theorem irrational_prime_series_of_finite_truncation (M : ℕ → ℝ)
    (hM : ∀ n, (primeGap0 n : ℝ) ≤ M n)
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N L : ℕ,
      N₀ ≤ N ∧ 1 ≤ L ∧ Summable (majorantRemainderTerm M h N L) ∧
      majorantRemainder M h N L < integerDistance (signedWindow h N L)) :
    Irrational (∑' n : ℕ, primeDyadicTerm n)
```

<a id="res-truncation-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `irrational_prime_series_of_finite_truncation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_05/Challenge.lean#L196) (E251_05, line 196), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_05/PaperStatementsQ.lean#L20) (PaperStatementsQ.lean, line 20), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_05.json) (E251_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-irr-equivalence"></a>

## Corollary 6.1 (exact irrationality reformulation), page 10

> *The prime-value dyadic series is irrational if and only if the prime-gap dyadic series is. Both series converge by the polynomial bound proved above; neither side is proved irrational.*

The Lean declarations below together state this result or one that implies it. The second Lean statement gives the equivalence of irrationality of $\Pi$ and $G$, and the first gives convergence of both series; the Lean statements add the identity $\Pi=2+G$ and the same equivalence for $\sum_{n\ge0}p_n2^{-n}=4+2G$.

1. [`ErdosProblems.Erdos251.PaperR7.infinite_prime_gap_identity`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L47)

```lean
theorem infinite_prime_gap_identity :
    Summable primeDyadicTerm ∧ Summable primeGapDyadicTerm ∧
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n
```

2. [`ErdosProblems.Erdos251.PaperR7.irrationality_reformulation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L56)

```lean
theorem irrationality_reformulation :
    (Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)) ∧
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n ∧
    (Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n))
```

<a id="res-irr-equivalence-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `infinite_prime_gap_identity`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_01/Challenge.lean#L205) (E251_01, line 205), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_01/PaperStatementsG.lean#L44) (PaperStatementsG.lean, line 44), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_01.json) (E251_01)
- `irrationality_reformulation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_01/Challenge.lean#L211) (E251_01, line 211), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_01/PaperStatementsG.lean#L49) (PaperStatementsG.lean, line 49), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_01.json) (E251_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-gap-nonperiodic"></a>

## Proposition 6.2 (prime gaps do not become periodic), page 10

> *For every positive $`h`$, the actual consecutive-prime-gap sequence is not eventually periodic with period $`h`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.prime_gaps_not_eventually_periodic`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L175)

```lean
theorem prime_gaps_not_eventually_periodic {h : ℕ} (hh : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → primeGap0 (N + h) = primeGap0 N
```

<a id="res-gap-nonperiodic-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `prime_gaps_not_eventually_periodic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E251_02/Challenge.lean#L102) (E251_02, line 102), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E251_02/PaperStatementsG.lean#L68) (PaperStatementsG.lean, line 68), [replay report](../evidence/comparator/replay-35935225572/receipt-E251_02.json) (E251_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
