# Formal evidence: Prime-Gap Dyadic Series:\\Perturbations, Exact Criteria and Certificates

This record belongs to the paper [erdos251-prime-gap-reasoning-surface.pdf](../paper/251/erdos251-prime-gap-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`c91562bd574a`](https://github.com/wcook04/plectis-erdos/tree/c91562bd574a387cde904481e609c7b4cacebb14) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35882032091](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35882032091) at corpus commit [`a2faa350b45a`](https://github.com/wcook04/plectis-erdos-lean/tree/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3) (tag `paper-evidence-2026-09-23`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 36 results: 33 with a Lean proof of the whole statement, 3 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 32 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="long251-res-sparse-rationalisation"></a>

## Theorem 2.1 (sparse changes preserving congruences), page 3

> *Let $`a_n\in\mathbb{N}`$ and $`A=\sum_{n\ge0}a_n2^{-n-1}<\infty`$. For every cutoff $`K`$ and every $`f:\mathbb{N}\to\mathbb{R}`$ tending to infinity, there are a set $`S\subseteq[K,\infty)`$ of upper Banach density zero and a nondegenerate interval $`I\subset(A,\infty)`$ with the following property. Every $`r\in I`$ has the form
> ``` math
> r=\sum_{n\ge0}(a_n+e_n)2^{-n-1},
> ```
> where $`e_n\in\mathbb{N}`$ is supported on $`S`$, $`e_n\le f(n)`$ eventually, and, for every integer $`q\ge1`$, there is an $`N_q`$, chosen independently of $`r`$, such that
> ``` math
> q\mid e_n\quad\hbox{and}\quad q\mid\sum_{i<n}e_i
>  \qquad(n\ge N_q).
> ```
> For every $`\varepsilon>0`$, the construction can instead be chosen with $`e_n\le(\log(n+3))^\varepsilon`$ eventually and $`|S\cap[X,2X)|=O_\varepsilon(X/\log\log X)`$. In that case the empirical distributions of original and corrected unnormalised blocks of length $`m(X)=o(\log\log X)`$, sampled at the same integer starts in $`[X,2X)`$, have total variation distance tending to zero, uniformly over $`r`$. Precisely the coupling error is at most $`m|S\cap[X,2X+m)|/X`$; with $`\|\Phi\|_\infty\le B_0`$ the bounded-test error is at most twice this quantity times $`B_0`$, also for tests depending on the starting index.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos251.PaperR9.SparseAmbient.arbitrary_word_sparse_rationalisation_uniform`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/SparseAmbientR9.lean#L269)

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

2. [`ErdosProblems.Erdos251.PaperR11.SparsePaper.polylogarithmic_word_interval_uniform`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/SparsePaperR11.lean#L137)

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

3. [`ErdosProblems.Erdos251.PaperCompleteR20.bounded_test_finite_coupling`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR20/SparseConstructionAudit.lean#L8)

```lean
theorem bounded_test_finite_coupling {α : Type*} (a b : ℕ → α)
    (X m : ℕ) (S : Finset ℕ)
    (hS : ∀ N ∈ Ico X (2*X), ∀ i : Fin m,
      a (N+i.val) ≠ b (N+i.val) → N+i.val ∈ S)
    (B : ℝ) (hB : 0 ≤ B) (Φ : ℕ → (Fin m → α) → ℝ)
    (ha : ∀ N ∈ Ico X (2*X), |Φ N (fun i => a (N+i.val))| ≤ B)
    (hb : ∀ N ∈ Ico X (2*X), |Φ N (fun i => b (N+i.val))| ≤ B) :
    |testMean a X m Φ - testMean b X m Φ| ≤ 2*B*(m : ℝ)*S.card/X
```

<a id="long251-res-sparse-rationalisation-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `arbitrary_word_sparse_rationalisation_uniform` | [E251_01/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L113) | [UniformSparseRationalisation.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/UniformSparseRationalisation.lean#L50) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |
| `polylogarithmic_word_interval_uniform` | [E251_01/Challenge.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L87) | [UniformSparseRationalisation.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/UniformSparseRationalisation.lean#L20) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |
| `bounded_test_finite_coupling` | [E251_01/Challenge.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L51) | [PaperStatementsA.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/PaperStatementsA.lean#L20) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |

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

<a id="long251-res-local-targets"></a>

## Corollary 2.2 (target intervals arbitrarily close to the original sum), page 7

> *For the sparse theorem for an arbitrary sequence, the target interval can additionally be required to lie in $`(A,A+\eta)`$ for any prescribed $`\eta>0`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperCompleteR20.local_target_interval`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR20/LocalTargetInterval.lean#L38)

```lean
theorem local_target_interval (a : ℕ → ℕ) {A η : ℝ}
    (ha : HasSum (fun n => (a n : ℝ)/2^(n+1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) (hη : 0 < η) :
    ∃ start : ℕ, ∃ l u : ℝ, ∃ Nq : ℕ → ℕ,
      (Set.range (centre f start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre f start)) ∧
      A < l ∧ l < u ∧ u < A+η ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ Set.range (centre f start)) ∧
        (∀ n < K, a n+e n = a n) ∧
        (∀ᶠ n in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        HasSum (fun n => ((a n+e n : ℕ) : ℝ)/2^(n+1)) r
```

<a id="long251-res-local-targets-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `local_target_interval` | [E251_01/Challenge.lean, line 153](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L153) | [PaperStatementsI.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/PaperStatementsI.lean#L21) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-abel"></a>

## Proposition 4.1 (finite summation by parts), page 12

> *For every rational sequence $`P`$ and every $`n\ge0`$,
> ``` math
> \sum_{i=0}^{n}\frac{P(i)}{2^{\,i+1}}
>  =P(0)+\sum_{i=0}^{n-1}\frac{P(i+1)-P(i)}{2^{\,i+1}}
>        -\frac{P(n)}{2^{\,n+1}} .
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.dyadicPartialSumQ_eq_start_add_differences`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L138)

```lean
theorem dyadicPartialSumQ_eq_start_add_differences
    (P : ℕ → ℚ) (n : ℕ) :
    dyadicPartialSumQ P (n + 1) =
      P 0 + dyadicDifferencePartialSumQ P n - P n / 2 ^ (n + 1)
```

<a id="long251-res-abel-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `dyadicPartialSumQ_eq_start_add_differences` | [E251_01/Challenge.lean, line 232](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L232) | [PaperStatementsG.lean, line 135](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/PaperStatementsG.lean#L135) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-parts"></a>

## Theorem 4.2 (prime-gap reformulation), page 12

> *Let $`p_0=2,p_1=3,\ldots`$ be the primes in increasing order and $`g_i=p_{i+1}-p_i`$. For every $`n\ge0`$,
> ``` math
> \sum_{i=0}^{n}\frac{p_i}{2^{\,i+1}}
>  =2+\sum_{i=0}^{n-1}\frac{g_i}{2^{\,i+1}}-\frac{p_n}{2^{\,n+1}} .
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.prime0_dyadic_summation_by_parts`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L172)

```lean
theorem prime0_dyadic_summation_by_parts (n : ℕ) :
    dyadicPartialSumQ (fun i => (prime0 i : ℚ)) (n + 1) =
      2 + primeGapPartialSumQ n - (prime0 n : ℚ) / 2 ^ (n + 1)
```

<a id="long251-res-parts-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `prime0_dyadic_summation_by_parts` | [E251_01/Challenge.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L238) | [PaperStatementsG.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/PaperStatementsG.lean#L149) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-infinite"></a>

## Theorem 4.3 (infinite prime-gap identity), page 12

> *Both series converge and
> ``` math
> \sum_{n\ge0}\frac{p_n}{2^{\,n+1}}
>  \;=\;2+\sum_{n\ge0}\frac{g_n}{2^{\,n+1}} .
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.infinite_prime_gap_identity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L47)

```lean
theorem infinite_prime_gap_identity :
    Summable primeDyadicTerm ∧ Summable primeGapDyadicTerm ∧
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n
```

<a id="long251-res-infinite-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `infinite_prime_gap_identity` | [E251_01/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L205) | [PaperStatementsG.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/PaperStatementsG.lean#L44) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-irr-equivalence"></a>

## Corollary 4.4 (exact irrationality reformulation), page 13

> *<span id="res:irr-equivalence" label="res:irr-equivalence"></span> $`\Pi`$ is irrational if and only if $`S=\sum_{n\ge0}g_n2^{-(n+1)}`$ is irrational. The corresponding zero-based series with denominator $`2^n`$ equals $`4+2S`$ and has the same irrationality status.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.irrationality_reformulation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L56)

```lean
theorem irrationality_reformulation :
    (Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)) ∧
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n ∧
    (Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n))
```

<a id="long251-res-irr-equivalence-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrationality_reformulation` | [E251_01/Challenge.lean, line 211](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L211) | [PaperStatementsG.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/PaperStatementsG.lean#L49) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-block"></a>

## Theorem 5.2 (block identity), page 13

> *For every $`N`$ and $`h`$,
> ``` math
> T_{N+h}=2^{h}T_N-B_{h,N},
>  \qquad\text{hence}\qquad
>  \sigma_h(N)=(2^{h}-1)\,T_N-B_{h,N} .
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.real_block_identity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L76)

```lean
theorem real_block_identity {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h ∧
    realTailShift T h N = ((2 ^ h : ℝ) - 1) * T N - dyadicTailBlock g N h
```

<a id="long251-res-block-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `real_block_identity` | [E251_01/Challenge.lean, line 252](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L252) | [PaperStatementsH.lean, line 18](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/PaperStatementsH.lean#L18) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-escape-irrational"></a>

## Theorem 5.3 (exact rationality classification), page 14

> *Let $`T:\mathbb{N}\to\mathbb{R}`$ satisfy $`T_{N+1}=2T_N-g_{N+1}`$ with integer coefficients $`g`$. The following are equivalent:*
> 
> 1.  *$`T_0`$ is rational;*
> 
> 2.  *$`\sigma_h(N)`$ is an integer for some $`h\ge1`$ and some $`N`$;*
> 
> 3.  *for some fixed $`h\ge1`$, $`\sigma_h(N)`$ is an integer at every sufficiently large $`N`$.*
> 
> *Consequently $`T_0`$ is irrational if and only if every positive-length shift is nonintegral at every index, equivalently if and only if for every $`h\ge1`$ and every cutoff some later $`N`$ has $`\sigma_h(N)\notin\mathbb{Z}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.rationality_classification`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L94)

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

<a id="long251-res-escape-irrational-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rationality_classification` | [E251_01/Challenge.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L220) | [PaperStatementsG.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/PaperStatementsG.lean#L91) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-true-tail"></a>

## Lemma 5.4 (the boundary condition identifying a true tail), page 15

> *Let $`a_1,a_2,\ldots`$ be real numbers with $`\sum_{j\ge1}|a_j|2^{-j}<\infty`$, and let $`U_{N+1}=2U_N-a_{N+1}`$. Then
> ``` math
> U_N=\sum_{j\ge1}a_{N+j}2^{-j}\quad\hbox{for every }N
>  \quad\Longleftrightarrow\quad 2^{-N}U_N\longrightarrow0.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperCompleteR20.real_dyadic_orbit_eq_true_tail_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR20/TrueTail.lean#L57)

```lean
theorem real_dyadic_orbit_eq_true_tail_iff (a U : ℕ → ℝ)
    (habs : Summable (fun j : ℕ => |a (j + 1)| / (2 : ℝ) ^ (j + 1)))
    (hrec : ∀ N, U (N + 1) = 2 * U N - a (N + 1)) :
    (∀ N, U N = realDyadicTail a N) ↔
      Tendsto (fun N : ℕ => U N / 2 ^ N) atTop (𝓝 0)
```

<a id="long251-res-true-tail-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `real_dyadic_orbit_eq_true_tail_iff` | [E251_01/Challenge.lean, line 268](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_01/Challenge.lean#L268) | [PaperStatementsC.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_01/PaperStatementsC.lean#L19) | [E251_01](../evidence/comparator/replay-35882032091/receipt-E251_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-freepair"></a>

## Theorem 5.5 (pairs of congruent indices), page 15

> *$`S`$ is irrational if and only if for every $`t\ge1`$ and every $`N_0`$ there are $`N,M\ge N_0`$ with $`M\equiv N\pmod t`$ and $`T_M-T_N\notin\mathbb{Z}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.actual_free_pair_criterion`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L189)

```lean
theorem actual_free_pair_criterion :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral realPrimeGapTail
```

<a id="long251-res-freepair-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `actual_free_pair_criterion` | [E251_02/Challenge.lean, line 66](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L66) | [PaperStatementsL.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsL.lean#L20) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-lcmdiagonal"></a>

## Theorem 5.6 ([criterion using least common multiples](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/OrderLatticeDiagonal.lean#L153)), page 16

> *Let $`g:\mathbb{N}\to\mathbb{Z}`$ and $`T:\mathbb{N}\to\mathbb{R}`$ satisfy $`T_{N+1}=2T_N-g_{N+1}`$. Then $`T_0`$ is irrational if and only if $`T_{2L_j}-T_{L_j}\notin\mathbb{Z}`$ for every $`j\ge0`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.irrational_initial_iff_all_lcmDiagonal_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/OrderLatticeDiagonal.lean#L153)

```lean
theorem irrational_initial_iff_all_lcmDiagonal_nonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral
          (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j))
```

<a id="long251-res-lcmdiagonal-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_initial_iff_all_lcmDiagonal_nonintegral` | [E251_02/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L80) | [PaperStatementsM.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsM.lean#L73) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-smallpair"></a>

## Theorem 6.1 (adjacent small-shift obstruction), page 16

> *Let $`T`$ satisfy the dyadic tail recurrence with integer coefficients $`g`$, and fix $`h`$ and $`N`$. If
> ``` math
> -1<\sigma_h(N)<1,\qquad -1<\sigma_h(N+1)<1,
>  \qquad g_{N+h+1}\ne g_{N+1},
> ```
> then $`\sigma_h(N)`$ and $`\sigma_h(N+1)`$ cannot both be integers. Consequently, if such a pair occurs beyond every threshold, the $`h`$-shift is not eventually integral.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.rational_small_pair_bundle`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L267)

```lean
theorem rational_small_pair_bundle {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ) :
    (∀ N, ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
      (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) →
      g (N + h + 1) ≠ g (N + 1) →
      ¬ (RatIntegral (tailShift T h N) ∧ RatIntegral (tailShift T h (N + 1)))) ∧
    ((∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
       (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) →
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))
```

<a id="long251-res-smallpair-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rational_small_pair_bundle` | [E251_02/Challenge.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L115) | [PaperStatementsG.lean, line 79](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsG.lean#L79) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-smallpair-real"></a>

## Corollary 6.2 (real form and the sufficient condition), page 17

> *The same statement holds for a real orbit, with the same proof. If for every $`h\ge1`$ and every cutoff some later $`N`$ satisfies the three displayed conditions for the actual prime gaps, then $`\Pi`$ is irrational.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.real_small_pair_prime_endpoint`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L298)

```lean
theorem real_small_pair_prime_endpoint {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h : ℕ) :
    (∀ N, ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
      (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) →
      g (N + h + 1) ≠ g (N + 1) →
      ¬ (RealIntegral (realTailShift T h N) ∧ RealIntegral (realTailShift T h (N + 1)))) ∧
    ((∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
       (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) →
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N)) ∧
    ((∀ h' : ℕ, 0 < h' → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ((-1 < realTailShift realPrimeGapTail h' N ∧
        realTailShift realPrimeGapTail h' N < 1) ∧
       (-1 < realTailShift realPrimeGapTail h' (N + 1) ∧
        realTailShift realPrimeGapTail h' (N + 1) < 1)) ∧
      primeGap0 (N + h' + 1) ≠ primeGap0 (N + 1)) →
      Irrational (∑' n : ℕ, primeDyadicTerm n))
```

<a id="long251-res-smallpair-real-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `real_small_pair_prime_endpoint` | [E251_02/Challenge.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L140) | [PaperStatementsG.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsG.lean#L113) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-gap-nonperiodic"></a>

## Proposition 6.3 (prime gaps do not become periodic), page 17

> *<span id="res:gap-nonperiodic" label="res:gap-nonperiodic"></span> For every positive $`h`$, the actual consecutive-prime-gap sequence is not eventually periodic with period $`h`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.prime_gaps_not_eventually_periodic`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L175)

```lean
theorem prime_gaps_not_eventually_periodic {h : ℕ} (hh : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → primeGap0 (N + h) = primeGap0 N
```

<a id="long251-res-gap-nonperiodic-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `prime_gaps_not_eventually_periodic` | [E251_02/Challenge.lean, line 102](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L102) | [PaperStatementsG.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsG.lean#L68) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-signedwindow"></a>

## Theorem 6.4 ([an equivalent signed interval test](https://github.com/wcook04/plectis-erdos/blob/3d6d938d696fed0fb71dd55115a18a73738ff223/lean/ErdosProblems/Erdos251/AffineShiftEscape.lean#L113)), page 17

> *Assume $`\delta_N`$ is even. The conjunction $`-1<D_N<1`$, $`-1<D_{N+1}<1`$, $`\delta_N\ne0`$ is equivalent to
> ``` math
> \bigl(\delta_N=2\ \hbox{ and }\tfrac12<D_N<1\bigr)
>  \quad\hbox{or}\quad
>  \bigl(\delta_N=-2\ \hbox{ and }-1<D_N<-\tfrac12\bigr).
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.real_signed_two_window`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L135)

```lean
theorem real_signed_two_window {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (-1 < realTailShift T h N ∧ realTailShift T h N < 1 ∧
      -1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1 ∧
      g (N + h + 1) ≠ g (N + 1)) ↔
    ((g (N + h + 1) - g (N + 1) = 2 ∧
       1 / 2 < realTailShift T h N ∧ realTailShift T h N < 1) ∨
     (g (N + h + 1) - g (N + 1) = -2 ∧
       -1 < realTailShift T h N ∧ realTailShift T h N < -(1 / 2)))
```

<a id="long251-res-signedwindow-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `real_signed_two_window` | [E251_02/Challenge.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L128) | [PaperStatementsG.lean, line 102](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsG.lean#L102) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-explicit-remainder"></a>

## Proposition 6.5 (explicit remainder), page 17

> *For integers $`h,N\ge0`$ and $`L\ge1`$ put
> ``` math
> F_{h,N,L}=\sum_{j=1}^{L}\frac{g_{N+h+j}-g_{N+j}}{2^{\,j}},\qquad
>  P(x)=x^4+8x^3+36x^2+104x+150,
> ```
> ``` math
> E_{h,N,L}=\frac{1250}{2^{L}}\bigl(P(N+h+L+2)+P(N+L+2)\bigr).
> ```
> Then $`\bigl|\sigma_h(N)-F_{h,N,L}\bigr|\le E_{h,N,L}`$. In particular $`|F_{h,N,L}|+E_{h,N,L}<1`$ certifies $`|\sigma_h(N)|<1`$, and $`\operatorname{dist}(F_{h,N,L},\mathbb{Z})>E_{h,N,L}`$ certifies $`\sigma_h(N)\notin\mathbb{Z}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.explicit_remainder_certificate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperTailBoundsR7.lean#L211)

```lean
theorem explicit_remainder_certificate (h N L : ℕ) :
    |realTailShift realPrimeGapTail h N - signedWindow h N L| ≤ explicitRemainder h N L ∧
    (|signedWindow h N L| + explicitRemainder h N L < 1 →
      |realTailShift realPrimeGapTail h N| < 1) ∧
    (explicitRemainder h N L < integerDistance (signedWindow h N L) →
      ¬ RealIntegral (realTailShift realPrimeGapTail h N))
```

<a id="long251-res-explicit-remainder-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `explicit_remainder_certificate` | [E251_02/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L181) | [PaperStatementsO.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsO.lean#L21) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-finite-smallpair"></a>

## Proposition 6.6 (a certified adjacent pair), page 18

> *For the actual prime gaps, $`h=1`$ and $`N=2`$ satisfy the three hypotheses of Theorem 6.1: both $`\sigma_1(2)`$ and $`\sigma_1(3)`$ lie in $`(-1,1)`$ and are nonintegral, and $`g_4=2\ne4=g_3`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.finite_small_pair`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperFiniteCertificatesR7.lean#L111)

```lean
theorem finite_small_pair :
    (-1 < realTailShift realPrimeGapTail 1 2 ∧
      realTailShift realPrimeGapTail 1 2 < 1) ∧
    (-1 < realTailShift realPrimeGapTail 1 3 ∧
      realTailShift realPrimeGapTail 1 3 < 1) ∧
    ¬ RealIntegral (realTailShift realPrimeGapTail 1 2) ∧
    ¬ RealIntegral (realTailShift realPrimeGapTail 1 3) ∧
    primeGap0 4 = 2 ∧ primeGap0 3 = 4
```

<a id="long251-res-finite-smallpair-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `finite_small_pair` | [E251_02/Challenge.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L195) | [PaperStatementsP.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsP.lean#L20) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-one-tail-certificate"></a>

## Proposition 6.7 (a one-tail signed certificate), page 18

> *Let $`D_{N+1}=2D_N-\delta_N`$ with real $`D_N`$, and suppose $`\delta_N=2s`$ for $`s\in\{-1,1\}`$. If integers $`A,B,Q`$ satisfy $`Q>0`$, $`B\ge0`$, $`|QD_N-A|\le B`$, and
> ``` math
> 2sA-Q>2B,\qquad Q-sA>B,
> ```
> then $`1/2<sD_N<1`$, $`|D_{N+1}|<1`$, and both $`D_N,D_{N+1}`$ are nonintegral. In particular the adjacent small-shift obstruction is certified from just one tail enclosure.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperCompleteR20.one_tail_signed_certificate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR20/FiniteSeparation.lean#L6)

```lean
theorem one_tail_signed_certificate (D D' : ℝ) (s A B Q : ℤ)
    (hs : s = -1 ∨ s = 1) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hstep : D' = 2 * D - (2 * s : ℤ))
    (herr : |(Q : ℝ) * D - A| ≤ B)
    (hlo : 2 * s * A - Q > 2 * B) (hhi : Q - s * A > B) :
    ((1/2 : ℝ) < (s : ℝ)*D ∧ (s : ℝ)*D < 1) ∧ |D'| < 1 ∧
      D ∉ Set.range ((↑) : ℤ → ℝ) ∧ D' ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="long251-res-one-tail-certificate-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `one_tail_signed_certificate` | [E251_02/Challenge.lean, line 210](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L210) | [PaperStatementsB.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsB.lean#L23) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-denominatorfloor"></a>

## Theorem 7.1 (a denominator bound checked by exact integer comparisons), page 19

> *Let $`a\in\mathbb{Z}`$ and let $`b`$ be a positive integer. If $`\Pi=a/b`$ then $`b\ge2^{589}>10^{177}`$, and the same floor holds for every rational equal to $`S`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos251.PaperR7.denominator_floor_both`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperFiniteCertificatesR7.lean#L142)

```lean
theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ((∑' n, primeDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) ∧
    ((∑' n, primeGapDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b)
```

2. [`ErdosProblems.Erdos251.PaperR7.denominator_floor_decimal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperFiniteCertificatesR7.lean#L137)

```lean
theorem denominator_floor_decimal : (10 ^ 177 : ℕ) < 2 ^ 589
```

<a id="long251-res-denominatorfloor-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `denominator_floor_both` | [E251_02/Challenge.lean, line 225](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L225) | [ExactDenominatorFloors.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/ExactDenominatorFloors.lean#L19) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |
| `denominator_floor_decimal` | [E251_02/Challenge.lean, line 235](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L235) | [PaperStatementsF.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsF.lean#L27) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-cfexclusion"></a>

## Theorem 7.2 (certified continued-fraction exclusion), page 19

> *Every rational equal to $`\Pi`$, and hence every rational equal to $`S`$, has reduced denominator $`q\ge2^{39997}`$, and therefore $`q>10^{12040}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.LargeCertificate.denominator_floor_both`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/verification/Erdos251LargeCertificate/ErdosProblems/Erdos251/PaperLargeCertificateR7.lean#L29)

```lean
theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b)
    (hS : (∑' n, primeDyadicTerm n) = a / b ∨
      (∑' n, primeGapDyadicTerm n) = a / b) :
    2 ^ 39997 ≤ b ∧ 10 ^ 12040 < b
```

<a id="long251-res-cfexclusion-comparator"></a>

**Comparator:** not yet compared.

<a id="long251-res-boundedperturbation"></a>

## Theorem 8.1 (bounded-perturbation obstruction), page 21

> *Let $`a_n`$ be natural numbers with $`\sum_{n\ge0}a_n2^{-(n+1)}`$ convergent. For every integer $`M\ge1`$ and every cutoff $`K`$ there are digits $`\varepsilon_n\in\{0,1\}`$, zero for $`n<K`$, such that $`\sum_{n\ge0}(a_n+M\varepsilon_n)2^{-(n+1)}`$ is rational.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.rational_bounded_perturbation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L200)

```lean
theorem rational_bounded_perturbation {a : ℕ → ℕ}
    (ha : Summable (fun n => (a n : ℝ) / 2 ^ (n + 1)))
    (M K : ℕ) (hM : 0 < M) :
    ∃ (δ : ℕ → ℕ) (r : ℚ),
      (∀ n, δ n = 0 ∨ δ n = 1) ∧
      (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((a n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ)
```

<a id="long251-res-boundedperturbation-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rational_bounded_perturbation` | [E251_02/Challenge.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_02/Challenge.lean#L106) | [PaperStatementsG.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_02/PaperStatementsG.lean#L71) | [E251_02](../evidence/comparator/replay-35882032091/receipt-E251_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-shiftedcount"></a>

## Proposition 8.2 (finite counting for shifted gap differences), page 22

> *Write $`p_n`$ for the primes indexed from $`p_0=2`$ and $`g_n=p_{n+1}-p_n`$. For $`h\ge2`$ and $`r\in\mathbb{Z}`$, let $`M_{h,r}(N)`$ count $`n<N`$ with $`g_{n+h}-g_n=r`$. Let $`Q_{N,H,r}`$ count triples $`(x,d,s)`$ with $`x<p_N`$, $`0<d<s\le H`$, $`d+r>0`$, and all four integers $`x,x+d,x+s,x+s+d+r`$ prime. Then, for every $`N,H\ge0`$,
> ``` math
> (H+1)M_{h,r}(N)\le
>  (h+1)p_{N+h+1}+(H+1)Q_{N,H,r}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR9.ShiftCounting.shifted_count_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/ShiftedGapCountingR9.lean#L152)

```lean
theorem shifted_count_bound (h N H : ℕ) (hh : 2 ≤ h) (r : ℤ) :
    (H + 1) * (shiftedMatches h N r).card ≤
      (h + 1) * prime0 (N + (h + 1)) + (H + 1) * (quadCandidates N H r).card
```

<a id="long251-res-shiftedcount-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `shifted_count_bound` | [E251_03/Challenge.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_03/Challenge.lean#L64) | [PaperStatementsR.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_03/PaperStatementsR.lean#L21) | [E251_03](../evidence/comparator/replay-35882032091/receipt-E251_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-nonconcentration"></a>

## Theorem 8.3 (nonconcentration is perturbation-stable), page 22

> *Let $`a:\mathbb{N}\to\mathbb{Z}`$ have fixed-block nonconcentration, let $`E\subset\mathbb{Z}`$ be finite, and let $`b_n=a_n+e_n`$ with $`e_n\in E`$ for every $`n`$. Then $`b`$ has fixed-block nonconcentration.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.finite_perturbation_stability`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperNonconcentrationR7.lean#L100)

```lean
theorem finite_perturbation_stability
    (a b : ℕ → ℤ) (E : Finset ℤ)
    (ha : FixedBlockNonconcentration a)
    (hE : ∀ n, b n - a n ∈ E) :
    FixedBlockNonconcentration b
```

where [`FixedBlockNonconcentration`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperNonconcentrationR7.lean#L30) is

```lean
def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}
```

<a id="long251-res-nonconcentration-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `finite_perturbation_stability` | [E251_03/Challenge.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_03/Challenge.lean#L75) | [PaperStatementsF.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_03/PaperStatementsF.lean#L21) | [E251_03](../evidence/comparator/replay-35882032091/receipt-E251_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-nonconc-primes"></a>

## Corollary 8.4 (nonconcentration does not force irrationality), page 23

> *Fix $`M\ge1`$ and $`K\ge0`$, and let $`b`$ be the perturbed sequence supplied by Theorem 8.1 at the actual prime gaps. Then $`\sum_{n\ge0}b_n2^{-(n+1)}`$ is rational, $`b_n=g_n`$ for $`n<K`$, $`b_n-g_n\in\{0,M\}`$ and $`b_n\equiv g_n\pmod M`$ for every $`n`$, $`b`$ has fixed-block nonconcentration, and the cumulative sequence $`P_n=2+\sum_{i<n}b_i`$ satisfies $`p_n\le P_n\le p_n+Mn`$ and hence $`P_n\sim n\log n`$.*

The Lean proof assumes Schlage-Puchta's density lemma and the prime number theorem. Lean takes this input as a hypothesis (`PrimeNumberTheorem`, `SchlagePuchtaLemma4`); it is not proved in Lean.

1. [`ErdosProblems.Erdos251.PaperCompleteR21.nonconcentration_does_not_force_irrationality`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR21/PerturbedPrimePositions.lean#L126)

```lean
theorem nonconcentration_does_not_force_irrationality
    (M : ℕ) (hM : 0 < M) (K : ℕ)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ)))
    (hPNT : Tendsto (fun n : ℕ => (prime0 n : ℝ) / ((n : ℝ) * Real.log n))
      atTop (𝓝 1)) :
    ∃ (b : ℕ → ℕ) (q : ℚ),
      HasSum (fun n => (b n : ℝ) / 2 ^ (n + 1)) (q : ℝ) ∧
      (∀ n < K, b n = primeGap0 n) ∧
      (∀ n, (b n : ℤ) - primeGap0 n = 0 ∨ (b n : ℤ) - primeGap0 n = (M : ℤ)) ∧
      (∀ n, primeGap0 n ≤ b n) ∧
      (∀ n, b n % M = primeGap0 n % M) ∧
      FixedBlockNonconcentration (fun n => (b n : ℤ)) ∧
      (∀ n, prime0 n ≤ 2 + ∑ i ∈ range n, b i) ∧
      (∀ n, 2 + ∑ i ∈ range n, b i ≤ prime0 n + M * n) ∧
      Tendsto (fun n : ℕ => ((2 + ∑ i ∈ range n, b i : ℕ) : ℝ) / ((n : ℝ) * Real.log n))
        atTop (𝓝 1)
```

2. [`ErdosProblems.Erdos251.PaperCompleteR21.perturbed_position_bounds`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR21/PerturbedPrimePositions.lean#L67)

```lean
theorem perturbed_position_bounds (M : ℕ) (δ : ℕ → ℕ) (hδ : ∀ n, δ n ≤ 1) (n : ℕ) :
    prime0 n ≤ 2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) ∧
      2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) ≤ prime0 n + M * n
```

3. [`ErdosProblems.Erdos251.PaperCompleteR21.sum_range_primeGap0`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR21/PerturbedPrimePositions.lean#L45)

```lean
theorem sum_range_primeGap0 (n : ℕ) :
    ∑ i ∈ range n, primeGap0 i = prime0 n - 2
```

4. [`ErdosProblems.Erdos251.PaperCompleteR21.perturbed_position_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR21/PerturbedPrimePositions.lean#L59)

```lean
theorem perturbed_position_eq (M : ℕ) (δ : ℕ → ℕ) (n : ℕ) :
    2 + ∑ i ∈ range n, (primeGap0 i + M * δ i) =
      prime0 n + M * ∑ i ∈ range n, δ i
```

5. [`ErdosProblems.Erdos251.PaperCompleteR21.position_asymptotic_of_prime_asymptotic`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR21/PerturbedPrimePositions.lean#L90)

```lean
theorem position_asymptotic_of_prime_asymptotic
    (P p : ℕ → ℝ) (M : ℝ)
    (hle : ∀ n, p n ≤ P n) (hge : ∀ n, P n ≤ p n + M * n)
    (hp : Tendsto (fun n : ℕ => p n / ((n : ℝ) * Real.log n)) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => P n / ((n : ℝ) * Real.log n)) atTop (𝓝 1)
```

The assumed input [`PrimeNumberTheorem`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L28) is

```lean
def PrimeNumberTheorem : Prop :=
  Tendsto (fun n => (prime0 n : ℝ) / scale n) atTop (𝓝 1)
```

The assumed input [`SchlagePuchtaLemma4`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L22) is

```lean
def SchlagePuchtaLemma4 : Prop :=
  ∀ k : ℕ, ∀ F : MvPolynomial (Fin (k + 1)) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval
      (fun i : Fin (k + 1) => (primeGap0 (n + i.val) : ℤ)) F = 0}
```

<a id="long251-res-nonconc-primes-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="long251-res-sparse-nonconcentration"></a>

## Proposition 8.5 (nonconcentration under sparse changes), page 23

> *Let $`a,b:\mathbb{N}\to\mathbb{Z}`$ agree off a set $`S`$ of ordinary density zero. If $`a`$ has fixed-block nonconcentration, then so does $`b`$. No boundedness assumption on $`a-b`$ is needed.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperCompleteR20.sparse_nonconcentration`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR20/SparseNonconcentration.lean#L80)

```lean
theorem sparse_nonconcentration (a b : ℕ → ℤ) (S : Set ℕ)
    (hS : ZeroDensity S) (hab : ∀ n, n ∉ S → a n = b n)
    (ha : FixedBlockNonconcentration a) : FixedBlockNonconcentration b
```

<a id="long251-res-sparse-nonconcentration-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `sparse_nonconcentration` | [E251_03/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_03/Challenge.lean#L117) | [PaperStatementsK.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_03/PaperStatementsK.lean#L21) | [E251_03](../evidence/comparator/replay-35882032091/receipt-E251_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-jointcountermodel"></a>

## Corollary 8.6 (simultaneous prime-gap countermodel), page 24

> *For every prescribed finite prime-gap prefix and $`0<\varepsilon\le1`$, there is an altered sequence $`b=g+e`$, with $`P_n=2+\sum_{i<n}b_i`$, for which one can simultaneously impose a rational dyadic value, nonnegative integer corrections eventually at most $`(\log(n+3))^\varepsilon`$, all fixed eventual coefficient and cumulative congruences, fixed-block polynomial nonconcentration, and vanishing total variation distance between unnormalised block distributions for lengths $`o(\log\log X)`$. The cumulative positions satisfy
> ``` math
> 0\le P_n-p_n=O_\varepsilon\left(
>     \frac{n(\log(n+3))^\varepsilon}{\log\log n}\right),
>  \qquad P_n\sim n\log n.
> ```*

The Lean proof assumes Schlage-Puchta's density lemma and the prime number theorem. Lean takes this input as a hypothesis (`PrimeNumberTheorem`, `SchlagePuchtaLemma4`); it is not proved in Lean.

1. [`ErdosProblems.Erdos251.PaperCompleteR21.long_joint_prime_gap_countermodel`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR21/JointPrimeGapCountermodel.lean#L256)

```lean
theorem long_joint_prime_gap_countermodel
    (hSP : SchlagePuchtaLemma4) (hPNT : PrimeNumberTheorem)
    (K : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ e : ℕ → ℕ, ∃ r : ℚ, ∃ C : ℝ, 0 < C ∧
      (∀ n, n < K → e n = 0) ∧
      HasSum (fun n => ((primeGap0 n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
        primeGap0 n + e n ≡ primeGap0 n [MOD q] ∧
        cumulative (fun i => primeGap0 i + e i) n ≡ prime0 n [MOD q]) ∧
      FixedBlockNonconcentration (fun n => ((primeGap0 n + e n : ℕ) : ℤ)) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        Tendsto (fun X =>
          blockTV primeGap0 (fun n => primeGap0 n + e n) X (m X)) atTop (𝓝 0)) ∧
      (∀ n, prime0 n ≤ cumulative (fun i => primeGap0 i + e i) n) ∧
      (∀ᶠ n : ℕ in atTop,
        (cumulative (fun i => primeGap0 i + e i) n : ℝ) - prime0 n
          ≤ C * ((n : ℝ) * polylog ε n / Real.log (Real.log (n : ℝ)))) ∧
      Tendsto (fun n =>
        (cumulative (fun i => primeGap0 i + e i) n : ℝ) / scale n) atTop (𝓝 1)
```

2. [`ErdosProblems.Erdos251.PaperCompleteR21.cut_prefix_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR21/JointPrimeGapCountermodel.lean#L228)

```lean
theorem cut_prefix_bound {α : ℝ} (hα : 0 < α) (start : ℕ)
    (hc : StrictMono (centre (polylog α) start)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ((cut (centre (polylog α) start) hc n : ℕ) : ℝ) ≤ C * n / iterlog n
```

The assumed input [`PrimeNumberTheorem`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L28) is

```lean
def PrimeNumberTheorem : Prop :=
  Tendsto (fun n => (prime0 n : ℝ) / scale n) atTop (𝓝 1)
```

The assumed input [`SchlagePuchtaLemma4`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L22) is

```lean
def SchlagePuchtaLemma4 : Prop :=
  ∀ k : ℕ, ∀ F : MvPolynomial (Fin (k + 1)) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval
      (fun i : Fin (k + 1) => (primeGap0 (n + i.val) : ℤ)) F = 0}
```

<a id="long251-res-jointcountermodel-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="long251-res-sparse"></a>

## Theorem 8.7 (sparsity of the two-window event), page 25

> *Fix $`h\ge1`$. The set of $`N\ge1`$ at which the three hypotheses of Theorem 6.1 hold for the actual prime gaps has density zero. For the same $`h`$, the set of $`N`$ with $`g_{N+h+1}=g_{N+1}`$ also has density zero.*

The Lean proof assumes Schlage-Puchta's density lemma. Lean takes this input as a hypothesis (`SchlagePuchtaLemma4`); it is not proved in Lean.

1. [`ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_two_window_sparse`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR21/TwoWindowSparsity.lean#L38)

```lean
theorem prime_gap_two_window_sparse (h : ℕ) (hh : 0 < h)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))) :
    ZeroDensity {N | 1 ≤ N ∧
        (-1 < shift realPrimeGapTail h N ∧ shift realPrimeGapTail h N < 1) ∧
        (-1 < shift realPrimeGapTail h (N + 1) ∧
          shift realPrimeGapTail h (N + 1) < 1) ∧
        (primeGap0 (N + h + 1) : ℤ) ≠ (primeGap0 (N + 1) : ℤ)} ∧
      ZeroDensity {N | (primeGap0 (N + h + 1) : ℤ) = (primeGap0 (N + 1) : ℤ)}
```

2. [`ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_equal_shift_zeroDensity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR21/TwoWindowSparsity.lean#L50)

```lean
theorem prime_gap_equal_shift_zeroDensity (h : ℕ) (hh : 0 < h)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))) :
    ZeroDensity {N | primeGap0 (N + h + 1) = primeGap0 (N + 1)}
```

3. [`ErdosProblems.Erdos251.PaperCompleteR21.primeGap_tail_recurrence`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR21/TwoWindowSparsity.lean#L30)

```lean
theorem primeGap_tail_recurrence :
    Recurrence (fun n => (primeGap0 n : ℤ)) realPrimeGapTail
```

The assumed input [`SchlagePuchtaLemma4`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/ActualPrimePaperR11.lean#L22) is

```lean
def SchlagePuchtaLemma4 : Prop :=
  ∀ k : ℕ, ∀ F : MvPolynomial (Fin (k + 1)) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval
      (fun i : Fin (k + 1) => (primeGap0 (n + i.val) : ℤ)) F = 0}
```

<a id="long251-res-sparse-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="long251-res-polignacfail"></a>

## Theorem 8.8 (recurring values are not enough), page 26

> *There is a sequence $`(a_n)_{n\ge1}`$ of positive even integers with the following properties. The values $`2`$ and $`4`$ each occur infinitely often at indices divisible by every fixed $`t\ge1`$. The sequence is unbounded, not eventually periodic, and satisfies $`a_n=O(\log n)`$. The series $`\sum_{n\ge1}a_n2^{-n}`$ equals $`6`$, and every scaled tail $`\sum_{j\ge1}a_{N+j}2^{-j}`$ is an integer, so every tail shift is integral. The increasing odd sequence $`P_n=3+\sum_{j\le n}a_j`$ satisfies $`P_n\sim n\log n`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR8.LogCarry.exists_logarithmic_recurring_values_countermodel`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/LogarithmicCarryAsymptoticsR8.lean#L368)

```lean
theorem exists_logarithmic_recurring_values_countermodel :
    ∃ a U : ℕ → ℤ,
      let P : ℕ → ℤ := fun n => 3 + ∑ j ∈ range n, a (j + 1);
      (∀ n, 1 ≤ n → 0 < a n ∧ (2 : ℤ) ∣ a n) ∧
      (∀ t, 0 < t → ∀ N, ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧ a i = 2 ∧ a j = 4) ∧
      (∀ B : ℤ, ∀ N : ℕ, ∃ n, N ≤ n ∧ B < a n) ∧
      (∀ h : ℕ, 0 < h → ¬ ∃ N₀, ∀ n, N₀ ≤ n → a (n + h) = a n) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → (a n : ℝ) ≤ C * Real.log (n : ℝ)) ∧
      HasSum (fun j : ℕ => (a (j + 1) : ℝ) / 2 ^ (j + 1)) 6 ∧
      (∀ N, HasSum (fun j : ℕ => (a (N + j + 1) : ℝ) / 2 ^ (j + 1)) (U N : ℝ)) ∧
      (∀ N h, ∃ z : ℤ,
        (∑' j : ℕ, (a (N + h + j + 1) : ℝ) / 2 ^ (j + 1)) -
        (∑' j : ℕ, (a (N + j + 1) : ℝ) / 2 ^ (j + 1)) = z) ∧
      StrictMono P ∧ (∀ n, ∃ z : ℤ, P n = 2 * z + 1) ∧
      Tendsto (fun n : ℕ => (P n : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 1)
```

<a id="long251-res-polignacfail-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_logarithmic_recurring_values_countermodel` | [E251_03/Challenge.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_03/Challenge.lean#L219) | [PaperStatementsA.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_03/PaperStatementsA.lean#L34) | [E251_03](../evidence/comparator/replay-35882032091/receipt-E251_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-polynomialcountermodel"></a>

## Proposition 8.9 (quadratic polynomial-shift countermodel), page 28

> *Put $`c_n=2(n^2+4n+2)`$ and $`U_n=2(n+4)^2`$. Then $`c_n`$ is positive, even and strictly increasing, $`U_{n+1}=2U_n-c_{n+1}`$, every shift $`U_{N+h}-U_N`$ is integral, $`c_{n+1}-c_n=4n+10`$ is never $`\pm2`$, and
> ``` math
> \sum_{j\ge1}\frac{c_j}{2^{\,j}}=32 .
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.polynomial_countermodel`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L27)

```lean
theorem polynomial_countermodel :
    (∀ n, 0 < polynomialGapWord n) ∧
    (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧
    StrictMono polynomialGapWord ∧
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧
    (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧
    (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n = 4 * (n : ℤ) + 10) ∧
    (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 ∧
      polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2) ∧
    HasSum (fun n : ℕ => (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)) 32
```

<a id="long251-res-polynomialcountermodel-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `polynomial_countermodel` | [E251_03/Challenge.lean, line 261](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_03/Challenge.lean#L261) | [PaperStatementsG.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_03/PaperStatementsG.lean#L72) | [E251_03](../evidence/comparator/replay-35882032091/receipt-E251_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-telescope"></a>

## Proposition 8.10 (exact telescoping), page 29

> *For every $`n\ge0`$, $`\sum_{i=0}^{n-1}\kappa_i2^{-(i+1)}=K_0-K_n2^{-n}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.carryPartialSum_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1137)

```lean
theorem carryPartialSum_eq (K : ℕ → ℚ) (n : ℕ) :
    carryPartialSum K n = K 0 - K n / 2 ^ n
```

<a id="long251-res-telescope-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `carryPartialSum_eq` | [E251_03/Challenge.lean, line 273](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_03/Challenge.lean#L273) | [PaperStatementsG.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_03/PaperStatementsG.lean#L147) | [E251_03](../evidence/comparator/replay-35882032091/receipt-E251_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-xr-totient"></a>

## Proposition D.1 (a shift of totient length), page 34

> *Let $`T:\mathbb{N}\to\mathbb{Q}`$ satisfy the dyadic tail recurrence with integer coefficients. If the reduced denominator $`d`$ of $`T_N`$ is odd, then $`\sigma_{\varphi(d)}(N)`$ is an integer.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.tailShift_integral_totient_of_odd_den`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L877)

```lean
theorem tailShift_integral_totient_of_odd_den
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ)
    (hodd : Odd (T N).den) :
    RatIntegral (tailShift T (T N).den.totient N)
```

<a id="long251-xr-totient-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tailShift_integral_totient_of_odd_den` | [E251_04/Challenge.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_04/Challenge.lean#L47) | [PaperStatementsG.lean, line 191](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_04/PaperStatementsG.lean#L191) | [E251_04](../evidence/comparator/replay-35882032091/receipt-E251_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-xr-propagate"></a>

## Proposition D.2 (propagation), page 34

> *Let $`T:\mathbb{N}\to\mathbb{R}`$ satisfy $`T_{n+1}=2T_n-a_{n+1}`$ with integer coefficients, and define $`\sigma_h(N)=T_{N+h}-T_N`$. For fixed $`h,N\ge0`$, if $`\sigma_h(N)`$ is an integer, then $`\sigma_h(N+k)`$ is an integer for every $`k\ge0`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperCompleteR20.realTailShift_integral_add`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR20/RealPropagation.lean#L27)

```lean
theorem realTailShift_integral_add
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (hInt : RealIntegral (realTailShift T h N)) :
    ∀ k : ℕ, RealIntegral (realTailShift T h (N + k))
```

<a id="long251-xr-propagate-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `realTailShift_integral_add` | [E251_04/Challenge.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_04/Challenge.lean#L77) | [PaperStatementsM.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_04/PaperStatementsM.lean#L26) | [E251_04](../evidence/comparator/replay-35882032091/receipt-E251_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-xr-truncation"></a>

## Proposition D.3 (finite truncation), page 35

> *Let $`M:\mathbb{N}\to\mathbb{R}`$ satisfy $`M(n)\ge g_n`$ for every $`n`$ and $`\sum_{n\ge0}M(n)2^{-n}<\infty`$, and put
> ``` math
> S_{h,N,L}=\sum_{j=1}^{L}\frac{g_{N+h+j}-g_{N+j}}{2^{\,j}},\qquad
>  R_{h,N,L}(M)=\sum_{j>L}\frac{M(N+h+j)+M(N+j)}{2^{\,j}} .
> ```
> If for every $`h\ge1`$ and every $`N_0`$ there are $`N\ge N_0`$ and $`L\ge1`$ with $`\operatorname{dist}(S_{h,N,L},\mathbb{Z})>R_{h,N,L}(M)`$, then the nonintegrality condition in Problem 10.1 holds.*

The Lean declaration below states this result or one that implies it. The Lean statement assumes only $M(n)\ge g_n$ and convergence of the series $R_{h,N,L}(M)$ at the triples $(h,N,L)$ used; the printed hypothesis $\sum_{n\ge0}M(n)2^{-n}<\infty$ gives that convergence, and the conclusion is the nonintegrality condition of the escape problem for every $h\ge1$.

[`ErdosProblems.Erdos251.PaperR7.cofinal_escape_of_finite_truncation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperTailBoundsR7.lean#L261)

```lean
theorem cofinal_escape_of_finite_truncation (M : ℕ → ℝ)
    (hM : ∀ n, (primeGap0 n : ℝ) ≤ M n)
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N L : ℕ,
      N₀ ≤ N ∧ 1 ≤ L ∧ Summable (majorantRemainderTerm M h N L) ∧
      majorantRemainder M h N L < integerDistance (signedWindow h N L)) :
    CofinalNonintegralTailShifts realPrimeGapTail
```

where [`CofinalNonintegralTailShifts`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PrimeGapDyadicTail.lean#L1408) is

```lean
def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬RealIntegral (realTailShift T h N)
```

<a id="long251-xr-truncation-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cofinal_escape_of_finite_truncation` | [E251_04/Challenge.lean, line 144](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_04/Challenge.lean#L144) | [PaperStatementsN.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_04/PaperStatementsN.lean#L21) | [E251_04](../evidence/comparator/replay-35882032091/receipt-E251_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-complete-truncation"></a>

## Proposition D.4 (completeness of finite separation), page 35

> *Suppose $`D\in\mathbb{R}`$, $`S_L\in\mathbb{R}`$ and $`R_L\ge0`$ satisfy $`|D-S_L|\le R_L`$ and $`R_L\to0`$. Then
> ``` math
> D\notin\mathbb{Z}\quad\Longleftrightarrow\quad
>  \text{there exists }L\text{ with }\operatorname{dist}(S_L,\mathbb{Z})>R_L.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperCompleteR20.finite_separation_complete`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCompleteR20/FiniteSeparation.lean#L25)

```lean
theorem finite_separation_complete (D : ℝ) (S R : ℕ → ℝ)
    (hR : ∀ L, 0 ≤ R L) (herr : ∀ L, |D-S L| ≤ R L)
    (hlim : Tendsto R atTop (𝓝 0)) :
    D ∉ Set.range ((↑) : ℤ → ℝ) ↔
      ∃ L, R L < Metric.infDist (S L) (Set.range ((↑) : ℤ → ℝ))
```

<a id="long251-res-complete-truncation-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `finite_separation_complete` | [E251_04/Challenge.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_04/Challenge.lean#L157) | [PaperStatementsB.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_04/PaperStatementsB.lean#L17) | [E251_04](../evidence/comparator/replay-35882032091/receipt-E251_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-xr-boundedpolignac"></a>

## Proposition D.6 (bounded recurring-values countermodel), page 38

> *Put $`U_0=4`$ and, for $`n\ge1`$, $`U_n=6`$ when $`n=k!`$ for some $`k\ge3`$ and $`U_n=4`$ otherwise, and set $`a_n=2U_{n-1}-U_n`$ for $`n\ge1`$. Then $`a_n\in\{2,4,8\}`$. For every $`k\ge3`$, the value $`2`$ occurs at index $`k!`$ and the value $`4`$ at index $`2\,k!`$, so both recur infinitely often at indices divisible by any fixed $`t\ge1`$. The series $`\sum_{n\ge1}a_n2^{-n}`$ equals $`4`$ and every tail $`\sum_{j\ge1}a_{N+j}2^{-j}`$ equals the integer $`U_N`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos251.PaperR7.bounded_recurring_values_countermodel`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperBoundedCarryR7.lean#L179)

```lean
theorem bounded_recurring_values_countermodel :
    (∀ n, 1 ≤ n → factorialCarryDigit n = 2 ∨
      factorialCarryDigit n = 4 ∨ factorialCarryDigit n = 8) ∧
    (∀ k, 3 ≤ k → factorialCarryDigit k.factorial = 2 ∧
      factorialCarryDigit (2 * k.factorial) = 4) ∧
    (∀ t, 0 < t → ∀ N, ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧
      factorialCarryDigit i = 2 ∧ factorialCarryDigit j = 4) ∧
    HasSum (fun j : ℕ => (factorialCarryDigit (j + 1) : ℝ) / 2 ^ (j + 1)) 4 ∧
    (∀ N, HasSum (fun j : ℕ =>
      (factorialCarryDigit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (factorialCarry N : ℝ))
```

<a id="long251-xr-boundedpolignac-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `bounded_recurring_values_countermodel` | [E251_04/Challenge.lean, line 179](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_04/Challenge.lean#L179) | [PaperStatementsE.lean, line 18](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_04/PaperStatementsE.lean#L18) | [E251_04](../evidence/comparator/replay-35882032091/receipt-E251_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long251-res-affinecollapse"></a>

## Theorem E.1 (equivalent arithmetic-progression tests), page 40

> *For every rational dyadic tail recurrence and all $`h,N,r\ge0`$,
> ``` math
> \begin{equation}
>  D_{N+r}\in-B_{h,N,r}+2^{r+1}\mathbb{Z}\quad\Longleftrightarrow\quad D_N\in2\mathbb{Z}.
> \label{eq:affinecollapse}\ltx@label{long251:eq:affinecollapse}
> \end{equation}
> ```
> Consequently, if every $`\delta_N`$ is even, then
> ``` math
> \begin{equation}
>  \begin{split}
>  &\bigl(\forall N_0\ \exists N,r:\ N_0<N\text{ and }
>  D_{N+r}\notin-B_{h,N,r}+2^{r+1}\mathbb{Z}\bigr)\\
>  &\hspace{12mm}\Longleftrightarrow\quad
>  D_N\notin\mathbb{Z}\text{ for arbitrarily large }N.
>  \end{split}
> \label{eq:affinecofinal}\ltx@label{long251:eq:affinecofinal}
> \end{equation}
> ```*
> 
> *There is a second equivalence. Let $`b:\mathbb{N}\to\mathbb{Q}`$ satisfy $`|D_N|\le b(N)`$ for every $`N`$, and suppose that for every $`N`$ and every positive integer $`q`$ there is an $`r`$ with
> ``` math
> \begin{equation}
>  2b(N+r)q<2^r.
> \label{eq:dyadicscale}\ltx@label{long251:eq:dyadicscale}
> \end{equation}
> ```
> Then
> ``` math
> \begin{equation}
>  \begin{split}
>  &\forall N_0\ \exists N,r:\ N_0<N\text{ and }
>    \forall z\in\mathbb{Z},\quad
>    b(N+r)<|B_{h,N,r}-2^rz|\\
>  &\hspace{35mm}\Longleftrightarrow\quad
>  D_N\notin\mathbb{Z}\text{ for arbitrarily large }N.
>  \end{split}
> \label{eq:fixedcollapse}\ltx@label{long251:eq:fixedcollapse}
> \end{equation}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos251.PaperR7.affine_circularity_bundle`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos251/PaperCoreR7.lean#L241)

```lean
theorem affine_circularity_bundle {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    (∀ h N r : ℕ,
      RatAffinePowTwo (tailShift T h (N + r))
        (dyadicTailBlock (shiftDigit g h) N r) r ↔
      RatEvenIntegral (tailShift T h N)) ∧
    (∀ h : ℕ,
      (∀ N, ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) →
      ((∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
        ¬ RatAffinePowTwo (tailShift T h (N + r))
          (dyadicTailBlock (shiftDigit g h) N r) r) ↔
        ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))) ∧
    (∀ (h : ℕ) (bound : ℕ → ℚ),
      (∀ N, |tailShift T h N| ≤ bound N) → DyadicScaleDominates bound →
      ((∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧ ∀ z : ℤ,
        bound (N + r) <
          |(dyadicTailBlock (shiftDigit g h) N r : ℚ) - 2 ^ r * (z : ℚ)|) ↔
        ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N)))
```

<a id="long251-res-affinecollapse-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `affine_circularity_bundle` | [E251_04/Challenge.lean, line 84](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E251_04/Challenge.lean#L84) | [PaperStatementsM.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E251_04/PaperStatementsM.lean#L32) | [E251_04](../evidence/comparator/replay-35882032091/receipt-E251_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
