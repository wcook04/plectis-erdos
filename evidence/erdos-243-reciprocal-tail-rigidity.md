# Formal evidence: Cubic-Rate Irrationality and Reciprocal-Tail Rigidity

This record belongs to the paper [erdos-243-reciprocal-tail-rigidity.pdf](../paper/243/erdos-243-reciprocal-tail-rigidity.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`be89e72217ec`](https://github.com/wcook04/plectis-erdos/tree/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 18 results: 18 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 18 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="res-originalbounded"></a>

## Corollary 1.1 (bounded increments of $`P_n/a_n`$), page 2

> *Let $`a_1<a_2<\cdots`$ be positive integers, $`a_{n+1}/a_n^2\to1`$, and $`\sum_{n\ge1}1/a_n\in\mathbb{Q}`$. Put $`P_n=\prod_{j<n}a_j`$. If
> ``` math
> \limsup_{n\to\infty}\frac{P_n}{a_n}
>  \left(\frac{a_n^2}{a_{n+1}}-1\right)<+\infty,
> ```
> then $`a_{n+1}=a_n^2-a_n+1`$ for all sufficiently large $`n`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.original_coordinate_bounded_defect`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/ProductDefect.lean#L211)

```lean
theorem original_coordinate_bounded_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hupper : ∃ M : ℝ, ∃ N, ∀ n, N ≤ n → productDefect a n ≤ M) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1
```

<a id="res-originalbounded-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `original_coordinate_bounded_defect`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L152) (E243_06, line 152), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/OriginalCoordinateBoundedDefect.lean#L27) (OriginalCoordinateBoundedDefect.lean, line 27), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-bounded"></a>

## Theorem 1.2 (bounded negative part), page 3

> *Let $`a,C,D:\mathbb{N}\to\mathbb{N}`$ and $`E:\mathbb{N}\to\mathbb{Z}`$ satisfy*
> 
> 1.  *$`a_n>1`$ and $`C_n>0`$ for every $`n`$;*
> 
> 2.  *the exact dynamics $`C_{n+1}+D_n=a_nC_n`$ and $`D_{n+1}=a_nD_n`$;*
> 
> 3.  *$`E_n=D_n-(a_n-1)C_n`$ for every $`n`$;*
> 
> 4.  **eventual strict centring*: $`|E_n|<C_n`$ for all large $`n`$;*
> 
> 5.  **eventually bounded negative part*: $`-B\le E_n`$ for all large $`n`$, for some integer $`B\ge0`$;*
> 
> 6.  **vanishing relative error*: for every integer $`K\ge1`$ there is an $`N`$ with $`K\,|E_n|<C_n`$ for all $`n\ge N`$.*
> 
> *Then $`E_n=0`$ for all sufficiently large $`n`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.eventuallyBoundedNegativePart_eventually_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2360)

```lean
theorem eventuallyBoundedNegativePart_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0
```

<a id="res-bounded-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `eventuallyBoundedNegativePart_eventually_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L107) (E243_08, line 107), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsA.lean#L295) (PaperStatementsA.lean, line 295), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-cor"></a>

## Corollary 2.1, page 4

> *Under Theorem 1.2, the multipliers satisfy $`a_{n+1}=a_n^2-a_n+1`$ eventually.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.bounded_negative_endpoint_eventual_multiplier`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L179)

```lean
theorem bounded_negative_endpoint_eventual_multiplier
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∃ N, ∀ n, N ≤ n → 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)
```

<a id="res-cor-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `bounded_negative_endpoint_eventual_multiplier`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_09/Challenge.lean#L59) (E243_09, line 59), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_09/PaperStatementsA.lean#L197) (PaperStatementsA.lean, line 197), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_09.json) (E243_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-update"></a>

## Proposition 3.1 (error identities), page 4

> *<span id="res:defect" label="res:defect"></span> For an exact integer state,
> ``` math
> C_{n+1}=C_n-E_n,\qquad
>  \bigl(a_{n+1}-a_n^2+a_n-1\bigr)C_{n+1}=a_n^2E_n-E_{n+1}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.error_identities`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L21)

```lean
theorem error_identities (a aNext D C : ℤ) :
    nextTailState a D C = C - centeredState a D C ∧
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C)
```

<a id="res-update-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `error_identities`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_09/Challenge.lean#L71) (E243_09, line 71), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_09/PaperStatementsA.lean#L208) (PaperStatementsA.lean, line 208), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_09.json) (E243_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-absorb"></a>

## Theorem 3.2 (absorption and descent), page 4

> *<span id="res:descent" label="res:descent"></span> For a positive exact state with strict centring, $`E_n=0`$ implies $`E_{n+1}=0`$. For any positive integer state with $`C_{n+1}=C_n-E_n`$, eventual nonnegativity of $`E_n`$ implies its eventual vanishing.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.absorption_and_descent`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L120)

```lean
theorem absorption_and_descent :
    (∀ (a C D : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) →
      (∀ n, Int.natAbs (E n) < C n) →
      ∀ n, E n = 0 → E (n + 1) = 0) ∧
    (∀ (C : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) →
      (∃ N, ∀ n, N ≤ n → 0 ≤ E n) →
      ∃ N, ∀ n, N ≤ n → E n = 0)
```

<a id="res-absorb-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `absorption_and_descent`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_09/Challenge.lean#L46) (E243_09, line 46), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_09/PaperStatementsA.lean#L185) (PaperStatementsA.lean, line 185), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_09.json) (E243_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-step"></a>

## Corollary 3.3 (two zero errors), page 5

> *<span id="res:eventual" label="res:eventual"></span> If $`E_n=E_{n+1}=0`$ and $`C_{n+1}\ne0`$, then $`a_{n+1}=a_n^2-a_n+1`$. Thus eventual zero error in a positive exact state implies the eventual Sylvester recurrence.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.sylvesterNext_eq_of_centered_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1787)

```lean
theorem sylvesterNext_eq_of_centered_zero
    (a aNext D C : ℤ)
    (hCnext : nextTailState a D C ≠ 0)
    (hE : centeredState a D C = 0)
    (hEnext :
      centeredState aNext (nextDenState a D) (nextTailState a D C) = 0) :
    aNext = sylvesterNext a
```

2. [`ErdosProblems.Erdos243.PaperCompleteR7.natural_sylvester_of_eventual_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L156)

```lean
theorem natural_sylvester_of_eventual_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hzero : ∃ N, ∀ n, N ≤ n → E n = 0) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)
```

<a id="res-step-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `sylvesterNext_eq_of_centered_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L139) (E243_02, line 139), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L314) (PaperStatementsA.lean, line 314), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)
- `natural_sylvester_of_eventual_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_09/Challenge.lean#L78) (E243_09, line 78), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_09/PaperStatementsA.lean#L228) (PaperStatementsA.lean, line 228), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_09.json) (E243_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-crt"></a>

## Lemma 3.4 (consecutive multiples), page 5

> *For pairwise coprime integers $`m_0,\ldots,m_{B-1}\ge2`$ and every lower bound, there is a larger $`t`$ such that $`m_i\mid t+i`$ for each $`i<B`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.exists_shifted_consecutiveMultiples`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L839)

```lean
theorem exists_shifted_consecutiveMultiples
    {k : ℕ}
    (m : Fin k → ℕ)
    (hm : ∀ i, 1 < m i)
    (hpair : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (L : ℕ) :
    ∃ x, L < x ∧ ∀ i : Fin k, m i ∣ x + i.1
```

<a id="res-crt-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exists_shifted_consecutiveMultiples`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_09/Challenge.lean#L88) (E243_09, line 88), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_09/PaperStatementsA.lean#L297) (PaperStatementsA.lean, line 297), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_09.json) (E243_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-barrier"></a>

## Theorem 3.5 (Chinese remainder theorem and first crossing), page 5

> *Let $`u:\mathbb{N}\to\mathbb{N}`$ tend to infinity and let $`B\ge1`$ be an integer with $`u_{n+1}\le u_n+B`$ for every $`n`$. There is no sequence of pairwise coprime integers $`m_i\ge2`$ for which $`\gcd(m_i,u_t)=1`$ whenever $`i<t`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.no_boundedRise_of_tailAvoidance`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L903)

```lean
theorem no_boundedRise_of_tailAvoidance
    (u m : ℕ → ℕ) (N B : ℕ)
    (hB : 0 < B)
    (hm : ∀ n, N ≤ n → 1 < m n)
    (hpair : ∀ {i j : ℕ}, N ≤ i → N ≤ j → i ≠ j →
      Nat.Coprime (m i) (m j))
    (havoid : ∀ {i t : ℕ}, N ≤ i → i < t →
      Nat.Coprime (m i) (u t))
    (hrise : ∀ n, N ≤ n → u (n + 1) ≤ u n + B)
    (huTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    False
```

<a id="res-barrier-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `no_boundedRise_of_tailAvoidance`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_10/Challenge.lean#L55) (E243_10, line 55), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_10/BoundedRiseReducedTail.lean#L12) (BoundedRiseReducedTail.lean, line 12), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_10.json) (E243_10)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-reduced"></a>

## Proposition 3.6 (persistent coprimality), page 6

> *In a reduced exact tail, $`\gcd(a_n,v_n)=1`$. Distinct multipliers are pairwise coprime, and every earlier multiplier is coprime to every later numerator.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.persistent_coprimality`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Reduction.lean#L16)

```lean
theorem persistent_coprimality
    (a u v : ℕ → ℕ)
    (hred : ∀ n, Nat.Coprime (u n) (v n))
    (hu : ∀ n, u (n + 1) + v n = a n * u n)
    (hv : ∀ n, v (n + 1) = a n * v n) :
    (∀ n, Nat.Coprime (a n) (v n)) ∧
    (∀ i j, i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ i t, i < t → Nat.Coprime (a i) (u t))
```

<a id="res-reduced-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `persistent_coprimality`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L83) (E243_08, line 83), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsA.lean#L247) (PaperStatementsA.lean, line 247), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-gcdstab"></a>

## Proposition 3.7 (gcd stabilisation), page 6

> *For a positive exact state, suppose that some fixed integer $`B\ge1`$ satisfies $`-B\le E_n<0`$ at infinitely many indices. Then $`G_n=\gcd(C_n,D_n)`$ is eventually constant. Division by its stable value gives a reduced exact tail.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.gcd_stabilises_and_reduces`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Reduction.lean#L103)

```lean
theorem gcd_stabilises_and_reduces
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hnegative : ∃ B : ℕ, ∀ N, ∃ t,
      N ≤ t ∧ E t < 0 ∧ -(B : ℤ) ≤ E t) :
    ∃ N g : ℕ, 0 < g ∧
      (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
      (∀ n, N ≤ n → 0 < C n / g) ∧
      (∀ n, N ≤ n → Nat.Coprime (C n / g) (D n / g)) ∧
      (∀ n, N ≤ n → C (n + 1) / g + D n / g = a n * (C n / g)) ∧
      (∀ n, N ≤ n → D (n + 1) / g = a n * (D n / g))
```

<a id="res-gcdstab-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `gcd_stabilises_and_reduces`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L68) (E243_08, line 68), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsA.lean#L224) (PaperStatementsA.lean, line 224), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-massscalar"></a>

## Theorem 5.1 (a convergent sum of relative increases), page 8

> *<span id="res:mass" label="res:mass"></span> Let $`C_n`$ be positive integers and $`E_n`$ integers satisfying $`C_{n+1}=C_n-E_n`$. If
> ``` math
> \sum_n\frac{(-E_n)_+}{C_n}<\infty,
> ```
> then $`E_n=0`$ eventually. Neither denominator dynamics nor vanishing relative error is required.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.finite_negative_mass_paper`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Frontier.lean#L84)

```lean
theorem finite_negative_mass_paper :
    (∀ (C : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, 0 < C n) →
      (∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) →
      Summable (fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ)) →
      ∃ N, ∀ n, N ≤ n → E n = 0) ∧
    (∀ (a C D : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, 0 < C n) →
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) →
      Summable (fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ)) →
      ∃ N, ∀ n, N ≤ n →
        (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ))
```

<a id="res-massscalar-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `finite_negative_mass_paper`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L177) (E243_08, line 177), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsL.lean#L114) (PaperStatementsL.lean, line 114), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-weightedrecord"></a>

## Theorem 6.1 (a convergent weighted sum over new maxima), page 9

> *Assume the growth and rationality hypotheses of Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">3</a>. Let $`f:[1,\infty)\to[0,\infty)`$ be finite and nonincreasing, with $`\int_1^\infty f(t)\,dt=\infty`$. Then the sequence is eventually Sylvester if and only if, for some integer $`B\ge0`$,
> ``` math
> \sum_{n\in\mathcal R}(-V_n-B)_+f(U_n)<\infty.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR11.canonical_weighted_record_excess`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR11/CanonicalRecords.lean#L202)

```lean
theorem canonical_weighted_record_excess
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : IntegralUnbounded f) :
    (∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1) ↔
      ∃ B : ℕ, Summable (paperRecordCharge (canonicalLcmNumerator a p q)
        (canonicalLcmDigit a p q) B f)
```

<a id="res-weightedrecord-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `canonical_weighted_record_excess`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L220) (E243_02, line 220), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/CompletePaperRecords.lean#L102) (CompletePaperRecords.lean, line 102), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-lcmbounded"></a>

## Corollary 6.2 (a bound using the least common multiple), page 11

> *Assume the hypotheses of Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">3</a>. Write $`A_n=\operatorname{lcm}(a_1,\ldots,a_{n-1})`$ with $`A_1=1`$. If
> ``` math
> \limsup_{n\to\infty}\frac{A_n}{a_n}
>  \left(\frac{a_n^2}{a_{n+1}}-1\right)<\infty,
> ```
> then the sequence is eventually Sylvester.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.original_coordinate_lcm_bounded_defect`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/LcmDefect.lean#L49)

```lean
theorem original_coordinate_lcm_bounded_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hupper : ∃ M : ℝ, ∃ N, ∀ n, N ≤ n → lcmDefect a n ≤ M) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1
```

<a id="res-lcmbounded-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `original_coordinate_lcm_bounded_defect`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_09/Challenge.lean#L109) (E243_09, line 109), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_09/PaperStatementsS.lean#L17) (PaperStatementsS.lean, line 17), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_09.json) (E243_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-inclusiveone"></a>

## Corollary 7.1 (an inclusive one-sided $`1/n`$ bound), page 12

> *Let $`a_1<a_2<\cdots`$ be positive integers with $`a_{n+1}/a_n^2\to1`$ and $`\sum_n1/a_n\in\mathbb{Q}`$. Suppose that for some $`K\ge0`$ and $`\varepsilon>0`$,
> ``` math
> \gamma_n:=a_n^2/a_{n+1}-1\le \frac1n+\frac{K}{n^{1+\varepsilon}}
>  \quad\hbox{for all large }n.
> ```
> Then the sequence is eventually Sylvester. In particular, the conclusion holds under the pointwise eventual bound $`\gamma_n\le1/n`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR20.original_coordinate_inclusive_one`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR20/InclusiveOne.lean#L207)

```lean
theorem original_coordinate_inclusive_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε)
    (hbound : ∃ N : ℕ, ∀ n, N ≤ n →
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 ≤
        1 / (n : ℝ) + K / (n : ℝ) ^ (1 + ε)) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1
```

2. [`ErdosProblems.Erdos243.PaperCompleteR20.original_coordinate_inclusive_one_pointwise`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR20/InclusiveOne.lean#L225)

```lean
theorem original_coordinate_inclusive_one_pointwise
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hbound : ∃ N : ℕ, ∀ n, N ≤ n →
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 ≤ 1 / (n : ℝ)) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1
```

<a id="res-inclusiveone-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `original_coordinate_inclusive_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L220) (E243_06, line 220), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStatementsB.lean#L19) (PaperStatementsB.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `original_coordinate_inclusive_one_pointwise`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L234) (E243_06, line 234), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStatementsB.lean#L33) (PaperStatementsB.lean, line 33), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-cubicrate"></a>

## Theorem 7.2 (cubic-rate irrationality), page 12

> *A strictly increasing sequence of positive integers with
> ``` math
> a_n^2/a_{n+1}=1+\frac3n+o(n^{-3})
> ```
> has irrational reciprocal sum.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L70)

```lean
theorem cubic_rate_irrationality_unconditional
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv) :
    Irrational Sv
```

<a id="res-cubicrate-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cubic_rate_irrationality_unconditional`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L76) (E243_01, line 76), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStructuresAC.lean#L31) (PaperStructuresAC.lean, line 31), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-frontier"></a>

## Proposition 8.1 (necessary profile), page 14

> *The integer tail of a sequence satisfying Problem <a href="#res:problem" data-reference-type="ref" data-reference="res:problem">3</a>’s hypotheses but not its conclusion has $`E_n\ne0`$ eventually, $`|E_n|/C_n\to0`$, unbounded negative magnitudes along negative indices, and
> ``` math
> \sum_n\frac{(-E_n)_+}{C_n}=\infty.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.canonical_frontier`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Frontier.lean#L151)

```lean
theorem canonical_frontier
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    (∃ N, ∀ n, N ≤ n → E n ≠ 0) ∧
    Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0) ∧
    (∀ N B : ℕ, ∃ n, N ≤ n ∧ E n < -(B : ℤ)) ∧
    Tendsto (fun N ↦ ∑ n ∈ Finset.range N,
      max (-(E n : ℝ)) 0 / (C n : ℝ)) atTop atTop
```

<a id="res-frontier-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `canonical_frontier`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L159) (E243_08, line 159), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsL.lean#L84) (PaperStatementsL.lean, line 84), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-weights"></a>

## Lemma 8.3 (weights and linear density), page 15

> *Let $`u_j`$ be positive integers, let $`w_j\ge0`$, and put $`F(X)=\sum_{u_j\le X}w_j`$, with the sum allowed a priori to be $`+\infty`$. Then $`\liminf_{X\to\infty}F(X)/X=0`$ if and only if there is a finite nonincreasing $`f:[1,\infty)\to[0,\infty)`$ with $`\int_1^\infty f(t)\,dt=\infty`$ and $`\sum_jw_jf(u_j)<\infty`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR20.real_lowerDensityZero_iff_exists_admissible_real_weight`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR20/RealCutoffCriterion.lean#L87)

```lean
theorem real_lowerDensityZero_iff_exists_admissible_real_weight
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j) :
    RealPrefixLowerDensityZero u (fun j => (w j : ℝ≥0∞)) ↔
      ∃ f : ℝ → ℝ,
        AntitoneOn f (Ici 1) ∧
        (∀ t : ℝ, 1 ≤ t → 0 ≤ f t) ∧
        PaperCompleteR11.IntegralUnbounded f ∧
        Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ))
```

<a id="res-weights-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `real_lowerDensityZero_iff_exists_admissible_real_weight`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_09/Challenge.lean#L139) (E243_09, line 139), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_09/PaperStatementsJ.lean#L23) (PaperStatementsJ.lean, line 23), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_09.json) (E243_09)

Challenge for `real_lowerDensityZero_iff_exists_admissible_real_weight`:

```lean
theorem real_lowerDensityZero_iff_exists_admissible_real_weight
    (u : ℕ → ℕ) (w : ℕ → ℝ≥0) (hu : ∀ j, 0 < u j) :
    RealPrefixLowerDensityZero u (fun j => (w j : ℝ≥0∞)) ↔
      ∃ f : ℝ → ℝ,
        AntitoneOn f (Ici 1) ∧
        (∀ t : ℝ, 1 ≤ t → 0 ≤ f t) ∧
        IntegralUnbounded f ∧
        Summable (fun j : ℕ => (w j : ℝ) * f (u j : ℕ)) := by sorry
```

<a id="res-residue"></a>

## Theorem B.2 (factorial residue reduction), page 17

> *For all $`h`$ and all integers $`a\equiv b \pmod{(h+1)!}`$, the orbit from $`a`$ survives $`h`$ forced updates exactly when the orbit from $`b`$ does.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.forcedSurvives_iff_of_modEq_factorial`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L134)

```lean
theorem forcedSurvives_iff_of_modEq_factorial
    {h : ℕ} {a b : ℤ}
    (hab : a ≡ b [ZMOD ((h + 1).factorial : ℤ)]) :
    ForcedSurvives h 0 a ↔ ForcedSurvives h 0 b
```

<a id="res-residue-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `forcedSurvives_iff_of_modEq_factorial`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L252) (E243_08, line 252), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsK.lean#L54) (PaperStatementsK.lean, line 54), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
