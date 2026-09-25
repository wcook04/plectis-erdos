# Formal evidence: Denominators and Rationality Criteria\\for $\sum_{n\ge2}(n!-1)^{-1}$

This record belongs to the paper [erdos68-factorial-reasoning-surface.pdf](../paper/68/erdos68-factorial-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`be89e72217ec`](https://github.com/wcook04/plectis-erdos/tree/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 18 results: 18 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 18 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="long68-res-prime-pole"></a>

## Theorem 1.2 (maximal prime-power survival), page 3

> *Let $`M\ge2`$, let $`p`$ be a prime dividing $`L_M`$, and put $`e=v_p(L_M)`$. Let $`J=\{n:2\le n\le M,\ v_p(d_n)=e\}`$ and write $`d_n=p^eu_n`$ for $`n\in J`$. Then, with inverses in $`\mathbb F_p`$,
> ``` math
> \begin{equation}
> \label{long68:eq:prime-pole-survival}
>  v_p\bigl(\operatorname{den}(H_M)\bigr)=e
>  \quad\Longleftrightarrow\quad
>  \sum_{n\in J}u_n^{-1}\ne0\quad\hbox{in }\mathbb F_p.
> \end{equation}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.maximal_prime_power_survival`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompletePrimePole.lean#L117)

```lean
theorem maximal_prime_power_survival {M p : ℕ} (_hM : 2 ≤ M)
    (hp : p.Prime) (hpL : p ∣ factorialGapPrefixLCM M) :
    (factorialGapPrefix M).den.factorization p =
        (factorialGapPrefixLCM M).factorization p ↔
      (∑ n ∈ (Finset.Icc 2 M).filter
          (fun n => (n.factorial - 1).factorization p =
            (factorialGapPrefixLCM M).factorization p),
        (((n.factorial - 1) /
          p ^ (factorialGapPrefixLCM M).factorization p : ℕ) : ZMod p)⁻¹) ≠ 0
```

<a id="long68-res-prime-pole-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `maximal_prime_power_survival`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_01/Challenge.lean#L112) (E68_01, line 112), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_01/PaperStatementsA.lean#L224) (PaperStatementsA.lean, line 224), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_01.json) (E68_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long68-res-wilson-cofinality"></a>

## Proposition 1.3 (cofinal first prime occurrences), page 4

> *For every integer $`B\ge0`$ there are a prime $`q`$ and an integer $`m>B`$ with $`m<q`$, $`q\mid m!-1`$ and $`\gcd(q,k!-1)=1`$ for every $`k`$ with $`2\le k<m`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.cofinal_first_prime_occurrences`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L180)

```lean
theorem cofinal_first_prime_occurrences :
    ∀ B : ℕ, ∃ q m : ℕ, B < m ∧ q.Prime ∧ m < q ∧
      q ∣ m.factorial - 1 ∧
      ∀ k : ℕ, 2 ≤ k → k < m → Nat.Coprime q (k.factorial - 1)
```

<a id="long68-res-wilson-cofinality-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cofinal_first_prime_occurrences`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_01/Challenge.lean#L82) (E68_01, line 82), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_01/PaperStatementsA.lean#L150) (PaperStatementsA.lean, line 150), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_01.json) (E68_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long68-res-product-lcm"></a>

## Lemma 2.1 (product, least common multiple, pairwise gcd), page 5

> *For positive integers $`x_1,\ldots,x_k`$,
> ``` math
> \prod_{i=1}^{k}x_i\ \Big|\ \operatorname{lcm}(x_1,\ldots,x_k)\prod_{i<j}\gcd(x_i,x_j).
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.product_lcm_pairwise_gcd`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L189)

```lean
theorem product_lcm_pairwise_gcd (xs : List ℕ) :
    xs.prod ∣ _root_.Erdos68.listLCM xs * _root_.Erdos68.pairwiseGCDProduct xs
```

<a id="long68-res-product-lcm-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `product_lcm_pairwise_gcd`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_01/Challenge.lean#L136) (E68_01, line 136), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_01/PaperStatementsE.lean#L17) (PaperStatementsE.lean, line 17), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_01.json) (E68_01)

Challenge for `product_lcm_pairwise_gcd`:

```lean
theorem product_lcm_pairwise_gcd (xs : List ℕ) :
    xs.prod ∣ listLCM xs * pairwiseGCDProduct xs := by sorry
```

<a id="long68-res-gap-gcd"></a>

## Lemma 2.2 (factorial-gap gcd), page 5

> *For $`2\le i<j`$, the integer $`g=\gcd(i!-1,j!-1)`$ divides $`j!/i!-1`$, and $`g\le j!/i!-1<j^{\,j-i}`$.*

The Lean declaration below states this result.

[`Erdos68.factorial_gap_gcd_exact`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L288)

```lean
theorem factorial_gap_gcd_exact
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    let g := Nat.gcd (m.factorial - 1) (n.factorial - 1)
    let Q := n.descFactorial (n - m)
    g ∣ Q - 1 ∧ g ≤ Q - 1 ∧ Q - 1 < n ^ (n - m)
```

<a id="long68-res-gap-gcd-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `factorial_gap_gcd_exact`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_01/Challenge.lean#L146) (E68_01, line 146), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_01/FactorialGapBounds.lean#L19) (FactorialGapBounds.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_01.json) (E68_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long68-res-segment"></a>

## Lemma 2.3 (segment inequality), page 5

> *For $`2\le k\le N-1`$,
> ``` math
> \begin{equation}
> \label{long68:eq:segment}
>  \sum_{n=N-k+1}^{N}\log(n!-1)
>  \ \le\ \log L_N+\binom{k+1}{3}\log N.
> \end{equation}
> ```*

The Lean declaration below states this result or one that implies it. The Lean inequality holds for every $k$ with $0\le k\le N-1$; the printed statement is its range $2\le k\le N-1$.

[`Erdos68.factorialGapSegment_log_sum_le_channelLCM_add_choose`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/ChannelIntegralCongruence.lean#L566)

```lean
theorem factorialGapSegment_log_sum_le_channelLCM_add_choose
    {D k : ℕ} (hkD : k < D) :
    (∑ n ∈ Finset.Ico (D + 1 - k) (D + 1),
      Real.log ((n.factorial - 1 : ℕ) : ℝ)) ≤
      Real.log (channelLCM D : ℝ) +
        (((k + 1).choose 3 : ℕ) : ℝ) * Real.log (D : ℝ)
```

<a id="long68-res-segment-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `factorialGapSegment_log_sum_le_channelLCM_add_choose`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_01/Challenge.lean#L153) (E68_01, line 153), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_01/FactorialGapBounds.lean#L27) (FactorialGapBounds.lean, line 27), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_01.json) (E68_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long68-res-lcm-growth"></a>

## Theorem 2.4 (common-denominator growth), page 5

> *``` math
> \liminf_{N\to\infty}\frac{\log L_N}{N^{3/2}\log N}
>  \ \ge\ \frac{2\sqrt2}{3}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.common_denominator_growth_liminf`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteLiminf.lean#L42)

```lean
theorem common_denominator_growth_liminf :
    ((2 * Real.sqrt 2 / 3 : ℝ) : EReal) ≤
      Filter.liminf (fun N : ℕ =>
        ((Real.log (_root_.Erdos68.channelLCM N : ℝ) /
          ((N : ℝ) ^ ((3 : ℝ) / 2) * Real.log (N : ℝ)) : ℝ) : EReal)) atTop
```

<a id="long68-res-lcm-growth-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `common_denominator_growth_liminf`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_01/Challenge.lean#L166) (E68_01, line 166), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_01/CommonDenominatorGrowth.lean#L30) (CommonDenominatorGrowth.lean, line 30), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_01.json) (E68_01)

Challenge for `common_denominator_growth_liminf`:

```lean
theorem common_denominator_growth_liminf :
    ((2 * Real.sqrt 2 / 3 : ℝ) : EReal) ≤
      Filter.liminf (fun N : ℕ =>
        ((Real.log (channelLCM N : ℝ) /
          ((N : ℝ) ^ ((3 : ℝ) / 2) * Real.log (N : ℝ)) : ℝ) : EReal)) atTop := by sorry
```

<a id="long68-res-carry-equivalence"></a>

## Theorem 3.1 (an exact criterion from successive partial sums), page 8

> *For $`m\ge3`$,
> ``` math
> \begin{equation}
> \label{long68:eq:unit-window}
>  b_m=1
>  \iff m\mid Z_m
>  \iff 1+\varepsilon_m<m\Delta_m\le2+\varepsilon_m .
> \end{equation}
> ```*
> 
> *Moreover
> ``` math
> \begin{align}
>  S\in\mathbb{Q}
>  &\iff b_m=1\ \hbox{for all sufficiently large }m,
>  \label{long68:eq:carry-rationality}\\
>  S\notin\mathbb{Q}
>  &\iff \forall B\ \exists m>B:\ m\nmid Z_m .
>  \label{long68:eq:strict-misses}
> \end{align}
> ```
> If $`S=a/q`$ with $`a\in\mathbb{Z}`$, $`q\ge1`$ and $`b_m\ne1`$, then $`q\nmid(m-1)!`$ and $`q\ge m`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.strict_successor_characterisation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L77)

```lean
theorem strict_successor_characterisation :
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
      ((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m ↔
        1 + 1 / ((m.factorial : ℝ) - 1) <
            (m : ℝ) * factorialGapPredecessorGap m ∧
        (m : ℝ) * factorialGapPredecessorGap m ≤
            2 + 1 / ((m.factorial : ℝ) - 1))) ∧
    (¬ Irrational _root_.Erdos68.factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
    (∀ (m q : ℕ) (a : ℤ), 3 ≤ m → 0 < q →
      _root_.Erdos68.factorialGapSeries = (a : ℝ) / (q : ℝ) →
      factorialGapStepCarry m ≠ 1 →
      (¬ q ∣ (m - 1).factorial) ∧ m ≤ q)
```

<a id="long68-res-carry-equivalence-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `strict_successor_characterisation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_01/Challenge.lean#L185) (E68_01, line 185), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_01/PaperStatementsB.lean#L66) (PaperStatementsB.lean, line 66), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_01.json) (E68_01)

Challenge for `strict_successor_characterisation`:

```lean
theorem strict_successor_characterisation :
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
      ((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m ↔
        1 + 1 / ((m.factorial : ℝ) - 1) <
            (m : ℝ) * factorialGapPredecessorGap m ∧
        (m : ℝ) * factorialGapPredecessorGap m ≤
            2 + 1 / ((m.factorial : ℝ) - 1))) ∧
    (¬ Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) ∧
    (∀ (m q : ℕ) (a : ℤ), 3 ≤ m → 0 < q →
      factorialGapSeries = (a : ℝ) / (q : ℝ) →
      factorialGapStepCarry m ≠ 1 →
      (¬ q ∣ (m - 1).factorial) ∧ m ≤ q) := by sorry
```

<a id="long68-res-companion-orbit"></a>

## Proposition 3.2 (rationality and factorial residues), page 10

> *``` math
> S\in\mathbb{Q}
>  \quad\Longleftrightarrow\quad
>  \lfloor m!C\rfloor\equiv-2\pmod m
>  \quad\hbox{for all sufficiently large }m.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.companion_orbit`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L38)

```lean
theorem companion_orbit :
    ¬ Irrational _root_.Erdos68.factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0
```

<a id="long68-res-companion-orbit-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `companion_orbit`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_01/Challenge.lean#L88) (E68_01, line 88), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_01/PaperStatementsA.lean#L155) (PaperStatementsA.lean, line 155), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_01.json) (E68_01)

Challenge for `companion_orbit`:

```lean
theorem companion_orbit :
    ¬ Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0 := by sorry
```

<a id="long68-res-lower-escape"></a>

## Proposition 3.3 (lower-interval criterion), page 10

> *``` math
> \begin{equation}
> \label{long68:eq:lower-escape}
>  S\notin\mathbb{Q}
>  \quad\Longleftrightarrow\quad
>  \forall B\ \exists m>B:\ E_m\le m\theta_{m-1}.
> \end{equation}
> ```
> For $`m\ge3`$ the finite condition
> ``` math
> \begin{equation}
> \label{long68:eq:finite-escape}
>  m\Delta_m\le1+\varepsilon_m
>  \quad\hbox{or}\quad
>  1+\varepsilon_m+\frac2m\le m\Delta_m
> \end{equation}
> ```
> implies the escape inequality in (10). Cofinally many instances of (11) therefore imply $`S\notin\mathbb{Q}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.lower_interval_criterion`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L102)

```lean
theorem lower_interval_criterion :
    (Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        factorialGapScaledTail m ≤
          (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1)) ∧
    (∀ m : ℕ, 3 ≤ m →
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m) →
      factorialGapScaledTail m ≤
        (m : ℝ) * canonicalRemainder _root_.Erdos68.factorialGapSeries (m - 1)) ∧
    ((∀ B : ℕ, ∃ m : ℕ, 3 ≤ m ∧ B < m ∧
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m)) →
      Irrational _root_.Erdos68.factorialGapSeries)
```

<a id="long68-res-lower-escape-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `lower_interval_criterion`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_01/Challenge.lean#L94) (E68_01, line 94), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_01/PaperStatementsA.lean#L207) (PaperStatementsA.lean, line 207), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_01.json) (E68_01)

Challenge for `lower_interval_criterion`:

```lean
theorem lower_interval_criterion :
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        factorialGapScaledTail m ≤
          (m : ℝ) * canonicalRemainder factorialGapSeries (m - 1)) ∧
    (∀ m : ℕ, 3 ≤ m →
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m) →
      factorialGapScaledTail m ≤
        (m : ℝ) * canonicalRemainder factorialGapSeries (m - 1)) ∧
    ((∀ B : ℕ, ∃ m : ℕ, 3 ≤ m ∧ B < m ∧
      ((m : ℝ) * factorialGapPredecessorGap m ≤ 1 + 1 / ((m.factorial : ℝ) - 1) ∨
        1 + 1 / ((m.factorial : ℝ) - 1) + 2 / (m : ℝ) ≤
          (m : ℝ) * factorialGapPredecessorGap m)) →
      Irrational factorialGapSeries) := by sorry
```

<a id="long68-res-shift-family"></a>

## Theorem 3.4 (a criterion for the shifts $`t\ge-1`$), page 12

> *For every integer $`t\ge-1`$, the series $`S_t`$ is rational exactly when
> ``` math
> \bigl\lceil t\,m!\,C_t\bigr\rceil\equiv2\pmod m
> ```
> for all sufficiently large $`m`$, and irrational exactly when that residue is missed cofinally. The member $`t=-1`$ is $`S`$, and the member $`t=0`$ is $`e-2`$, for which the scaled correction is always $`0`$ and hence misses the residue class at every $`m\ge3`$, proving the irrationality of $`e`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos68.PaperComplete.uniform_family_boundary`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L123)

```lean
theorem uniform_family_boundary {t : ℤ} (ht : -1 ≤ t) :
    (¬ Irrational (shiftGapSeries t) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2) ∧
    (Irrational (shiftGapSeries t) ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2)
```

2. [`ErdosProblems.Erdos68.PaperComplete.uniform_family_members`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L134)

```lean
theorem uniform_family_members :
    shiftGapSeries (-1) = _root_.Erdos68.factorialGapSeries ∧
    shiftGapSeries 0 = Real.exp 1 - 2 ∧
    (∀ m : ℕ, ⌈(0 : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant 0⌉ = 0) ∧
    (∀ m : ℕ, 3 ≤ m → ¬ (m : ℤ) ∣ (0 : ℤ) - 2) ∧
    Irrational (Real.exp 1)
```

<a id="long68-res-shift-family-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `uniform_family_boundary`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_02/Challenge.lean#L85) (E68_02, line 85), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_02/PaperStatementsC.lean#L39) (PaperStatementsC.lean, line 39), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_02.json) (E68_02)
- `uniform_family_members`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_02/Challenge.lean#L94) (E68_02, line 94), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_02/PaperStatementsC.lean#L47) (PaperStatementsC.lean, line 47), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_02.json) (E68_02)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `uniform_family_members`:

```lean
theorem uniform_family_members :
    shiftGapSeries (-1) = factorialGapSeries ∧
    shiftGapSeries 0 = Real.exp 1 - 2 ∧
    (∀ m : ℕ, ⌈(0 : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant 0⌉ = 0) ∧
    (∀ m : ℕ, 3 ≤ m → ¬ (m : ℤ) ∣ (0 : ℤ) - 2) ∧
    Irrational (Real.exp 1) := by sorry
```

<a id="long68-res-global-residue"></a>

## Theorem 4.1 (a sufficient tail inequality), page 13

> *Suppose that for every $`B`$ there is a natural parameter $`p\ge3`$ with $`p>B`$, $`R_p>1`$, and
> ``` math
> \begin{equation}
> \label{long68:eq:global-scale}
>  (2p+1)L^{\mathrm{blk}}_p<K_p\rho_p .
> \end{equation}
> ```
> Then $`S`$ is irrational.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.global_complementary_criterion_nat`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L154)

```lean
theorem global_complementary_criterion_nat
    (hcert : ∀ B : ℕ, ∃ p : ℕ,
      3 ≤ p ∧ B < p ∧ 1 < factorialBlockPrivateModulus p ∧
      factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * complementaryProjectedResidue
          (factorialBlockTailNumerator p) (factorialBlockPrivateModulus p)) :
    Irrational _root_.Erdos68.factorialGapSeries
```

<a id="long68-res-global-residue-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `global_complementary_criterion_nat`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_05/Challenge.lean#L220) (E68_05, line 220), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_05/PaperStatementsA.lean#L86) (PaperStatementsA.lean, line 86), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_05.json) (E68_05)

Challenge for `global_complementary_criterion_nat`:

```lean
theorem global_complementary_criterion_nat
    (hcert : ∀ B : ℕ, ∃ p : ℕ,
      3 ≤ p ∧ B < p ∧ 1 < factorialBlockPrivateModulus p ∧
      factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * complementaryProjectedResidue
          (factorialBlockTailNumerator p) (factorialBlockPrivateModulus p)) :
    Irrational factorialGapSeries := by sorry
```

<a id="long68-res-normalform"></a>

## Theorem 5.1 (divisibility of the difference), page 15

> *For every finite integer support and every $`d\ge2`$ there is an integer $`k`$ with $`V_{d}(c)=M(c)+(d!-1)k`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.supported_integral_normal_form`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteSupportedBands.lean#L17)

```lean
theorem supported_integral_normal_form (f : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℤ, channelNumerator f d = factorialMoment f + ((d.factorial : ℤ) - 1) * k
```

<a id="long68-res-normalform-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `supported_integral_normal_form`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_02/Challenge.lean#L75) (E68_02, line 75), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_02/PaperStatementsC.lean#L31) (PaperStatementsC.lean, line 31), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_02.json) (E68_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long68-res-bandbreakpoint"></a>

## Theorem 5.2 (constant values of the floor in the weights), page 16

> *Let $`d\ge2`$ and $`k\ge0`$, and suppose every supported index $`i`$ satisfies $`kd\le i<(k+1)d`$. Then $`M(c)=(d!)^kV_{d}(c)`$. In particular, cancellation on the interval $`d\le i<2d`$ forces $`M(c)=0`$; and if every supported index is at least $`d`$ while $`M(c)\ne0`$ and $`V_{d}(c)=0`$, then some supported index is at least $`2d`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos68.PaperComplete.supported_quotient_band`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteSupportedBands.lean#L24)

```lean
theorem supported_quotient_band (f : ℕ →₀ ℤ) (d k : ℕ)
    (hlo : ∀ n ∈ f.support, k * d ≤ n)
    (hhi : ∀ n ∈ f.support, n < (k + 1) * d) :
    factorialMoment f = (d.factorial : ℤ) ^ k * channelNumerator f d
```

2. [`ErdosProblems.Erdos68.PaperComplete.supported_first_band_cancellation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteSupportedBands.lean#L42)

```lean
theorem supported_first_band_cancellation (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hhi : ∀ n ∈ f.support, n < 2 * d)
    (hz : channelNumerator f d = 0) : factorialMoment f = 0
```

3. [`ErdosProblems.Erdos68.PaperComplete.supported_breakpoint_escape`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteSupportedBands.lean#L51)

```lean
theorem supported_breakpoint_escape (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hz : channelNumerator f d = 0) (hm : factorialMoment f ≠ 0) :
    ∃ n ∈ f.support, 2 * d ≤ n
```

<a id="long68-res-bandbreakpoint-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `supported_quotient_band`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_02/Challenge.lean#L79) (E68_02, line 79), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_02/PaperStatementsC.lean#L34) (PaperStatementsC.lean, line 34), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_02.json) (E68_02)
- `supported_first_band_cancellation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_02/Challenge.lean#L69) (E68_02, line 69), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_02/PaperStatementsC.lean#L26) (PaperStatementsC.lean, line 26), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_02.json) (E68_02)
- `supported_breakpoint_escape`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_02/Challenge.lean#L63) (E68_02, line 63), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_02/PaperStatementsC.lean#L21) (PaperStatementsC.lean, line 21), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_02.json) (E68_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long68-res-moment-ideal"></a>

## Theorem 5.3 (the set of attainable moments), page 17

> *Fix $`D\ge2`$ and a prime $`p`$ with $`D/2<p\le D`$. Put
> ``` math
> H=D(2p-1),\qquad
>  G_D=\gcd\{|u_n|:D<n\le H\},\qquad
>  \mu_D=L_D\frac{G_D}{\gcd(G_D,a_D)}.
> ```
> The moments of finite integer vectors supported on $`n\ge2`$ and cancelling all weighted sums $`2,\ldots,D`$ are exactly $`\mu_D\mathbb{Z}`$. The integer $`\mu_D`$ is positive, is independent of the eligible prime $`p`$, and is attained by a vector of coefficients with gcd one, that is, by a primitive vector.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos68.PaperComplete.exact_moment_ideal_with_primitive_attainment`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteMomentIdeal.lean#L242)

```lean
theorem exact_moment_ideal_with_primitive_attainment {D p : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    0 < minimumMoment D p ∧
    (∀ m : ℤ, AttainsMoment D m ↔ minimumMoment D p ∣ m) ∧
    ∃ f : ℕ →₀ ℤ, Admissible f ∧ LowChannels D f ∧
      factorialMoment f = minimumMoment D p ∧ PrimitiveVector f
```

2. [`ErdosProblems.Erdos68.PaperComplete.minimumMoment_independent_prime`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteMomentIdeal.lean#L321)

```lean
theorem minimumMoment_independent_prime {D p q : ℕ} (hD : 2 ≤ D)
    (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hq : q.Prime) (hDq : D / 2 < q) (hqD : q ≤ D) :
    minimumMoment D p = minimumMoment D q
```

<a id="long68-res-moment-ideal-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exact_moment_ideal_with_primitive_attainment`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_02/Challenge.lean#L246) (E68_02, line 246), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_02/MomentIdeal.lean#L45) (MomentIdeal.lean, line 45), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_02.json) (E68_02)
- `minimumMoment_independent_prime`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_02/Challenge.lean#L254) (E68_02, line 254), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_02/MomentIdeal.lean#L102) (MomentIdeal.lean, line 102), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_02.json) (E68_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long68-res-residual-transparency"></a>

## Theorem 5.4 (how the coefficient choices change the remainder), page 18

> *For the vector in (19),
> ``` math
> \mathcal R\!\left(tK_D+\sum_{n>D}z_nU_n\right)
>  =tL_D(S-H_D)+\sum_{n>D}z_n.
> ```
> The residual series converges for every finite vector supported away from index zero. A zero-moment vector has integral residual, and any two finite vectors with the same factorial moment have residuals differing by an integer.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos68.PaperComplete.residual_transparency`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteResidualIdentity.lean#L116)

```lean
theorem residual_transparency {D : ℕ} (hD : 2 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) *
        (_root_.Erdos68.factorialGapSeries - gapPrefixReal D) +
      (coordinateMass z : ℝ)
```

2. [`ErdosProblems.Erdos68.PaperComplete.summable_fullResidual`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteResidualIdentity.lean#L166)

```lean
theorem summable_fullResidual {f : ℕ →₀ ℤ} (h0 : f 0 = 0) :
    Summable (fullResidualTerm f)
```

3. [`ErdosProblems.Erdos68.PaperComplete.zero_moment_residual_integral`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteResidualIdentity.lean#L185)

```lean
theorem zero_moment_residual_integral {f : ℕ →₀ ℤ}
    (h0 : f 0 = 0) (hm : factorialMoment f = 0) :
    ∃ k : ℤ, fullResidual f = (k : ℝ)
```

4. [`ErdosProblems.Erdos68.PaperComplete.equal_moment_residual_integer_difference`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteResidualIdentity.lean#L195)

```lean
theorem equal_moment_residual_integer_difference {f g : ℕ →₀ ℤ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hm : factorialMoment f = factorialMoment g) :
    ∃ k : ℤ, fullResidual f - fullResidual g = (k : ℝ)
```

<a id="long68-res-residual-transparency-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `residual_transparency`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_03/Challenge.lean#L93) (E68_03, line 93), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_03/ResidualIntegerClass.lean#L16) (ResidualIntegerClass.lean, line 16), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_03.json) (E68_03)
- `summable_fullResidual`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_03/Challenge.lean#L101) (E68_03, line 101), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_03/ResidualIntegerClass.lean#L43) (ResidualIntegerClass.lean, line 43), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_03.json) (E68_03)
- `zero_moment_residual_integral`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_03/Challenge.lean#L105) (E68_03, line 105), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_03/ResidualIntegerClass.lean#L66) (ResidualIntegerClass.lean, line 66), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_03.json) (E68_03)
- `equal_moment_residual_integer_difference`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_03/Challenge.lean#L110) (E68_03, line 110), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_03/ResidualIntegerClass.lean#L90) (ResidualIntegerClass.lean, line 90), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_03.json) (E68_03)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `residual_transparency`:

```lean
theorem residual_transparency {D : ℕ} (hD : 2 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) *
        (factorialGapSeries - gapPrefixReal D) +
      (coordinateMass z : ℝ) := by sorry
```

<a id="long68-res-channel-radius"></a>

## Theorem 5.5 (a lower bound for the support parameter), page 19

> *Let $`t,M,R\in\mathbb{N}`$ satisfy
> ``` math
> t\ge2^{32},\qquad M>0,\qquad L_{2t^2}\mid M,\qquad M<(R+1)!-1 .
> ```
> Then $`3t^3<2(R+1)`$. Consequently no family satisfying these hypotheses for all sufficiently large $`t`$ has $`(R(t)+1)/t^3\le3/2`$ eventually, and none has $`R(t)=o(t^3)`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos68.PaperComplete.square_subsequence_radius`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L234)

```lean
theorem square_subsequence_radius {t M R : ℕ}
    (ht : 2 ^ 32 ≤ t) (hM : 0 < M)
    (hdiv : _root_.Erdos68.channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1)
```

2. [`ErdosProblems.Erdos68.PaperComplete.radius_no_eventual_ratio_upper`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L258)

```lean
theorem radius_no_eventual_ratio_upper (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ _root_.Erdos68.channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      (((R t : ℕ) : ℝ) + 1) / (t : ℝ) ^ 3 ≤ (3 : ℝ) / 2
```

3. [`ErdosProblems.Erdos68.PaperComplete.radius_not_littleO`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L277)

```lean
theorem radius_not_littleO (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ _root_.Erdos68.channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => (R t : ℝ)) =o[Filter.atTop]
      (fun t : ℕ => (t : ℝ) ^ 3)
```

<a id="long68-res-channel-radius-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `square_subsequence_radius`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_03/Challenge.lean#L136) (E68_03, line 136), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_03/PaperStatementsB.lean#L87) (PaperStatementsB.lean, line 87), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_03.json) (E68_03)
- `radius_no_eventual_ratio_upper`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_03/Challenge.lean#L120) (E68_03, line 120), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_03/PaperStatementsB.lean#L73) (PaperStatementsB.lean, line 73), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_03.json) (E68_03)
- `radius_not_littleO`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_03/Challenge.lean#L128) (E68_03, line 128), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_03/PaperStatementsB.lean#L80) (PaperStatementsB.lean, line 80), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_03.json) (E68_03)

Challenge for `square_subsequence_radius`:

```lean
theorem square_subsequence_radius {t M R : ℕ}
    (ht : 2 ^ 32 ≤ t) (hM : 0 < M)
    (hdiv : channelLCM (2 * t ^ 2) ∣ M)
    (hsmall : M < (R + 1).factorial - 1) :
    3 * t ^ 3 < 2 * (R + 1) := by sorry
```

Challenge for `radius_no_eventual_ratio_upper`:

```lean
theorem radius_no_eventual_ratio_upper (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      (((R t : ℕ) : ℝ) + 1) / (t : ℝ) ^ 3 ≤ (3 : ℝ) / 2 := by sorry
```

Challenge for `radius_not_littleO`:

```lean
theorem radius_not_littleO (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    ¬ (fun t : ℕ => (R t : ℝ)) =o[Filter.atTop]
      (fun t : ℕ => (t : ℝ) ^ 3) := by sorry
```

<a id="long68-res-radius-constant"></a>

## Corollary 5.6 (the asymptotic lower bound), page 20

> *Let $`M(t),R(t)`$ satisfy $`M(t)>0`$, $`L_{2t^2}\mid M(t)`$ and $`M(t)<(R(t)+1)!-1`$ for all sufficiently large $`t`$. Then
> ``` math
> \liminf_{t\to\infty}\frac{R(t)+1}{t^3}\ \ge\ \frac{16}{9}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.asymptotic_radius_constant_liminf`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteLiminf.lean#L54)

```lean
theorem asymptotic_radius_constant_liminf (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ _root_.Erdos68.channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    (((16 : ℝ) / 9) : EReal) ≤
      Filter.liminf (fun t : ℕ =>
        ((((R t + 1 : ℕ) : ℝ) / (t : ℝ) ^ 3 : ℝ) : EReal)) atTop
```

<a id="long68-res-radius-constant-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `asymptotic_radius_constant_liminf`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_06/Challenge.lean#L164) (E68_06, line 164), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_06/CommonDenominatorGrowth.lean#L35) (CommonDenominatorGrowth.lean, line 35), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_06.json) (E68_06)

Challenge for `asymptotic_radius_constant_liminf`:

```lean
theorem asymptotic_radius_constant_liminf (M R : ℕ → ℕ)
    (hH : ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      0 < M t ∧ channelLCM (2 * t ^ 2) ∣ M t ∧
      M t < (R t + 1).factorial - 1) :
    (((16 : ℝ) / 9) : EReal) ≤
      Filter.liminf (fun t : ℕ =>
        ((((R t + 1 : ℕ) : ℝ) / (t : ℝ) ^ 3 : ℝ) : EReal)) atTop := by sorry
```

<a id="long68-res-translator"></a>

## Theorem 5.7 (changing just one weighted sum), page 21

> *Let $`p\ge3`$ be prime and let $`c_{p-1}=p`$, $`c_p=-1`$, with every other coefficient zero. Then $`M(c)=0`$, $`V_{p}(c)=p!-1`$, and $`V_{d}(c)=0`$ for every $`d\ge2`$ with $`d\ne p`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.prime_channel_corrector`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L299)

```lean
theorem prime_channel_corrector {p : ℕ} (hp : p.Prime) :
    _root_.Erdos68.factorialMoment (_root_.Erdos68.primeTranslatorCoeff p)
      (_root_.Erdos68.primeTranslatorIndex p) = 0 ∧
    _root_.Erdos68.channelNumerator (_root_.Erdos68.primeTranslatorCoeff p)
      (_root_.Erdos68.primeTranslatorIndex p) p = (p.factorial : ℤ) - 1 ∧
    (∀ d : ℕ, 2 ≤ d → d ≠ p →
      _root_.Erdos68.channelNumerator (_root_.Erdos68.primeTranslatorCoeff p)
        (_root_.Erdos68.primeTranslatorIndex p) d = 0)
```

<a id="long68-res-translator-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `prime_channel_corrector`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_04/Challenge.lean#L39) (E68_04, line 39), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_04/PaperStatementsB.lean#L53) (PaperStatementsB.lean, line 53), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_04.json) (E68_04)

Challenge for `prime_channel_corrector`:

```lean
theorem prime_channel_corrector {p : ℕ} (hp : p.Prime) :
    factorialMoment (primeTranslatorCoeff p)
      (primeTranslatorIndex p) = 0 ∧
    channelNumerator (primeTranslatorCoeff p)
      (primeTranslatorIndex p) p = (p.factorial : ℤ) - 1 ∧
    (∀ d : ℕ, 2 ≤ d → d ≠ p →
      channelNumerator (primeTranslatorCoeff p)
        (primeTranslatorIndex p) d = 0) := by sorry
```
