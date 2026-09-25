# Formal evidence: The Binary Totient Series, Section 2

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="lem-gsound"></a>

## Lemma 2.1 (A residue certificate excludes an integral tail difference), page 7

> *Let $`c:\mathbb{N}\to\mathbb{N}`$ satisfy $`c(n)\le n`$ for all $`n`$. For $`h,N,L\in\mathbb{N}`$, $`\mathcal C_c(h,N,L) \Rightarrow R^{c}_{N+h} - R^{c}_{N} \notin \mathbb{Z}`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.certificate_sound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/GenericTailCertificates.lean#L66)

```lean
theorem certificate_sound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (h N L : ℕ) (hcert : certificate c h N L) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_difference`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/GenericTailCertificates.lean#L48)

```lean
theorem scaled_difference (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    (2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ) =
      binaryCoeffTail c (N + h + L) - binaryCoeffTail c (N + L)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.truncation_error_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/GenericTailCertificates.lean#L55)

```lean
theorem truncation_error_bound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    |(2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ)| ≤ (N : ℝ) + h + L + 2
```

<a id="lem-gsound-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `certificate_sound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L95) (E249_02, line 95), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L30) (PaperStatementsAW.lean, line 30), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `scaled_difference`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L107) (E249_02, line 107), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L40) (PaperStatementsAW.lean, line 40), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `truncation_error_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L118) (E249_02, line 118), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L49) (PaperStatementsAW.lean, line 49), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-gperiod"></a>

## Lemma 2.2 (Generic tail-period law), page 7

> *Let $`c:\mathbb{N}\to\mathbb{N}`$ satisfy $`c(n)\le n`$ for all $`n`$. If $`T_c = p/(2^{e}m)`$ with $`p\in\mathbb{Z}`$, $`e\ge0`$ and $`m`$ a positive odd integer, and if $`h\ge1`$ satisfies $`m\mid 2^h-1`$, then $`R^{c}_{N+h} - R^{c}_{N} \in \mathbb{Z}`$ for every $`N \ge e`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.generic_tail_period`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/GenericTailCertificates.lean#L98)

```lean
theorem generic_tail_period (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (p : ℤ) (e m h N : ℕ) (hm : 0 < m) (hN : e ≤ N)
    (hdvd : m ∣ 2 ^ h - 1)
    (hS : binaryCoeffSeries c = (p : ℝ) / ((2 : ℝ) ^ e * m)) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∈ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_tail_split`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/GenericTailCertificates.lean#L33)

```lean
theorem scaled_tail_split (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (N L : ℕ) :
    (2 : ℝ) ^ L * binaryCoeffTail c N =
      (windowPrefix c N L : ℝ) + binaryCoeffTail c (N + L)
```

<a id="lem-gperiod-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `generic_tail_period`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L100) (E249_02, line 100), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L34) (PaperStatementsAW.lean, line 34), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `scaled_tail_split`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L113) (E249_02, line 113), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L45) (PaperStatementsAW.lean, line 45), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-gamma"></a>

## Theorem 2.4 (A rational sequence agreeing with any finite totient prefix), page 8

> *Let $`B\ge1`$ and $`P>B`$ be integers. Define $`\gamma : \mathbb{N}\to \mathbb{N}`$ by
> ``` math
> \gamma(n) := \varphi(n) \ \ (n \le B), \qquad
>   \gamma(n) := \begin{cases} n-1, & P \mid n \\ n, & P \nmid n \end{cases}
>   \ \ (n > B).
> ```
> Then:*
> 
> 1.  *$`\gamma(n) \le n`$ for all $`n`$, so $`\gamma`$ lies in the same coefficient class as $`\varphi`$;*
> 
> 2.  *$`\gamma(n) = \varphi(n)`$ for every $`n \le B`$, and consequently $`D_\gamma(h,N,L) = D_\varphi(h,N,L)`$ for every $`(h,N,L)`$ with $`N + h + L \le B`$;*
> 
> 3.  *$`T_\gamma = 2-\sum_{n\le B}(n-\varphi(n))/2^n-1/(2^P-1)\in\mathbb{Q}`$, and the odd part of its reduced denominator is *exactly* $`2^P-1`$;*
> 
> 4.  *$`\mathrm{Sep}_\gamma`$ is false; indeed it fails already at $`h = P`$.*
> 
> *Hence for every $`B`$ there is a coefficient sequence in the same class, agreeing with $`\varphi`$ on all of $`[1,B]`$, whose quantified condition is false.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_le`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodel.lean#L15)

```lean
theorem gamma_le (B P n : ℕ) : gamma B P n ≤ n
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_prefix`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodel.lean#L21)

```lean
theorem gamma_prefix (B P n : ℕ) (hn : n ≤ B) : gamma B P n = Nat.totient n
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.discrepancy_prefix`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodel.lean#L24)

```lean
theorem discrepancy_prefix (B P h N L : ℕ) (hB : N + h + L ≤ B) :
    GenericTailCertificates.discrepancy (gamma B P) h N L =
      GenericTailCertificates.discrepancy Nat.totient h N L
```

4. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_series`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodel.lean#L108)

```lean
theorem exact_series (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = 2 -
      (∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℝ) / 2 ^ n) -
      1 / ((2 : ℝ) ^ P - 1)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.value_cast`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L31)

```lean
theorem value_cast (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = (value B P : ℝ)
```

6. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_denominator`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L39)

```lean
theorem exact_denominator (B P : ℕ) (hBP : B < P) :
    ∃ e ≤ B, (value B P).den = 2 ^ e * (2 ^ P - 1)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.no_certificate_after_prefix`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L51)

```lean
theorem no_certificate_after_prefix (B P : ℕ) (hBP : B < P) :
    ∀ N : ℕ, B ≤ N → ∀ L : ℕ, ¬ GenericTailCertificates.certificate (gamma B P) P N L
```

8. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_not_separation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L69)

```lean
theorem gamma_not_separation (B P : ℕ) (hBP : B < P) : ¬ separation (gamma B P)
```

<a id="thm-gamma-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `gamma_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L140) (E249_02, line 140), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L129) (PaperStatementsAE.lean, line 129), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `gamma_prefix`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L146) (E249_02, line 146), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L133) (PaperStatementsAE.lean, line 133), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `discrepancy_prefix`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L131) (E249_02, line 131), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L122) (PaperStatementsAE.lean, line 122), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `exact_series`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L85) (E249_02, line 85), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L22) (PaperStatementsAW.lean, line 22), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `value_cast`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L91) (E249_02, line 91), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L27) (PaperStatementsAW.lean, line 27), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `exact_denominator`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L136) (E249_02, line 136), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L126) (PaperStatementsAE.lean, line 126), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `no_certificate_after_prefix`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L149) (E249_02, line 149), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L135) (PaperStatementsAE.lean, line 135), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `gamma_not_separation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L143) (E249_02, line 143), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L131) (PaperStatementsAE.lean, line 131), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `discrepancy_prefix`:

```lean
theorem discrepancy_prefix (B P h N L : ℕ) (hB : N + h + L ≤ B) :
    discrepancy (gamma B P) h N L =
      discrepancy Nat.totient h N L := by sorry
```

Challenge for `no_certificate_after_prefix`:

```lean
theorem no_certificate_after_prefix (B P : ℕ) (hBP : B < P) :
    ∀ N : ℕ, B ≤ N → ∀ L : ℕ, ¬ certificate (gamma B P) P N L := by sorry
```

<a id="cor-b1"></a>

## Corollary 2.5 (The limit of a finite-prefix argument), page 8

> *No proof rule uniform over all $`c:\mathbb{N}\to\mathbb{N}`$ with $`c(n)\le n`$ can establish $`\mathrm{Sep}`$ from a single fixed prefix $`\{c(n):n\le B\}`$: Theorem 2.4 supplies a rational countermodel with that same prefix. This does *not* invalidate an argument that uses the fixed arithmetic sequence $`\varphi`$ together with compatible information at arbitrarily large horizons; the theorem gives a different $`\gamma_B`$ for each $`B`$, not one sequence agreeing with $`\varphi`$ at every $`B`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.no_uniform_prefix_rule`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L74)

```lean
theorem no_uniform_prefix_rule (B : ℕ) :
    ¬ (∀ c : ℕ → ℕ, (∀ n, c n ≤ n) → (∀ n, n ≤ B → c n = Nat.totient n) → separation c)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_not_separation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L69)

```lean
theorem gamma_not_separation (B P : ℕ) (hBP : B < P) : ¬ separation (gamma B P)
```

<a id="cor-b1-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `no_uniform_prefix_rule`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L153) (E249_02, line 153), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L138) (PaperStatementsAE.lean, line 138), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)
- `gamma_not_separation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L143) (E249_02, line 143), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L131) (PaperStatementsAE.lean, line 131), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b2"></a>

## Proposition 2.7 (Three particular equivalences), page 9

> 1.  **Certificate completeness.* The complete residue tests considered here are equivalent to the corresponding nonintegrality assertions. Rewriting the quantified condition using one of these equivalences does not weaken it.*
> 
> 2.  **A selectable two-point sample.* The condition is as follows. For every $`h\ge1`$ and $`X_0`$, choose $`X,L\in\mathbb{N}`$ with $`X\ge\max(X_0,1)`$ and $`16(2X+h+L+2)\le2^L`$, a nonempty set $`T\subseteq[X,2X)\cap\mathbb{N}`$, a set $`P\subseteq T\times T`$ of ordered pairs, and a real number $`\delta\ge0`$. With $`E_N=\exp(2\pi iD(h,N,L)/2^L)`$, require
>     ``` math
>     |E_i-E_j|\ge\delta\quad((i,j)\in P),\qquad
>        \frac{2|T|^2}{5}\le |P|\delta^2.
>     ```
>     This condition is equivalent to irrationality. For the converse, irrationality and the doubling map allow $`T=\{N,N+1\}`$ and $`P=\{(N,N+1),(N+1,N)\}`$ at arbitrarily large $`N`$, with $`\delta=9/10`$. The numerical requirement is then $`8/5\le2(9/10)^2`$. The freedom to select $`T`$ matters: this is not an estimate on a sample prescribed in advance, such as all prime positions.*
> 
> 3.  **Four integral tail differences.* For $`H\ge0`$ and positive integers $`p,q`$, the conjunction
>     ``` math
>     R_{2kH}-R_{kH}\in\mathbb{Z}\qquad(k\in\{1,p,q,pq\})
>     ```
>     is equivalent to $`R_{2H}-R_H\in\mathbb{Z}`$ alone. The affine transport identity for $`H\mapsto kH`$ preserves integrality, so the three additional conditions add no restriction. Neither $`p`$ nor $`q`$ need be prime.*
> 
> *These three equivalences explain why these particular reformulations retain the original arithmetic question. They do not rule out useful weaker intermediate lemmas. The full-block and fixed-margin conditions in §<a href="#sec:survivors" data-reference-type="ref" data-reference="sec:survivors">3</a> ask for additional quantitative information that the three arguments above do not supply.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.three_particular_equivalences`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ThreeParticularEquivalences.lean#L33)

```lean
theorem three_particular_equivalences :
    (PeriodMultipleKillSupply ↔ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ (DTWWindowSeparatedPairs ↔
          Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ (∀ H p q : ℕ, 0 < p → 0 < q →
          ((IsIntegralValue (totientTail (2 * H) - totientTail H)
              ∧ IsIntegralValue (totientTail (2 * (p * H)) - totientTail (p * H))
              ∧ IsIntegralValue (totientTail (2 * (q * H)) - totientTail (q * H))
              ∧ IsIntegralValue
                  (totientTail (2 * (p * q * H)) - totientTail (p * q * H)))
            ↔ IsIntegralValue (totientTail (2 * H) - totientTail H)))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.two_point_sample_numerical_requirement`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/ThreeParticularEquivalences.lean#L55)

```lean
theorem two_point_sample_numerical_requirement :
    2 * ((2 : ℝ)) ^ 2 / 5 = 8 / 5 ∧ (8 : ℝ) / 5 ≤ 2 * (9 / 10) ^ 2
```

<a id="prop-b2-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `three_particular_equivalences`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L86) (E249_03, line 86), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsAU.lean#L439) (PaperStatementsAU.lean, line 439), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `two_point_sample_numerical_requirement`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L37) (E249_03, line 37), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsAK.lean#L99) (PaperStatementsAK.lean, line 99), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b4"></a>

## Proposition 2.9 (Failure of a specified two-adic congruence construction), page 10

> *A certificate requires the residue to lie farther than $`N+h+L+2`$ from either endpoint modulo $`2^L`$. In the specific construction below, a pulse places the residue at $`2^{K-1}`$ modulo $`2^K`$, but the defining congruence is $`p\equiv1+2^{K-1}\pmod{2^K}`$. Hence $`p\ge1+2^{K-1}`$. At $`N=p-K`$, $`h=H`$, and $`L=K`$, the error bound is $`p+H+2>2^{K-1}`$, so the residue does not satisfy the certificate inequalities. This calculation defeats this construction at every depth. It does not prove a corresponding statement for every use of the Chinese Remainder Theorem or every prescribed totient pattern.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_construction_never_certifies`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseCertificateFailure.lean#L29)

```lean
theorem twoAdic_pulse_construction_never_certifies
    (H K : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, p.Prime ∧ H + K < p ∧ 2 ^ (K - 1) < p ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ¬ certifiedKill H (p - K) K
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_defining_congruence`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseCertificateFailure.lean#L60)

```lean
theorem twoAdic_pulse_defining_congruence (H K B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧ 1 + 2 ^ (K - 1) ≤ p
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_error_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseCertificateFailure.lean#L85)

```lean
theorem twoAdic_pulse_error_bound (H K p : ℕ) (hKp : K ≤ p)
    (hp : 2 ^ (K - 1) < p) :
    (p - K) + H + K + 2 = p + H + 2 ∧ 2 ^ (K - 1) < p + H + 2
```

<a id="prop-b4-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `twoAdic_pulse_construction_never_certifies`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L99) (E249_03, line 99), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsAU.lean#L482) (PaperStatementsAU.lean, line 482), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `twoAdic_pulse_defining_congruence`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L27) (E249_03, line 27), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsAK.lean#L82) (PaperStatementsAK.lean, line 82), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `twoAdic_pulse_error_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L32) (E249_03, line 32), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsAK.lean#L86) (PaperStatementsAK.lean, line 86), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b5"></a>

## Proposition 2.11 (Information lost by specific carry descriptions), page 10

> 1.  *Fix $`m\ge2`$ and write $`R=\lfloor(m+1)/2\rfloor`$. For $`r=0,\ldots,R`$, let $`c_r`$ vanish except at $`c_r(m)=R-r`$ and $`c_r(m+1)=2r`$. Each sequence satisfies $`0\le c_r(n)\le n`$, has the same binary sum $`R2^{-m}`$, and has the same coefficients and scaled tails before position $`m`$. Its scaled tail at position $`m`$ is $`r`$. The common history therefore does not determine that tail. A finite set of labels that determines the tail for each member of this family must contain at least $`R+1=\lfloor(m+1)/2\rfloor+1`$ elements, one for each value of $`r`$.*
> 
> 2.  *Reduction modulo $`2^L`$ forgets the initial value after the same $`L`$ recurrence steps: two affine binary orbits with different seeds satisfy $`\mathrm{orbit}_u(L) - \mathrm{orbit}_v(L) = 2^{L}(u_0 - v_0)`$, so the endpoint residue mod $`2^{L}`$ is independent of the initial carry.*
> 
> 3.  *Fix a precision $`u\ge1`$, a finite list of nonnegative valuations $`\nu_j`$ and odd integers $`a_j`$, and an initial integer $`e_0`$. There are integers $`z_j`$ such that
>     ``` math
>     c_j=2^{\nu_j}(a_j+2^u z_j),\qquad
>        e_{j+1}=2e_j+c_j,\qquad |e_{j+1}|\le2^{\nu_j+u-1}.
>     ```
>     At each step, choose the centred representative of $`2e_j+2^{\nu_j}a_j`$ modulo $`2^{\nu_j+u}`$. The unrestricted integers $`z_j`$ are essential: the assertion does not prescribe the full coefficients $`c_j`$.*
> 
> *These statements exclude decoders using only the specified common history, distinctions using only the endpoint residue, and contradictions using only the stated local symbols. They do not prove that the actual totient expansion cannot be studied by automata. A proposed application must verify that it uses no additional arithmetic information that the comparison families fail to preserve.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_common_history`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L93)

```lean
theorem balancedPulse_common_history (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r ≤ balancedPulseRadius m) :
    (∀ n : ℕ, n ≠ m → n ≠ m + 1 → balancedPulseCoeff m r n = 0)
      ∧ balancedPulseCoeff m r m = balancedPulseRadius m - r
      ∧ balancedPulseCoeff m r (m + 1) = 2 * r
      ∧ (∀ n : ℕ, balancedPulseCoeff m r n ≤ n)
      ∧ binaryCoeffSeries (balancedPulseCoeff m r)
          = (balancedPulseRadius m : ℝ) / 2 ^ m
      ∧ (∀ N : ℕ, N < m → binaryCoeffTail (balancedPulseCoeff m r) N
          = (balancedPulseRadius m : ℝ) / 2 ^ (m - N))
      ∧ binaryCoeffTail (balancedPulseCoeff m r) m = (r : ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_tail_at`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L30)

```lean
theorem balancedPulse_tail_at (m r : ℕ) (hm : 2 ≤ m)
    (hr : r ≤ balancedPulseRadius m) :
    binaryCoeffTail (balancedPulseCoeff m r) m = (r : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_series`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L76)

```lean
theorem balancedPulse_series (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r ≤ balancedPulseRadius m) :
    binaryCoeffSeries (balancedPulseCoeff m r)
      = (balancedPulseRadius m : ℝ) / 2 ^ m
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_label_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L114)

```lean
theorem balancedPulse_label_lower_bound {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ) (decode : Λ → ℕ)
    (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_no_decoder_from_common_state`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L122)

```lean
theorem balancedPulse_no_decoder_from_common_state
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.affineBinaryOrbit_difference_and_reset`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L134)

```lean
theorem affineBinaryOrbit_difference_and_reset (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L = (2 : ℤ) ^ L * (u0 - v0)
      ∧ affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L]
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.fixed_precision_carry_completion`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L146)

```lean
theorem fixed_precision_carry_completion (u : ℕ) (hu : 0 < u)
    (symbols : List VUSymbol) (hodd : ∀ σ ∈ symbols, Odd σ.unit) (e : ℤ) :
    ∃ states : List ℤ,
      VUOrbit u e symbols states ∧
      List.Forall₂ (fun σ e' => |e'| ≤ vuRadius u σ) symbols states
```

<a id="prop-b5-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `balancedPulse_common_history`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L124) (E249_03, line 124), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsAZ.lean#L18) (PaperStatementsAZ.lean, line 18), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `balancedPulse_tail_at`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L156) (E249_03, line 156), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsAZ.lean#L47) (PaperStatementsAZ.lean, line 47), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `balancedPulse_series`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L150) (E249_03, line 150), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsAZ.lean#L42) (PaperStatementsAZ.lean, line 42), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `balancedPulse_label_lower_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L137) (E249_03, line 137), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsAZ.lean#L30) (PaperStatementsAZ.lean, line 30), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `balancedPulse_no_decoder_from_common_state`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L143) (E249_03, line 143), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsAZ.lean#L36) (PaperStatementsAZ.lean, line 36), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `affineBinaryOrbit_difference_and_reset`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L170) (E249_03, line 170), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsD.lean#L18) (PaperStatementsD.lean, line 18), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `fixed_precision_carry_completion`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L197) (E249_03, line 197), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStructuresR.lean#L63) (PaperStructuresR.lean, line 63), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b6"></a>

## Proposition 2.12 (Four limits of particular linear constructions), page 11

> *The following four constructions have different limitations. They must not be read as a claim that every finite family of totient sections is independent: the full family has the explicit relations described in the short paper.*
> 
> 1.  **Dyadic sections and an integer identity.* The retained family of $`2^e+1`$ dyadic sections is linearly independent over $`\mathbb{Q}`$ for $`e\ge1`$ (Proposition 1.6). Separately, positive integers $`Q,v`$ and integers $`A,b`$ cannot satisfy
>     ``` math
>     A\ne0,\qquad QvA=b,\qquad |b|<Qv,
>     ```
>     because $`|A|\ge1`$ gives $`|b|\ge Qv`$. This elementary incompatibility concerns the displayed requirements; it does not exclude every argument using an adjugate matrix.*
> 
> 2.  **Möbius incidence.* $`U_N(i,j) = \mu((i{+}1)/(j{+}1))`$ when $`(j{+}1) \mid (i{+}1)`$ and $`0`$ otherwise is lower triangular with unit diagonal, so $`\det U_N = 1`$ for every $`N`$. Hence multiplication by $`U_N`$ is injective; the corresponding coefficient transformation cannot create a nonzero vector in its kernel.*
> 
> 3.  **Adjugate reconstruction.* Let $`w_i\in\mathbb{Q}`$ and $`x_i\in\mathbb{N}`$ be finite families with $`\sum_i w_i\varphi(x_i)=1`$. Reconstructing each value from two tails and bounding them separately gives the error bound $`\sum_i|w_i|(3x_i+4)`$. It is at least $`3`$, since
>     ``` math
>     1\le\sum_i|w_i|\varphi(x_i)\le\sum_i|w_i|x_i.
>     ```
>     Consequently this particular bound cannot be less than $`1`$, whatever the size of the evaluation matrix.*
> 
> 4.  **Finite combinations of shifts.* The synthetic sequence in Observation <a href="#prop:B4b-kill" data-reference-type="ref" data-reference="prop:B4b-kill">164</a> has the prescribed differences $`a_{(q-1)H-1}=\varphi(H)`$ for $`2\le q<t`$, where $`H=\operatorname{lcm}(1,\ldots,t)`$. It is of the form $`a_i=2c_i-c_{i+1}`$, and every finite integer combination of its shifts has the same form with a correspondingly shifted state. Thus these linear operations alone do not remove the compatible carry recurrence. Their uniform bounds depend on the absolute coefficient sum, as made explicit in that observation. The construction does not assert that $`a_i`$ equals the actual totient difference at other indices.*
> 
> *A further limitation concerns quotients of the finite sums $`t(Y,r)=\sum_{d=1}^{Y}\mu(d)/(2^d-1)^r`$. For $`e\ge1`$ and $`Y\ge4`$,
> ``` math
> \frac{t(Y,e+2)^2}{t(Y,2e+2)}-(S-\tfrac12)>\frac1{480}.
> ```
> The proof bounds each infinite sum $`\sum_{d\ge1}\mu(d)/(2^d-1)^r`$, $`r\ge3`$, between $`1429/1512`$ and $`1`$, and its truncation error after $`Y\ge4`$ terms by $`1/3584`$. Thus the lower bound holds for every stated pair $`e,Y`$, not just a finite list of computed examples. These results concern the listed matrices, estimates, and comparison sequence. The fourth item has the explicit construction and source theorem given in Observation <a href="#prop:B4b-kill" data-reference-type="ref" data-reference="prop:B4b-kill">164</a>. A different finite-dimensional argument, or one using further arithmetic assumptions, is not excluded. Proposition 1.7 is conditional on rationality of $`S`$ and is not, by itself, a counterexample. The separate rational $`5/4`$ comparison supplies the counterexample to the generic rank bound.*

The Lean declarations below together state this result or one that implies it. Independence of the $2^e+1$ retained dyadic sections is proved for every $e\ge0$, and item (i) takes $e\ge1$; the synthetic sequence of item (iv) is built for $t\ge3$, the range of the observation it cites. In item (iii) the bound $\sum_i|w_i|(3x_i+4)$ is the Lean definition of the two-tail cost, obtained by writing $\varphi(x)=2R_{x-1}-R_x$ and using $R_M\le M+2$ for each tail; the Lean statement proves the two displayed inequalities and that this cost is at least $3$. The remaining items, the bounds $1429/1512\le\sum_{d\ge1}\mu(d)/(2^d-1)^r<1$ for $r\ge3$ with truncation error at most $1/3584$ for $Y\ge4$, and the $1/480$ inequality are stated as printed.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_retained_dyadic_sections_independent`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L72)

```lean
theorem b6_retained_dyadic_sections_independent (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1
      ∧ LinearIndependent ℚ (canonicalTotientKernelFamily e)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_compressed_adjoint_identity_impossible`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L80)

```lean
theorem b6_compressed_adjoint_identity_impossible
    {Q v : ℕ} (hQ : 0 < Q) (hv : 0 < v) {A b : ℤ}
    (hA : A ≠ 0) (hid : (Q : ℤ) * (v : ℤ) * A = b) :
    ¬ |b| < (Q : ℤ) * (v : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_mobius_incidence_unimodular_and_injective`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L101)

```lean
theorem b6_mobius_incidence_unimodular_and_injective (N : ℕ) :
    (∀ i j : Fin N,
        IncidenceQuotientHermitePade.incidenceMobiusMatrix N i j =
          if (j : ℕ) + 1 ∣ (i : ℕ) + 1 then
            ArithmeticFunction.moebius (((i : ℕ) + 1) / ((j : ℕ) + 1)) else 0)
      ∧ (IncidenceQuotientHermitePade.incidenceMobiusMatrix N).BlockTriangular
          OrderDual.toDual
      ∧ (∀ i : Fin N,
          IncidenceQuotientHermitePade.incidenceMobiusMatrix N i i = 1)
      ∧ Matrix.det (IncidenceQuotientHermitePade.incidenceMobiusMatrix N) = 1
      ∧ Function.Injective
          (IncidenceQuotientHermitePade.incidenceMobiusMatrix N).mulVec
      ∧ ∀ c : Fin N → ℤ,
          (IncidenceQuotientHermitePade.incidenceMobiusMatrix N).mulVec c = 0
            ↔ c = 0
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_adjugate_tail_cost_floor`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L129)

```lean
theorem b6_adjugate_tail_cost_floor
    {ι : Type*} [Fintype ι] (w : ι → ℚ) (x : ι → ℕ)
    (hisolate : ∑ i, w i * (Nat.totient (x i) : ℚ) = 1) :
    (1 : ℚ) ≤ ∑ i, |w i| * (Nat.totient (x i) : ℚ)
      ∧ (∑ i, |w i| * (Nat.totient (x i) : ℚ)) ≤ ∑ i, |w i| * (x i : ℚ)
      ∧ totientAdjugateTailCost w x = ∑ i, |w i| * (3 * (x i : ℚ) + 4)
      ∧ (3 : ℚ) ≤ totientAdjugateTailCost w x
      ∧ ¬ totientAdjugateTailCost w x < 1
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_synthetic_sequence_prescribed_differences`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L165)

```lean
theorem b6_synthetic_sequence_prescribed_differences {t : ℕ} (ht : 3 ≤ t) :
    (∀ k : ℕ, k ∈ lcmAnchorStates t →
        lcmAnchorPulseState t k = -(Nat.totient (periodLcm t) : ℤ))
      ∧ (∀ k : ℕ, k ∉ lcmAnchorStates t → lcmAnchorPulseState t k = 0)
      ∧ (∀ q : ℕ, 2 ≤ q → q < t →
          (q - 1) * periodLcm t ∈ lcmAnchorStates t)
      ∧ (∀ i : ℕ, lcmAnchorPulseLetter t i =
          2 * lcmAnchorPulseState t i - lcmAnchorPulseState t (i + 1))
      ∧ ∀ q : ℕ, 2 ≤ q → q < t →
          lcmAnchorPulseLetter t ((q - 1) * periodLcm t - 1)
              = (Nat.totient (periodLcm t) : ℤ)
            ∧ lcmAnchorPulseLetter t ((q - 1) * periodLcm t - 1)
              = deltaTotient (periodLcm t) (q * periodLcm t)
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_synthetic_shift_combinations_same_form`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L199)

```lean
theorem b6_synthetic_shift_combinations_same_form
    (t : ℕ) (terms : List (ℕ × ℤ)) :
    (∀ i : ℕ,
        lcmAnchorShiftPolynomialState t terms i =
          shiftLinearCombination terms (lcmAnchorPulseState t) i)
      ∧ (∀ i : ℕ,
          lcmAnchorShiftPolynomialLetter t terms i =
            shiftLinearCombination terms (lcmAnchorPulseLetter t) i)
      ∧ (∀ i : ℕ,
          lcmAnchorShiftPolynomialLetter t terms i =
            2 * lcmAnchorShiftPolynomialState t terms i -
              lcmAnchorShiftPolynomialState t terms (i + 1))
      ∧ (∀ n L : ℕ,
          dyadicClearedPrefix (lcmAnchorShiftPolynomialLetter t terms) n L =
            (2 : ℤ) ^ L * lcmAnchorShiftPolynomialState t terms n -
              lcmAnchorShiftPolynomialState t terms (n + L))
      ∧ (∀ i : ℕ, |lcmAnchorShiftPolynomialState t terms i| ≤
          shiftLinearWeight terms * (Nat.totient (periodLcm t) : ℤ))
      ∧ (∀ i : ℕ, |lcmAnchorShiftPolynomialLetter t terms i| ≤
          shiftLinearWeight terms * (2 * (Nat.totient (periodLcm t) : ℤ)))
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersennePrefix_eq_icc_sum`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L236)

```lean
theorem b6_mobiusMersennePrefix_eq_icc_sum (Y r : ℕ) :
    mobiusMersennePrefix Y r =
      ∑ d ∈ Finset.Icc 1 Y,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ r
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersenne_rung_estimates`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L253)

```lean
theorem b6_mobiusMersenne_rung_estimates {r Y : ℕ} (hr : 3 ≤ r) (hY : 4 ≤ Y) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r
      ∧ mobiusMersenneTheta r < 1
      ∧ |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤ (1 : ℝ) / 3584
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L262)

```lean
theorem b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half :
    mobiusMersenneTheta 2 = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L270)

```lean
theorem b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      (∑ d ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ (e + 2)) ^ 2 /
        (∑ d ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ (2 * e + 2)) -
        ((∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2)
```

<a id="prop-b6-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `b6_retained_dyadic_sections_independent`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L158) (E249_04, line 158), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsL.lean#L18) (PaperStatementsL.lean, line 18), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `b6_compressed_adjoint_identity_impossible`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L221) (E249_03, line 221), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsG.lean#L104) (PaperStatementsG.lean, line 104), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `b6_mobius_incidence_unimodular_and_injective`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L125) (E249_04, line 125), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsK.lean#L17) (PaperStatementsK.lean, line 17), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `b6_adjugate_tail_cost_floor`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L211) (E249_03, line 211), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsG.lean#L95) (PaperStatementsG.lean, line 95), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `b6_synthetic_sequence_prescribed_differences`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L262) (E249_03, line 262), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsI.lean#L120) (PaperStatementsI.lean, line 120), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)
- `b6_synthetic_shift_combinations_same_form`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L82) (E249_04, line 82), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsI.lean#L117) (PaperStatementsI.lean, line 117), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `b6_mobiusMersennePrefix_eq_icc_sum`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L177) (E249_04, line 177), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsO.lean#L23) (PaperStatementsO.lean, line 23), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `b6_mobiusMersenne_rung_estimates`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L183) (E249_04, line 183), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsO.lean#L28) (PaperStatementsO.lean, line 28), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L111) (E249_04, line 111), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsJ.lean#L20) (PaperStatementsJ.lean, line 20), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_03/Challenge.lean#L227) (E249_03, line 227), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_03/PaperStatementsG.lean#L109) (PaperStatementsG.lean, line 109), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_03.json) (E249_03)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `b6_mobius_incidence_unimodular_and_injective`:

```lean
theorem b6_mobius_incidence_unimodular_and_injective (N : ℕ) :
    (∀ i j : Fin N,
        incidenceMobiusMatrix N i j =
          if (j : ℕ) + 1 ∣ (i : ℕ) + 1 then
            ArithmeticFunction.moebius (((i : ℕ) + 1) / ((j : ℕ) + 1)) else 0)
      ∧ (incidenceMobiusMatrix N).BlockTriangular
          OrderDual.toDual
      ∧ (∀ i : Fin N,
          incidenceMobiusMatrix N i i = 1)
      ∧ Matrix.det (incidenceMobiusMatrix N) = 1
      ∧ Function.Injective
          (incidenceMobiusMatrix N).mulVec
      ∧ ∀ c : Fin N → ℤ,
          (incidenceMobiusMatrix N).mulVec c = 0
            ↔ c = 0 := by sorry
```

<a id="prop-b7"></a>

## Proposition 2.13 (The coefficient properties of the rational example), page 12

> *The rational sequence in Proposition 1.9 satisfies uniform boundedness, $`c(n)\le n`$, agreement with $`\varphi(n)`$ modulo $`2`$ at every index, and the stated separated-carry form of aperiodicity. Consequently, those properties alone cannot imply irrationality of a dyadic series. The example does not exclude arguments using further totient identities, including its multiplicative relations.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_rational_parityComparison`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalParityCountermodelProperties.lean#L28)

```lean
theorem exists_rational_parityComparison :
    ∃ c : ℕ → ℕ, ParityComparisonProperties c ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.parityComparisonProperties_do_not_imply_irrational`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalParityCountermodelProperties.lean#L37)

```lean
theorem parityComparisonProperties_do_not_imply_irrational :
    ¬ ∀ c : ℕ → ℕ, ParityComparisonProperties c →
        Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n)
```

<a id="prop-b7-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exists_rational_parityComparison`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L200) (E249_04, line 200), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAJ.lean#L301) (PaperStatementsAJ.lean, line 301), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `parityComparisonProperties_do_not_imply_irrational`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L205) (E249_04, line 205), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAJ.lean#L468) (PaperStatementsAJ.lean, line 468), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
