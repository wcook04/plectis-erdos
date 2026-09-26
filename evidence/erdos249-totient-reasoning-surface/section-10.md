# Formal evidence: The Binary Totient Series, Section 10

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="prop-rational-series-preserving-totient-parity"></a>

## Proposition 10.1 (A rational series preserving totient parity and the stated separation properties), page 96

> *There exists $`c:\mathbb N\to\mathbb N`$ such that: $`c(n)\le6`$ for all $`n`$; $`c(n)\le n`$; $`c(n)\equiv\varphi(n)\pmod2`$ for every $`n`$; for every $`N,G,K`$ there is a block of $`K`$ explicit $`(6,0)`$ carry-pulse pairs beyond $`N`$, each pair separated by more than $`G`$; and $`\sum_n c(n)/2^n = 3/2`$.*

The Lean declarations below together state this result.

1. [`Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_six`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L227)

```lean
theorem parityCoboundaryWeight_le_six (n : ℕ) :
    parityCoboundaryWeight n ≤ 6
```

2. [`Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_self`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L155)

```lean
theorem parityCoboundaryWeight_le_self (n : ℕ) :
    parityCoboundaryWeight n ≤ n
```

3. [`Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_mod_two_eq_totient`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L194)

```lean
theorem parityCoboundaryWeight_mod_two_eq_totient (n : ℕ) :
    parityCoboundaryWeight n % 2 = Nat.totient n % 2
```

4. [`Erdos249257.TotientParityCoboundaryCountermodel.exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L457)

```lean
theorem exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs
    (N G K : ℕ) :
    ∃ k : ℕ,
      N < 2 ^ (k + 3) ∧
      ∀ i : ℕ, i < K →
        2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
        parityCoboundaryWeight (2 ^ (k + i + 3)) = 6 ∧
        parityCoboundaryWeight (2 ^ (k + i + 3) + 1) = 0
```

5. [`Erdos249257.TotientParityCoboundaryCountermodel.tsum_parityCoboundaryWeight_eq_three_halves`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L359)

```lean
theorem tsum_parityCoboundaryWeight_eq_three_halves :
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) = 3 / 2
```

<a id="prop-rational-series-preserving-totient-parity-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `parityCoboundaryWeight_le_six`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_26/Challenge.lean#L138) (E249_26, line 138), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L42) (PaperStatementsAG.lean, line 42), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_26.json) (E249_26)
- `parityCoboundaryWeight_le_self`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_26/Challenge.lean#L134) (E249_26, line 134), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L39) (PaperStatementsAG.lean, line 39), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_26.json) (E249_26)
- `parityCoboundaryWeight_mod_two_eq_totient`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_26/Challenge.lean#L142) (E249_26, line 142), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L45) (PaperStatementsAG.lean, line 45), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_26.json) (E249_26)
- `exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_26/Challenge.lean#L124) (E249_26, line 124), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L16) (PaperStatementsAG.lean, line 16), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_26.json) (E249_26)
- `tsum_parityCoboundaryWeight_eq_three_halves`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L65) (E249_02, line 65), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAG.lean#L48) (PaperStatementsAG.lean, line 48), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-complement-divisibility-after-multiplication"></a>

## Lemma 10.2 (Complement divisibility after multiplication), page 98

> *Write $`x=a/b`$ in lowest terms, where $`a\in\mathbb{Z}`$ and $`b\ge1`$. Let $`c\in\mathbb{Z}`$ and let $`H`$ be a positive divisor of $`b`$. If the reduced denominator of $`cx`$ divides $`H`$, then
> ``` math
> b/H\mid c.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.complementDenominator_dvd_scalar`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos249/PaperCompleteR21/ScalarLocalisationAndInversePhaseGauge.lean#L29)

```lean
theorem complementDenominator_dvd_scalar
    (x : ℚ) (c : ℤ) {H : ℕ} (_hHpos : 0 < H) (hH : H ∣ x.den)
    (hscaled : ((c : ℚ) * x).den ∣ H) :
    ((x.den / H : ℕ) : ℤ) ∣ c
```

<a id="lem-complement-divisibility-after-multiplication-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `complementDenominator_dvd_scalar`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_26/Challenge.lean#L149) (E249_26, line 149), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_26/PaperStatementsAJ.lean#L168) (PaperStatementsAJ.lean, line 168), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_26.json) (E249_26)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-nonvanishing-unique-largest-denominator-exponent"></a>

## Lemma 10.3 (Nonvanishing from a unique largest denominator exponent), page 99

> *Let $`I`$ be a finite set, let $`u_i\in\mathbb{Z}`$ and $`e_i\in\mathbb{N}`$ for $`i\in I`$, and suppose that $`m\in I`$ satisfies $`e_i<e_m`$ for every $`i\ne m`$. If $`u_m`$ is odd, then
> ``` math
> 2^{e_m}\sum_{i\in I}\frac{u_i}{2^{e_i}}
>    =\sum_{i\in I}u_i2^{e_m-e_i}\equiv1\pmod2.
> ```
> In particular, the sum is nonzero.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_clearing`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos249/PaperCompleteR20/SignedDyadicClearing.lean#L8)

```lean
theorem signed_dyadic_clearing {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α)
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (2 : ℚ) ^ e m * (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) =
      ((∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i) : ℤ) : ℚ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_sum_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos249/PaperCompleteR20/SignedDyadicClearing.lean#L28)

```lean
theorem signed_dyadic_sum_ne_zero {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) ≠ 0
```

3. [`Erdos249257.SignedQMomentObstruction.scaled_dyadic_sum_odd`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/Erdos249257/SignedQMomentObstruction.lean#L78)

```lean
theorem scaled_dyadic_sum_odd {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) % 2 = 1
```

<a id="lem-nonvanishing-unique-largest-denominator-exponent-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `signed_dyadic_clearing`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_06/Challenge.lean#L108) (E249_06, line 108), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_06/PaperStatementsAE.lean#L170) (PaperStatementsAE.lean, line 170), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_06.json) (E249_06)
- `signed_dyadic_sum_ne_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_06/Challenge.lean#L115) (E249_06, line 115), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_06/PaperStatementsAE.lean#L177) (PaperStatementsAE.lean, line 177), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_06.json) (E249_06)
- `scaled_dyadic_sum_odd`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_06/Challenge.lean#L128) (E249_06, line 128), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_06/PaperStatementsAF.lean#L30) (PaperStatementsAF.lean, line 30), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_06.json) (E249_06)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-nonzero-minor-survives-inverse-phase"></a>

## Proposition 10.4 (A nonzero minor survives inverse-phase column weights), page 100

> *Let $`d\ge1`$ be an integer, let $`e_0,\ldots,e_{d-1}`$ be nonnegative integers, and let $`z_0,\ldots,z_{d-1}`$ be nonzero complex numbers. Write $`P_{ij}=z_j^{e_i}`$, and suppose $`e_{i_0}=1`$ for some $`i_0`$. Multiplying column $`j`$ by $`W_j=z_j^{-1}`$ gives
> ``` math
> (P\operatorname{diag}(W))_{i_0j}=1,\qquad
>  \det(P\operatorname{diag}(W))=\det(P)\prod_{j=0}^{d-1}z_j^{-1}.
> ```
> Thus a nonzero determinant remains nonzero while row $`i_0`$ becomes constant. If all $`|z_j|=1`$, its absolute value is also unchanged.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.inversePhaseGauge_locks_row_and_preserves_minor`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos249/PaperCompleteR21/ScalarLocalisationAndInversePhaseGauge.lean#L51)

```lean
theorem inversePhaseGauge_locks_row_and_preserves_minor
    {d : ℕ} (_hd : 1 ≤ d) (e : Fin d → ℕ) (z : Fin d → ℂ)
    (hz : ∀ j, z j ≠ 0) (i₀ : Fin d) (hi₀ : e i₀ = 1) :
    (∀ j, (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹)) i₀ j = 1) ∧
      Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹))
          = Matrix.det (phasePowerMatrix e z) * ∏ j, (z j)⁻¹ ∧
      (Matrix.det (phasePowerMatrix e z) ≠ 0 →
        Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹)) ≠ 0) ∧
      ((∀ j, ‖z j‖ = 1) →
        ‖Matrix.det (phasePowerMatrix e z * Matrix.diagonal (fun j => (z j)⁻¹))‖
          = ‖Matrix.det (phasePowerMatrix e z)‖)
```

<a id="prop-nonzero-minor-survives-inverse-phase-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `inversePhaseGauge_locks_row_and_preserves_minor`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_26/Challenge.lean#L164) (E249_26, line 164), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_26/PaperStatementsAY.lean#L94) (PaperStatementsAY.lean, line 94), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_26.json) (E249_26)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-tail-integrality-lcm-grid"></a>

## Proposition 10.5 (Tail integrality on an LCM grid), page 100

> *$`S\in\mathbb Q \implies \exists t_1,\ \forall t\ge t_1,\
> \forall q,m:\mathbb N,\ 0<q \implies {R}(q\cdot
> {H}(t)+m\cdot{H}(t)) -
> {R}(q\cdot{H}(t)) \in
> \mathbb Z`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L8)

```lean
theorem lcm_grid_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail ((q + m) * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ)
```

<a id="prop-tail-integrality-lcm-grid-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `lcm_grid_flatness`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_09/Challenge.lean#L267) (E249_09, line 267), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L205) (PaperStatementsAT.lean, line 205), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_09.json) (E249_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-grid-certificate-gives-nonintegral"></a>

## Proposition 10.6 (A finite-grid certificate gives a nonintegral pair), page 100

> *Let $`Q\subseteq\mathbb N_{>0}`$ be finite and nonempty. For each $`q\in Q`$, put $`A_q=\sum_{j=1}^{L}\varphi(qH+j)2^{L-j}`$ and $`B_q=qH+L+2`$. Suppose $`B_q<2^L`$ for every $`q\in Q`$ and
> ``` math
> \forall q_i\in Q\ \exists q_j\in Q,\qquad
>  B_{q_j}<(A_{q_i}-A_{q_j})\bmod2^L.
> ```
> Then $`R_{q_jH}-R_{q_iH}\notin\mathbb Z`$ for some $`q_i,q_j\in Q`$. The proof and a four-point example are given in Theorem 6.56.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L12)

```lean
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L36)

```lean
theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="prop-finite-grid-certificate-gives-nonintegral-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paperGridNumerator_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L275) (E249_10, line 275), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAX.lean#L238) (PaperStatementsAX.lean, line 238), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)
- `finite_grid_nonintegral_pair`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_10/Challenge.lean#L260) (E249_10, line 260), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_10/PaperStatementsAX.lean#L223) (PaperStatementsAX.lean, line 223), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_10.json) (E249_10)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-exact-dyadic-rank-infinite-dimensionality"></a>

## Theorem 10.7 (Exact dyadic rank and infinite-dimensionality), page 101

> *For every $`e\ge1`$, the family
> ``` math
> \{n\mapsto\varphi(n),\ n\mapsto\varphi(2n)\}
>  \ \cup\ \{n\mapsto\varphi(2^j n+r):1\le j\le e,\ 0<r<2^j,\ r\text{ odd}\}
> ```
> is linearly independent over $`\mathbb{Q}`$. It contains $`2^e+1`$ sequences and spans the sections through level $`e`$ by the zero- and even-residue reductions.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_entries`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L33)

```lean
theorem canonicalTotientKernelFamily_entries (e : ℕ) :
    canonicalTotientKernelFamily e (Sum.inl 0) = (fun n => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily e (Sum.inl 1)
        = (fun n => (Nat.totient (2 * n) : ℚ)) ∧
      ∀ (j : Fin e) (r : Fin (2 ^ j.val)),
        canonicalTotientKernelFamily e (Sum.inr ⟨j, r⟩)
          = fun n => (Nat.totient (2 ^ (j.val + 1) * n + (2 * r.val + 1)) : ℚ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_independent_card_and_span`](https://github.com/wcook04/plectis-erdos/blob/7f3dbf0947c387335ffd392b689eea5721017d84/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L53)

```lean
theorem canonicalTotientKernelFamily_independent_card_and_span (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Function.Injective (canonicalTotientKernelFamily e) ∧
      Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 ∧
      Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))
        = Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) ∧
      ¬ FiniteDimensional ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily))
```

<a id="thm-exact-dyadic-rank-infinite-dimensionality-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `canonicalTotientKernelFamily_entries`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_25/Challenge.lean#L260) (E249_25, line 260), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_25/PaperStatementsBB.lean#L24) (PaperStatementsBB.lean, line 24), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_25.json) (E249_25)
- `canonicalTotientKernelFamily_independent_card_and_span`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_26/Challenge.lean#L205) (E249_26, line 205), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_26/PaperStatementsBB.lean#L27) (PaperStatementsBB.lean, line 27), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_26.json) (E249_26)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
