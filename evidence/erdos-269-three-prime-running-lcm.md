# Formal evidence: No Finite Separable Representation\\at Three Prime Generators

This record belongs to the paper [erdos-269-three-prime-running-lcm.pdf](../paper/269/erdos-269-three-prime-running-lcm.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`be89e72217ec`](https://github.com/wcook04/plectis-erdos/tree/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 13 results: 12 with a Lean proof of the whole statement, 1 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 12 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="res-infinite-rank"></a>

## Theorem 2.1 (no finite separation of the kernel), page 2

> *Let $`p,q,r`$ be primes with $`p\ne q`$, $`p\ne r`$ and $`q\ne r`$. For every $`n\ge0`$ there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$ such that, for every $`k\ge0`$,
> ``` math
> \det\bigl(\operatorname{K}(I(a),J(b),k)\bigr)_{0\le a,b<n}\ne0.
> ```
> Consequently, for no finite $`d`$ do there exist rational-valued functions $`f_\ell(i)`$ and $`G_\ell(j,k)`$, $`0\le\ell<d`$, satisfying
> ``` math
> \operatorname{K}(i,j,k)=\sum_{\ell<d}f_\ell(i)G_\ell(j,k)
>  \qquad\hbox{for all }i,j,k.
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperR7.paper_uniform_rank_and_nonseparation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L22)

```lean
theorem paper_uniform_rank_and_nonseparation {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (_hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ, ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
      ∀ k : ℕ, (Matrix.det fun a b : Fin n =>
        threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
    (∀ d : ℕ, ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
      ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k)
```

<a id="res-infinite-rank-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_uniform_rank_and_nonseparation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_02/Challenge.lean#L85) (E269_02, line 85), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_02/PaperStatementsA.lean#L252) (PaperStatementsA.lean, line 252), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_02.json) (E269_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-admissible-modular-minors"></a>

## Corollary 2.2 (the same minors modulo integers coprime to $`30`$), page 3

> *For $`(p,q,r)=(2,3,5)`$ and every $`n\ge1`$, there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$, chosen independently of $`B`$ and $`k`$, such that for every $`B\ge2`$ coprime to $`30`$ and every $`k\ge0`$, the selected $`n\times n`$ kernel matrix has unit determinant over $`\mathbb Z/B\mathbb Z`$, with each reciprocal prime power interpreted by its modular inverse.*

The Lean declaration below states this result or one that implies it. The Lean statement holds for every $n\ge0$ and, for the same $I,J$, also gives nonzero rational determinants at every $k$ and an invertible kernel matrix modulo $B$; its unit-determinant clause for $n\ge1$ is the printed statement.

[`ErdosProblems.Erdos269.PaperR7.admissible_modular_minors`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperR7ModularMinors.lean#L133)

```lean
theorem admissible_modular_minors (n : ℕ) :
    ∃ I J : Fin n → ℕ, Function.Injective I ∧ Function.Injective J ∧
      (∀ k : ℕ,
        (Matrix.det fun i j : Fin n => threePrimeKernelQ 2 3 5 (I i) (J j) k) ≠ 0) ∧
      (∀ B : ℕ, 2 ≤ B → Nat.Coprime B 30 → ∀ k : ℕ,
        IsUnit (Matrix.det fun i j : Fin n => kernelMod235 B (I i) (J j) k) ∧
        IsUnit (Matrix.of fun i j : Fin n => kernelMod235 B (I i) (J j) k))
```

<a id="res-admissible-modular-minors-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `admissible_modular_minors`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_08/Challenge.lean#L103) (E269_08, line 103), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_08/PaperStatementsA.lean#L238) (PaperStatementsA.lean, line 238), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_08.json) (E269_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-finite-cut-rank"></a>

## Proposition 2.4 (rank of a matrix of threshold columns), page 3

> *Let $`m\ge1`$ and let $`c`$ lie in a field with $`c\ne 0,1`$. For $`0\le k\le m`$ write $`v_k`$ for the length-$`m`$ column with a $`1`$ in each of the first $`k`$ coordinates and $`c`$ thereafter. A matrix whose distinct columns are $`v_k`$ for $`k`$ in a nonempty set $`E`$ has rank $`|E|-\mathbf 1_{\{0,m\}\subseteq E}`$.*

The Lean declaration below states this result or one that implies it. The Lean statement drops the hypothesis that $E$ is nonempty; for nonempty $E\subseteq\{0,\ldots,m\}$ and any finite matrix whose set of columns is $\{v_k:k\in E\}$ it gives the printed rank $|E|-\mathbf 1_{\{0,m\}\subseteq E}$.

[`ErdosProblems.Erdos269.PaperR7.rank_cutMatrix`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperR7FiniteCutRank.lean#L182)

```lean
theorem rank_cutMatrix {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutVector c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0
```

<a id="res-finite-cut-rank-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `rank_cutMatrix`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_02/Challenge.lean#L146) (E269_02, line 146), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_02/PaperStructuresH.lean#L18) (PaperStructuresH.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_02.json) (E269_02)

Challenge for `rank_cutMatrix`:

```lean
theorem rank_cutMatrix {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutVector c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0 := by sorry
```

<a id="res-two-prime-transcendence"></a>

## Theorem 3.1 (both two-prime sums), page 4

> *<span id="res:two-prime-repeated-transcendence" label="res:two-prime-repeated-transcendence"></span> Let $`p<q`$ be distinct primes. Put $`\theta=\log p/\log q`$ and $`A=\sum_{n\ge0}p^{-n}q^{-\lfloor n\theta\rfloor}`$. Let $`\mathcal R_{p,q}`$ sum the reciprocal running LCM at every positive $`\{p,q\}`$-smooth integer, and let $`\mathcal D_{p,q}`$ count each distinct running LCM once. Then
> ``` math
> \begin{equation}
> \label{eq:two-prime-affine}
>  \mathcal D_{p,q}=\frac{(q-p)A+p}{q-1},\qquad
>  \mathcal R_{p,q}=\frac{(p+q-1)A-(p-1)A^2}{q-1}.
> \end{equation}
> ```
> Both numbers are transcendental.*

The Lean proof assumes the transcendence theorem of Bugeaud and Laurent. Lean takes this input as a hypothesis (`BugeaudLaurentTranscendence`); it is not proved in Lean.

1. [`ErdosProblems.Erdos269.PaperCompleteR21.two_prime_affine_and_quadratic`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L841)

```lean
theorem two_prime_affine_and_quadratic {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    distinctSum p q
        = (((q : ℝ) - (p : ℝ)) * PaperR7.twoPrimeHeckeValue p q + (p : ℝ))
          / ((q : ℝ) - 1) ∧
      repeatedSum p q
        = (((p : ℝ) + (q : ℝ) - 1) * PaperR7.twoPrimeHeckeValue p q
            - ((p : ℝ) - 1) * (PaperR7.twoPrimeHeckeValue p q) ^ 2)
          / ((q : ℝ) - 1)
```

2. [`ErdosProblems.Erdos269.PaperCompleteR21.two_prime_sums_transcendental`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L872)

```lean
theorem two_prime_sums_transcendental (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (distinctSum p q) ∧ Transcendental ℚ (repeatedSum p q)
```

3. [`ErdosProblems.Erdos269.PaperCompleteR21.runningLcm_eq_twoPrimeHeight`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L88)

```lean
theorem runningLcm_eq_twoPrimeHeight {p q x : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hx : x ≠ 0) :
    runningLcm p q x = twoPrimeHeight p q x
```

4. [`ErdosProblems.Erdos269.PaperCompleteR21.twoPrimeHeight_smooth`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L159)

```lean
theorem twoPrimeHeight_smooth {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (i j : ℕ) :
    twoPrimeHeight p q (p ^ i * q ^ j)
      = (p ^ i * q ^ qExp p q i) * (p ^ pExp p q j * q ^ j)
```

5. [`ErdosProblems.Erdos269.PaperCompleteR21.qExp_pExp_succ`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L190)

```lean
theorem qExp_pExp_succ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (b : ℕ) :
    qExp p q (pExp p q (b + 1)) = b ∧ qExp p q (pExp p q (b + 1) + 1) = b + 1
```

6. [`ErdosProblems.Erdos269.PaperCompleteR21.pExp_qExp_succ`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L228)

```lean
theorem pExp_qExp_succ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) {n : ℕ}
    (hjump : qExp p q (n + 1) ≠ qExp p q n) :
    pExp p q (qExp p q n + 1) = n
```

7. [`ErdosProblems.Erdos269.PaperCompleteR21.runningLcmValues_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L440)

```lean
theorem runningLcmValues_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    runningLcmValues p q =
      Set.range (jumpLeft p q) ∪ Set.range (jumpRight p q)
```

8. [`ErdosProblems.Erdos269.PaperCompleteR21.repeatedSum_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L375)

```lean
theorem repeatedSum_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    repeatedSum p q = (∑' n : ℕ, aTerm p q n) * (∑' j : ℕ, cTerm p q j)
```

9. [`ErdosProblems.Erdos269.PaperCompleteR21.distinctSum_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L497)

```lean
theorem distinctSum_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    distinctSum p q = (∑' n : ℕ, aTerm p q n) + ∑' b : ℕ, cTerm p q (b + 1)
```

10. [`ErdosProblems.Erdos269.PaperCompleteR21.bSum_eq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L603)

```lean
theorem bSum_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (∑' b : ℕ, cTerm p q (b + 1))
      = ((p : ℝ) - ((p : ℝ) - 1) * (∑' n : ℕ, aTerm p q n)) / ((q : ℝ) - 1)
```

11. [`ErdosProblems.Erdos269.PaperCompleteR21.heckeValue_boundary`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L662)

```lean
theorem heckeValue_boundary {p q : ℕ} (hp : 1 < p) (hq : 1 < q) :
    (∑' n : ℕ, aTerm p q n)
      = (p : ℝ) / ((p : ℝ) - 1)
        - ((q : ℝ) - 1) *
          heckeMahlerSeries (Real.logb q p) ((p : ℝ)⁻¹) ((q : ℝ)⁻¹)
```

12. [`ErdosProblems.Erdos269.PaperCompleteR21.irrational_logb_of_primes`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L721)

```lean
theorem irrational_logb_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational (Real.logb q p)
```

13. [`ErdosProblems.Erdos269.PaperCompleteR21.transcendental_heckeValue`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L775)

```lean
theorem transcendental_heckeValue (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (PaperR7.twoPrimeHeckeValue p q)
```

The assumed input [`BugeaudLaurentTranscendence`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L630) is

```lean
def BugeaudLaurentTranscendence : Prop :=
  ∀ θ β α : ℝ, Irrational θ → 0 < θ → θ < 1 →
    IsAlgebraic ℚ β → IsAlgebraic ℚ α → β ≠ 0 → α ≠ 0 →
    |β| < 1 → |β| * |α| ^ θ < 1 →
    Transcendental ℚ (heckeMahlerSeries θ β α)
```

<a id="res-two-prime-transcendence-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-lcm"></a>

## Proposition 4.1 (the running least common multiple), page 5

> *Let $`p,q,r`$ be pairwise distinct primes and $`x\ge1`$. Then the running LCM equals the three-prime height: $`\operatorname{L}(x)=\operatorname{H}(x)`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperCompleteR20.running_lcm_real_cutoff_exact`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L49)

```lean
theorem running_lcm_real_cutoff_exact {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x : ℝ} (hx : 1 ≤ x) :
    realPrefixLcm p q r x = realThreePrimeHeight p q r x
```

<a id="res-lcm-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `running_lcm_real_cutoff_exact`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_01/Challenge.lean#L176) (E269_01, line 176), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L67) (PaperStatementsD.lean, line 67), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_01.json) (E269_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-cell"></a>

## Proposition 4.2 (cells and jumps), page 5

> *The running LCM is constant when the three integer logarithms are constant. A jump in exactly one logarithm multiplies it by the corresponding prime. The first $`n`$ positive powers of each prime, together with $`1`$, form $`3n+1`$ distinct points.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones, for real $x,y\ge1$. Equal integer logarithms give equal running LCMs, and an increase by one in exactly one of $\lfloor\log_px\rfloor$, $\lfloor\log_qx\rfloor$, $\lfloor\log_rx\rfloor$, with the other two unchanged, multiplies the running LCM by that prime. The count also records that the $3n$ positive powers alone are distinct.

1. [`ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_eq_of_sameLogCell`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L65)

```lean
theorem realPrefixLcm_eq_of_sameLogCell
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hcell : SameThreePrimeRealLogCell p q r x y) :
    realPrefixLcm p q r x = realPrefixLcm p q r y
```

2. [`ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_first`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L87)

```lean
theorem realPrefixLcm_jump_first
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊ + 1)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realPrefixLcm p q r y = p * realPrefixLcm p q r x
```

3. [`ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_second`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L117)

```lean
theorem realPrefixLcm_jump_second
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊ + 1)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realPrefixLcm p q r y = q * realPrefixLcm p q r x
```

4. [`ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_third`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L129)

```lean
theorem realPrefixLcm_jump_third
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊ + 1) :
    realPrefixLcm p q r y = r * realPrefixLcm p q r x
```

5. [`ErdosProblems.Erdos269.PaperR7.paper_jump_count`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L69)

```lean
theorem paper_jump_count {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) :
    (threePrimePositiveJumpSet p q r n).card = 3 * n ∧
    (threePrimeJumpSetWithOrigin p q r n).card = 3 * n + 1
```

<a id="res-cell-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `realPrefixLcm_eq_of_sameLogCell`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_01/Challenge.lean#L124) (E269_01, line 124), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L20) (PaperStatementsD.lean, line 20), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_01.json) (E269_01)
- `realPrefixLcm_jump_first`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_01/Challenge.lean#L132) (E269_01, line 132), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L27) (PaperStatementsD.lean, line 27), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_01.json) (E269_01)
- `realPrefixLcm_jump_second`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_01/Challenge.lean#L142) (E269_01, line 142), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L36) (PaperStatementsD.lean, line 36), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_01.json) (E269_01)
- `realPrefixLcm_jump_third`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_01/Challenge.lean#L152) (E269_01, line 152), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L45) (PaperStatementsD.lean, line 45), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_01.json) (E269_01)
- `paper_jump_count`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_01/Challenge.lean#L206) (E269_01, line 206), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_01/PaperStatementsA.lean#L247) (PaperStatementsA.lean, line 247), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_01.json) (E269_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-fibre-prop"></a>

## Proposition 4.3 (grouping terms with the same height), page 6

> *For a finite exponent box $`\mathcal B`$, set $`F(H)=\{(i,j,k)\in\mathcal B:\operatorname{H}(p^iq^jr^k)=H\}`$. Then
> ``` math
> \begin{equation}
> \label{res:fibre}
>  \sum_{(i,j,k)\in\mathcal B}\operatorname{K}(i,j,k)=\sum_H\frac{\#F(H)}H.
> \end{equation}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos269.finiteSmoothKernelSum_groupedByHeight`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L407)

```lean
theorem finiteSmoothKernelSum_groupedByHeight
    (p q r hp hq hr : ℕ) :
    (∑ e ∈ smoothExponentBox hp hq hr,
      threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
      ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
        (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹)
```

<a id="res-fibre-prop-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `finiteSmoothKernelSum_groupedByHeight`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_01/Challenge.lean#L228) (E269_01, line 228), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_01/ThreePrimeStructure.lean#L84) (ThreePrimeStructure.lean, line 84), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_01.json) (E269_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-dyadic-alphabet"></a>

## Lemma 4.4 (integer coefficients and four possible bases), page 6

> *For every $`a\ge0`$, $`m_a`$ is a positive integer and $`b_a\in\{2,6,10,30\}`$. The word “numerator” does not impose the positional-digit restriction $`m_a<b_a`$; that restriction need not hold.*

The Lean declaration below states this result or one that implies it. For every $a\ge0$ the Lean statement gives $m_a\in\mathbb Z_{>0}$ and $b_a\in\{2,6,10,30\}$, and adds $m_4=65$ and $b_4=30$, which show that $m_a<b_a$ can fail. In Lean $b_a$ is defined as $2$, multiplied by $3$ when a power of $3$ lies strictly between $2^a$ and $2^{a+1}$ and by $5$ when a power of $5$ does; `threePrimeHeight_dyadicBlock_succ` proves that this equals $\hgt(2^{a+1})/\hgt(2^a)$.

[`ErdosProblems.Erdos269.PaperCompleteR20.dyadic_alphabet_whole`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperCompleteR20/DyadicAlphabetWhole.lean#L19)

```lean
theorem dyadic_alphabet_whole :
    (∀ a : ℕ,
      (∃ m : ℕ, 0 < m ∧ literalForcing235 a = (m : ℚ)) ∧
      (dyadicBlockBase235 a = 2 ∨ dyadicBlockBase235 a = 6 ∨
        dyadicBlockBase235 a = 10 ∨ dyadicBlockBase235 a = 30)) ∧
    literalForcing235 4 = 65 ∧ dyadicBlockBase235 4 = 30 ∧
    (∃ a : ℕ, dyadicBlockBase235 a < dyadicOrderedBlockDigit235 a)
```

<a id="res-dyadic-alphabet-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `dyadic_alphabet_whole`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_08/Challenge.lean#L145) (E269_08, line 145), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_08/PaperStatementsC.lean#L52) (PaperStatementsC.lean, line 52), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_08.json) (E269_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-actual-orbit"></a>

## Proposition 4.5 (the tail recurrence and a quadratic bound), page 6

> *The series defining $`S,T_a`$ converge. For every $`a\ge0`$,
> ``` math
> X_{a+1}=b_aX_a-m_a,\qquad
>  0<X_a\le\frac{8640}{343}(a+1)^2<90(a+1)^2.
> ```
> For every integer $`B\ge1`$, either some $`BX_a`$ is integral and all later states are integral, or $`\operatorname{dist}(BX_a,\mathbb Z)\ge1/31`$ at arbitrarily large indices.*

The Lean declaration below states this result or one that implies it. The dichotomy is proved for every integer $B$, and the printed statement takes $B\ge1$; convergence of $S$ and $T_a$, the recurrence and the bounds $0<X_a\le\frac{8640}{343}(a+1)^2<90(a+1)^2$ are stated as printed. In the recurrence $b_a$ and $m_a$ enter through closed forms that `threePrimeHeight_dyadicBlock_succ` and `literalForcing235_eq_digit` identify with $\hgt(2^{a+1})/\hgt(2^a)$ and the printed sum defining $m_a$.

[`ErdosProblems.Erdos269.PaperR7.short_actual_orbit`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperR7SeriesIdentification.lean#L168)

```lean
theorem short_actual_orbit :
    Summable smoothReciprocal235 ∧
    (∀ a : ℕ, Summable (fun n : ℕ => dyadicShellMassR235 (a + n))) ∧
    (∀ a : ℕ,
      trueNormalizedState (a + 1) =
        (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
          (dyadicOrderedBlockDigit235 a : ℝ)) ∧
    (∀ a : ℕ, 0 < trueNormalizedState a ∧
      trueNormalizedState a ≤ (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 ∧
      (8640 / 343 : ℝ) * ((a + 1 : ℕ) : ℝ) ^ 2 <
        90 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ B : ℤ,
      (∃ a : ℕ, ∀ n, a ≤ n → ∃ z : ℤ,
        (B : ℝ) * trueNormalizedState n = (z : ℝ)) ∨
      (∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
        FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31)))
```

<a id="res-actual-orbit-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `short_actual_orbit`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_08/Challenge.lean#L160) (E269_08, line 160), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_08/PaperStatementsC.lean#L138) (PaperStatementsC.lean, line 138), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_08.json) (E269_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-denominator-reduction"></a>

## Theorem 4.6 (rationality gives positive integer tails), page 7

> *If $`S=A/D`$ in lowest terms, where $`D=2^u3^v5^wB`$ and $`\gcd(B,30)=1`$, then for every $`a\ge a_0=u+1+2v+3w`$,
> ``` math
> d_a=BX_a\in\mathbb Z_{>0},\qquad
>  d_{a+1}=b_ad_a-Bm_a,\qquad d_a\le90B(a+1)^2.
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement drops the hypotheses that $A/D$ is in lowest terms and that $\gcd(B,30)=1$: it applies to every representation $S=A/D$ with $D=2^u3^v5^wB$ and $B\ge1$, and gives for $a\ge u+1+2v+3w$ that $d_a=BX_a$ is a positive integer with $d_{a+1}=b_ad_a-Bm_a$ and $d_a\le90B(a+1)^2$. There $b_a$ and $m_a$ enter through closed forms that `threePrimeHeight_dyadicBlock_succ` and `literalForcing235_eq_digit` identify with the printed definitions.

[`ErdosProblems.Erdos269.PaperR7.short_fixed_split_bridge`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperR7RationalBridge.lean#L80)

```lean
theorem short_fixed_split_bridge {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a : ℕ, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      0 < paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ ((90 * B * (a + 1) ^ 2 : ℕ) : ℤ)
```

<a id="res-denominator-reduction-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `short_fixed_split_bridge`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_08/Challenge.lean#L178) (E269_08, line 178), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_08/PaperStatementsC.lean#L155) (PaperStatementsC.lean, line 155), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_08.json) (E269_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-exact-onset"></a>

## Corollary 4.7 (the first index at which the denominator clears), page 7

> *Under the same lowest-terms hypothesis, put $`M=2^u3^v5^w`$ and let $`\operatorname{den}`$ denote the positive reduced denominator. For $`a\ge1`$,
> ``` math
> \operatorname{den}(BX_a)=\frac{M}{\gcd(M,h_a)}.
> ```
> Consequently $`BX_a`$ is integral exactly when $`2^a\ge\max(2^{u+1},3^v,5^w)`$. The first such $`a`$ can be found by integer comparisons, without logarithmic rounding.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos269.PaperR13.exact_denominators_and_minimal_clearing`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperExactDenominatorR13.lean#L334)

```lean
theorem exact_denominators_and_minimal_clearing
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a)
    (hval : paperSeries235 =
      (N : ℝ) / ((2 ^ u * 3 ^ v * 5 ^ w * B : ℕ) : ℝ)) :
    ((rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a : ℚ) : ℝ) =
        trueNormalizedState a ∧
      (rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w * B) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      ((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      (((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den = 1 ↔
        firstClearingIndex u v w ≤ a)
```

2. [`ErdosProblems.Erdos269.PaperR13.scaled_state_is_integer_iff_firstClearingIndex_le`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperExactDenominatorR13.lean#L309)

```lean
theorem scaled_state_is_integer_iff_firstClearingIndex_le
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a) :
    (∃ z : ℤ,
      (B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a = (z : ℚ)) ↔
      firstClearingIndex u v w ≤ a
```

3. [`ErdosProblems.Erdos269.PaperR13.clearingCondition_iff_max`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperExactDenominatorR13.lean#L166)

```lean
theorem clearingCondition_iff_max {u v w a : ℕ} :
    ClearingCondition u v w a ↔
      1 ≤ a ∧ max (2 ^ (u + 1)) (max (3 ^ v) (5 ^ w)) ≤ 2 ^ a
```

<a id="res-exact-onset-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exact_denominators_and_minimal_clearing`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_05/Challenge.lean#L152) (E269_05, line 152), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_05/PaperStatementsG.lean#L102) (PaperStatementsG.lean, line 102), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_05.json) (E269_05)
- `scaled_state_is_integer_iff_firstClearingIndex_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_04/Challenge.lean#L150) (E269_04, line 150), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_04/PaperStatementsF.lean#L50) (PaperStatementsF.lean, line 50), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_04.json) (E269_04)
- `clearingCondition_iff_max`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_04/Challenge.lean#L105) (E269_04, line 105), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_04/PaperStatementsA.lean#L243) (PaperStatementsA.lean, line 243), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_04.json) (E269_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-consumer"></a>

## Lemma 5.1 (least positive residues), page 8

> *If $`d`$ is a positive integer with $`d\le K`$ and $`d\equiv -BF\pmod W`$, where $`W\ge1`$, then $`\operatorname{lpr}_W(-BF)\le K`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperR7.paper_finite_endpoint_obstruction`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L138)

```lean
theorem paper_finite_endpoint_obstruction {W K : ℕ} {d B F : ℤ}
    (hW : 0 < W) (hd : 0 < d) (hbound : d ≤ (K : ℤ))
    (hmod : Int.ModEq (W : ℤ) d (-B * F)) :
    leastPositiveResidue W (-B * F) ≤ K
```

<a id="res-consumer-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_finite_endpoint_obstruction`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_08/Challenge.lean#L154) (E269_08, line 154), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_08/PaperStatementsC.lean#L127) (PaperStatementsC.lean, line 127), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_08.json) (E269_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-windowconsumer"></a>

## Theorem 5.2 (a residue criterion for irrationality), page 8

> *The number $`S`$ is irrational if and only if
> ``` math
> \begin{equation}
> \label{eq:escape}
>  \begin{gathered}
>  \text{for every }B\ge1\text{ with }\gcd(B,30)=1
>  \text{ and every }a_0\ge1,\\
>  \text{there are }\ell\ge a_0,\ h\ge1\text{ such that}
>  \operatorname{lpr}_{W_{\ell,h}}(-BF_{\ell,h})>K(B,\ell+h).
>  \end{gathered}
> \end{equation}
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one, with $K(B,\ell+h)=90B(\ell+h+1)^2$ written out. The windows are built from closed forms for $b_a$ and $m_a$ that `threePrimeHeight_dyadicBlock_succ` and `literalForcing235_eq_digit` identify with the printed definitions.

[`ErdosProblems.Erdos269.PaperR7.short_window_equivalence`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos269/PaperR7WindowResults.lean#L51)

```lean
theorem short_window_equivalence :
    Irrational paperSeries235 ↔ ShortPaperEscape
```

<a id="res-windowconsumer-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `short_window_equivalence`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E269_08/Challenge.lean#L217) (E269_08, line 217), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E269_08/PaperStatementsG.lean#L134) (PaperStatementsG.lean, line 134), [replay report](../evidence/comparator/replay-35935225572/receipt-E269_08.json) (E269_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
