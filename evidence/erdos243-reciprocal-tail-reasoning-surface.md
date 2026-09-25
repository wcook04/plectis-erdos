# Formal evidence: Reciprocal-Tail Rigidity: Theorems, Proofs and Questions

This record belongs to the paper [erdos243-reciprocal-tail-reasoning-surface.pdf](../paper/243/erdos243-reciprocal-tail-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`be89e72217ec`](https://github.com/wcook04/plectis-erdos/tree/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 53 results: 53 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 51 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="long243-res-cubicrate"></a>

## Theorem 2.1 (cubic-rate irrationality), page 3

> *If strictly increasing positive integers satisfy $`a_n^2/a_{n+1}=1+3/n+o(n^{-3})`$, then $`\sum_n1/a_n`$ is irrational.*

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

<a id="long243-res-cubicrate-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cubic_rate_irrationality_unconditional`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L76) (E243_01, line 76), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStructuresAC.lean#L31) (PaperStructuresAC.lean, line 31), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-nonintegralrate"></a>

## Theorem

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR21.nonintegral_regular_rate_irrational`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/NonintegralRegularRate.lean#L196)

```lean
theorem nonintegral_regular_rate_irrational
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (l : ℝ) (hl : 1 < l) (hnonint : ∀ d : ℕ, l ≠ (d : ℝ))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ l *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + l / (n : ℝ))))
      atTop (nhds 0)) :
    Irrational (∑' n : ℕ, 1 / (a n : ℝ))
```

<a id="long243-res-nonintegralrate-comparator"></a>

**Comparator:** not yet compared.

<a id="long243-res-cubicexclusion"></a>

## Theorem 2.2 (rising-factorial cubic exclusion), page 3

> *Let $`a,C,D:\mathbb{N}\to\mathbb{Z}_{>0}`$ satisfy
> ``` math
> \begin{equation}
> \label{long243:eq:cubicorbit}
>  C_{n+1}=a_nC_n-D_n,\qquad D_{n+1}=a_nD_n .
> \end{equation}
> ```
> Then for every $`A\in\mathbb{Q}_{>0}`$ and every $`B\in\mathbb{Q}`$,
> ``` math
> \liminf_{X\to\infty}
>  \frac{\#\{n\le X:C_n\ne A\,n(n+1)(n+2)+B\}}{X}>0 .
> ```
> In particular no such orbit satisfies $`C_n=A\,n(n+1)(n+2)+B`$ for all large $`n`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR21.cubic_exclusion_unconditional`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L54)

```lean
theorem cubic_exclusion_unconditional
    (a C D : ℕ → ℤ) (ha : ∀ n, 0 < a n) (hC : ∀ n, 0 < C n) (hD : ∀ n, 0 < D n)
    (hCrec : ∀ n, C (n + 1) = a n * C n - D n)
    (hDrec : ∀ n, D (n + 1) = a n * D n)
    (A B : ℚ) (hA : 0 < A) :
    (∃ dens : ℝ, 0 < dens ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        dens * (X : ℝ) ≤ (exceptionCount
          {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}
          (X + 1) : ℝ)) ∧
      ¬ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℚ) = A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B
```

<a id="long243-res-cubicexclusion-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cubic_exclusion_unconditional`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L63) (E243_01, line 63), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStructuresAC.lean#L19) (PaperStructuresAC.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-periodicobstruction"></a>

## Lemma 2.3 (periodic obstruction principle), page 5

> *Let $`h,L`$ be positive integers and let $`j_1,\ldots,j_L`$ be fixed integer offsets. Suppose that for every sufficiently large $`n`$ in one residue class modulo $`h`$ at least one of $`n+j_1,\ldots,n+j_L`$ lies in $`S`$. Then $`\underline d(S)\ge1/(Lh)`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR11.fixed_offsets_periodic_lowerDensity`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR11/DensityTransport.lean#L156)

```lean
theorem fixed_offsets_periodic_lowerDensity (E : Set ℕ) (s L T r : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hr : r < s) (offset : Fin L → ℕ)
    (hhit : ∀ n : ℕ, T ≤ n → n % s = r →
      ∃ i : Fin L, n + offset i ∈ E) :
    LowerDensityAtLeast E (1 / ((L : ℝ) * (s : ℝ)))
```

<a id="long243-res-periodicobstruction-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `fixed_offsets_periodic_lowerDensity`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L108) (E243_01, line 108), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/CompletePaperRecords.lean#L96) (CompletePaperRecords.lean, line 96), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-gcdshape"></a>

## Lemma 2.4 (gcd stabilisation and the primitive shape), page 5

> *Write $`G_n=\gcd(C_n,D_n)`$. Then $`6A`$ is a positive integer, $`G_n`$ divides $`6A`$ for every $`n`$, and $`G_n`$ is eventually equal to a positive integer $`g`$. On the tail where $`G_n=g`$, put $`u_n=C_n/g`$, $`v_n=D_n/g`$ and $`Q(n)=P(n)/g`$. Then
> ``` math
> \begin{equation}
> \label{long243:eq:primitivetail}
>  u_{n+1}=a_nu_n-v_n,\qquad v_{n+1}=a_nv_n,\qquad \gcd(u_n,v_n)=1,
>  \qquad\gcd(u_n,u_{n+1})=1,
> \end{equation}
> ```
> and there are $`m\in\mathbb{Z}_{>0}`$ and $`c\in\{-1,1\}`$ with
> ``` math
> \begin{equation}
> \label{long243:eq:Qmc}
>  Q(n)=\frac m6n(n+1)(n+2)+c .
> \end{equation}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR21.cubic_profile_gcd_stabilisation_and_primitive_shape`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/CubicProfileGcdShape.lean#L103)

```lean
theorem cubic_profile_gcd_stabilisation_and_primitive_shape
    (a C D : ℕ → ℕ) (A B : ℚ) (hA : 0 < A)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hzero : ZeroLowerDensity
      {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}) :
    ∃ M : ℤ, 0 < M ∧ (M : ℚ) = 6 * A ∧
      (∀ n : ℕ, (Nat.gcd (C n) (D n) : ℤ) ∣ M) ∧
      ∃ g N : ℕ, 0 < g ∧
        (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
        ∃ m c : ℤ, 0 < m ∧ (c = 1 ∨ c = -1) ∧
          (∀ n : ℕ,
            (A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B) / (g : ℚ)
              = (m : ℚ) / 6 * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + (c : ℚ)) ∧
          (∀ n, N ≤ n →
            C (n + 1) / g + D n / g = a n * (C n / g) ∧
            D (n + 1) / g = a n * (D n / g) ∧
            Nat.Coprime (C n / g) (D n / g) ∧
            Nat.Coprime (C n / g) (C (n + 1) / g) ∧
            0 < C n / g ∧ 0 < D n / g)
```

<a id="long243-res-gcdshape-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cubic_profile_gcd_stabilisation_and_primitive_shape`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L138) (E243_01, line 138), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStatementsA.lean#L74) (PaperStatementsA.lean, line 74), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-reduciblecase"></a>

## Lemma 2.5 (the multiplier supply, and the reducible case), page 6

> *On the primitive tail, $`\gcd(a_n,v_n)=1`$, the multipliers at distinct indices are pairwise coprime, infinitely many of them exceed $`1`$, and the cubic $`Q_{m,c}`$ of <a href="#long243:eq:Qmc" data-reference-type="eqref" data-reference="long243:eq:Qmc">[long243:eq:Qmc]</a> is irreducible over $`\mathbb{Q}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR11.primitive_zero_density_paper_multiplier_lemma`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR11/PrimitiveMultiplierSupply.lean#L244)

```lean
theorem primitive_zero_density_paper_multiplier_lemma
    (a u v : ℕ → ℕ) (m c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c}) :
    (c = 1 ∨ c = -1) ∧
    (∀ n, T ≤ n → Nat.Coprime (a n) (v n)) ∧
    (∀ i j, T ≤ i → T ≤ j → i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ N, ∃ n, max T N ≤ n ∧ 1 < a n) ∧
    (∀ B N, ∃ p j : ℕ, Nat.Prime p ∧ B < p ∧ max T N ≤ j ∧ p ∣ a j) ∧
    Irreducible (rationalBinomialCubic (m : ℚ) (c : ℚ))
```

<a id="long243-res-reduciblecase-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `primitive_zero_density_paper_multiplier_lemma`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L123) (E243_01, line 123), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStatementsA.lean#L46) (PaperStatementsA.lean, line 46), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-squarespec"></a>

## Lemma 2.6 (square specialisation), page 6

> *Let $`f\in\mathbb{Q}[T]`$ be irreducible with root $`\alpha`$, and let $`H\in\mathbb{Q}[T]`$ satisfy $`H(\alpha)\ne0`$. If for all but finitely many primes $`\ell`$ every root $`r\in\mathbb{F}_\ell`$ of the reduction of $`f`$ has $`H(r)`$ a square in $`\mathbb{F}_\ell^\times`$, then $`H(\alpha)`$ is a square in $`\mathbb{Q}(\alpha)^\times`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L35)

```lean
theorem squareSpecialisation : SquareSpecialisation
```

where [`SquareSpecialisation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/CubicRateExclusionChain.lean#L25) is

```lean
def SquareSpecialisation : Prop :=
  ∀ (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀) (f H : Polynomial ℚ),
    Irreducible f → Polynomial.aeval α f = 0 → Polynomial.aeval α H ≠ 0 →
    ∀ (d : ℕ), 0 < d → ∀ G J : Polynomial ℤ,
    G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f →
    J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H →
    (∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
        (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
        (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
          IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) →
    ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
      β ≠ 0 ∧ β ^ 2 = Polynomial.aeval α H
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation_holds`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationDedekind.lean#L184)

```lean
theorem squareSpecialisation_holds :
    ∀ (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀) (f H : Polynomial ℚ),
      Irreducible f → Polynomial.aeval α f = 0 → Polynomial.aeval α H ≠ 0 →
      ∀ (d : ℕ), 0 < d → ∀ G J : Polynomial ℤ,
      G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f →
      J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H →
      (∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
          (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
          (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
            IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) →
      ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
        β ≠ 0 ∧ β ^ 2 = Polynomial.aeval α H
```

<a id="long243-res-squarespec-comparator"></a>

**Comparator:** not yet compared.

<a id="long243-res-transportsquare"></a>

## Proposition 2.7 (the square forced by the numerator recurrence), page 7

> *Write $`\kappa=m/6`$ and $`\eta=6c/m`$, so that $`Q_{m,c}(n)=\kappa f(n+1)`$ for $`f(T)=T^3-T+\eta`$. Then $`\alpha^2-1`$ is a square in $`\mathbb{Q}(\alpha)^\times`$ for a root $`\alpha`$ of $`f`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR21.transport_square_unconditional`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/SquareSpecialisationUnconditional.lean#L39)

```lean
theorem transport_square_unconditional
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀)
    (hroot : α ^ 3 = α - algebraMap ℚ L₀ (6 * (c : ℚ) / (m : ℚ))) :
    ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
      β ≠ 0 ∧ β ^ 2 = α ^ 2 - 1
```

<a id="long243-res-transportsquare-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `transport_square_unconditional`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L88) (E243_01, line 88), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStructuresAC.lean#L41) (PaperStructuresAC.lean, line 41), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-scaletwelve"></a>

## Lemma 2.8 (classification of the scales), page 8

> *Let $`m`$ be a positive integer, let $`c\in\{-1,1\}`$ and $`\eta=6c/m`$, and suppose $`T^3-T+\eta`$ is irreducible over $`\mathbb{Q}`$ with a root $`\alpha`$ such that $`\alpha^2-1`$ is a square in $`\mathbb{Q}(\alpha)^\times`$. Then $`m=12`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR20.scale_twelve_of_square_in_rootField`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR20/ScaleTwelve.lean#L36)

```lean
theorem scale_twelve_of_square_in_rootField
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℤ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α : L)
    (hirr : Irreducible
      (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))))
    (hroot : α ^ 3 = α -
      algebraMap ℚ L (6 * (c : ℚ) / (m : ℚ)))
    (hsquare : ∃ β : L,
      β ∈ IntermediateField.adjoin ℚ ({α} : Set L) ∧
      β ^ 2 = α ^ 2 - 1) :
    m = 12
```

<a id="long243-res-scaletwelve-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `scale_twelve_of_square_in_rootField`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L168) (E243_01, line 168), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStatementsP.lean#L18) (PaperStatementsP.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-modseven"></a>

## Lemma 2.9 (the two forbidden words), page 9

> *For $`Q_{12,1}`$, every sufficiently late four-index window beginning at $`n\equiv0\pmod7`$ contains an exceptional index. For $`Q_{12,-1}`$, the same holds for windows beginning at $`n\equiv1\pmod7`$. In either case, $`\underline d(S)\ge1/7`$. No phase-free four-index obstruction is asserted.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR20.plus_one_forbidden_word`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR20/TwoForbiddenWords.lean#L18)

```lean
theorem plus_one_forbidden_word (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ n, T ≤ n → (n : ZMod 7) = 0 →
      ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ cubicTwelveProfile 1 (n + j)) ∧
    LowerDensityAtLeast {n : ℕ | u n ≠ cubicTwelveProfile 1 n} (1 / 7)
```

2. [`ErdosProblems.Erdos243.PaperCompleteR20.minus_one_forbidden_word`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR20/TwoForbiddenWords.lean#L38)

```lean
theorem minus_one_forbidden_word (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ n, T ≤ n → (n : ZMod 7) = 1 →
      ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ cubicTwelveProfile (-1) (n + j)) ∧
    LowerDensityAtLeast {n : ℕ | u n ≠ cubicTwelveProfile (-1) n} (1 / 7)
```

<a id="long243-res-modseven-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `plus_one_forbidden_word`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L199) (E243_01, line 199), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStructuresAD.lean#L24) (PaperStructuresAD.lean, line 24), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)
- `minus_one_forbidden_word`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L191) (E243_01, line 191), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStructuresAD.lean#L17) (PaperStructuresAD.lean, line 17), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-extraction"></a>

## Lemma 2.10 (integer extraction at a regular rate), page 10

> *Let $`\lambda>1`$ and let $`C_n`$ be positive integers with
> ``` math
> \begin{equation}
> \label{long243:eq:regularrate}
>  \frac{C_{n+1}}{C_n}=1+\frac\lambda n+o(n^{-\lambda}).
> \end{equation}
> ```
> Then $`\lambda`$ is an integer $`d\ge2`$, and there are $`A\in\mathbb{Q}_{>0}`$ and $`B\in\mathbb{Q}`$ with $`C_n=A\,n(n+1)\cdots(n+d-1)+B`$ for all large $`n`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/RegularRateExtraction.lean#L874)

```lean
theorem regular_rate_extraction {l : ℝ} (hl : 1 < l) (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n)
      atTop (nhds 0)) :
    ∃ d : ℕ, 2 ≤ d ∧ l = (d : ℝ) ∧
      ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℝ) = (A : ℝ) * risingPow d (n : ℝ) + (B : ℝ)
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction_cubic`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/RegularRateExtraction.lean#L1151)

```lean
theorem regular_rate_extraction_cubic (C : ℕ → ℤ) (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (B : ℝ)
```

<a id="long243-res-extraction-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `regular_rate_extraction`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L216) (E243_01, line 216), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStatementsG.lean#L17) (PaperStatementsG.lean, line 17), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)
- `regular_rate_extraction_cubic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L235) (E243_01, line 235), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStatementsN.lean#L19) (PaperStatementsN.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-tailratio"></a>

## Lemma 2.11 (the tail ratio reads the growth defect), page 11

> *Let $`a_n`$ be strictly increasing positive integers with $`a_{n+1}/a_n^2\to1`$ and $`\sum_n1/a_n`$ rational, and let $`(C_n,D_n)`$ be the integer tail. Write $`\gamma_n=a_n^2/a_{n+1}-1`$. Then
> ``` math
> \frac{C_{n+1}}{C_n}=1+\gamma_n+O(a_n^{-1}),
>  \qquad a_n\ge\exp(c\,2^n)\ \text{eventually for some }c>0 .
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement bounds the error explicitly, $|C_{n+1}/C_n-a_n^2/a_{n+1}|\le16/a_n$ for all large $n$; since $a_n^2/a_{n+1}=1+\gamma_n$, this gives the printed $O(a_n^{-1})$, and the growth bound $a_n\ge\exp(c\,2^n)$ is as printed. Lean indexes the sequence from $0$; the first conclusion is unchanged by this shift, and the second holds after replacing $c$ by $c/2$.

[`ErdosProblems.Erdos243.PaperCompleteR7.canonical_tail_ratio_quantitative`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/QuantitativeTail.lean#L204)

```lean
theorem canonical_tail_ratio_quantitative
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    let C := canonicalNaturalNumerator a p q
    (∃ N, ∀ n, N ≤ n →
      |(C (n + 1) : ℝ) / (C n : ℝ) -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| ≤ 16 / (a n : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N, ∀ n, N ≤ n →
      Real.exp (c * (2 : ℝ) ^ n) ≤ (a n : ℝ))
```

<a id="long243-res-tailratio-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `canonical_tail_ratio_quantitative`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_01/Challenge.lean#L257) (E243_01, line 257), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_01/PaperStatementsL.lean#L109) (PaperStatementsL.lean, line 109), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_01.json) (E243_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-update"></a>

## Proposition 4.1 (update law), page 16

> *For all $`a,D,C\in\mathbb{Z}`$,
> ``` math
> aC-D=C-\bigl(D-(a-1)C\bigr).
> ```
> Consequently, every exact orbit satisfies $`C_{n+1}=C_n-E_n`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.nextTailState_eq_sub_centered`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L57)

```lean
theorem nextTailState_eq_sub_centered (a D C : ℤ) :
    nextTailState a D C = C - centeredState a D C
```

<a id="long243-res-update-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `nextTailState_eq_sub_centered`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L128) (E243_02, line 128), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L305) (PaperStatementsA.lean, line 305), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-scale"></a>

## Proposition 4.3 (scaling the numerator and denominator), page 18

> *For every $`s,a,D,C\in\mathbb{Z}`$,
> ``` math
> a(sD)=s\,(aD),\qquad
>  a(sC)-sD=s\,(aC-D),
> ```
> ``` math
> sD-(a-1)sC=s\,[D-(a-1)C].
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.state_scale`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L31)

```lean
theorem state_scale (s a D C : ℤ) :
    nextDenState a (s * D) = s * nextDenState a D ∧
    nextTailState a (s * D) (s * C) = s * nextTailState a D C ∧
    centeredState a (s * D) (s * C) = s * centeredState a D C
```

<a id="long243-res-scale-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `state_scale`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L112) (E243_02, line 112), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L254) (PaperStatementsA.lean, line 254), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-defect"></a>

## Theorem 5.1 (defect identity), page 18

> *For all $`a,a',D,C\in\mathbb{Z}`$,
> ``` math
> \begin{aligned}
>  \relax[a'-(a^2-a+1)]\,(aC-D)
>  &=a^2[D-(a-1)C]\\
>  &\quad-\bigl[aD-(a'-1)(aC-D)\bigr],
>  \end{aligned}
> ```
> that is, $`\Delta_n\,C_{n+1}=a_n^{2}E_n-E_{n+1}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.sylvesterDefect_mul_nextTailState`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1775)

```lean
theorem sylvesterDefect_mul_nextTailState
    (a aNext D C : ℤ) :
    sylvesterDefect a aNext * nextTailState a D C =
      a ^ 2 * centeredState a D C -
        centeredState aNext (nextDenState a D) (nextTailState a D C)
```

<a id="long243-res-defect-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `sylvesterDefect_mul_nextTailState`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L132) (E243_02, line 132), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L308) (PaperStatementsA.lean, line 308), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-step"></a>

## Theorem 5.3 (two vanishing errors force the step), page 19

> *Let $`a,a',D,C\in\mathbb{Z}`$ with $`aC-D\ne0`$. If
> ``` math
> D-(a-1)C=0,\qquad aD-(a'-1)(aC-D)=0,
> ```
> then $`a'=a^2-a+1`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.sylvesterNext_eq_of_centered_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1787)

```lean
theorem sylvesterNext_eq_of_centered_zero
    (a aNext D C : ℤ)
    (hCnext : nextTailState a D C ≠ 0)
    (hE : centeredState a D C = 0)
    (hEnext :
      centeredState aNext (nextDenState a D) (nextTailState a D C) = 0) :
    aNext = sylvesterNext a
```

<a id="long243-res-step-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `sylvesterNext_eq_of_centered_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L139) (E243_02, line 139), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L314) (PaperStatementsA.lean, line 314), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-secondorder"></a>

## Theorem 5.4 (eliminating the denominator from two steps), page 19

> *Let $`a,a_1,u,u_1,u_2,v,v_1,h,h_1`$ be integers satisfying
> ``` math
> hu_1+v=au,\qquad hv_1=av,\qquad h_1u_2+v_1=a_1u_1.
> ```
> Then $`a^2u+hh_1u_2=h(a+a_1)u_1`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.reduced_second_order_int`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Arithmetic.lean#L42)

```lean
theorem reduced_second_order_int
    (a aNext u uNext uNextNext v vNext h hNext : ℤ)
    (hu : h * uNext + v = a * u)
    (hv : h * vNext = a * v)
    (huNext : hNext * uNextNext + vNext = aNext * uNext) :
    a ^ 2 * u + h * hNext * uNextNext =
      h * (a + aNext) * uNext
```

<a id="long243-res-secondorder-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `reduced_second_order_int`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L103) (E243_02, line 103), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L246) (PaperStatementsA.lean, line 246), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-curvature"></a>

## Theorem 5.5 (a square identity without cancellation), page 20

> *Let $`a,a_1,p,p_1,p_2,q`$ be integers with $`q=ap-p_1`$ and $`p_2+a^2p=(a+a_1)p_1`$. Then
> ``` math
> q^2+\bigl(pp_2-p_1^2\bigr)=(a_1-a)pp_1.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.cancellationFree_curvature_square`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/DynamicCancellation.lean#L309)

```lean
theorem cancellationFree_curvature_square
    {a aNext p pNext pNextNext q : ℤ}
    (hq : q = a * p - pNext)
    (hrec : pNextNext + a ^ 2 * p = (a + aNext) * pNext) :
    q ^ 2 + (p * pNextNext - pNext ^ 2) =
      (aNext - a) * p * pNext
```

<a id="long243-res-curvature-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cancellationFree_curvature_square`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L161) (E243_02, line 161), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsH.lean#L16) (PaperStatementsH.lean, line 16), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-oldmodulussaturation"></a>

## Lemma 5.6 (saturation modulo an old denominator), page 20

> *Let $`M\ge2`$. Any finite word $`r_0,\ldots,r_k`$ of units modulo $`M`$ is compatible with the cancellation-free recurrences modulo $`M`$, with all reduced denominator residues equal to zero. Consequently the eliminated two-step identity alone imposes no further restriction on such unit words when the multiplier residues are free.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR21.unit_word_saturates_old_modulus`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ReducedStepLocalArithmetic.lean#L39)

```lean
theorem unit_word_saturates_old_modulus
    (M : ℕ) (hM : 2 ≤ M) (k : ℕ) (r : ℕ → ZMod M)
    (hr : ∀ i, i ≤ k → IsUnit (r i)) :
    ∃ a v : ℕ → ZMod M,
      (∀ i, i ≤ k → v i = 0) ∧
      (∀ i, i < k → r (i + 1) + v i = a i * r i) ∧
      (∀ i, i < k → v (i + 1) = a i * v i) ∧
      (∀ i, i + 2 ≤ k →
        r (i + 2) = (a i + a (i + 1)) * r (i + 1) - a i ^ 2 * r i)
```

<a id="long243-res-oldmodulussaturation-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `unit_word_saturates_old_modulus`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L92) (E243_02, line 92), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L175) (PaperStatementsA.lean, line 175), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-eventual"></a>

## Theorem 5.7 (sequence form), page 21

> *Let $`a,D,C:\mathbb{N}\to\mathbb{Z}`$ satisfy $`D_{n+1}=a_nD_n`$ and $`C_{n+1}=a_nC_n-D_n`$. If $`E_n=0`$ for all sufficiently large $`n`$ and $`C_{n+1}\ne0`$ for all sufficiently large $`n`$, then $`a_{n+1}=a_n^{2}-a_n+1`$ for all sufficiently large $`n`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.sylvesterNext_eventually_of_centered_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1805)

```lean
theorem sylvesterNext_eventually_of_centered_zero
    (a D C : ℕ → ℤ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, C (n + 1) = nextTailState (a n) (D n) (C n))
    (hE : ∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0)
    (hCne : ∃ N, ∀ n, N ≤ n → C (n + 1) ≠ 0) :
    ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n)
```

<a id="long243-res-eventual-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `sylvesterNext_eventually_of_centered_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L148) (E243_02, line 148), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L322) (PaperStatementsA.lean, line 322), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-absorb"></a>

## Theorem 5.8 (zero is absorbing), page 21

> *Let $`a,C,D:\mathbb{N}\to\mathbb{N}`$ be an exact orbit of natural numbers, so $`C_{n+1}+D_n=a_nC_n`$ and $`D_{n+1}=a_nD_n`$, and let $`E_n=D_n-(a_n-1)C_n`$. Suppose the centring is strict, $`|E_n|<C_n`$ for every $`n`$. If $`E_n=0`$ then $`E_{n+1}=0`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.centeredState_zero_absorbing`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2227)

```lean
theorem centeredState_zero_absorbing
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hcentered : ∀ n, Int.natAbs (E n) < C n)
    (n : ℕ) (hzero : E n = 0) :
    E (n + 1) = 0
```

<a id="long243-res-absorb-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `centeredState_zero_absorbing`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L118) (E243_02, line 118), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L276) (PaperStatementsA.lean, line 276), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-arithmeticrecord"></a>

## Theorem 6.1 (boundedness and a weighted sum over new maxima), page 22

> *Let $`a_n,L_n,U_n`$ be positive integers and $`V_n`$ integers satisfying
> ``` math
> \begin{gathered}
>  L_{n+1}=\operatorname{lcm}(L_n,a_n),\qquad \rho_n=\gcd(L_n,a_n),\\
>  \rho_nU_{n+1}=U_n-V_n,\qquad
>  V_n=L_n-(a_n-1)U_n,\qquad -U_n\le2V_n.
>  \end{gathered}
> ```
> Let $`f:[1,\infty)\to[0,\infty)`$ be finite and nonincreasing, with $`\int_1^\infty f(t)\,dt=\infty`$. For each fixed integer $`B\ge0`$,
> ``` math
> \sup_n U_n<\infty
>  \quad\Longleftrightarrow\quad
>  \sum_{n\in\mathcal R}(-V_n-B)_+f(U_n)<\infty.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR11.arithmetic_weighted_record_dichotomy`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR11/ArithmeticWeightedRecord.lean#L264)

```lean
theorem arithmetic_weighted_record_dichotomy
    (a L U : ℕ → ℕ) (V : ℕ → ℤ)
    (ha : ∀ n, 0 < a n) (hLpos : ∀ n, 0 < L n) (hU : ∀ n, 0 < U n)
    (hL : ∀ n, L (n + 1) = Nat.lcm (L n) (a n))
    (hstate : ∀ n, (Nat.gcd (L n) (a n) : ℤ) * U (n + 1) =
      (U n : ℤ) - V n)
    (herror : ∀ n, V n = (L n : ℤ) - ((a n : ℤ) - 1) * U n)
    (hcenter : ∀ n, -(U n : ℤ) ≤ 2 * V n)
    (B : ℕ) (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : IntegralUnbounded f) :
    (∃ H : ℕ, ∀ n, U n ≤ H) ↔ Summable (paperRecordCharge U V B f)
```

<a id="long243-res-arithmeticrecord-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `arithmetic_weighted_record_dichotomy`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L233) (E243_02, line 233), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/CompletePaperRecords.lean#L150) (CompletePaperRecords.lean, line 150), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-weightedrecord"></a>

## Theorem 6.2 (a convergent weighted sum over new maxima), page 23

> *Assume the growth and rationality hypotheses of Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>, and let $`f`$ be as in Theorem 6.1. The sequence is eventually Sylvester if and only if, for some integer $`B\ge0`$,
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

<a id="long243-res-weightedrecord-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `canonical_weighted_record_excess`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L220) (E243_02, line 220), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/CompletePaperRecords.lean#L102) (CompletePaperRecords.lean, line 102), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-valuationtransition"></a>

## Lemma 7.1 (the denominator valuation transition), page 26

> *Let $`u,v,a`$ be positive integers, $`\gcd(u,v)=1`$, and $`w=au-v>0`$. Put $`h=\gcd(w,av)`$ and $`v'=av/h`$. For a prime $`p`$, write $`r=\nu_p(a)`$, $`s=\nu_p(v)`$ and $`t=\nu_p(w)`$. Then
> ``` math
> \nu_p(v')=
>  \begin{cases}
>  \max(r,s),&r\ne s,\\
>  \max(0,2s-t),&r=s.
>  \end{cases}
> ```
> In particular $`\nu_p(v')\le\max(r,s)`$. A strict loss relative to $`s`$ requires $`r=s\ge1`$ and $`t>s`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_transition`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ReducedStepLocalArithmetic.lean#L244)

```lean
theorem reduced_denominator_valuation_transition
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h) :
    (a.factorization p ≠ v.factorization p →
        v'.factorization p = max (a.factorization p) (v.factorization p))
    ∧ (a.factorization p = v.factorization p →
        v'.factorization p
          = max 0 (2 * v.factorization p - w.factorization p))
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_le_max`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ReducedStepLocalArithmetic.lean#L262)

```lean
theorem reduced_denominator_valuation_le_max
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h) :
    v'.factorization p ≤ max (a.factorization p) (v.factorization p)
```

3. [`ErdosProblems.Erdos243.PaperCompleteR21.reduced_denominator_valuation_strict_loss`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ReducedStepLocalArithmetic.lean#L279)

```lean
theorem reduced_denominator_valuation_strict_loss
    {u v a w h v' p : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hv : 0 < v) (ha : 0 < a)
    (hcop : Nat.Coprime u v)
    (hw : w + v = a * u) (hwpos : 0 < w)
    (hh : h = Nat.gcd w (a * v))
    (hv'def : v' = a * v / h)
    (hloss : v'.factorization p < v.factorization p) :
    a.factorization p = v.factorization p ∧ 1 ≤ v.factorization p ∧
      v.factorization p < w.factorization p
```

<a id="long243-res-valuationtransition-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `reduced_denominator_valuation_transition`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L78) (E243_02, line 78), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L162) (PaperStatementsA.lean, line 162), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)
- `reduced_denominator_valuation_le_max`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L56) (E243_02, line 56), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L142) (PaperStatementsA.lean, line 142), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)
- `reduced_denominator_valuation_strict_loss`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L66) (E243_02, line 66), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L151) (PaperStatementsA.lean, line 151), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-powerpersistence"></a>

## Corollary 7.2 (persistence of a prime power), page 27

> *Suppose $`p^k\mid v_s`$. If $`w_n<p^{k+1}`$ at every step from $`s`$ through $`t-1`$, then $`p^k\mid v_t`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR20.primePower_persists`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR20/PowerPersistence.lean#L27)

```lean
theorem primePower_persists
    (a u v w hc : ℕ → ℕ) {p k s t : ℕ}
    (hp : p.Prime)
    (hst : s ≤ t)
    (hcop : ∀ n, Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, 0 < v n)
    (hq : ∀ n, w n + v n = a n * u n)
    (hwpos : ∀ n, 0 < w n)
    (hnum : ∀ n, w n = hc n * u (n + 1))
    (hden : ∀ n, a n * v n = hc n * v (n + 1))
    (hstart : p ^ k ∣ v s)
    (hsmall : ∀ n, s ≤ n → n < t → w n < p ^ (k + 1)) :
    p ^ k ∣ v t
```

<a id="long243-res-powerpersistence-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `primePower_persists`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_02/Challenge.lean#L41) (E243_02, line 41), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_02/PaperStatementsA.lean#L61) (PaperStatementsA.lean, line 61), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_02.json) (E243_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-recorddichotomy"></a>

## Theorem 7.3 (increments of the running maximum), page 27

> *Let $`\Theta=\limsup_n(H_{n+1}-H_n)/\ell(H_n)`$ on a rational-tail orbit under the standing hypotheses, and suppose $`E_n`$ is not eventually zero. Then either $`G_n`$ is unbounded and $`\Theta`$ is infinite, or $`G_n`$ stabilises at a value $`g`$ and $`\Theta\ge g\,v_T/\varphi(v_T)`$ for every late $`T`$, so that $`\Theta>g\ge1`$. For any orbit under the standing hypotheses, therefore, $`\Theta=0`$ or $`\Theta>1`$, and $`\Theta\le1`$ forces the eventual Sylvester recurrence.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR11.canonical_quantitative_record_dichotomy`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR11/QuantitativeRecordDichotomy.lean#L340)

```lean
theorem canonical_quantitative_record_dichotomy
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    ((∀ B : ℕ, ∃ n, B < Nat.gcd (C n) (D n)) ∧ recordTheta C = ⊤) ∨
    ∃ N g : ℕ, 0 < g ∧ (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
      (∀ T : ℕ, N + 2 ≤ T →
        (((g : ℝ) * (D T / g : ℕ) / Nat.totient (D T / g) : ℝ) : EReal) ≤ recordTheta C) ∧
      (g : EReal) < recordTheta C
```

2. [`ErdosProblems.Erdos243.PaperCompleteR11.canonical_recordTheta_zero_or_gt_one`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR11/QuantitativeRecordDichotomy.lean#L308)

```lean
theorem canonical_recordTheta_zero_or_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)) :
    recordTheta (canonicalNaturalNumerator a p q) = 0 ∨
      (1 : EReal) < recordTheta (canonicalNaturalNumerator a p q)
```

3. [`ErdosProblems.Erdos243.PaperCompleteR11.canonical_recordTheta_eq_zero_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR11/QuantitativeRecordDichotomy.lean#L321)

```lean
theorem canonical_recordTheta_eq_zero_iff
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)) :
    recordTheta (canonicalNaturalNumerator a p q) = 0 ↔
      ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)
```

4. [`ErdosProblems.Erdos243.PaperCompleteR11.canonical_recordTheta_gt_one`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR11/InclusiveLimsup.lean#L54)

```lean
theorem canonical_recordTheta_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    (1 : EReal) < recordTheta (canonicalNaturalNumerator a p q)
```

<a id="long243-res-recorddichotomy-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `canonical_quantitative_record_dichotomy`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L70) (E243_03, line 70), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/CompletePaperRecords.lean#L210) (CompletePaperRecords.lean, line 210), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `canonical_recordTheta_zero_or_gt_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L132) (E243_03, line 132), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStatementsM.lean#L44) (PaperStatementsM.lean, line 44), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `canonical_recordTheta_eq_zero_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L114) (E243_03, line 114), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStatementsM.lean#L24) (PaperStatementsM.lean, line 24), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `canonical_recordTheta_gt_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L123) (E243_03, line 123), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStatementsM.lean#L34) (PaperStatementsM.lean, line 34), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-loglogboundary"></a>

## Corollary 7.4 (the double-logarithmic bound), page 27

> *If
> ``` math
> \limsup_n\frac{(-E_n)_+}{\ell(C_n)}\le1,
> ```
> then the sequence is eventually Sylvester. Every counterexample therefore satisfies
> ``` math
> \limsup_n\frac{(-E_n)_+}{\ell(C_n)}>1.
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR11.canonical_inclusive_logLog_criterion`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR11/InclusiveLimsup.lean#L129)

```lean
theorem canonical_inclusive_logLog_criterion
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hlim : let C := canonicalNaturalNumerator a p q
      let D := canonicalDenominator a q
      let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
      limsup (fun n ↦ (negativeErrorLogLogCharge C E n : EReal)) atTop ≤ 1) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)
```

2. [`ErdosProblems.Erdos243.PaperCompleteR11.canonical_negativeError_limsup_gt_one`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR11/InclusiveLimsup.lean#L108)

```lean
theorem canonical_negativeError_limsup_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    (1 : EReal) < limsup (fun n ↦ (negativeErrorLogLogCharge C E n : EReal)) atTop
```

<a id="long243-res-loglogboundary-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `canonical_inclusive_logLog_criterion`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L85) (E243_03, line 85), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/CompletePaperRecords.lean#L260) (CompletePaperRecords.lean, line 260), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `canonical_negativeError_limsup_gt_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L148) (E243_03, line 148), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStatementsI.lean#L25) (PaperStatementsI.lean, line 25), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-recordamplified"></a>

## Theorem 7.5 (bounds allowing for previous decreases), page 30

> *Under the standing hypotheses, the following are equivalent: eventual Sylvester behaviour; $`\limsup_n\mathcal A_n<\infty`$; $`\limsup_nR_n\delta_n<\infty`$. Each of those two limits superior is $`0`$ or $`+\infty`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.recordAmplified`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L975)

```lean
theorem recordAmplified :
    (O.EventuallySylvester ↔
        Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop ≠ ⊤) ∧
      (O.EventuallySylvester ↔
        Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop ≠ ⊤) ∧
      (Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop = 0 ∨
        Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop = ⊤) ∧
      (Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop = 0 ∨
        Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop = ⊤)
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp_bddAbove_iff_sylvester`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L931)

```lean
theorem amp_bddAbove_iff_sylvester :
    O.EventuallySylvester ↔ ∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K
```

3. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Rdelta_bddAbove_iff_amp`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L948)

```lean
theorem Rdelta_bddAbove_iff_amp :
    (∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K) ↔
      (∃ K : ℝ, ∀ᶠ n in atTop, (O.R n : ℝ) * O.delta n ≤ K)
```

4. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.eventuallySylvester_of_amp_le`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L587)

```lean
theorem eventuallySylvester_of_amp_le (K : ℕ) (hK1 : 1 ≤ K) (N₀ : ℕ)
    (hbd : ∀ n, N₀ ≤ n → O.amp n ≤ (K : ℝ)) : O.EventuallySylvester
```

5. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.coprimeMultiplier_cofinal`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L187)

```lean
theorem coprimeMultiplier_cofinal (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n)
```

6. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.largePrime_coprimeMultiplier`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L295)

```lean
theorem largePrime_coprimeMultiplier (B : ℕ) (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) ∧
      ∃ p, Nat.Prime p ∧ p ∣ O.a n ∧ B < p
```

7. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.primeBlock_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L546)

```lean
theorem primeBlock_supply (B N₀ : ℕ) (hcanc : ∀ m, N₀ ≤ m → O.canc m ≤ B) :
    ∀ j : ℕ, ∃ T, N₀ ≤ T ∧ ∃ P : Finset ℕ, P.card = j ∧
      ∀ p ∈ P, Nat.Prime p ∧ B < p ∧ p ∣ O.v T
```

8. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc_lt_of_amp_le`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L462)

```lean
theorem canc_lt_of_amp_le (hns : ¬ O.EventuallySylvester) (K : ℕ) (hK1 : 1 ≤ K)
    (N₀ : ℕ) (hbd : ∀ n, N₀ ≤ n → O.amp n ≤ (K : ℝ)) :
    ∃ N, ∀ s, N ≤ s → O.canc s < 2 * K
```

9. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta_negPart_comparison`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L738)

```lean
theorem delta_negPart_comparison :
    ∃ N, ∀ n, N ≤ n →
      |O.delta n - (O.negPart n : ℝ) / (O.u n : ℝ)| ≤ 3 / (O.a n : ℝ)
```

10. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R_delta_sub_amp_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L870)

```lean
theorem R_delta_sub_amp_tendsto_zero :
    Tendsto (fun n ↦ (O.R n : ℝ) * O.delta n - O.amp n) atTop (𝓝 0)
```

<a id="long243-res-recordamplified-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `recordAmplified`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L240) (E243_03, line 240), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStructuresT.lean#L394) (PaperStructuresT.lean, line 394), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `amp_bddAbove_iff_sylvester`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L217) (E243_03, line 217), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStructuresT.lean#L357) (PaperStructuresT.lean, line 357), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `Rdelta_bddAbove_iff_amp`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L212) (E243_03, line 212), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStructuresT.lean#L352) (PaperStructuresT.lean, line 352), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `eventuallySylvester_of_amp_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_04/Challenge.lean#L84) (E243_04, line 84), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_04/PaperStructuresV.lean#L331) (PaperStructuresV.lean, line 331), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_04.json) (E243_04)
- `coprimeMultiplier_cofinal`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L221) (E243_03, line 221), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStructuresT.lean#L361) (PaperStructuresT.lean, line 361), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `largePrime_coprimeMultiplier`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L230) (E243_03, line 230), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStructuresT.lean#L384) (PaperStructuresT.lean, line 384), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `primeBlock_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L235) (E243_03, line 235), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStructuresT.lean#L389) (PaperStructuresT.lean, line 389), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `canc_lt_of_amp_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L296) (E243_03, line 296), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStructuresV.lean#L323) (PaperStructuresV.lean, line 323), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `delta_negPart_comparison`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L225) (E243_03, line 225), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStructuresT.lean#L379) (PaperStructuresT.lean, line 379), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)
- `R_delta_sub_amp_tendsto_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_03/Challenge.lean#L208) (E243_03, line 208), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_03/PaperStructuresT.lean#L344) (PaperStructuresT.lean, line 344), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_03.json) (E243_03)

Challenge for `recordAmplified`:

```lean
theorem recordAmplified (O : StandingOrbit) :
    (O.EventuallySylvester ↔
        Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop ≠ ⊤) ∧
      (O.EventuallySylvester ↔
        Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop ≠ ⊤) ∧
      (Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop = 0 ∨
        Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop = ⊤) ∧
      (Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop = 0 ∨
        Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop = ⊤) := by sorry
```

Challenge for `amp_bddAbove_iff_sylvester`:

```lean
theorem amp_bddAbove_iff_sylvester (O : StandingOrbit) :
    O.EventuallySylvester ↔ ∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K := by sorry
```

Challenge for `Rdelta_bddAbove_iff_amp`:

```lean
theorem Rdelta_bddAbove_iff_amp (O : StandingOrbit) :
    (∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K) ↔
      (∃ K : ℝ, ∀ᶠ n in atTop, (O.R n : ℝ) * O.delta n ≤ K) := by sorry
```

Challenge for `eventuallySylvester_of_amp_le`:

```lean
theorem eventuallySylvester_of_amp_le (O : StandingOrbit) (K : ℕ) (hK1 : 1 ≤ K) (N₀ : ℕ)
    (hbd : ∀ n, N₀ ≤ n → O.amp n ≤ (K : ℝ)) : O.EventuallySylvester := by sorry
```

Challenge for `coprimeMultiplier_cofinal`:

```lean
theorem coprimeMultiplier_cofinal (O : StandingOrbit) (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) := by sorry
```

Challenge for `largePrime_coprimeMultiplier`:

```lean
theorem largePrime_coprimeMultiplier (O : StandingOrbit) (B : ℕ) (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) ∧
      ∃ p, Nat.Prime p ∧ p ∣ O.a n ∧ B < p := by sorry
```

Challenge for `primeBlock_supply`:

```lean
theorem primeBlock_supply (O : StandingOrbit) (B N₀ : ℕ) (hcanc : ∀ m, N₀ ≤ m → O.canc m ≤ B) :
    ∀ j : ℕ, ∃ T, N₀ ≤ T ∧ ∃ P : Finset ℕ, P.card = j ∧
      ∀ p ∈ P, Nat.Prime p ∧ B < p ∧ p ∣ O.v T := by sorry
```

Challenge for `canc_lt_of_amp_le`:

```lean
theorem canc_lt_of_amp_le (O : StandingOrbit) (hns : ¬ O.EventuallySylvester) (K : ℕ) (hK1 : 1 ≤ K)
    (N₀ : ℕ) (hbd : ∀ n, N₀ ≤ n → O.amp n ≤ (K : ℝ)) :
    ∃ N, ∀ s, N ≤ s → O.canc s < 2 * K := by sorry
```

Challenge for `delta_negPart_comparison`:

```lean
theorem delta_negPart_comparison (O : StandingOrbit) :
    ∃ N, ∀ n, N ≤ n →
      |O.delta n - (O.negPart n : ℝ) / (O.u n : ℝ)| ≤ 3 / (O.a n : ℝ) := by sorry
```

Challenge for `R_delta_sub_amp_tendsto_zero`:

```lean
theorem R_delta_sub_amp_tendsto_zero (O : StandingOrbit) :
    Tendsto (fun n ↦ (O.R n : ℝ) * O.delta n - O.amp n) atTop (𝓝 0) := by sorry
```

<a id="long243-res-criticalrate"></a>

## Corollary 7.6 (the critical rate), page 30

> *Under the standing hypotheses and $`\delta_n=O(1/n)`$, with no convergence of $`n\delta_n`$ assumed, eventual Sylvester behaviour is equivalent to $`u_n=O(n)`$ and to $`(-\tilde e_n)_+=O(1)`$. A counterexample at the critical rate therefore has $`\limsup_nu_n/n=\infty`$ and $`\limsup_n(-\tilde e_n)_+=\infty`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.criticalRate`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L1033)

```lean
theorem criticalRate
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ))) :
    (O.EventuallySylvester ↔ (fun n : ℕ ↦ (O.u n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ))) ∧
      (O.EventuallySylvester ↔
        (fun n : ℕ ↦ (O.negPart n : ℝ)) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)))
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.criticalRate_counterexample`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L1197)

```lean
theorem criticalRate_counterexample
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)))
    (hns : ¬ O.EventuallySylvester) :
    Filter.limsup (fun n ↦ (((O.u n : ℝ) / (n : ℝ) : ℝ) : EReal)) atTop = ⊤ ∧
      Filter.limsup (fun n ↦ ((O.negPart n : ℝ) : EReal)) atTop = ⊤
```

3. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R_le_of_u_le`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/AmplifiedRecordEquivalence.lean#L1016)

```lean
theorem R_le_of_u_le {c N : ℕ} (h : ∀ n, N ≤ n → O.u n ≤ c * n) :
    ∀ n, N ≤ n → O.R n ≤ O.R N + c * n
```

<a id="long243-res-criticalrate-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `criticalRate`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_04/Challenge.lean#L136) (E243_04, line 136), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_04/PaperStructuresT.lean#L369) (PaperStructuresT.lean, line 369), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_04.json) (E243_04)
- `criticalRate_counterexample`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_04/Challenge.lean#L143) (E243_04, line 143), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_04/PaperStructuresT.lean#L376) (PaperStructuresT.lean, line 376), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_04.json) (E243_04)
- `R_le_of_u_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_04/Challenge.lean#L132) (E243_04, line 132), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_04/PaperStructuresT.lean#L352) (PaperStructuresT.lean, line 352), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_04.json) (E243_04)

Challenge for `criticalRate`:

```lean
theorem criticalRate (O : StandingOrbit)
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ))) :
    (O.EventuallySylvester ↔ (fun n : ℕ ↦ (O.u n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ))) ∧
      (O.EventuallySylvester ↔
        (fun n : ℕ ↦ (O.negPart n : ℝ)) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ))) := by sorry
```

Challenge for `criticalRate_counterexample`:

```lean
theorem criticalRate_counterexample (O : StandingOrbit)
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)))
    (hns : ¬ O.EventuallySylvester) :
    Filter.limsup (fun n ↦ (((O.u n : ℝ) / (n : ℝ) : ℝ) : EReal)) atTop = ⊤ ∧
      Filter.limsup (fun n ↦ ((O.negPart n : ℝ) : EReal)) atTop = ⊤ := by sorry
```

Challenge for `R_le_of_u_le`:

```lean
theorem R_le_of_u_le (O : StandingOrbit) {c N : ℕ} (h : ∀ n, N ≤ n → O.u n ≤ c * n) :
    ∀ n, N ≤ n → O.R n ≤ O.R N + c * n := by sorry
```

<a id="long243-res-oddpowersupply"></a>

## Lemma 7.7 (large odd prime powers in the reduced denominator), page 31

> *Under the standing hypotheses, for every fixed $`A>0`$ and every sufficiently large $`n`$, the reduced denominator $`v_n`$ has an odd prime-power divisor $`Q=p^k`$ with
> ``` math
> Q>(H_n+2)^A,\qquad H_n=\max_{j\le n}C_j.
> ```
> The prime $`p`$ may depend on $`n`$; no stable-gcd or prime-arrival assumption is imposed.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.oddPrimePower_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ReducedDenominatorPrimePowers.lean#L790)

```lean
theorem oddPrimePower_supply (A : ℝ) (hA : 0 < A) :
    ∃ N, ∀ n, N ≤ n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧ Odd (p ^ k) ∧
      p ^ k ∣ O.v n ∧ ((O.Hmax n : ℝ) + 2) ^ A < ((p ^ k : ℕ) : ℝ)
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.oddPrimePower_supply_nat`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ReducedDenominatorPrimePowers.lean#L718)

```lean
theorem oddPrimePower_supply_nat (A : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧
      p ^ k ∣ O.v n ∧ (O.Hmax n + 2) ^ A < p ^ k
```

<a id="long243-res-oddpowersupply-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `oddPrimePower_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_04/Challenge.lean#L185) (E243_04, line 185), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_04/PaperStructuresU.lean#L337) (PaperStructuresU.lean, line 337), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_04.json) (E243_04)
- `oddPrimePower_supply_nat`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_04/Challenge.lean#L190) (E243_04, line 190), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_04/PaperStructuresU.lean#L342) (PaperStructuresU.lean, line 342), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_04.json) (E243_04)

Challenge for `oddPrimePower_supply`:

```lean
theorem oddPrimePower_supply (O : StandingOrbit) (A : ℝ) (hA : 0 < A) :
    ∃ N, ∀ n, N ≤ n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧ Odd (p ^ k) ∧
      p ^ k ∣ O.v n ∧ ((O.Hmax n : ℝ) + 2) ^ A < ((p ^ k : ℕ) : ℝ) := by sorry
```

Challenge for `oddPrimePower_supply_nat`:

```lean
theorem oddPrimePower_supply_nat (O : StandingOrbit) (A : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧
      p ^ k ∣ O.v n ∧ (O.Hmax n + 2) ^ A < p ^ k := by sorry
```

<a id="long243-res-unitrecord"></a>

## Theorem 7.8 (unit record increments), page 31

> *Under the standing hypotheses, if $`R_{n+1}-R_n\le1`$ for all large $`n`$, then $`a_{n+1}=a_n^2-a_n+1`$ for all large $`n`$. Hence the sequence is eventually Sylvester if and only if $`\#\{n:R_{n+1}-R_n\ge2\}`$ is finite. No hypothesis is placed on drawdowns, on record-setting jumps, or on the cancellation factors $`h_n`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.unitRecordIncrement_sylvesterNext`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ReducedDenominatorPrimePowers.lean#L846)

```lean
theorem unitRecordIncrement_sylvesterNext
    (hinc : ∃ N, ∀ n, N ≤ n → O.R (n + 1) - O.R n ≤ 1) :
    ∃ M, ∀ n, M ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.unitRecordIncrement_criterion`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ReducedDenominatorPrimePowers.lean#L950)

```lean
theorem unitRecordIncrement_criterion :
    (∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ↔
      {n : ℕ | 2 ≤ O.R (n + 1) - O.R n}.Finite
```

<a id="long243-res-unitrecord-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `unitRecordIncrement_sylvesterNext`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_04/Challenge.lean#L231) (E243_04, line 231), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_04/PaperStructuresW.lean#L189) (PaperStructuresW.lean, line 189), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_04.json) (E243_04)
- `unitRecordIncrement_criterion`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_04/Challenge.lean#L195) (E243_04, line 195), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_04/PaperStructuresU.lean#L347) (PaperStructuresU.lean, line 347), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_04.json) (E243_04)

Challenge for `unitRecordIncrement_sylvesterNext`:

```lean
theorem unitRecordIncrement_sylvesterNext (O : StandingOrbit)
    (hinc : ∃ N, ∀ n, N ≤ n → O.R (n + 1) - O.R n ≤ 1) :
    ∃ M, ∀ n, M ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by sorry
```

Challenge for `unitRecordIncrement_criterion`:

```lean
theorem unitRecordIncrement_criterion (O : StandingOrbit) :
    (∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ↔
      {n : ℕ | 2 ≤ O.R (n + 1) - O.R n}.Finite := by sorry
```

<a id="long243-res-epochenergy"></a>

## Theorem 7.9 (counting crossings before a prime power is lost), page 32

> *Let the orbit satisfy the reduced recurrences of this section, with $`2|\tilde e_n|<u_n`$ from an index $`s`$. Let $`p\ge3`$ be prime, $`Q=p^{\ell}`$ divide $`v_s`$ with $`Q\ge16`$, put $`L=pQ/2`$, and assume $`R_s<L/2`$. Assume that $`u_t\ge L`$ for some $`t>s`$, and let $`\tau`$ be the first such index, let $`J`$ be the set of steps in $`[s,\tau)`$ that first cross at least one odd multiple of $`p`$ in $`(L/2,L]`$, and put $`X=\sum_{n\in J}(d_n-2)`$. Then every $`n\in J`$ is a record step with $`h_n=1`$ and $`d_n\ge3`$, and $`pQ\le(8p+8)\lvert J\rvert+4X+8p`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.epoch_energy_named_crossing_set`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ProtectedEpochBarrierCount.lean#L149)

```lean
theorem epoch_energy_named_crossing_set
    (a u v w hc : ℕ → ℕ) (p l s τ : ℕ) (J : Finset ℕ)
    (hp : p.Prime)
    (hp3 : 3 ≤ p)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hcentre : ∀ n, s ≤ n → 2 * ((u n : ℤ) - (w n : ℤ)).natAbs < u n)
    (hprot : p ^ l ∣ v s)
    (hQ : 16 ≤ p ^ l)
    (hRs : 4 * runningMax u s < p * p ^ l)
    (hsτ : s < τ)
    (hτ : p * p ^ l ≤ 2 * u τ)
    (hτfirst : ∀ n, s < n → n < τ → 2 * u n < p * p ^ l)
    (hJ : ∀ n, n ∈ J ↔ (s ≤ n ∧ n < τ ∧ ∃ b : ℕ, Odd b ∧ p ∣ b ∧
      p * p ^ l < 4 * b ∧ 2 * b ≤ p * p ^ l ∧
      b ≤ u (n + 1) ∧ ∀ j, s ≤ j → j < n → u (j + 1) < b)) :
    (∀ n ∈ J, runningMax u n < u (n + 1) ∧ hc n = 1 ∧ u n + 3 ≤ u (n + 1)) ∧
      p * p ^ l ≤ (8 * p + 8) * J.card
        + 4 * ∑ n ∈ J, (u (n + 1) - u n - 2) + 8 * p
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.mem_barrierIdx_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ProtectedEpochBarrierCount.lean#L34)

```lean
theorem mem_barrierIdx_iff {Q : ℕ} (hQ : 16 ≤ Q) (k : ℕ) :
    k ∈ barrierIdx Q ↔ Q < 4 * (2 * k + 1) ∧ 2 * (2 * k + 1) ≤ Q
```

<a id="long243-res-epochenergy-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `epoch_energy_named_crossing_set`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_05/Challenge.lean#L40) (E243_05, line 40), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_05/PaperStatementsK.lean#L28) (PaperStatementsK.lean, line 28), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_05.json) (E243_05)
- `mem_barrierIdx_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_05/Challenge.lean#L29) (E243_05, line 29), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_05/PaperStatementsA.lean#L117) (PaperStatementsA.lean, line 117), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_05.json) (E243_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-energycriterion"></a>

## Theorem 7.10 (two convergence criteria for large record jumps), page 33

> *Under the standing hypotheses, the sum $`\mathcal E=\sum_{n\ \mathrm{record}}\bigl(\mathbf 1_{d_n\ge3}u_n^{-1/2}
> +(d_n-2)_+u_n^{-1}\bigr)`$ is finite if and only if the sequence is eventually Sylvester; and $`\sum_{n\ \mathrm{record}}(d_n-2)_+u_n^{-1/2}`$ is finite if and only if the sequence is eventually Sylvester.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_criterion`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/RecordJumpEnergySeries.lean#L468)

```lean
theorem energy_criterion :
    (Summable O.energy ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ∧
      (Summable O.energySqrt ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1)
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_summable_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/RecordJumpEnergySeries.lean#L414)

```lean
theorem energy_summable_iff :
    Summable O.energy ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1
```

3. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt_summable_iff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/RecordJumpEnergySeries.lean#L455)

```lean
theorem energySqrt_summable_iff :
    Summable O.energySqrt ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1
```

4. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_le_two_energySqrt`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/RecordJumpEnergySeries.lean#L161)

```lean
theorem energy_le_two_energySqrt (n : ℕ) : O.energy n ≤ 2 * O.energySqrt n
```

5. [`ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.exists_late_energy_window`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/RecordJumpEnergySeries.lean#L263)

```lean
theorem exists_late_energy_window (hunb : ∀ M : ℕ, ∃ n, M < O.u n) (S : ℕ) :
    ∃ (s τ : ℕ) (J : Finset ℕ), S ≤ s ∧ s < τ ∧ (∀ n ∈ J, s ≤ n ∧ n < τ) ∧
      (1 : ℝ) / 16 ≤ ∑ n ∈ J, O.energy n
```

6. [`ErdosProblems.Erdos243.PaperCompleteR21.energy_window_real_bound`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/RecordJumpEnergySeries.lean#L84)

```lean
theorem energy_window_real_bound {pr P K X : ℝ}
    (hpr : 3 ≤ pr) (hPsq : pr * pr ≤ P) (hP16 : 16 * pr ≤ P)
    (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hineq : P ≤ (8 * pr + 8) * K + 4 * X + 8 * pr) :
    (1 : ℝ) / 16 ≤ K / Real.sqrt (P / 2) + X / (P / 2)
```

<a id="long243-res-energycriterion-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `energy_criterion`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_05/Challenge.lean#L138) (E243_05, line 138), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_05/PaperStructuresU.lean#L307) (PaperStructuresU.lean, line 307), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_05.json) (E243_05)
- `energy_summable_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_05/Challenge.lean#L148) (E243_05, line 148), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_05/PaperStructuresU.lean#L317) (PaperStructuresU.lean, line 317), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_05.json) (E243_05)
- `energySqrt_summable_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_05/Challenge.lean#L133) (E243_05, line 133), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_05/PaperStructuresU.lean#L302) (PaperStructuresU.lean, line 302), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_05.json) (E243_05)
- `energy_le_two_energySqrt`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_05/Challenge.lean#L145) (E243_05, line 145), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_05/PaperStructuresU.lean#L314) (PaperStructuresU.lean, line 314), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_05.json) (E243_05)
- `exists_late_energy_window`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_05/Challenge.lean#L153) (E243_05, line 153), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_05/PaperStructuresU.lean#L322) (PaperStructuresU.lean, line 322), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_05.json) (E243_05)
- `energy_window_real_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_05/Challenge.lean#L71) (E243_05, line 71), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_05/PaperStatementsD.lean#L21) (PaperStatementsD.lean, line 21), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_05.json) (E243_05)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `energy_criterion`:

```lean
theorem energy_criterion (O : StandingOrbit) :
    (Summable O.energy ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ∧
      (Summable O.energySqrt ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) := by sorry
```

Challenge for `energy_summable_iff`:

```lean
theorem energy_summable_iff (O : StandingOrbit) :
    Summable O.energy ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by sorry
```

Challenge for `energySqrt_summable_iff`:

```lean
theorem energySqrt_summable_iff (O : StandingOrbit) :
    Summable O.energySqrt ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by sorry
```

Challenge for `energy_le_two_energySqrt`:

```lean
theorem energy_le_two_energySqrt (O : StandingOrbit) (n : ℕ) : O.energy n ≤ 2 * O.energySqrt n := by sorry
```

Challenge for `exists_late_energy_window`:

```lean
theorem exists_late_energy_window (O : StandingOrbit) (hunb : ∀ M : ℕ, ∃ n, M < O.u n) (S : ℕ) :
    ∃ (s τ : ℕ) (J : Finset ℕ), S ≤ s ∧ s < τ ∧ (∀ n ∈ J, s ≤ n ∧ n < τ) ∧
      (1 : ℝ) / 16 ≤ ∑ n ∈ J, O.energy n := by sorry
```

<a id="long243-res-slownegative"></a>

## Theorem 7.11 (slow negative part), page 33

> *Let $`(a,C,D)`$ be an exact orbit of natural numbers with $`a_n>1`$, $`C_n>0`$, $`D_0\ge1`$, under vanishing relative error. Suppose that for some $`\delta\in(0,1)`$ and all large $`n`$ with $`E_n<0`$ one has $`-E_n\le(1-\delta)\ell(C_n)`$. Then $`E_n=0`$ for all large $`n`$, and $`a_{n+1}=a_n^2-a_n+1`$ for all large $`n`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.slowNegative_eventually_zero_and_sylvesterNext_unconditional`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ExactOrbitRecordDichotomy.lean#L559)

```lean
theorem slowNegative_eventually_zero_and_sylvesterNext_unconditional
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (δ : ℝ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hDstep : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hslow : ∃ N, ∀ n, N ≤ n → E n < 0 →
      -((E n : ℤ) : ℝ) ≤ (1 - δ) * recordLogLog ((C n : ℕ) : ℝ)) :
    (∃ N, ∀ n, N ≤ n → E n = 0) ∧
      ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_recordTheta_gt_one`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ExactOrbitRecordDichotomy.lean#L363)

```lean
theorem exactOrbit_recordTheta_gt_one
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    (1 : EReal) < recordTheta C
```

3. [`ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_one_le_recordTheta`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ExactOrbitRecordDichotomy.lean#L522)

```lean
theorem exactOrbit_one_le_recordTheta
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    (1 : EReal) ≤ recordTheta C
```

4. [`ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_unbounded_of_error_not_eventually_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ExactOrbitRecordDichotomy.lean#L288)

```lean
theorem exactOrbit_unbounded_of_error_not_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    ∀ H : ℕ, ∃ n, H ≤ C n
```

5. [`ErdosProblems.Erdos243.PaperCompleteR21.tail_multiplier_quadratic_lower`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ExactOrbitRecordDichotomy.lean#L145)

```lean
theorem tail_multiplier_quadratic_lower
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hsmall : 4 * Int.natAbs (E n) < C n) :
    4 * a n ^ 2 ≤ 5 * a (n + 1) + 5 * a n
```

6. [`ErdosProblems.Erdos243.PaperCompleteR21.tail_binaryTower_lower`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ExactOrbitRecordDichotomy.lean#L254)

```lean
theorem tail_binaryTower_lower
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (h4 : 4 ≤ a N) :
    ∀ k, 2 * binaryTower k ≤ a (N + k)
```

7. [`ErdosProblems.Erdos243.PaperCompleteR21.exists_multiplier_ge_four`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ExactOrbitRecordDichotomy.lean#L218)

```lean
theorem exists_multiplier_ge_four
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (M : ℕ) :
    ∃ t, M ≤ t ∧ N ≤ t ∧ 4 ≤ a t
```

<a id="long243-res-slownegative-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `slowNegative_eventually_zero_and_sylvesterNext_unconditional`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L94) (E243_06, line 94), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStructuresAB.lean#L36) (PaperStructuresAB.lean, line 36), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `exactOrbit_recordTheta_gt_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L136) (E243_06, line 136), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStructuresAE.lean#L156) (PaperStructuresAE.lean, line 156), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `exactOrbit_one_le_recordTheta`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L125) (E243_06, line 125), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStructuresAE.lean#L144) (PaperStructuresAE.lean, line 144), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `exactOrbit_unbounded_of_error_not_eventually_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L75) (E243_06, line 75), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStructuresAB.lean#L19) (PaperStructuresAB.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `tail_multiplier_quadratic_lower`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L56) (E243_06, line 56), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStructuresAA.lean#L18) (PaperStructuresAA.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `tail_binaryTower_lower`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L110) (E243_06, line 110), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStructuresAB.lean#L51) (PaperStructuresAB.lean, line 51), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `exists_multiplier_ge_four`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L85) (E243_06, line 85), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStructuresAB.lean#L28) (PaperStructuresAB.lean, line 28), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `tail_multiplier_quadratic_lower`:

```lean
theorem tail_multiplier_quadratic_lower (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hsmall : 4 * Int.natAbs (E n) < C n) :
    4 * a n ^ 2 ≤ 5 * a (n + 1) + 5 * a n := by sorry
```

Challenge for `tail_binaryTower_lower`:

```lean
theorem tail_binaryTower_lower (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (h4 : 4 ≤ a N) :
    ∀ k, 2 * binaryTower k ≤ a (N + k) := by sorry
```

Challenge for `exists_multiplier_ge_four`:

```lean
theorem exists_multiplier_ge_four (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (M : ℕ) :
    ∃ t, M ≤ t ∧ N ≤ t ∧ 4 ≤ a t := by sorry
```

<a id="long243-res-strausbounded"></a>

## Theorem 7.12 (bounded or slowly growing increments of the product ratio), page 34

> *Let $`a_1<a_2<\cdots`$ be positive integers with $`a_{n+1}/a_n^2\to1`$ and $`\sum_{n\ge1}1/a_n=p/q`$, where $`p,q`$ are positive integers. Put
> ``` math
> Q_n=\frac{a_1a_2\cdots a_{n-1}}{a_n}
>      \left(\frac{a_n^2}{a_{n+1}}-1\right).
> ```
> If $`\limsup_nQ_n<\infty`$, the sequence is eventually Sylvester. The same conclusion holds if, for some $`\delta>0`$ and all large $`n`$,
> ``` math
> Q_n\le\frac{1-\delta}{q}\,
>  \ell(a_1\cdots a_{n-1}/a_n).
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR7.original_coordinate_bounded_defect`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/ProductDefect.lean#L211)

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

2. [`ErdosProblems.Erdos243.PaperCompleteR21.original_coordinate_slow_growth_defect`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/SlowGrowthProductIncrements.lean#L155)

```lean
theorem original_coordinate_slow_growth_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (δ : ℝ) (hδ : 0 < δ)
    (hslow : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productDefect a n ≤ (1 - δ) / (q : ℝ) *
        recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ))) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1
```

3. [`ErdosProblems.Erdos243.PaperCompleteR21.recordTheta_le_of_slow_negative`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/SlowGrowthProductIncrements.lean#L61)

```lean
theorem recordTheta_le_of_slow_negative
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ))
    (c : ℝ) (hc0 : 0 ≤ c) (N : ℕ)
    (hslow : ∀ n, N ≤ n → -((E n : ℤ) : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ)) :
    recordTheta C ≤ ((c : ℝ) : EReal)
```

4. [`ErdosProblems.Erdos243.PaperCompleteR21.prefix_ratio_le_canonicalNumerator`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/SlowGrowthProductIncrements.lean#L111)

```lean
theorem prefix_ratio_le_canonicalNumerator
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    (prefixProduct a n : ℝ) / (a n : ℝ) ≤
      ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)
```

<a id="long243-res-strausbounded-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `original_coordinate_bounded_defect`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L152) (E243_06, line 152), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/OriginalCoordinateBoundedDefect.lean#L27) (OriginalCoordinateBoundedDefect.lean, line 27), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `original_coordinate_slow_growth_defect`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L176) (E243_06, line 176), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStatementsL.lean#L65) (PaperStatementsL.lean, line 65), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `recordTheta_le_of_slow_negative`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L204) (E243_06, line 204), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStatementsR.lean#L21) (PaperStatementsR.lean, line 21), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `prefix_ratio_le_canonicalNumerator`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L190) (E243_06, line 190), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStatementsL.lean#L79) (PaperStatementsL.lean, line 79), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-onethreshold"></a>

## Corollary 7.13 (the $`1/n`$ threshold), page 35

> *Let $`a_1<a_2<\cdots`$ be positive integers with $`a_{n+1}/a_n^2\to1`$ and $`\sum_n1/a_n\in\mathbb{Q}`$. If
> ``` math
> \limsup_{n\to\infty} n\,(a_n^2/a_{n+1}-1)_+<1,
> ```
> then $`a_{n+1}=a_n^2-a_n+1`$ for all large $`n`$. The same conclusion holds if, for some $`K\ge0`$ and $`\varepsilon>0`$,
> ``` math
> \frac{a_n^2}{a_{n+1}}-1\le\frac1n+\frac{K}{n^{1+\varepsilon}}
>  \quad\hbox{eventually}.
> ```
> In particular the one-sided bound by $`1/n`$ is included.*

The Lean declarations below together state this result or one that implies it. The strict limsup case, the bound $1/n+K/n^{1+\varepsilon}$ and the one-sided bound $1/n$ are, in that order, `original_coordinate_strict_one`, `original_coordinate_inclusive_one` and `original_coordinate_inclusive_one_pointwise`, with the limsup hypothesis written as an eventual bound by some $r<1$. Lean indexes the sequence from $0$, so in the paper's indexing its hypotheses read $(n-1)(a_n^2/a_{n+1}-1)_+\le r$ and $a_n^2/a_{n+1}-1\le1/(n-1)+K/(n-1)^{1+\varepsilon}$ eventually, and the printed hypotheses imply them.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.original_coordinate_strict_one`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ProductDefectThresholds.lean#L92)

```lean
theorem original_coordinate_strict_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (r : ℝ) (hr : r < 1)
    (hlimsup : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) * max ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1) 0 ≤ r) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1
```

2. [`ErdosProblems.Erdos243.PaperCompleteR20.original_coordinate_inclusive_one`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR20/InclusiveOne.lean#L207)

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

3. [`ErdosProblems.Erdos243.PaperCompleteR20.original_coordinate_inclusive_one_pointwise`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR20/InclusiveOne.lean#L225)

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

<a id="long243-res-onethreshold-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `original_coordinate_strict_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L250) (E243_06, line 250), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStatementsF.lean#L16) (PaperStatementsF.lean, line 16), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `original_coordinate_inclusive_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L220) (E243_06, line 220), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStatementsB.lean#L19) (PaperStatementsB.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)
- `original_coordinate_inclusive_one_pointwise`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_06/Challenge.lean#L234) (E243_06, line 234), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_06/PaperStatementsB.lean#L33) (PaperStatementsB.lean, line 33), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_06.json) (E243_06)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-classicalhalfspace"></a>

## Proposition 7.14 (comparison of the two signs), page 37

> *The factor $`M_n=D_n/L_n`$ divides $`G_n=\gcd(C_n,D_n)`$. Thus $`G_n/M_n`$ is a positive integer and $`E_n/M_n=(G_n/M_n)\tilde e_n`$ is an integer with the same sign as $`E_n`$. The sign of the growth ratio minus one also depends on a correction term. The exact recurrences give, whenever $`a_{n+1}C_nC_{n+1}\ne0`$,
> ``` math
> \begin{equation}
> \label{long243:eq:shiftedsign}
>  \frac{a_n^2}{a_{n+1}}-1=-\frac{E_n}{C_n}+\Lambda_n,
>  \qquad
>  \Lambda_n=\frac{\bigl(1-E_n/C_n\bigr)\bigl(a_n-1+E_{n+1}/C_{n+1}\bigr)}{a_{n+1}},
> \end{equation}
> ```
> and, under the standing positive rational-tail hypotheses, $`0<\Lambda_n<3/a_n`$ for all sufficiently large $`n`$. The Erdős–Straus quantity of Theorem 3 is
> ``` math
> Z_n^{\mathrm{ES}}=
>  \frac{[a_1,\ldots,a_n]}{a_{n+1}}
>  \left(\frac{a_{n+1}^2}{a_{n+2}}-1\right).
> ```
> Its least common multiple includes $`a_n`$ but not the clearing denominator $`q`$. It is not $`Q_n=(P_n/a_n)\gamma_n`$ from the preceding subsection, nor $`L_n\gamma_{n+1}/a_{n+1}`$ under our convention $`L_n=\operatorname{lcm}(q,a_1,\ldots,a_{n-1})`$. Being a positive multiple of the next growth defect, $`Z_n^{\mathrm{ES}}`$ has the sign of $`\Lambda_{n+1}-E_{n+1}/C_{n+1}`$. For all sufficiently large $`n`$, it is positive when $`E_{n+1}\le0`$; for $`E_{n+1}>0`$, it is negative precisely when $`E_{n+1}/C_{n+1}>\Lambda_{n+1}`$. On a Sylvester tail $`E_n=0`$ and $`\Lambda_n=(a_n-1)/a_{n+1}>0`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.overlapDebt_dvd_gcd`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L206)

```lean
theorem overlapDebt_dvd_gcd
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    0 < cumulativeOverlapDebt q a n ∧
      cumulativeOverlapDebt q a n *  cumulativeDigitLcm q a n =
        canonicalDenominator a q n ∧
      cumulativeOverlapDebt q a n ∣
        Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n)
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.canonicalError_div_overlapDebt`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L225)

```lean
theorem canonicalError_div_overlapDebt
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    0 < Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) /
        cumulativeOverlapDebt q a n ∧
      ((cumulativeOverlapDebt q a n : ℕ) : ℤ) ∣ canonicalError a p q n ∧
      ((Nat.gcd (canonicalNaturalNumerator a p q n)
          (canonicalDenominator a q n) : ℕ) : ℤ) ∣ canonicalError a p q n ∧
      canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) =
        ((Nat.gcd (canonicalNaturalNumerator a p q n) (canonicalDenominator a q n) /
            cumulativeOverlapDebt q a n : ℕ) : ℤ) *
          (canonicalError a p q n /
            ((Nat.gcd (canonicalNaturalNumerator a p q n)
              (canonicalDenominator a q n) : ℕ) : ℤ)) ∧
      (0 < canonicalError a p q n ↔
        0 < canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ)) ∧
      (canonicalError a p q n < 0 ↔
        canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) < 0) ∧
      (canonicalError a p q n = 0 ↔
        canonicalError a p q n / ((cumulativeOverlapDebt q a n : ℕ) : ℤ) = 0)
```

3. [`ErdosProblems.Erdos243.PaperCompleteR21.growthDefect_eq_neg_relativeError_add_shiftedCorrection`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L325)

```lean
theorem growthDefect_eq_neg_relativeError_add_shiftedCorrection
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (hne : aNext * C * CNext ≠ 0) :
    a ^ 2 / aNext - 1 =
      -(E / C) + shiftedCorrectionTerm a aNext C CNext E ENext
```

4. [`ErdosProblems.Erdos243.PaperCompleteR21.canonical_growthDefect_identity`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L415)

```lean
theorem canonical_growthDefect_identity
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 =
      -(((canonicalError a p q n : ℤ) : ℝ) /
          ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)) +
        canonicalCorrection a p q n
```

5. [`ErdosProblems.Erdos243.PaperCompleteR21.canonicalCorrection_pos_and_lt_three_div`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L459)

```lean
theorem canonicalCorrection_pos_and_lt_three_div
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ n, N ≤ n →
      0 < canonicalCorrection a p q n ∧
        canonicalCorrection a p q n < 3 / (a n : ℝ)
```

6. [`ErdosProblems.Erdos243.PaperCompleteR21.shiftedCorrectionTerm_pos_and_lt_three_div`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L380)

```lean
theorem shiftedCorrectionTerm_pos_and_lt_three_div
    {A ANext C CNext E ENext : ℝ}
    (hA : 2 ≤ A) (hANext : A ^ 2 / 2 ≤ ANext)
    (hθ : |E / C| ≤ 1 / 4) (hθNext : |ENext / CNext| ≤ 1 / 4) :
    0 < shiftedCorrectionTerm A ANext C CNext E ENext ∧
      shiftedCorrectionTerm A ANext C CNext E ENext < 3 / A
```

7. [`ErdosProblems.Erdos243.PaperCompleteR21.erdosStraus_lcm_includes_digit_not_denominator`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L527)

```lean
theorem erdosStraus_lcm_includes_digit_not_denominator (a : ℕ → ℕ) (n : ℕ) :
    cumulativeDigitLcm 1 a (n + 1) = Nat.lcm (cumulativeDigitLcm 1 a n) (a n) ∧
      a n ∣ cumulativeDigitLcm 1 a (n + 1) ∧
      cumulativeDigitLcm 1 a 0 = 1
```

8. [`ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity_ne_productDefect_ne_lcmShift`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L543)

```lean
theorem erdosStrausQuantity_ne_productDefect_ne_lcmShift :
    ∃ (a : ℕ → ℕ) (q n : ℕ), 0 < q ∧ (∀ m, 0 < a m) ∧
      erdosStrausQuantity a n ≠ productDefect a n ∧
      erdosStrausQuantity a n ≠
        (cumulativeDigitLcm q a n : ℝ) *
          ((a (n + 1) : ℝ) ^ 2 / (a (n + 2) : ℝ) - 1) / (a (n + 1) : ℝ)
```

9. [`ErdosProblems.Erdos243.PaperCompleteR21.erdosStrausQuantity_sign`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L573)

```lean
theorem erdosStrausQuantity_sign
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ n, N ≤ n →
      (0 < erdosStrausQuantity a n ↔
        ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
            ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ) <
          canonicalCorrection a p q (n + 1)) ∧
      (erdosStrausQuantity a n < 0 ↔
        canonicalCorrection a p q (n + 1) <
          ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
            ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ)) ∧
      (canonicalError a p q (n + 1) ≤ 0 → 0 < erdosStrausQuantity a n) ∧
      (0 < canonicalError a p q (n + 1) →
        (erdosStrausQuantity a n < 0 ↔
          canonicalCorrection a p q (n + 1) <
            ((canonicalError a p q (n + 1) : ℤ) : ℝ) /
              ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ)))
```

10. [`ErdosProblems.Erdos243.PaperCompleteR21.sylvesterTail_shiftedCorrection`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L351)

```lean
theorem sylvesterTail_shiftedCorrection
    {a aNext D DNext C CNext E ENext : ℝ}
    (hD : DNext = a * D)
    (hC : CNext = a * C - D)
    (hE : E = D - (a - 1) * C)
    (hENext : ENext = DNext - (aNext - 1) * CNext)
    (ha : 1 < a)
    (hsyl : aNext = a ^ 2 - a + 1)
    (hzero : E = 0) :
    ENext = 0 ∧
      shiftedCorrectionTerm a aNext C CNext E ENext = (a - 1) / aNext ∧
      0 < shiftedCorrectionTerm a aNext C CNext E ENext
```

11. [`ErdosProblems.Erdos243.PaperCompleteR21.overlapDebt_mul_lcmClearedNumerator`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L135)

```lean
theorem overlapDebt_mul_lcmClearedNumerator
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    ((cumulativeOverlapDebt q a n : ℕ) : ℤ) * lcmClearedNumerator a p q n =
      clearedIntegerNumerator a p q n
```

12. [`ErdosProblems.Erdos243.PaperCompleteR21.digitProductScale_eq_canonicalDenominator`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ClassicalHalfspaceSigns.lean#L82)

```lean
theorem digitProductScale_eq_canonicalDenominator (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    digitProductScale q a n = canonicalDenominator a q n
```

<a id="long243-res-classicalhalfspace-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `overlapDebt_dvd_gcd`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L215) (E243_07, line 215), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsQ.lean#L89) (PaperStatementsQ.lean, line 89), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `canonicalError_div_overlapDebt`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L153) (E243_07, line 153), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsQ.lean#L22) (PaperStatementsQ.lean, line 22), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `growthDefect_eq_neg_relativeError_add_shiftedCorrection`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L62) (E243_07, line 62), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsE.lean#L18) (PaperStatementsE.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `canonical_growthDefect_identity`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L112) (E243_07, line 112), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsL.lean#L45) (PaperStatementsL.lean, line 45), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `canonicalCorrection_pos_and_lt_three_div`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L101) (E243_07, line 101), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsL.lean#L35) (PaperStatementsL.lean, line 35), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `shiftedCorrectionTerm_pos_and_lt_three_div`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L73) (E243_07, line 73), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsE.lean#L28) (PaperStatementsE.lean, line 28), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `erdosStraus_lcm_includes_digit_not_denominator`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L209) (E243_07, line 209), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsQ.lean#L82) (PaperStatementsQ.lean, line 82), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `erdosStrausQuantity_ne_productDefect_ne_lcmShift`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L178) (E243_07, line 178), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsQ.lean#L49) (PaperStatementsQ.lean, line 49), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `erdosStrausQuantity_sign`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L186) (E243_07, line 186), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsQ.lean#L58) (PaperStatementsQ.lean, line 58), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `sylvesterTail_shiftedCorrection`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L81) (E243_07, line 81), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsE.lean#L36) (PaperStatementsE.lean, line 36), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `overlapDebt_mul_lcmClearedNumerator`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L224) (E243_07, line 224), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsQ.lean#L99) (PaperStatementsQ.lean, line 99), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `digitProductScale_eq_canonicalDenominator`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L174) (E243_07, line 174), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsQ.lean#L44) (PaperStatementsQ.lean, line 44), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-coprimalitycap"></a>

## Proposition 7.15 (an elementary interval bound), page 38

> *Let $`m_0<m_1<\cdots`$ be pairwise coprime integers at least $`2`$ with $`\theta=\sum_i1/m_i<1`$. For all integers $`x\ge1`$ and $`L\ge1`$ satisfying $`L>k/(1-\theta)`$, where $`k=\#\{i:m_i\le x+L\}`$, the interval $`[x,x+L)`$ contains an integer divisible by no $`m_i`$. If also $`\ell(m_i)=i+O(1)`$, then for every $`\epsilon>0`$ there are an index $`T`$ and a strictly increasing sequence of positive integers $`(u_n)`$ such that
> ``` math
> m_i\nmid u_n\quad\text{for every }i\ge T\text{ and every }n,
>  \qquad
>  u_{n+1}-u_n\le(1+\epsilon)\ell(u_n)\quad\text{eventually}.
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.exists_avoiding_in_window`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/WindowAvoidance.lean#L201)

```lean
theorem exists_avoiding_in_window
    {m : ℕ → ℕ} (hmono : StrictMono m) (hm2 : ∀ i, 2 ≤ m i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    {θ : ℝ} (hsum : Summable fun i => (1 : ℝ) / (m i : ℝ))
    (hθ : ∑' i, (1 : ℝ) / (m i : ℝ) = θ) (hθ1 : θ < 1)
    {x L : ℕ} (hx : 1 ≤ x) (hL : 1 ≤ L)
    (hkL : ((({i | m i ≤ x + L} : Set ℕ).ncard : ℝ)) / (1 - θ) < (L : ℝ)) :
    ∃ n, x ≤ n ∧ n < x + L ∧ ∀ i, ¬ m i ∣ n
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.exists_slow_rise_avoiding_sequence`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/WindowAvoidance.lean#L423)

```lean
theorem exists_slow_rise_avoiding_sequence
    {m : ℕ → ℕ} (hmono : StrictMono m) (hm2 : ∀ i, 2 ≤ m i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    {θ : ℝ} (hsum : Summable fun i => (1 : ℝ) / (m i : ℝ))
    (hθ : ∑' i, (1 : ℝ) / (m i : ℝ) = θ) (hθ1 : θ < 1)
    (hscale : ∃ C : ℝ, ∀ i, |ellScale (m i : ℝ) - (i : ℝ)| ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (T : ℕ) (u : ℕ → ℕ), StrictMono u ∧ (∀ n, 0 < u n) ∧
      (∀ i, T ≤ i → ∀ n, ¬ m i ∣ u n) ∧
      ∀ᶠ n in atTop, ((u (n + 1) : ℝ) - (u n : ℝ)) ≤ (1 + ε) * ellScale (u n : ℝ)
```

<a id="long243-res-coprimalitycap-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exists_avoiding_in_window`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L238) (E243_07, line 238), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsD.lean#L25) (PaperStatementsD.lean, line 25), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `exists_slow_rise_avoiding_sequence`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L248) (E243_07, line 248), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsD.lean#L35) (PaperStatementsD.lean, line 35), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-descent"></a>

## Theorem 8.1 (descent), page 39

> *Let $`C,E:\mathbb{N}\to\mathbb{N}`$ satisfy $`C_{n+1}+E_n=C_n`$ for every $`n`$. Then $`E_n=0`$ for all sufficiently large $`n`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.centeredState_eventually_zero`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L1843)

```lean
theorem centeredState_eventually_zero
    (C E : ℕ → ℕ) (hrec : ∀ n, C (n + 1) + E n = C n) :
    ∃ N, ∀ n, N ≤ n → E n = 0
```

<a id="long243-res-descent-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `centeredState_eventually_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L279) (E243_07, line 279), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsA.lean#L287) (PaperStatementsA.lean, line 287), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-constant"></a>

## Theorem 9.2 (no constant negative magnitude), page 40

> *For any $`m,c\in\mathbb{N}`$ with $`m>0`$, there is no pair of sequences $`a,D:\mathbb{N}\to\mathbb{N}`$ with $`a_n\ge2`$ for all $`n`$ satisfying $`D_{n+1}=a_nD_n`$ and <a href="#long243:eq:shape" data-reference-type="eqref" data-reference="long243:eq:shape">[long243:eq:shape]</a>. The same holds if the shape equation only begins at some index.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.no_constantNegative_shapeEquation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/NegativeMagnitudeExclusions.lean#L38)

```lean
theorem no_constantNegative_shapeEquation
    (m c : ℕ) (hm : 0 < m) :
    ¬ ∃ a D : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, D n + m = (a n - 1) * (c + n * m))
```

2. [`ErdosProblems.Erdos243.PaperCompleteR21.no_eventuallyConstantNegative_shapeEquation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/NegativeMagnitudeExclusions.lean#L52)

```lean
theorem no_eventuallyConstantNegative_shapeEquation
    (m c N : ℕ) (hm : 0 < m) :
    ¬ ∃ a D : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, D (N + n) + m = (a (N + n) - 1) * (c + n * m))
```

<a id="long243-res-constant-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `no_constantNegative_shapeEquation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L263) (E243_07, line 263), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsA.lean#L131) (PaperStatementsA.lean, line 131), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)
- `no_eventuallyConstantNegative_shapeEquation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_07/Challenge.lean#L271) (E243_07, line 271), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_07/PaperStatementsA.lean#L138) (PaperStatementsA.lean, line 138), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_07.json) (E243_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-periodic"></a>

## Theorem 10.1 (no periodic negative magnitude), page 41

> *Let $`a,D,C,e:\mathbb{N}\to\mathbb{N}`$ with $`a_n\ge2`$, $`e_n>0`$ and $`e_n<a_n`$ for every $`n`$, satisfying
> ``` math
> D_{n+1}=a_nD_n,\qquad C_{n+1}=C_n+e_n,\qquad D_n+e_n=(a_n-1)C_n ,
> ```
> and suppose $`e_{n+h}=e_n`$ and $`C_{n+h}=C_n+M`$ for some $`h>0`$ and $`M>0`$. This is impossible.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR21.no_periodicNegative_shapeEquation`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/NegativeMagnitudeExclusions.lean#L68)

```lean
theorem no_periodicNegative_shapeEquation
    (h M : ℕ) (hh : 0 < h) (hM : 0 < M) :
    ¬ ∃ a D C e : ℕ → ℕ,
      (∀ n, 2 ≤ a n) ∧
      (∀ n, 0 < e n) ∧
      (∀ n, e n < a n) ∧
      (∀ n, D (n + 1) = a n * D n) ∧
      (∀ n, C (n + 1) = C n + e n) ∧
      (∀ n, D n + e n = (a n - 1) * C n) ∧
      (∀ n, e (n + h) = e n) ∧
      (∀ n, C (n + h) = C n + M)
```

<a id="long243-res-periodic-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `no_periodicNegative_shapeEquation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L55) (E243_08, line 55), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsA.lean#L140) (PaperStatementsA.lean, line 140), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-crt"></a>

## Lemma 11.1 (shifted blocks of consecutive multiples), page 42

> *Let $`m_0,\ldots,m_{B-1}`$ be pairwise coprime and at least $`2`$. For every bound there is a $`t`$ beyond it with $`m_i\mid t+i`$ for each $`i<B`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR21.exists_shiftedBlock_consecutiveMultiples`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ForbiddenBlockCrossing.lean#L26)

```lean
theorem exists_shiftedBlock_consecutiveMultiples
    (B : ℕ) (m : ℕ → ℕ)
    (hm : ∀ i, i < B → 2 ≤ m i)
    (hpair : ∀ i, i < B → ∀ j, j < B → i ≠ j → Nat.Coprime (m i) (m j))
    (L : ℕ) :
    ∃ t, L < t ∧ ∀ i, i < B → m i ∣ t + i
```

<a id="long243-res-crt-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exists_shiftedBlock_consecutiveMultiples`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L37) (E243_08, line 37), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsA.lean#L107) (PaperStatementsA.lean, line 107), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-barrier"></a>

## Theorem 11.3 (bounded increases and coprimality to earlier moduli), page 43

> *Let $`u:\mathbb{N}\to\mathbb{N}`$ tend to infinity with $`u_{n+1}\le u_n+B`$ for a fixed integer $`B\ge1`$. Then $`u`$ cannot remain coprime to infinitely many fresh pairwise coprime moduli: there is no family of pairwise coprime $`m_i\ge2`$, one for each index, such that $`\gcd(m_i,u_t)=1`$ whenever $`i<t`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR21.no_boundedRise_coprimeToEarlierModuli`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ForbiddenBlockCrossing.lean#L44)

```lean
theorem no_boundedRise_coprimeToEarlierModuli
    (u : ℕ → ℕ) (B : ℕ) (hB : 1 ≤ B)
    (hrise : ∀ n, u (n + 1) ≤ u n + B)
    (hTop : Filter.Tendsto u Filter.atTop Filter.atTop) :
    ¬ ∃ m : ℕ → ℕ,
      (∀ i, 2 ≤ m i) ∧
      (∀ i j, i ≠ j → Nat.Coprime (m i) (m j)) ∧
      (∀ i t, i < t → Nat.gcd (m i) (u t) = 1)
```

<a id="long243-res-barrier-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `no_boundedRise_coprimeToEarlierModuli`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L45) (E243_08, line 45), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsA.lean#L117) (PaperStatementsA.lean, line 117), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-reduced"></a>

## Proposition 11.4 (reduced tails are pairwise coprime), page 44

> *In a reduced exact tail, $`a_n`$ is coprime to $`v_n`$; the multipliers at distinct indices are pairwise coprime; and every earlier multiplier is coprime to every later numerator.*

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

<a id="long243-res-reduced-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `persistent_coprimality`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L83) (E243_08, line 83), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsA.lean#L247) (PaperStatementsA.lean, line 247), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-gcdstab"></a>

## Proposition 11.6 (the tail gcd stabilises), page 44

> *Let $`(a,D,C)`$ be an exact orbit of natural numbers, that is, a triple of $`\mathbb{N}`$-valued sequences with $`C_{n+1}+D_n=a_nC_n`$ and $`D_{n+1}=a_nD_n`$, whose error is $`E_n=D_n-(a_n-1)C_n`$. Suppose some fixed integer $`B\ge1`$ satisfies $`-B\le E_n<0`$ at infinitely many indices. Then $`\gcd(C_n,D_n)`$ is eventually constant, and beyond that index the orbit divided by the stable gcd is a reduced exact tail.*

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

<a id="long243-res-gcdstab-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `gcd_stabilises_and_reduces`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L68) (E243_08, line 68), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsA.lean#L224) (PaperStatementsA.lean, line 224), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-gcdsparse"></a>

## Proposition 11.7 (vanishing relative error makes strict gcd changes sparse), page 45

> *Let $`a,C,D:\mathbb{N}\to\mathbb{N}`$ satisfy $`C_{n+1}+D_n=a_nC_n`$ and $`D_{n+1}=a_nD_n`$ with $`C_n>0`$, and put $`E_n=D_n-(a_n-1)C_n`$, $`G_n=\gcd(C_n,D_n)`$ and $`\Gamma(N)=\#\{0\le j<N:G_j<G_{j+1}\}`$. If $`|E_n|/C_n\to0`$, then $`\Gamma(N)=o(N)`$. Moreover, for every starting bound $`B`$ and block length $`L`$, some $`n\ge B`$ satisfies
> ``` math
> G_n=G_{n+1}=\cdots=G_{n+L}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR7.sparse_gcd_changes`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR7/Limits.lean#L97)

```lean
theorem sparse_gcd_changes
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hlim : Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N ↦
      (((Finset.range N).filter (fun j ↦
        Nat.gcd (C j) (D j) < Nat.gcd (C (j + 1)) (D (j + 1)))).card : ℝ) /
          (N : ℝ)) atTop (nhds 0) ∧
    (∀ B L : ℕ, ∃ n, B ≤ n ∧ ∀ j, j ≤ L →
      Nat.gcd (C (n + j)) (D (n + j)) = Nat.gcd (C n) (D n))
```

<a id="long243-res-gcdsparse-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `sparse_gcd_changes`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L125) (E243_08, line 125), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsO.lean#L18) (PaperStatementsO.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-bounded"></a>

## Theorem 12.1 (bounded negative part), page 46

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

The Lean declaration below states this result or one that implies it. The Lean statement omits hypothesis (4), eventual strict centring $|E_n|<C_n$, which the printed theorem adds (it is also the case $K=1$ of (6)); hypotheses (1), (2), (3), (5) and (6) are as printed.

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

<a id="long243-res-bounded-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `eventuallyBoundedNegativePart_eventually_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L107) (E243_08, line 107), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsA.lean#L295) (PaperStatementsA.lean, line 295), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-cor"></a>

## Corollary 12.2, page 46

> *Under the hypotheses of Theorem 12.1, together with $`C_{n+1}\ne0`$ for all large $`n`$, the multipliers satisfy $`a_{n+1}=a_n^{2}-a_n+1`$ for all sufficiently large $`n`$.*

The Lean declaration below states this result or one that implies it. The Lean statement drops both eventual strict centring $|E_n|<C_n$ and the extra hypothesis $C_{n+1}\ne0$ for large $n$, which the printed corollary adds (the latter already follows from $C_n>0$); its conclusion $a_{n+1}=a_n^2-a_n+1$ for all large $n$ is the printed one.

[`ErdosProblems.Erdos243.boundedNegativePart_sylvesterNext_eventually`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/ReciprocalTailRigidity.lean#L2412)

```lean
theorem boundedNegativePart_sylvesterNext_eventually
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hbound : ∃ N B : ℕ, ∀ n, N ≤ n → -(B : ℤ) ≤ E n)
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (E n) < C n) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)
```

<a id="long243-res-cor-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `boundedNegativePart_sylvesterNext_eventually`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L93) (E243_08, line 93), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsA.lean#L269) (PaperStatementsA.lean, line 269), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-mass"></a>

## Theorem 13.1 (finite sum of relative increases), page 47

> *Let $`C_n\in\mathbb{N}_{>0}`$ and $`E_n\in\mathbb{Z}`$ satisfy $`C_{n+1}=C_n-E_n`$. If
> ``` math
> \sum_{n=0}^{\infty}\frac{(-E_n)_+}{C_n}<\infty,
> ```
> then $`E_n=0`$ eventually. For an exact reciprocal-tail orbit this implies $`a_{n+1}=a_n^2-a_n+1`$ eventually. No hypothesis $`|E_n|/C_n\to0`$ is required.*

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

<a id="long243-res-mass-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `finite_negative_mass_paper`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L177) (E243_08, line 177), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsL.lean#L114) (PaperStatementsL.lean, line 114), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-frontier"></a>

## Proposition 14.1 (necessary conditions on a counterexample), page 49

> *For the integer tail attached to any counterexample to Problem <a href="#long243:res:problem" data-reference-type="ref" data-reference="long243:res:problem">1</a>,
> ``` math
> E_n\ne0\quad\hbox{eventually},\qquad
>  \frac{|E_n|}{C_n}\longrightarrow0,
> ```
> and
> ``` math
> \limsup_{\substack{n\to\infty\\E_n<0}}(-E_n)=\infty,
>  \qquad
>  \sum_{n=0}^{\infty}\frac{(-E_n)_+}{C_n}=\infty .
> ```
> In particular, negative indices occur infinitely often. Thus the remaining regime consists of unbounded negative errors along exact reciprocal tails for which the sum of relative increases diverges.*

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

<a id="long243-res-frontier-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `canonical_frontier`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L159) (E243_08, line 159), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsL.lean#L84) (PaperStatementsL.lean, line 84), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-variablerise"></a>

## Proposition 14.6 (small increases when the prime moduli are sparse), page 53

> *There exist strictly increasing primes $`p_i`$ and a strictly increasing positive integer sequence $`u_n\to\infty`$ such that $`\gcd(u_n,p_i)=1`$ for all $`i,n`$ and
> ``` math
> u_{n+1}-u_n=O\bigl(\sqrt{\log\log(u_n+e^e)}\bigr)
>              =o\bigl(\log\log(u_n+3)\bigr).
> ```
> Thus the bounded-increment hypothesis of Theorem 11.3 cannot be replaced by an $`o(\log\log u_n)`$ bound without a quantitative restriction on the moduli.*

The Lean declaration below states this result or one that implies it. The Lean statement asserts the printed objects with the printed properties, with the $O$-bound written as $u_{n+1}-u_n\le C\sqrt{\log\log(u_n+e^e)}$ for every $n$ and the $o$-bound as $(u_{n+1}-u_n)/\log\log(u_n+3)\to0$.

[`ErdosProblems.Erdos243.PaperCompleteR21.exists_sparse_prime_coprime_sequence`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/WindowAvoidance.lean#L862)

```lean
theorem exists_sparse_prime_coprime_sequence :
    ∃ (p : ℕ → ℕ) (u : ℕ → ℕ),
      StrictMono p ∧ (∀ i, Nat.Prime (p i)) ∧
      StrictMono u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop atTop ∧
      (∀ i n, Nat.Coprime (u n) (p i)) ∧
      (∃ Cst : ℝ, ∀ n, ((u (n + 1) : ℝ) - (u n : ℝ))
          ≤ Cst * Real.sqrt (Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1))))) ∧
      Tendsto (fun n => ((u (n + 1) : ℝ) - (u n : ℝ))
          / Real.log (Real.log ((u n : ℝ) + 3))) atTop (𝓝 0)
```

<a id="long243-res-variablerise-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exists_sparse_prime_coprime_sequence`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L199) (E243_08, line 199), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsD.lean#L49) (PaperStatementsD.lean, line 49), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-gapconstant"></a>

## Theorem 14.7 (largest gaps between integers avoiding given multiples), page 54

> *Let $`m_0<m_1<\cdots`$ be pairwise coprime integers at least $`2`$ with $`\ell(m_j)=j+O(1)`$, where $`\ell(x)=\log_2\log_2\max(4,x)`$. Let $`\sigma=\prod_j(1-1/m_j)>0`$ and enumerate the positive integers divisible by no $`m_j`$ in increasing order as $`(u_n)`$. Then
> ``` math
> \limsup_{n\to\infty}\frac{u_{n+1}-u_n}{\ell(u_n)}=\sigma^{-1}.
> ```
> This is a statement about avoidance of multiples of whole moduli. It is not a statement about coprimality to composite $`m_j`$, or about integer tail orbits.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos243.PaperCompleteR21.maximal_gap_limsup_eq_inv_sigma`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/MaximalGapConstant.lean#L1041)

```lean
theorem maximal_gap_limsup_eq_inv_sigma
    (m : ℕ → ℕ) (hm2 : ∀ j, 2 ≤ m j) (hmono : StrictMono m)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    (Cs : ℝ) (hscale : ∀ j, |recordLogLog (m j : ℝ) - (j : ℝ)| ≤ Cs)
    (σ : ℝ) (hσpos : 0 < σ)
    (hσ : Tendsto (fun T => ∏ j ∈ Finset.range T, (1 - 1 / (m j : ℝ))) atTop (nhds σ)) :
    limsup (fun n : ℕ =>
        ((Nat.nth (Avoids m) (n + 1) : ℝ) - (Nat.nth (Avoids m) n : ℝ)) /
          recordLogLog (Nat.nth (Avoids m) n : ℝ)) atTop = σ⁻¹
```

<a id="long243-res-gapconstant-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `maximal_gap_limsup_eq_inv_sigma`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L221) (E243_08, line 221), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsI.lean#L55) (PaperStatementsI.lean, line 55), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long243-res-residue"></a>

## Theorem B.1 (factorial residue reduction), page 56

> *For all $`h`$ and all integers $`a\equiv b \pmod{(h+1)!}`$, the orbit from $`a`$ survives $`h`$ forced updates exactly when the orbit from $`b`$ does.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos243.PaperCompleteR21.forcedOrbit_survives_iff_of_factorial_modEq`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/PaperCompleteR21/ForcedOrbitResidueHorizon.lean#L21)

```lean
theorem forcedOrbit_survives_iff_of_factorial_modEq
    (h : ℕ) (a b : ℤ)
    (hab : a ≡ b [ZMOD ((h + 1).factorial : ℤ)]) :
    ForcedSurvives h 0 a ↔ ForcedSurvives h 0 b
```

2. [`ErdosProblems.Erdos243.forcedSurvives_iff_of_modEq_factorial`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos243/FiniteHorizonResidue.lean#L134)

```lean
theorem forcedSurvives_iff_of_modEq_factorial
    {h : ℕ} {a b : ℤ}
    (hab : a ≡ b [ZMOD ((h + 1).factorial : ℤ)]) :
    ForcedSurvives h 0 a ↔ ForcedSurvives h 0 b
```

<a id="long243-res-residue-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `forcedOrbit_survives_iff_of_factorial_modEq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L246) (E243_08, line 246), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsK.lean#L47) (PaperStatementsK.lean, line 47), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)
- `forcedSurvives_iff_of_modEq_factorial`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E243_08/Challenge.lean#L252) (E243_08, line 252), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E243_08/PaperStatementsK.lean#L54) (PaperStatementsK.lean, line 54), [replay report](../evidence/comparator/replay-35935225572/receipt-E243_08.json) (E243_08)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
