# Formal evidence: Hankel Determinants of Geometric Moments\\and Rational Lambert Values

This record belongs to the paper [erdos-1049-rational-base-lambert.pdf](../paper/1049/erdos-1049-rational-base-lambert.pdf). For every result it lists the Lean declarations that state it, and the recorded Comparator check where there is one. The inline links and margin marks in the paper use the same result mapping.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`436f55ebdafa`](https://github.com/wcook04/plectis-erdos/tree/436f55ebdafa67e4af0fff79f621c13f2ded12bf) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 7 results: 7 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 6 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below. Comparator checks separately declared statements, the axiom budget and kernel acceptance; it does not establish novelty, significance or peer review.

<a id="res-sharp-fixed-base"></a>

## Theorem 1.1 (the size of $`V_N^*`$ at a fixed base), page 1

> *Fix $`0<q<1`$ and write $`P=(q;q)_\infty`$, $`B_N=N(N-1)(2N-1)/6`$ and $`C_N=(N!)^2(N+1)!/2^N`$. There is a $`K(q)>0`$ with
> ``` math
> V_N^*(q)\sim K(q)\,C_Nq^{B_N}P^{2N}N^{-8F(1/q)}
>  \qquad(N\to\infty).
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base_exists`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/SharpFixedBaseShort.lean#L53)

```lean
theorem sharp_fixed_base_exists {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun N : ℕ => (PaperR16.actualMomentHankel q N).det /
        (K * leadC N * q ^ (N * (N - 1) * (2 * N - 1) / 6) *
          PaperR10.qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * PaperR16.lambert q))) atTop (𝓝 1)
```

<a id="res-sharp-fixed-base-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `sharp_fixed_base_exists`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_08/Challenge.lean#L171) (E1049_08, line 171), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_08/PaperStatementsU.lean#L25) (PaperStatementsU.lean, line 25), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_08.json) (E1049_08)

Challenge for `sharp_fixed_base_exists`:

```lean
theorem sharp_fixed_base_exists {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
        (K * leadC N * q ^ (N * (N - 1) * (2 * N - 1) / 6) *
          qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * lambert q))) atTop (𝓝 1) := by sorry
```

<a id="thm-geometric-moments"></a>

## Theorem 2.1 (geometric moment determinants), page 3

> *Let $`0<q<1`$ and $`a_k>0`$ for $`k\ge0`$. Suppose that, for fixed constants $`C>0`$ and $`\kappa\ge0`$,
> ``` math
> \begin{equation}
> \label{eq:automatic-shift-bound}
>  \frac{a_{k+h}}{a_k}\longrightarrow1\quad(k\to\infty)
>  \text{ for each fixed }h\ge0,
>  \qquad
>  \frac{a_{k+h}}{a_k}\le C(1+h)^\kappa\quad(k,h\ge0).
> \end{equation}
> ```
> For $`M_m=\sum_{k\ge0}a_kq^{(m+1)k}`$ and $`D_N=\det(M_{i+j})_{0\le i,j<N}`$, we have
> ``` math
> \begin{equation}
> \label{eq:geometric-limit}
>  D_N\sim\mathcal M(q)^3q^{B_N}P^{2N}\prod_{k=0}^{N-1}a_k
>  \qquad(N\to\infty).
> \end{equation}
> ```*

The Lean declaration below states this result or one that implies it. geometric_universality assumes positivity, 0 < q < 1, the fixed-shift ratio limit and the displayed uniform polynomial shift bound. It proves summability and the determinant ratio tending to one. gramM is the displayed MacMahon product, qPochhammerInfinity is P, and the finite sum of j squared is N(N-1)(2N-1)/6. The paper restricts kappa to nonnegative values; the declaration also accepts real kappa. No support is attached to the broader long-record ratio-limit remark.

[`ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality.geometric_universality`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/GeometricUniversality.lean#L1324)

```lean
theorem geometric_universality (hq0 : 0 < q) (hq1 : q < 1)
    {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) {C κ : ℝ}
    (hlim : ∀ h : ℕ, Tendsto (fun k => a (k + h) / a k) atTop (𝓝 1))
    (hbd : ∀ k h : ℕ, a (k + h) / a k ≤ C * (1 + (h : ℝ)) ^ κ) :
    HasProd (fun d : ℕ => ((1 - q ^ (d + 1)) ^ (d + 1))⁻¹) (gramM q) ∧ 0 < gramM q ∧
    (∀ m : ℕ, Summable fun k => a k * q ^ ((m + 1) * k)) ∧
    Tendsto (fun N : ℕ => geomHankelDet q a N /
        (gramM q ^ 3 * q ^ (∑ j ∈ range N, j ^ 2) * qPochhammerInfinity q q ^ (2 * N) *
          ∏ k ∈ range N, a k))
      atTop (𝓝 1)
```

<a id="thm-geometric-moments-comparator"></a>

**Comparator:** not yet compared.

Polynomial shift-bound specialisation matched to the existing Lean declaration; no Comparator association is recorded.

<a id="prop-weight-factorisation"></a>

## Proposition 3.1 (the positive moment weights), page 5

> *For every $`k\ge0`$,
> ``` math
> a_k=P^4\frac{R_k^{(2)}R_k^{(3)}}{(q;q)_k}.
> ```
> At fixed $`0<q<1`$ these weights satisfy
> ``` math
> P^5c_k\le a_k\le P^{-1}c_k,
>  \qquad \frac{a_{k+h}}{a_k}\le P^{-6}(1+h)^3\quad(k,h\ge0).
> ```*

The Lean declaration below states this result or one that implies it. `rogers_factorisation_proposition` gives, for the coefficients $\gamma_k$ of $G_q$ at fixed $0<q<1$, $\gamma_k=R_k^{(2)}R_k^{(3)}/(q;q)_k$, $P^5c_k\le P^4\gamma_k\le P^{-1}c_k$ with $c_k=(k+1)^2(k+2)/2$, and $P^4\gamma_{k+h}/(P^4\gamma_k)\le P^{-6}(1+h)^3$; with $a_k=[w^k]P^4G_q(w)$ these are the printed clauses.

[`ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogers_factorisation_proposition`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RogersFactorisationAnalytic.lean#L1312)

```lean
theorem rogers_factorisation_proposition :
    (∀ k : ℕ,
      momentWeight k = rogersR 2 k * rogersR 3 k * (qfac k)⁻¹ ∧
      qfac k * momentWeight k = rogersR 2 k * rogersR 3 k ∧
      (∃ p : Polynomial ℕ,
        ((p.map (Nat.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) =
          rogersR 2 k * rogersR 3 k ∧
        p.natDegree = k ^ 2 / 4 + k ^ 2 / 3 ∧
        p.eval 1 = 6 ^ k) ∧
      (∃ g : Polynomial ℤ,
        qfac k * momentWeight k =
          ((g.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ))) ∧
    (∀ q : ℝ, 0 < q → q < 1 →
      (∀ w : ℝ, 0 ≤ w → w < 1 →
        HasSum (fun k => realRogersR 2 k q * realRogersR 3 k q / qPochhammerFinite q q k * w ^ k)
          (actualGeneratingFunction q w)) ∧
      ∀ γ : ℕ → ℝ, (∀ w : ℝ, 0 ≤ w → w < 1 →
          HasSum (fun k => γ k * w ^ k) (actualGeneratingFunction q w)) →
        (∀ k, γ k = realRogersR 2 k q * realRogersR 3 k q / qPochhammerFinite q q k) ∧
        (∀ k, HasSum (fun m => ((coeff m (momentWeight k) : ℚ) : ℝ) * q ^ m) (γ k)) ∧
        (∀ k, realRogersR 2 k q = (rogersPoly2 k).eval₂ (Int.castRingHom ℝ) q ∧
          realRogersR 3 k q = (rogersPoly3 k).eval₂ (Int.castRingHom ℝ) q ∧
          qPochhammerFinite q q k * γ k =
            (rogersPoly2 k * rogersPoly3 k).eval₂ (Int.castRingHom ℝ) q) ∧
        (∀ k, qPochhammerInfinity q q ^ 5 * cK k ≤ qPochhammerInfinity q q ^ 4 * γ k ∧
          qPochhammerInfinity q q ^ 4 * γ k ≤ (qPochhammerInfinity q q)⁻¹ * cK k) ∧
        (∀ k h : ℕ, qPochhammerInfinity q q ^ 4 * γ (k + h) / (qPochhammerInfinity q q ^ 4 * γ k)
          ≤ ((qPochhammerInfinity q q)⁻¹) ^ 6 * (1 + (h : ℝ)) ^ 3) ∧
        (∀ k, 0 < qPochhammerInfinity q q ^ 4 * γ k) ∧
        (∀ h : ℕ, Tendsto (fun k => qPochhammerInfinity q q ^ 4 * γ (k + h) /
          (qPochhammerInfinity q q ^ 4 * γ k)) atTop (𝓝 1)))
```

<a id="prop-weight-factorisation-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `rogers_factorisation_proposition`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_09/Challenge.lean#L102) (E1049_09, line 102), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_09/PaperStructuresAA.lean#L214) (PaperStructuresAA.lean, line 214), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_09.json) (E1049_09)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-zudilin-sharp-qorder"></a>

## Theorem 3.2 (the first nonzero term of the Hankel determinant), page 8

> *For every $`N\ge1`$,
> ``` math
> \operatorname{ord}_q V_N^*=\frac{N(N-1)(2N-1)}6,
> ```
> and the coefficient of the first nonzero monomial is
> ``` math
> [q^{N(N-1)(2N-1)/6}]V_N^*
>    =\frac{(N!)^2(N+1)!}{2^N}.
> ```*

The Lean declarations below together state this result or one that implies it. The Lean statements hold for every $N\ge0$, the case $N=0$ being the empty determinant $V_0^*=1$. The exponent $N(N-1)(2N-1)/6$ is computed in natural numbers, where the subtractions and the division by $6$ are exact for $N\ge1$.

1. [`ErdosProblems.Erdos1049.order_zudilinNormalizedHankelDet_all`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L173)

```lean
theorem order_zudilinNormalizedHankelDet_all (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞)
```

2. [`ErdosProblems.Erdos1049.coeff_zudilinNormalizedHankelDet_all_rat`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L199)

```lean
theorem coeff_zudilinNormalizedHankelDet_all_rat (N : ℕ) :
    ((PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (zudilinNormalizedHankelDet N) : ℤ) : ℚ) =
      (N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ) / (2 : ℚ) ^ N
```

<a id="res-zudilin-sharp-qorder-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `order_zudilinNormalizedHankelDet_all`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_04/Challenge.lean#L72) (E1049_04, line 72), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_04/PaperStatementsG.lean#L49) (PaperStatementsG.lean, line 49), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_04.json) (E1049_04)
- `coeff_zudilinNormalizedHankelDet_all_rat`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_03/Challenge.lean#L162) (E1049_03, line 162), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_03/AdelicHeightBridge.lean#L62) (AdelicHeightBridge.lean, line 62), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_03.json) (E1049_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-rational-base-threshold"></a>

## Theorem 4.1 (rational-base region for Zudilin’s forms), page 10

> *Let $`a>b\ge1`$ be coprime integers with
> ``` math
> \begin{gathered}
>  b^{\mu}<a,\qquad\text{equivalently}\qquad
>  \frac{\log b}{\log a}<\theta^*,\\
>  \theta^*=\frac{C_0}{C_1}=0.4056830213840605\ldots,\\
>  \mu=\frac{C_1}{C_0}=2.4649786835749750\ldots.
> \end{gathered}
> ```
> Then $`F(a/b)`$ is irrational.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour_short`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L440)

```lean
theorem printed_contour_short :
    (4056830213840605 : ℝ) / 10 ^ 16 < zudilinContour ∧
      zudilinContour < (4056830213840606 : ℝ) / 10 ^ 16
```

2. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_mu`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L461)

```lean
theorem printed_mu :
    (24649786835749750 : ℝ) / 10 ^ 16 < paperMu ∧
      paperMu < (24649786835749751 : ℝ) / 10 ^ 16
```

3. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinJ_enclosure`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L334)

```lean
theorem zudilinJ_enclosure :
    (77943184475009095899 : ℝ) / 10 ^ 18 ≤ zudilinJ ∧
      zudilinJ ≤ (77943184475009095946 : ℝ) / 10 ^ 18
```

4. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinC0_enclosure`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L383)

```lean
theorem zudilinC0_enclosure :
    (221300088165005025116 : ℝ) / 10 ^ 18 ≤ zudilinC0 ∧
      zudilinC0 ≤ (221300088165005025132 : ℝ) / 10 ^ 18
```

5. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_le_tailHigh`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L156)

```lean
theorem trigammaSeries_le_tailHigh {x : ℝ} (hx : 1 ≤ x) : trigammaSeries x ≤ tailHigh x
```

6. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow_le_trigammaSeries`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L181)

```lean
theorem tailLow_le_trigammaSeries {x : ℝ} (hx : 1 ≤ x) : tailLow x ≤ trigammaSeries x
```

7. [`ErdosProblems.Erdos1049.PaperCompleteR21.zudilin_rpow_lt_iff_contourRegion`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L96)

```lean
theorem zudilin_rpow_lt_iff_contourRegion (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    ((b : ℝ) ^ zudilinMu < (a : ℝ)) ↔ ZudilinContourRegion a b
```

8. [`ErdosProblems.Erdos1049.PaperCompleteR21.zudilinContour_eq_inv_mu`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L82)

```lean
theorem zudilinContour_eq_inv_mu : zudilinContour = 1 / zudilinMu
```

9. [`ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu_mul_zudilinContour`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L86)

```lean
theorem zudilinMu_mul_zudilinContour : zudilinMu * zudilinContour = 1
```

10. [`ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L109)

```lean
theorem rational_base_threshold (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (h : (b : ℝ) ^ zudilinMu < (a : ℝ)) :
    Irrational (paperLambert ((a : ℝ) / b))
```

11. [`ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold_log`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L116)

```lean
theorem rational_base_threshold_log (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b)
    (h : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    Irrational (paperLambert ((a : ℝ) / b))
```

<a id="res-rational-base-threshold-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `printed_contour_short`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_07/Challenge.lean#L59) (E1049_07, line 59), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_07/PaperStatementsA.lean#L54) (PaperStatementsA.lean, line 54), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_07.json) (E1049_07)
- `printed_mu`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_07/Challenge.lean#L64) (E1049_07, line 64), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_07/PaperStatementsA.lean#L62) (PaperStatementsA.lean, line 62), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_07.json) (E1049_07)
- `zudilinJ_enclosure`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_01/Challenge.lean#L117) (E1049_01, line 117), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L56) (PaperStatementsA.lean, line 56), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_01.json) (E1049_01)
- `zudilinC0_enclosure`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_01/Challenge.lean#L112) (E1049_01, line 112), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L52) (PaperStatementsA.lean, line 52), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_01.json) (E1049_01)
- `trigammaSeries_le_tailHigh`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_07/Challenge.lean#L72) (E1049_07, line 72), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_07/PaperStatementsA.lean#L68) (PaperStatementsA.lean, line 68), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_07.json) (E1049_07)
- `tailLow_le_trigammaSeries`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_07/Challenge.lean#L69) (E1049_07, line 69), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_07/PaperStatementsA.lean#L66) (PaperStatementsA.lean, line 66), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_07.json) (E1049_07)
- `zudilin_rpow_lt_iff_contourRegion`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_01/Challenge.lean#L158) (E1049_01, line 158), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L92) (PaperStatementsA.lean, line 92), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_01.json) (E1049_01)
- `zudilinContour_eq_inv_mu`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_07/Challenge.lean#L75) (E1049_07, line 75), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_07/PaperStatementsA.lean#L106) (PaperStatementsA.lean, line 106), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_07.json) (E1049_07)
- `zudilinMu_mul_zudilinContour`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_07/Challenge.lean#L78) (E1049_07, line 78), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_07/PaperStatementsA.lean#L108) (PaperStatementsA.lean, line 108), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_07.json) (E1049_07)
- `rational_base_threshold`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_01/Challenge.lean#L174) (E1049_01, line 174), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_01/PaperStatementsJ.lean#L21) (PaperStatementsJ.lean, line 21), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_01.json) (E1049_01)
- `rational_base_threshold_log`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_01/Challenge.lean#L179) (E1049_01, line 179), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_01/PaperStatementsJ.lean#L25) (PaperStatementsJ.lean, line 25), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_01.json) (E1049_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-thirtyone-four"></a>

## Corollary 4.2, page 13

> *$`F\bigl((31/4)^r\bigr)`$ is irrational for every integer $`r\ge1`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR17.thirtyone_four_powers`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L117)

```lean
theorem thirtyone_four_powers (r : ℕ) (hr : 0 < r) :
    Irrational (paperLambert (((31 : ℝ) / 4) ^ r))
```

<a id="res-thirtyone-four-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `thirtyone_four_powers`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_07/Challenge.lean#L88) (E1049_07, line 88), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_07/RationalBaseRegion.lean#L63) (RationalBaseRegion.lean, line 63), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_07.json) (E1049_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-rational-base-measure"></a>

## Corollary 4.3 (an irrationality measure uniform over powers), page 13

> *For coprime $`a>b\ge1`$ with $`\theta=\log b/\log a<\theta^*`$ and every integer $`r\ge1`$,
> ``` math
> \mu_{\rm irr}\!\left(F((a/b)^r)\right)
>  \le\frac{1-\theta}{\theta^*-\theta}.
> ```
> Here $`\mu_{\rm irr}(\xi)`$ is the supremum of the exponents $`\nu`$ for which $`|\xi-p/q|<q^{-\nu}`$ has infinitely many reduced rational solutions. In particular, $`\mu_{\rm irr}(F((31/4)^r))<301`$ for every $`r\ge1`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_measure_uniform`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L194)

```lean
theorem rational_base_measure_uniform (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (hr : 0 < r)
    (hθ : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      (1 - Real.log (b : ℝ) / Real.log (a : ℝ)) /
        (zudilinContour - Real.log (b : ℝ) / Real.log (a : ℝ))
```

2. [`ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_power_measure_lt_301`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L205)

```lean
theorem thirtyoneFour_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301
```

3. [`ErdosProblems.Erdos1049.PaperR17.rational_base_power_measure`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L167)

```lean
theorem rational_base_power_measure (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : 0 < r) (hregion : ZudilinContourRegion a b) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      rationalBaseMeasureBound a b
```

4. [`ErdosProblems.Erdos1049.PaperR17.thirtyone_four_power_measure_lt_301`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L176)

```lean
theorem thirtyone_four_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301
```

<a id="cor-rational-base-measure-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `rational_base_measure_uniform`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_01/Challenge.lean#L212) (E1049_01, line 212), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_01/PaperStatementsI.lean#L23) (PaperStatementsI.lean, line 23), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_01.json) (E1049_01)
- `thirtyoneFour_power_measure_lt_301`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_01/Challenge.lean#L220) (E1049_01, line 220), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_01/PaperStatementsI.lean#L31) (PaperStatementsI.lean, line 31), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_01.json) (E1049_01)
- `rational_base_power_measure`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_01/Challenge.lean#L233) (E1049_01, line 233), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_01/RationalBaseRegion.lean#L55) (RationalBaseRegion.lean, line 55), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_01.json) (E1049_01)
- `thirtyone_four_power_measure_lt_301`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_01/Challenge.lean#L239) (E1049_01, line 239), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_01/RationalBaseRegion.lean#L74) (RationalBaseRegion.lean, line 74), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_01.json) (E1049_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
