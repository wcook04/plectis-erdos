# Formal evidence: Two Incomparable Denominator Exclusions\\for $\sum_{n\ge2}(n!-1)^{-1}$

This record belongs to the paper [erdos-68-factorial-denominator-irrationality.pdf](../paper/68/erdos-68-factorial-denominator-irrationality.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`e6c2d8f77ac2`](https://github.com/wcook04/plectis-erdos/tree/e6c2d8f77ac24753c5216a49f4daf7f7388b309f) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35882032091](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35882032091) at corpus commit [`a2faa350b45a`](https://github.com/wcook04/plectis-erdos-lean/tree/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3) (tag `paper-evidence-2026-09-23`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 6 results: 6 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 6 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="res-carry-characterization"></a>

## Theorem (exact carry characterisation)

> *<span id="res:strict-successor-complete-characterization" label="res:strict-successor-complete-characterization"></span> The following conditions are equivalent:
> ``` math
> S\notin\mathbb Q,\qquad
> (\forall B)(\exists m>B)\ b_m\ne1,\qquad
> (\forall B)(\exists m>B)\ m\nmid Z_m.
> ```
> In particular, [cofinal non-unit carries imply irrationality](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos68/FactorialZeroPlateau.lean#L953); equivalently, the original problem is the [criterion using the next integer](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos68/FactorialZeroPlateau.lean#L1090).*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.carry_characterisation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L45)

```lean
theorem carry_characterisation :
    (Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)
```

<a id="res-carry-characterization-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `carry_characterisation` | [E68_05/Challenge.lean, line 177](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E68_05/Challenge.lean#L177) | [PaperStatementsA.lean, line 38](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E68_05/PaperStatementsA.lean#L38) | [E68_05](../evidence/comparator/replay-35882032091/receipt-E68_05.json) |

Challenge for `carry_characterisation`:

```lean
theorem carry_characterisation :
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m) := by sorry
```

<a id="res-divisor-channel-coordinates"></a>

## Theorem (an integer basis with prescribed weighted sums)

> *Set
> ``` math
> T_n=ne_{n-1}-e_n,\qquad
> U_n=T_n-\sum_{\substack{d\mid n\\2\le d<n}}W_{d,n}U_d
> \quad(n\ge2).
> ```
> Then
> ``` math
> M(U_n)=0,\qquad V_d(U_n)=(d!-1)\mathbf1_{d=n}.
> ```
> The vectors $`e_1,U_2,U_3,\ldots`$ form an integral basis. Every finite vector has the unique finite expansion
> ``` math
> \begin{equation}
> \lambda=M(\lambda)e_1+
> \sum_{d\ge2}\frac{V_d(\lambda)-M(\lambda)}{d!-1}U_d.
> \label{eq:channel-basis-expansion}
> \end{equation}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.divisor_channel_coordinates`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos68/PaperCompleteDivisorCoordinates.lean#L260)

```lean
theorem divisor_channel_coordinates :
    (∀ n : ℕ, 2 ≤ n → factorialMoment (isolatedChannelUnit n) = 0) ∧
    (∀ n d : ℕ, 2 ≤ n → 2 ≤ d →
      channelNumerator (isolatedChannelUnit n) d =
        if d = n then (n.factorial : ℤ) - 1 else 0) ∧
    (∀ f : ℕ →₀ ℤ, f 0 = 0 →
      ∃! a : ℕ →₀ ℤ, channelSynthesis a = f) ∧
    (∀ a f : ℕ →₀ ℤ, channelSynthesis a = f →
      a 0 = factorialMoment f ∧
      ∀ d : ℕ, 2 ≤ d → a (d - 1) =
        (channelNumerator f d - factorialMoment f) / ((d.factorial : ℤ) - 1))
```

<a id="res-divisor-channel-coordinates-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `divisor_channel_coordinates` | [E68_05/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E68_05/Challenge.lean#L194) | [PaperStatementsA.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E68_05/PaperStatementsA.lean#L63) | [E68_05](../evidence/comparator/replay-35882032091/receipt-E68_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-finite-channel-moment-certificate"></a>

## Theorem (a finite formula for the gcd)

> *Choose a prime $`\ell`$ with $`D/2<\ell\le D`$ and put $`H=D(2\ell-1)`$. Then
> ``` math
> g_D=\gcd(u_{D+1},\ldots,u_H),\qquad H<2D^2.
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos68.PaperComplete.finite_channel_moment_certificate`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos68/PaperCompleteMomentHorizon.lean#L252)

```lean
theorem finite_channel_moment_certificate {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    let H
```

2. [`ErdosProblems.Erdos68.PaperComplete.finite_channel_moment_certificate_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos68/PaperCompleteMomentHorizon.lean#L260)

```lean
theorem finite_channel_moment_certificate_eq {D p G : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hG : IsScalarTailGcd D G) :
    G = finiteScalarGcd D (D * (2 * p - 1))
```

<a id="res-finite-channel-moment-certificate-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `finite_channel_moment_certificate` | [E68_05/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E68_05/Challenge.lean#L207) | [PaperStatementsA.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E68_05/PaperStatementsA.lean#L75) | [E68_05](../evidence/comparator/replay-35882032091/receipt-E68_05.json) |
| `finite_channel_moment_certificate_eq` | [E68_05/Challenge.lean, line 214](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E68_05/Challenge.lean#L214) | [PaperStatementsA.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E68_05/PaperStatementsA.lean#L81) | [E68_05](../evidence/comparator/replay-35882032091/receipt-E68_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-bandbreakpoint"></a>

## Theorem (constant values of the floor in the weights)

> *Let $`\lambda`$ be a finitely supported integer vector, let $`d\ge2`$ and $`k\ge0`$ be integers, and suppose each index $`n`$ in its support satisfies $`kd\le n<(k+1)d`$. Then
> ``` math
> M(\lambda)=(d!)^k V_d(\lambda).
> ```
> In particular, support in $`[d,2d)`$ and $`V_d(\lambda)=0`$ force $`M(\lambda)=0`$. If all supported indices are at least $`d`$, $`V_d(\lambda)=0`$ and $`M(\lambda)\ne0`$, some supported index is at least $`2d`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos68.PaperComplete.supported_quotient_band`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos68/PaperCompleteSupportedBands.lean#L24)

```lean
theorem supported_quotient_band (f : ℕ →₀ ℤ) (d k : ℕ)
    (hlo : ∀ n ∈ f.support, k * d ≤ n)
    (hhi : ∀ n ∈ f.support, n < (k + 1) * d) :
    factorialMoment f = (d.factorial : ℤ) ^ k * channelNumerator f d
```

2. [`ErdosProblems.Erdos68.PaperComplete.supported_first_band_cancellation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos68/PaperCompleteSupportedBands.lean#L42)

```lean
theorem supported_first_band_cancellation (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hhi : ∀ n ∈ f.support, n < 2 * d)
    (hz : channelNumerator f d = 0) : factorialMoment f = 0
```

3. [`ErdosProblems.Erdos68.PaperComplete.supported_breakpoint_escape`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos68/PaperCompleteSupportedBands.lean#L51)

```lean
theorem supported_breakpoint_escape (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hz : channelNumerator f d = 0) (hm : factorialMoment f ≠ 0) :
    ∃ n ∈ f.support, 2 * d ≤ n
```

<a id="res-bandbreakpoint-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `supported_quotient_band` | [E68_02/Challenge.lean, line 79](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E68_02/Challenge.lean#L79) | [PaperStatementsC.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E68_02/PaperStatementsC.lean#L34) | [E68_02](../evidence/comparator/replay-35882032091/receipt-E68_02.json) |
| `supported_first_band_cancellation` | [E68_02/Challenge.lean, line 69](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E68_02/Challenge.lean#L69) | [PaperStatementsC.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E68_02/PaperStatementsC.lean#L26) | [E68_02](../evidence/comparator/replay-35882032091/receipt-E68_02.json) |
| `supported_breakpoint_escape` | [E68_02/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E68_02/Challenge.lean#L63) | [PaperStatementsC.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E68_02/PaperStatementsC.lean#L21) | [E68_02](../evidence/comparator/replay-35882032091/receipt-E68_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-global-complementary-criterion"></a>

## Proposition (a sufficient tail inequality)

> *If arbitrarily large natural parameters $`p\ge3`$ satisfy
> ``` math
> \begin{equation}
> R_p>1,\qquad
> (2p+1)L_p^{\rm blk}<2p^2(2p-1)!\rho_p,
> \label{eq:global-complementary-target}
> \end{equation}
> ```
> then $`S`$ is irrational.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.global_complementary_criterion_nat`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L154)

```lean
theorem global_complementary_criterion_nat
    (hcert : ∀ B : ℕ, ∃ p : ℕ,
      3 ≤ p ∧ B < p ∧ 1 < factorialBlockPrivateModulus p ∧
      factorialBlockBudget p * factorialBlockEndpointLcm p <
        factorialBlockScale p * complementaryProjectedResidue
          (factorialBlockTailNumerator p) (factorialBlockPrivateModulus p)) :
    Irrational _root_.Erdos68.factorialGapSeries
```

<a id="res-global-complementary-criterion-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `global_complementary_criterion_nat` | [E68_05/Challenge.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E68_05/Challenge.lean#L220) | [PaperStatementsA.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E68_05/PaperStatementsA.lean#L86) | [E68_05](../evidence/comparator/replay-35882032091/receipt-E68_05.json) |

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

<a id="res-companion-orbit-rationality-boundary"></a>

## Theorem (rationality and factorial residues)

> *The following statements are equivalent:*
> 
> 1.  *$`S\in\mathbb Q`$;*
> 
> 2.  *$`(\lfloor m!C\rfloor+2)\bmod m=0`$ for every sufficiently large $`m`$.*
> 
> *Consequently,
> ``` math
> \begin{equation}
>  S\notin\mathbb Q
>  \quad\Longleftrightarrow\quad
>  (\forall B)(\exists m>B)\;
>    (\lfloor m!C\rfloor+2)\bmod m\ne0 .
>  \label{eq:companion-cofinal}
> \end{equation}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos68.PaperComplete.companion_orbit_boundary`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos68/PaperCompleteExisting.lean#L27)

```lean
theorem companion_orbit_boundary :
    (¬ Irrational _root_.Erdos68.factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0) ∧
    (Irrational _root_.Erdos68.factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        (facFloor companionConstant m + 2) % (m : ℤ) ≠ 0)
```

<a id="res-companion-orbit-rationality-boundary-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `companion_orbit_boundary` | [E68_05/Challenge.lean, line 185](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E68_05/Challenge.lean#L185) | [PaperStatementsA.lean, line 55](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E68_05/PaperStatementsA.lean#L55) | [E68_05](../evidence/comparator/replay-35882032091/receipt-E68_05.json) |

Challenge for `companion_orbit_boundary`:

```lean
theorem companion_orbit_boundary :
    (¬ Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (facFloor companionConstant m + 2) % (m : ℤ) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        (facFloor companionConstant m + 2) % (m : ℤ) ≠ 0) := by sorry
```
