# Formal evidence: Integer Linear Forms for a\\Factorial Reciprocal Series

This record belongs to the paper [erdos-68-factorial-denominator-irrationality.pdf](../paper/68/erdos-68-factorial-denominator-irrationality.pdf). For every result it lists the Lean declarations that state it, and the recorded Comparator check where there is one. The paper's verification concordance uses this result mapping.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`436f55ebdafa`](https://github.com/wcook04/plectis-erdos/tree/436f55ebdafa67e4af0fff79f621c13f2ded12bf) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 2 results: 2 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 2 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below. Comparator checks separately declared statements, the axiom budget and kernel acceptance; it does not establish novelty, significance or peer review.

<a id="res-divisor-channel-coordinates"></a>

## Theorem 2.1 (an integer basis with prescribed weighted sums), page 3

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

[`ErdosProblems.Erdos68.PaperComplete.divisor_channel_coordinates`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteDivisorCoordinates.lean#L260)

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

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `divisor_channel_coordinates`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_05/Challenge.lean#L194) (E68_05, line 194), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_05/PaperStatementsA.lean#L63) (PaperStatementsA.lean, line 63), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_05.json) (E68_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-finite-channel-moment-certificate"></a>

## Theorem 3.1 (a finite formula for the gcd), page 5

> *Choose a prime $`\ell`$ with $`D/2<\ell\le D`$ and put $`H=D(2\ell-1)`$. Then
> ``` math
> g_D=\gcd(u_{D+1},\ldots,u_H),\qquad H<2D^2.
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos68.PaperComplete.finite_channel_moment_certificate`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteMomentHorizon.lean#L252)

```lean
theorem finite_channel_moment_certificate {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    let H := D * (2 * p - 1)
    0 < finiteScalarGcd D H ∧
      IsScalarTailGcd D (finiteScalarGcd D H) ∧ H < 2 * D ^ 2
```

2. [`ErdosProblems.Erdos68.PaperComplete.finite_channel_moment_certificate_eq`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos68/PaperCompleteMomentHorizon.lean#L260)

```lean
theorem finite_channel_moment_certificate_eq {D p G : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D)
    (hG : IsScalarTailGcd D G) :
    G = finiteScalarGcd D (D * (2 * p - 1))
```

<a id="res-finite-channel-moment-certificate-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `finite_channel_moment_certificate`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_05/Challenge.lean#L207) (E68_05, line 207), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_05/PaperStatementsA.lean#L75) (PaperStatementsA.lean, line 75), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_05.json) (E68_05)
- `finite_channel_moment_certificate_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E68_05/Challenge.lean#L214) (E68_05, line 214), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E68_05/PaperStatementsA.lean#L81) (PaperStatementsA.lean, line 81), [replay report](../evidence/comparator/replay-35935225572/receipt-E68_05.json) (E68_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
