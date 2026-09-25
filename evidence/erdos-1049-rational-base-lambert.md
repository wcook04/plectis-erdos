# Formal evidence: Zudilin's Forms at Rational Bases\\and the Exact Normalised Hankel Order

This record belongs to the paper [erdos-1049-rational-base-lambert.pdf](../paper/1049/erdos-1049-rational-base-lambert.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`be89e72217ec`](https://github.com/wcook04/plectis-erdos/tree/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 16 results: 16 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 16 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="res-rational-base-threshold"></a>

## Theorem 2.1 (rational-base region for Zudilin’s forms), page 3

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

1. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour_short`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L440)

```lean
theorem printed_contour_short :
    (4056830213840605 : ℝ) / 10 ^ 16 < zudilinContour ∧
      zudilinContour < (4056830213840606 : ℝ) / 10 ^ 16
```

2. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_mu`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L461)

```lean
theorem printed_mu :
    (24649786835749750 : ℝ) / 10 ^ 16 < paperMu ∧
      paperMu < (24649786835749751 : ℝ) / 10 ^ 16
```

3. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinJ_enclosure`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L334)

```lean
theorem zudilinJ_enclosure :
    (77943184475009095899 : ℝ) / 10 ^ 18 ≤ zudilinJ ∧
      zudilinJ ≤ (77943184475009095946 : ℝ) / 10 ^ 18
```

4. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinC0_enclosure`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L383)

```lean
theorem zudilinC0_enclosure :
    (221300088165005025116 : ℝ) / 10 ^ 18 ≤ zudilinC0 ∧
      zudilinC0 ≤ (221300088165005025132 : ℝ) / 10 ^ 18
```

5. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_le_tailHigh`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L156)

```lean
theorem trigammaSeries_le_tailHigh {x : ℝ} (hx : 1 ≤ x) : trigammaSeries x ≤ tailHigh x
```

6. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow_le_trigammaSeries`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L181)

```lean
theorem tailLow_le_trigammaSeries {x : ℝ} (hx : 1 ≤ x) : tailLow x ≤ trigammaSeries x
```

7. [`ErdosProblems.Erdos1049.PaperCompleteR21.zudilin_rpow_lt_iff_contourRegion`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L96)

```lean
theorem zudilin_rpow_lt_iff_contourRegion (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    ((b : ℝ) ^ zudilinMu < (a : ℝ)) ↔ ZudilinContourRegion a b
```

8. [`ErdosProblems.Erdos1049.PaperCompleteR21.zudilinContour_eq_inv_mu`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L82)

```lean
theorem zudilinContour_eq_inv_mu : zudilinContour = 1 / zudilinMu
```

9. [`ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu_mul_zudilinContour`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L86)

```lean
theorem zudilinMu_mul_zudilinContour : zudilinMu * zudilinContour = 1
```

10. [`ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L109)

```lean
theorem rational_base_threshold (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (h : (b : ℝ) ^ zudilinMu < (a : ℝ)) :
    Irrational (paperLambert ((a : ℝ) / b))
```

11. [`ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold_log`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L116)

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

## Corollary 2.2, page 6

> *$`F\bigl((31/4)^r\bigr)`$ is irrational for every integer $`r\ge1`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR17.thirtyone_four_powers`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L117)

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

## Corollary 2.3 (an irrationality measure uniform over powers), page 7

> *For coprime $`a>b\ge1`$ with $`\theta=\log b/\log a<\theta^*`$ and every integer $`r\ge1`$,
> ``` math
> \mu_{\rm irr}\!\left(F((a/b)^r)\right)
>  \le\frac{1-\theta}{\theta^*-\theta}.
> ```
> Here $`\mu_{\rm irr}(\xi)`$ is the supremum of the exponents $`\nu`$ for which $`|\xi-p/q|<q^{-\nu}`$ has infinitely many reduced rational solutions. In particular, $`\mu_{\rm irr}(F((31/4)^r))<301`$ for every $`r\ge1`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_measure_uniform`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L194)

```lean
theorem rational_base_measure_uniform (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (hr : 0 < r)
    (hθ : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      (1 - Real.log (b : ℝ) / Real.log (a : ℝ)) /
        (zudilinContour - Real.log (b : ℝ) / Real.log (a : ℝ))
```

2. [`ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_power_measure_lt_301`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L205)

```lean
theorem thirtyoneFour_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301
```

3. [`ErdosProblems.Erdos1049.PaperR17.rational_base_power_measure`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L167)

```lean
theorem rational_base_power_measure (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : 0 < r) (hregion : ZudilinContourRegion a b) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      rationalBaseMeasureBound a b
```

4. [`ErdosProblems.Erdos1049.PaperR17.thirtyone_four_power_measure_lt_301`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L176)

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

<a id="res-sevenhalves"></a>

## Theorem 2.4 (the $`7/2`$ height condition), page 8

> *The [integer power certificate](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L32) $`2^{18}<7^7`$ yields the [Archimedean height condition](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L83)
> ``` math
> \frac{\log 7}{\log(7/2)}
>  <
>  \left(\frac12+\frac1{\pi^2}\right)^{-1}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.sevenHalves_archimedean_height_condition`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L83)

```lean
theorem sevenHalves_archimedean_height_condition :
    Real.log 7 / Real.log ((7 : ℝ) / 2) <
      ((1 : ℝ) / 2 + 1 / Real.pi ^ 2)⁻¹
```

<a id="res-sevenhalves-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `sevenHalves_archimedean_height_condition`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_05/Challenge.lean#L187) (E1049_05, line 187), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_05/PaperStatementsB.lean#L58) (PaperStatementsB.lean, line 58), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_05.json) (E1049_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-archimedean-cap"></a>

## Theorem 2.5 (a degree restriction for estimates valid at every base), page 9

> *Let $`(U_n,V_n)`$ be pairs in $`\mathbb Z[X]^2`$ satisfying $`\Lambda_n(x)=U_n(x)F(x)-V_n(x)\ne0`$, $`\deg U_n,\deg V_n\le\delta n^2(1+o(1))`$, $`\log\max(H(U_n),H(V_n))\le h n^2(1+o(1))`$ with $`H`$ the $`\ell^1`$ coefficient norm, and $`\log|\Lambda_n(x)|=-\sigma n^2\log x\,(1+o(1))`$ for every real $`x>1`$, with $`\sigma,\delta>0`$ and $`h\ge0`$ independent of $`x`$. Then with $`d_n=\max(\deg U_n,\deg V_n)`$, the homogenised forms $`b^{d_n}\Lambda_n(a/b)`$ tend to zero whenever $`\log b/\log a<\sigma/(\sigma+\delta)`$, and $`\sigma/(\sigma+\delta)\le1/2`$.*

The Lean declaration below states this result or one that implies it. The Lean statement needs $\Lambda_n(x)\ne0$ only for all sufficiently large $n$ at each real $x>1$. Its conclusions are $\sigma/(\sigma+\delta)\le1/2$ and the decay of $b^{d_n}\Lambda_n(a/b)$ for integers $a>b\ge1$ with $\log b/\log a<\sigma/(\sigma+\delta)$; this covers every printed case, since $b\ge a\ge2$ gives $\log b/\log a\ge1$.

[`ErdosProblems.Erdos1049.PaperR9.short_note_archimedean_cap`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperShortCapR9.lean#L162)

```lean
theorem short_note_archimedean_cap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : CapHypotheses U V F σ δ h) :
    σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    ∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
      Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)
```

<a id="res-archimedean-cap-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `short_note_archimedean_cap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_07/Challenge.lean#L132) (E1049_07, line 132), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_07/PaperStructuresR.lean#L30) (PaperStructuresR.lean, line 30), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_07.json) (E1049_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-zudilin-sharp-qorder"></a>

## Theorem 3.1 (the first nonzero term of the Hankel determinant), page 10

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

1. [`ErdosProblems.Erdos1049.order_zudilinNormalizedHankelDet_all`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L173)

```lean
theorem order_zudilinNormalizedHankelDet_all (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞)
```

2. [`ErdosProblems.Erdos1049.coeff_zudilinNormalizedHankelDet_all_rat`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L199)

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

<a id="res-sharp-fixed-base"></a>

## Theorem 3.2 (the size of $`V_N^*`$ at a fixed base), page 11

> *Fix $`0<q<1`$ and write $`P=(q;q)_\infty`$, $`B_N=N(N-1)(2N-1)/6`$ and $`C_N=(N!)^2(N+1)!/2^N`$. There is a $`K(q)>0`$ with
> ``` math
> V_N^*(q)\sim K(q)\,C_Nq^{B_N}P^{2N}N^{-8F(1/q)}
>  \qquad(N\to\infty).
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base_exists`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperCompleteR21/SharpFixedBaseShort.lean#L53)

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

<a id="res-nocorridor"></a>

## Theorem 4.1 (failure of the stated clearing conditions at $`3/2`$), page 13

> *For all $`N\ge1`$ and $`K\ge1`$ and all natural $`Q,D`$, the tuple $`(3,2,N,K,Q,D)`$ does not satisfy the [clearing conditions above](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L155).*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.threeHalves_no_coordinatewiseCorridor`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L155)

```lean
theorem threeHalves_no_coordinatewiseCorridor
    {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    ¬ CoordinatewiseCorridor 3 2 N K Q digit
```

<a id="res-nocorridor-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `threeHalves_no_coordinatewiseCorridor`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_05/Challenge.lean#L217) (E1049_05, line 217), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_05/RationalBaseBarrier.lean#L37) (RationalBaseBarrier.lean, line 37), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_05.json) (E1049_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-tailrec"></a>

## Theorem 4.2 (recurrence for the scaled remainder), page 13

> *Let $`r,s,B,\xi\in\mathbb{Q}`$ with $`r\ne0`$, let $`c:\mathbb{N}\to\mathbb{Q}`$, and define $`U_N`$ as above. Then for every $`N`$ the [recurrence for the scaled remainder](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L187) is
> ``` math
> U_{N+1}=r\,U_N-B\,c(N+1)\,s^{\,N+1}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.rationalBaseClearedTailQ_succ`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L187)

```lean
theorem rationalBaseClearedTailQ_succ
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    rationalBaseClearedTailQ r s B F coeff (N + 1) =
      r * rationalBaseClearedTailQ r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1)
```

<a id="res-tailrec-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `rationalBaseClearedTailQ_succ`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_05/Challenge.lean#L210) (E1049_05, line 210), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_05/RationalBaseBarrier.lean#L19) (RationalBaseBarrier.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_05.json) (E1049_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-forcing"></a>

## Theorem 4.3 (the forcing term), page 13

> *Let $`s,B`$ be natural numbers and $`c:\mathbb{N}\to\mathbb{N}`$.*
> 
> 1.  *If $`s\ge2`$, $`B\ge1`$ and $`c(N+1)\ge1`$, then $`2^{\,N+1}\le B\,c(N+1)\,s^{\,N+1}`$.*
> 
> 2.  *If $`s=1`$, then $`B\,c(N+1)\,s^{\,N+1}=B\,c(N+1)`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.forcing_term`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L186)

```lean
theorem forcing_term (B : ℕ) (c : ℕ → ℕ) (N : ℕ) :
    (∀ s : ℕ, 2 ≤ s → 1 ≤ B → 1 ≤ c (N + 1) →
      2 ^ (N + 1) ≤ rationalBaseForcingNat s B c N) ∧
      rationalBaseForcingNat 1 B c N = B * c (N + 1)
```

<a id="res-forcing-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `forcing_term`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_05/Challenge.lean#L163) (E1049_05, line 163), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_05/PaperStatementsK.lean#L27) (PaperStatementsK.lean, line 27), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_05.json) (E1049_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-bottomjet"></a>

## Lemma 4.4 (a residue and divisibility by $`3^R`$), page 14

> *Vanishing of the [residue modulo $`3^R`$](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L191) is exactly divisibility by the corresponding power of three: $`J_{3,R}(P)=0`$ if and only if $`3^R\mid H_W(P)`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.bottomJet3_eq_zero_iff_dvd`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L191)

```lean
theorem bottomJet3_eq_zero_iff_dvd (R W : ℕ) (P : Polynomial ℤ) :
    bottomJet3 R W P = 0 ↔ ((3 ^ R : ℕ) : ℤ) ∣ homEvalThreeTwo W P
```

<a id="res-bottomjet-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `bottomJet3_eq_zero_iff_dvd`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_07/Challenge.lean#L151) (E1049_07, line 151), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_07/PaperStatementsF.lean#L19) (PaperStatementsF.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_07.json) (E1049_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-jetkernel"></a>

## Theorem 4.5 (equal residues for two subset sums), page 14

> *Fix a truncation index $`W`$ and depths $`R,S`$, and let $`(U_j,V_j)_{j<M}`$ be any $`M`$ pairs of integral polynomials. Represent each subset of $`\{0,\dots,M-1\}`$ by its indicator vector in $`\{0,1\}^M`$. If the $`2^M`$ subsets outnumber the possible residue vectors in
> ``` math
> (\mathbb{Z}/3^R\mathbb{Z})^2\times(\mathbb{Z}/2^S\mathbb{Z})^2,
> ```
> then two distinct subsets have the same residue vector. Subtracting their indicator vectors gives a nonzero coefficient vector in $`\{-1,0,1\}^M`$ cancelling all four residues. The target has exact cardinality
> ``` math
> (3^R)^2(2^S)^2.
> ```
> In particular, if $`R>0`$ and $`4R+2S\le M`$, such a collision exists.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.fourJet_paper_statement`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L248)

```lean
theorem fourJet_paper_statement {M R S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ) :
    Fintype.card (FourJetSignature R S) = (3 ^ R) ^ 2 * (2 ^ S) ^ 2 ∧
    (Fintype.card (FourJetSignature R S) < 2 ^ M → PaperJetWitness R S W forms) ∧
    (0 < R → 4 * R + 2 * S ≤ M → PaperJetWitness R S W forms)
```

<a id="res-jetkernel-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `fourJet_paper_statement`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_05/Challenge.lean#L97) (E1049_05, line 97), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_05/PaperStatementsM.lean#L37) (PaperStatementsM.lean, line 37), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_05.json) (E1049_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-plucker-collapse"></a>

## Theorem 4.6 (vanishing minors and a residue count), page 14

> *Let $`R_0`$ be a commutative ring and let $`w_n=(A_n,B_n)\in R_0^2`$. Suppose that every row is unimodular ($`u_n A_n+v_n B_n=1`$ for some $`u_n,v_n`$) and every adjacent minor vanishes:
> ``` math
> A_nB_{n+1}-B_nA_{n+1}=0\qquad(n\ge0).
> ```
> Then every pairwise minor $`A_iB_j-B_iA_j`$ vanishes. In particular, take $`R_0=\mathbb{Z}/(2^S3^R)\mathbb{Z}`$ with $`R>0`$. If $`S+2R\le k`$, there are two distinct binary selectors $`s,t\in\{0,1\}^{k}`$ such that
> ``` math
> \sum_{i<k}s_iw_i=\sum_{i<k}t_iw_i.
> ```
> Thus $`S+2R`$ rows suffice, in place of the sufficient bound $`2S+4R`$ from the ambient two-coordinate count.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.plucker_paper_statement`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L269)

```lean
theorem plucker_paper_statement :
    (∀ (R₀ : Type u) [CommRing R₀] (w : ℕ → R₀ × R₀),
      (∀ n, IsCoprime (w n).1 (w n).2) →
      (∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) →
      ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0) ∧
    (∀ (R S k : ℕ)
      (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R)),
      (∀ n, IsCoprime (w n).1 (w n).2) →
      (∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) →
      0 < R → S + 2 * R ≤ k →
      ∃ s t : Fin k → Bool, s ≠ t ∧
        (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0)
```

<a id="res-plucker-collapse-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `plucker_paper_statement`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_05/Challenge.lean#L141) (E1049_05, line 141), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_05/PaperStatementsT.lean#L17) (PaperStatementsT.lean, line 17), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_05.json) (E1049_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-pade"></a>

## Proposition 4.7 (exponent model: summand bound and exact gap), page 15

> *Let $`\widetilde{E}_n=3n^{2}-n`$ and put
> ``` math
> \widetilde{P}(n,k)=2\bigl(k(n-k)+nk\bigr)+k(k-1),
> ```
> ``` math
> \widetilde{Q}(n,m)=2(n^{2}-n)+j^{2}+2jm+j-m^{2}+3m,
>  \qquad j=n-m-1 .
> ```
> Then, for integers $`n,k,m`$:*
> 
> 1.  *if $`0\le k\le n`$, the [summand exponent bound](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L30) is $`\widetilde{P}(n,k)\le\widetilde{E}_n`$, and the gap factors as $`\widetilde{E}_n-\widetilde{P}(n,k)=(n-k)(3n-k-1)`$;*
> 
> 2.  *the [exact gap identity](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L52) is $`\widetilde{E}_n-\widetilde{Q}(n,m)=2\bigl(n+m(m-1)\bigr)`$.*

The Lean declaration below states this result or one that implies it. The Lean statement proves $\widetilde E_n-\widetilde P(n,k)=(n-k)(3n-k-1)$ for all integers $n,k$, without $0\le k\le n$, and adds $\widetilde Q(n,m)\le\widetilde E_n$ for $n\ge0$ and $m\ge1$; the printed items are its first three clauses.

[`ErdosProblems.Erdos1049.PaperR7.pade_summand_bound_and_gap`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L201)

```lean
theorem pade_summand_bound_and_gap (n k m : ℤ) :
    (0 ≤ k → k ≤ n →
      rationalPadePSummandDenExpTwice n k ≤ rationalPadeDenExpTwice n) ∧
    rationalPadeDenExpTwice n - rationalPadePSummandDenExpTwice n k =
      (n - k) * (3 * n - k - 1) ∧
    rationalPadeDenExpTwice n - rationalPadeQMaxDenExpTwice n m =
      2 * (n + m * (m - 1)) ∧
    (0 ≤ n → 1 ≤ m →
      rationalPadeQMaxDenExpTwice n m ≤ rationalPadeDenExpTwice n)
```

<a id="res-pade-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `pade_summand_bound_and_gap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_05/Challenge.lean#L236) (E1049_05, line 236), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_05/PaperStatementsN.lean#L52) (PaperStatementsN.lean, line 52), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_05.json) (E1049_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-content"></a>

## Proposition 4.8 (rescaling two integer rows), page 15

> *Multiplying two integer rows by $`c_1`$ and $`c_2`$ multiplies their [determinant](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L124) by $`c_1c_2`$. The [integer identity](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L94) and its [absolute-value form](https://github.com/wcook04/plectis-erdos/blob/7380b7871687b6bcc41ca0143c61f232e8af6500/lean/ErdosProblems/Erdos1049/RationalPadeArithmetic.lean#L104) show that the added divisibility is accompanied by exactly the same factor in the real absolute value.*

The Lean declaration below states this result or one that implies it. The Lean statement adds that multiplying a row $(U,V)$ by $c_1$ multiplies its error $US-V$ by $c_1$ for every real $S$; its other clauses are the printed determinant identity, the absolute-value form with factor $|c_1||c_2|$ and divisibility by $c_1c_2$.

[`ErdosProblems.Erdos1049.PaperR7.integer_scalar_content`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L59)

```lean
theorem integer_scalar_content (S : ℝ) (cn cm Un Vn Um Vm : ℤ) :
    rationalPadeError S (cn * Un) (cn * Vn) =
      (cn : ℝ) * rationalPadeError S Un Vn ∧
    rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm) =
      cn * cm * rationalPadeExteriorDet Un Vn Um Vm ∧
    |rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm)| =
      |cn| * |cm| * |rationalPadeExteriorDet Un Vn Um Vm| ∧
    cn * cm ∣ rationalPadeExteriorDet (cn * Un) (cn * Vn) (cm * Um) (cm * Vm)
```

<a id="res-content-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `integer_scalar_content`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_04/Challenge.lean#L242) (E1049_04, line 242), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_04/PaperStatementsN.lean#L47) (PaperStatementsN.lean, line 47), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_04.json) (E1049_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-boundedfibre"></a>

## Theorem 4.9 (equal residues with close, distinct values), page 16

> *Let $`A,B,J`$ be finite sets and let $`f:A\to B`$, $`g:A\to\mathbb R`$ and $`\iota:A\to J`$. Suppose that each simultaneous fibre of $`(f,g)`$ has at most $`k`$ elements and that, for some $`\delta>0`$,
> ``` math
> \iota(x)=\iota(y)\quad\Longrightarrow\quad |g(x)-g(y)|<\delta.
> ```
> If $`|B||J|k<|A|`$, then some distinct $`x,y\in A`$ satisfy
> ``` math
> f(x)=f(y),\qquad 0<|g(x)-g(y)|<\delta.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.exists_small_real_escape_of_conditional_multiplicity`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos1049/QuantitativeSelectorEscape.lean#L79)

```lean
theorem exists_small_real_escape_of_conditional_multiplicity
    {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (f : α → β) (g : α → ℝ) (bin : α → ι) (k : ℕ) (δ : ℝ)
    (hg : ∀ x : α,
      (Finset.univ.filter fun y => f y = f x ∧ g y = g x).card ≤ k)
    (hdiam : ∀ x y : α, bin x = bin y → |g x - g y| < δ)
    (hcard : (Fintype.card β * Fintype.card ι) * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧
      0 < |g x - g y| ∧ |g x - g y| < δ
```

<a id="res-boundedfibre-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exists_small_real_escape_of_conditional_multiplicity`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1049_07/Challenge.lean#L160) (E1049_07, line 160), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1049_07/PaperStructuresP.lean#L14) (PaperStructuresP.lean, line 14), [replay report](../evidence/comparator/replay-35935225572/receipt-E1049_07.json) (E1049_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
