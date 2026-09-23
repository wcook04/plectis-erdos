# Formal evidence: Zudilin's Forms at Rational Bases:\\Proofs and Research Record

This record belongs to the paper [erdos1049-rational-base-lambert-reasoning-surface.pdf](../paper/1049/erdos1049-rational-base-lambert-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`e6c2d8f77ac2`](https://github.com/wcook04/plectis-erdos/tree/e6c2d8f77ac24753c5216a49f4daf7f7388b309f) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35882032091](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35882032091) at corpus commit [`a2faa350b45a`](https://github.com/wcook04/plectis-erdos-lean/tree/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3) (tag `paper-evidence-2026-09-23`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 35 results: 35 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 30 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="long1049-res-omega-indicator"></a>

## Lemma (the weight is an indicator)

> *On $`[0,1)`$ the function $`\omega`$ takes only the values $`0`$ and $`1`$, and $`\omega=1`$ exactly on the union of the thirteen half-open intervals listed above.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.omega_indicator`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperOmegaIndicatorR7.lean#L1297)

```lean
theorem omega_indicator (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (omegaWeight x = 0 ∨ omegaWeight x = 1) ∧
      (omegaWeight x = 1 ↔ InOmegaSupport x)
```

<a id="long1049-res-omega-indicator-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `omega_indicator` | [E1049_01/Challenge.lean, line 162](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L162) | [PaperStatementsA.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L95) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-region"></a>

## Theorem (rational-base region)

> *Let $`a>b\ge1`$ be coprime integers with
> ``` math
> b^{\mu}<a,
>  \qquad\text{equivalently}\qquad
>  \frac{\log b}{\log a}<\theta^{*}=0.40568302138406054\ldots
> ```
> Then $`F(a/b)=\sum_{m\ge1}(( a/b)^{m}-1)^{-1}`$ is irrational.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L418)

```lean
theorem printed_contour :
    (40568302138406054 : ℝ) / 10 ^ 17 < zudilinContour ∧
      zudilinContour < (40568302138406055 : ℝ) / 10 ^ 17
```

2. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.contour_enclosure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L487)

```lean
theorem contour_enclosure :
    (40568302138406054100 : ℝ) / 10 ^ 20 ≤ zudilinContour ∧
      zudilinContour ≤ (40568302138406054104 : ℝ) / 10 ^ 20
```

3. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinJ_enclosure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L334)

```lean
theorem zudilinJ_enclosure :
    (77943184475009095899 : ℝ) / 10 ^ 18 ≤ zudilinJ ∧
      zudilinJ ≤ (77943184475009095946 : ℝ) / 10 ^ 18
```

4. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.zudilinC0_enclosure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L383)

```lean
theorem zudilinC0_enclosure :
    (221300088165005025116 : ℝ) / 10 ^ 18 ≤ zudilinC0 ∧
      zudilinC0 ≤ (221300088165005025132 : ℝ) / 10 ^ 18
```

5. [`ErdosProblems.Erdos1049.PaperCompleteR21.zudilin_rpow_lt_iff_contourRegion`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L96)

```lean
theorem zudilin_rpow_lt_iff_contourRegion (a b : ℕ) (hb : 0 < b) (hab : b < a) :
    ((b : ℝ) ^ zudilinMu < (a : ℝ)) ↔ ZudilinContourRegion a b
```

6. [`ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L109)

```lean
theorem rational_base_threshold (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (h : (b : ℝ) ^ zudilinMu < (a : ℝ)) :
    Irrational (paperLambert ((a : ℝ) / b))
```

7. [`ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_threshold_log`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L116)

```lean
theorem rational_base_threshold_log (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b)
    (h : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    Irrational (paperLambert ((a : ℝ) / b))
```

<a id="long1049-res-region-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `printed_contour` | [E1049_01/Challenge.lean, line 102](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L102) | [PaperStatementsA.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L32) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `contour_enclosure` | [E1049_01/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L94) | [PaperStatementsA.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L26) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `zudilinJ_enclosure` | [E1049_01/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L117) | [PaperStatementsA.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L56) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `zudilinC0_enclosure` | [E1049_01/Challenge.lean, line 112](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L112) | [PaperStatementsA.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L52) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `zudilin_rpow_lt_iff_contourRegion` | [E1049_01/Challenge.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L158) | [PaperStatementsA.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L92) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `rational_base_threshold` | [E1049_01/Challenge.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L174) | [PaperStatementsJ.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsJ.lean#L21) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `rational_base_threshold_log` | [E1049_01/Challenge.lean, line 179](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L179) | [PaperStatementsJ.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsJ.lean#L25) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-31over4"></a>

## Theorem (the base $`31/4`$ outside the Bundschuh–Väänänen region)

> *$`F(31/4)`$ is irrational, and so is $`F\bigl((31/4)^{r}\bigr)`$ for every integer $`r\ge1`$. Here
> ``` math
> \frac{\log4}{\log31}=0.4036981731641997\ldots<\frac{81}{200}<\theta^{*},
> ```
> while
> ``` math
> 4^{\mu}=30.483515\ldots<31<4^{\mu_{\mathrm{BV}}}=32.369642\ldots
> ```
> with $`\mu_{\mathrm{BV}}=2\pi^{2}/(\pi^{2}-2)=2.508284761994\ldots`$, so $`31/4`$ lies outside the region $`\log b/\log a<1/2-1/\pi^{2}=0.3986788163576622\ldots`$ of \[bv1994, Thm. 2, p. 177\] and inside the region of Theorem <a href="#long1049:res:region" data-reference-type="ref" data-reference="long1049:res:region">2</a>.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_log_ratio`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedLogConstants.lean#L118)

```lean
theorem printed_log_ratio :
    (4036981731641997 : ℝ) / 10 ^ 16 < Real.log 4 / Real.log 31 ∧
      Real.log 4 / Real.log 31 < (4036981731641998 : ℝ) / 10 ^ 16
```

2. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_bv_cutoff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedLogConstants.lean#L195)

```lean
theorem printed_bv_cutoff :
    (3986788163576622 : ℝ) / 10 ^ 16 < 1 / 2 - 1 / Real.pi ^ 2 ∧
      1 / 2 - 1 / Real.pi ^ 2 < (3986788163576623 : ℝ) / 10 ^ 16
```

3. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_bvMu`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedLogConstants.lean#L218)

```lean
theorem printed_bvMu :
    (2508284761994 : ℝ) / 10 ^ 12 < paperBvMu ∧
      paperBvMu < (2508284761995 : ℝ) / 10 ^ 12
```

4. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.printed_four_rpow_bvMu`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedLogConstants.lean#L308)

```lean
theorem printed_four_rpow_bvMu :
    (32369642 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperBvMu ∧
      (4 : ℝ) ^ paperBvMu < (32369643 : ℝ) / 10 ^ 6
```

5. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedLogs.paperBvMu_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedLogConstants.lean#L212)

```lean
theorem paperBvMu_eq : paperBvMu = 1 / (1 / 2 - 1 / Real.pi ^ 2)
```

6. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_four_rpow_mu`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L625)

```lean
theorem printed_four_rpow_mu :
    (30483515 : ℝ) / 10 ^ 6 < (4 : ℝ) ^ paperMu ∧
      (4 : ℝ) ^ paperMu < (30483516 : ℝ) / 10 ^ 6
```

7. [`ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.four_rpow_mu_lt_thirtyOne`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/PrintedContourConstants.lean#L658)

```lean
theorem four_rpow_mu_lt_thirtyOne : (4 : ℝ) ^ paperMu < 31
```

8. [`ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L125)

```lean
theorem thirtyoneFour_irrational : Irrational (paperLambert ((31 : ℝ) / 4))
```

9. [`ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_pow_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L129)

```lean
theorem thirtyoneFour_pow_irrational (r : ℕ) (hr : 0 < r) :
    Irrational (paperLambert (((31 : ℝ) / 4) ^ r))
```

10. [`ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_ratio_chain`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L134)

```lean
theorem thirtyoneFour_ratio_chain :
    1 / 2 - 1 / Real.pi ^ 2 < Real.log 4 / Real.log 31 ∧
      Real.log 4 / Real.log 31 < (81 : ℝ) / 200 ∧
      (81 : ℝ) / 200 < zudilinContour
```

11. [`ErdosProblems.Erdos1049.PaperCompleteR21.inv_bvMu_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L153)

```lean
theorem inv_bvMu_eq : 1 / bvMu = 1 / 2 - 1 / Real.pi ^ 2
```

12. [`ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_between_rpow`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L169)

```lean
theorem thirtyoneFour_between_rpow :
    (4 : ℝ) ^ zudilinMu < 31 ∧ (31 : ℝ) < (4 : ℝ) ^ bvMu
```

13. [`ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_outside_bv_inside_contour`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L182)

```lean
theorem thirtyoneFour_outside_bv_inside_contour :
    ¬ BundschuhVaananenHeightRegion 31 4 ∧ ZudilinContourRegion 31 4
```

<a id="long1049-res-31over4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `printed_log_ratio` | [E1049_01/Challenge.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L140) | [PaperStatementsA.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L74) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `printed_bv_cutoff` | [E1049_01/Challenge.lean, line 130](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L130) | [PaperStatementsA.lean, line 66](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L66) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `printed_bvMu` | [E1049_01/Challenge.lean, line 125](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L125) | [PaperStatementsA.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L62) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `printed_four_rpow_bvMu` | [E1049_01/Challenge.lean, line 135](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L135) | [PaperStatementsA.lean, line 70](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L70) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `paperBvMu_eq` | [E1049_01/Challenge.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L122) | [PaperStatementsA.lean, line 60](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L60) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `printed_four_rpow_mu` | [E1049_01/Challenge.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L107) | [PaperStatementsA.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L40) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `four_rpow_mu_lt_thirtyOne` | [E1049_01/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L99) | [PaperStatementsA.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L30) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `thirtyoneFour_irrational` | [E1049_01/Challenge.lean, line 185](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L185) | [PaperStatementsJ.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsJ.lean#L30) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `thirtyoneFour_pow_irrational` | [E1049_01/Challenge.lean, line 188](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L188) | [PaperStatementsJ.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsJ.lean#L32) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `thirtyoneFour_ratio_chain` | [E1049_01/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L152) | [PaperStatementsA.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L83) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `inv_bvMu_eq` | [E1049_01/Challenge.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L145) | [PaperStatementsA.lean, line 78](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L78) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `thirtyoneFour_between_rpow` | [E1049_01/Challenge.lean, line 148](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L148) | [PaperStatementsA.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsA.lean#L80) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `thirtyoneFour_outside_bv_inside_contour` | [E1049_01/Challenge.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L200) | [PaperStatementsG.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsG.lean#L45) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-cor-rational-base-measure"></a>

## Corollary (an irrationality measure uniform over powers)

> *For coprime $`a>b\ge1`$ with $`\theta=\log b/\log a<\theta^*`$ and every integer $`r\ge1`$,
> ``` math
> \mu_{\rm irr}\!\left(F((a/b)^r)\right)
>  \le\frac{1-\theta}{\theta^*-\theta}.
> ```
> Here $`\mu_{\rm irr}(\xi)`$ is the supremum of the exponents $`\nu`$ for which $`|\xi-p/q|<q^{-\nu}`$ has infinitely many reduced rational solutions. In particular, $`\mu_{\rm irr}(F((31/4)^r))<301`$ for every $`r\ge1`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1049.PaperCompleteR21.rational_base_measure_uniform`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L194)

```lean
theorem rational_base_measure_uniform (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (_hcop : Nat.Coprime a b) (hr : 0 < r)
    (hθ : Real.log (b : ℝ) / Real.log (a : ℝ) < zudilinContour) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      (1 - Real.log (b : ℝ) / Real.log (a : ℝ)) /
        (zudilinContour - Real.log (b : ℝ) / Real.log (a : ℝ))
```

2. [`ErdosProblems.Erdos1049.PaperCompleteR21.thirtyoneFour_power_measure_lt_301`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RationalBaseThreshold.lean#L205)

```lean
theorem thirtyoneFour_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301
```

3. [`ErdosProblems.Erdos1049.PaperR17.rational_base_power_measure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L167)

```lean
theorem rational_base_power_measure (a b r : ℕ) (hb : 0 < b) (hab : b < a)
    (hr : 0 < r) (hregion : ZudilinContourRegion a b) :
    irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
      rationalBaseMeasureBound a b
```

4. [`ErdosProblems.Erdos1049.PaperR17.thirtyone_four_power_measure_lt_301`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperR17/SourceConsumers.lean#L176)

```lean
theorem thirtyone_four_power_measure_lt_301 (r : ℕ) (hr : 0 < r) :
    irrationalityExponent (paperLambert (((31 : ℝ) / 4) ^ r)) < 301
```

<a id="long1049-cor-rational-base-measure-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rational_base_measure_uniform` | [E1049_01/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L212) | [PaperStatementsI.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsI.lean#L23) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `thirtyoneFour_power_measure_lt_301` | [E1049_01/Challenge.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L220) | [PaperStatementsI.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/PaperStatementsI.lean#L31) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `rational_base_power_measure` | [E1049_01/Challenge.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L233) | [RationalBaseRegion.lean, line 55](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/RationalBaseRegion.lean#L55) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |
| `thirtyone_four_power_measure_lt_301` | [E1049_01/Challenge.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_01/Challenge.lean#L239) | [RationalBaseRegion.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_01/RationalBaseRegion.lean#L74) | [E1049_01](../evidence/comparator/replay-35882032091/receipt-E1049_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-archcap"></a>

## Theorem (a degree restriction for estimates valid at every base)

> *Let $`(U_n,V_n)\in\mathbb{Z}[x]^{2}`$ be a sequence such that, for constants $`\sigma,\delta>0`$ and $`h\ge0`$ independent of $`n`$ and of the base,*
> 
> 1.  *$`\Lambda_n(x):=U_n(x)F(x)-V_n(x)\ne0`$ for every real $`x>1`$;*
> 
> 2.  *$`\deg U_n,\deg V_n\le\delta n^{2}(1+o(1))`$;*
> 
> 3.  *the coefficient heights satisfy
>     ``` math
>     \log\max\bigl(H(U_n),H(V_n)\bigr)\le hn^{2}(1+o(1)),
>     ```
>     where $`H(P)`$ is the largest absolute value of a coefficient of $`P`$;*
> 
> 4.  *the remainders satisfy
>     ``` math
>     \log|\Lambda_n(x)|=-\sigma n^{2}\log x\,(1+o(1))
>     ```
>     for every real $`x>1`$.*
> 
> *Put $`d_n:=\max(\deg U_n,\deg V_n)`$. Then $`\sigma\le\delta`$, and for every fixed rational base $`a/b>1`$,
> ``` math
> \limsup_{n\to\infty}n^{-2}\log\bigl|b^{d_n}\Lambda_n(a/b)\bigr|
>  \le\delta\log b-\sigma\log(a/b).
> ```
> Consequently the homogenised forms tend to zero whenever $`\log b/\log a<\sigma/(\sigma+\delta)`$, a sufficient region whose cutoff is at most $`1/2`$. If the actual degrees satisfy $`d_n/n^{2}\to d`$, then $`d\ge\sigma`$ and the limit exists and equals $`d\log b-\sigma\log(a/b)`$; in that case the forms tend to zero below $`\log b/\log a=\sigma/(\sigma+d)`$ and their absolute values tend to infinity above it, so the exact-degree case has no decaying homogenised forms at $`3/2`$.*

The Lean declaration below states a result at least as strong as this one.

[`ErdosProblems.Erdos1049.PaperR9.long_record_archcap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperLongCapR9.lean#L411)

```lean
theorem long_record_archcap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : LongCapHypotheses U V F σ δ h) :
    σ ≤ δ ∧ σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    (∀ a b : ℕ, 1 ≤ b → b < a →
      Filter.limsup (fun n => Real.log |(b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n) atTop ≤
        δ * Real.log b - σ * Real.log ((a : ℝ) / b)) ∧
    (∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
        Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
          polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)) ∧
    (∀ d : ℝ,
      Tendsto (fun n => (pairWidth U V n : ℝ) / sqScale n) atTop (𝓝 d) →
        σ ≤ d ∧
        (∀ a b : ℕ, 1 ≤ b → b < a →
          Tendsto (fun n => Real.log |(b : ℝ) ^ pairWidth U V n *
            polynomialRemainder U V F ((a : ℝ) / b) n| / sqScale n) atTop
            (𝓝 (d * Real.log b - σ * Real.log ((a : ℝ) / b)))) ∧
        (∀ a b : ℕ, 1 ≤ b → b < a →
          (Real.log b / Real.log a < σ / (σ + d) →
            Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
              polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)) ∧
          (σ / (σ + d) < Real.log b / Real.log a →
            Tendsto (fun n => |(b : ℝ) ^ pairWidth U V n *
              polynomialRemainder U V F ((a : ℝ) / b) n|) atTop atTop)) ∧
        Tendsto (fun n => |(2 : ℝ) ^ pairWidth U V n *
          polynomialRemainder U V F ((3 : ℝ) / 2) n|) atTop atTop)
```

<a id="long1049-res-archcap-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `long_record_archcap` | [E1049_02/Challenge.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_02/Challenge.lean#L71) | [PaperStructuresD.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_02/PaperStructuresD.lean#L30) | [E1049_02](../evidence/comparator/replay-35882032091/receipt-E1049_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-cor-no-decay-below-square"></a>

## Corollary (nondecay when $`b<a<b^2`$)

> *Under the hypotheses of Theorem <a href="#long1049:res:archcap" data-reference-type="ref" data-reference="long1049:res:archcap">5</a>, for positive integers $`a,b`$ with $`b<a<b^2`$, the undivided forms $`b^{d_n}\Lambda_n(a/b)`$ do not tend to zero. No limit of $`d_n/n^2`$ is assumed.*

The Lean declaration below states a result at least as strong as this one.

[`ErdosProblems.Erdos1049.PaperR9.cleared_below_square_not_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperNoDecayR9.lean#L69)

```lean
theorem cleared_below_square_not_tendsto_zero
    (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : LongCapHypotheses U V F σ δ h)
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) (hsquare : a < b * b) :
    ¬ Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
      polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0)
```

<a id="long1049-cor-no-decay-below-square-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cleared_below_square_not_tendsto_zero` | [E1049_02/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_02/Challenge.lean#L113) | [ArchimedeanCap.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_02/ArchimedeanCap.lean#L35) | [E1049_02](../evidence/comparator/replay-35882032091/receipt-E1049_02.json) |

Challenge for `cleared_below_square_not_tendsto_zero`:

```lean
theorem cleared_below_square_not_tendsto_zero
    (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (σ δ h : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) (hh : 0 ≤ h)
    (hdeg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (width U V n : ℝ) ≤ (δ + ε) * (n : ℝ)^2)
    (hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log ((max (maxCoefficient (U n)) (maxCoefficient (V n)) : ℕ) : ℝ)
        ≤ (h + ε) * (n : ℝ)^2)
    (hne : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, remainder U V F x n ≠ 0)
    (hrate : ∀ x : ℝ, 1 < x →
      (fun n => Real.log |remainder U V F x n| - (-σ * Real.log x) * (n : ℝ)^2)
        =o[atTop] (fun n : ℕ => (n : ℝ)^2))
    (a b : ℕ) (hb : 1 ≤ b) (hab : b < a) (hsquare : a < b * b) :
    ¬ Tendsto (fun n => (b : ℝ) ^ width U V n *
      remainder U V F ((a : ℝ) / b) n) atTop (𝓝 0) := by sorry
```

<a id="long1049-res-sourceheight"></a>

## Lemma (coefficient heights of the constructed polynomials)

> *There is a constant $`h`$ with $`\log\max\bigl(H(U_n),H(V_n)\bigr)\le hn^{2}`$ for every $`n\ge1`$, where $`U_n`$ and $`V_n`$ are the polynomials of <a href="#long1049:eq:integer-polynomial-pair" data-reference-type="eqref" data-reference="long1049:eq:integer-polynomial-pair">[long1049:eq:integer-polynomial-pair]</a>.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1049.PaperCompleteR21.exists_quadratic_source_height_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/SourceCoefficientHeights.lean#L49)

```lean
theorem exists_quadratic_source_height_bound :
    ∃ h : ℝ, ∀ n : ℕ, 1 ≤ n →
      Real.log
          ((max (PaperR9.maxCoeffNat (PaperR11.sourceU n))
            (PaperR9.maxCoeffNat (PaperR13.sourceV n)) : ℕ) : ℝ) ≤
        h * (n : ℝ) ^ 2
```

2. [`ErdosProblems.Erdos1049.PaperCompleteR21.maxPairHeight_source_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/SourceCoefficientHeights.lean#L40)

```lean
theorem maxPairHeight_source_eq (n : ℕ) :
    PaperR9.maxPairHeight PaperR11.sourceU PaperR13.sourceV n =
      ((max (PaperR9.maxCoeffNat (PaperR11.sourceU n))
        (PaperR9.maxCoeffNat (PaperR13.sourceV n)) : ℕ) : ℝ)
```

<a id="long1049-res-sourceheight-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_quadratic_source_height_bound` | [E1049_02/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_02/Challenge.lean#L205) | [PaperStructuresQ.lean, line 337](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_02/PaperStructuresQ.lean#L337) | [E1049_02](../evidence/comparator/replay-35882032091/receipt-E1049_02.json) |
| `maxPairHeight_source_eq` | [E1049_02/Challenge.lean, line 213](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_02/Challenge.lean#L213) | [PaperStructuresQ.lean, line 346](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_02/PaperStructuresQ.lean#L346) | [E1049_02](../evidence/comparator/replay-35882032091/receipt-E1049_02.json) |

Challenge for `exists_quadratic_source_height_bound`:

```lean
theorem exists_quadratic_source_height_bound :
    ∃ h : ℝ, ∀ n : ℕ, 1 ≤ n →
      Real.log
          ((max (maxCoeffNat (sourceU n))
            (maxCoeffNat (sourceV n)) : ℕ) : ℝ) ≤
        h * (n : ℝ) ^ 2 := by sorry
```

Challenge for `maxPairHeight_source_eq`:

```lean
theorem maxPairHeight_source_eq (n : ℕ) :
    maxPairHeight sourceU sourceV n =
      ((max (maxCoeffNat (sourceU n))
        (maxCoeffNat (sourceV n)) : ℕ) : ℝ) := by sorry
```

<a id="long1049-res-powerbracket"></a>

## Theorem (sharp power bracket)

> *One has
> ``` math
> 2^{64}<3^{41}<2^{65}.
> ```
> Consequently
> ``` math
> \frac{41}{65}<\frac{\log2}{\log3},
>  \qquad
>  \frac{\log3}{\log2}<\frac{65}{41}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.power_bracket`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L24)

```lean
theorem power_bracket :
    (2 : ℕ) ^ 64 < 3 ^ 41 ∧ 3 ^ 41 < 2 ^ 65 ∧
      (41 : ℝ) / 65 < Real.log 2 / Real.log 3 ∧
      Real.log 3 / Real.log 2 < (65 : ℝ) / 41
```

<a id="long1049-res-powerbracket-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `power_bracket` | [E1049_03/Challenge.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_03/Challenge.lean#L57) | [PaperStatementsK.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_03/PaperStatementsK.lean#L36) | [E1049_03](../evidence/comparator/replay-35882032091/receipt-E1049_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-sharpgaps"></a>

## Corollary (gaps between the stated logarithmic thresholds)

> *For every $`\rho,\sigma\in\mathbb{R}`$ with $`0\le\rho`$ and $`1+\rho\le\sigma`$,
> ``` math
> \frac3{13}<\frac{\log2}{\log3}
>    -\left(\frac12-\frac1{\pi^2}\right),
>  \qquad
>  \frac3{13}<\frac{\log2}{\log3}-\Theta_{\mathrm{HP}}(\rho,\sigma),
> ```
> where $`\Theta_{\mathrm{HP}}`$ is the rectangular exponent threshold. Moreover
> ``` math
> \frac{\log3/\log2-1}{3}<\frac8{41}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.height_and_hankel_deficits`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L34)

```lean
theorem height_and_hankel_deficits (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - (1 / 2 - 1 / Real.pi ^ 2) ∧
      (3 : ℝ) / 13 < Real.log 2 / Real.log 3 - hpThreshold rho sigma ∧
      (Real.log 3 / Real.log 2 - 1) / 3 < (8 : ℝ) / 41
```

<a id="long1049-res-sharpgaps-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `height_and_hankel_deficits` | [E1049_03/Challenge.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_03/Challenge.lean#L68) | [PaperStatementsN.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_03/PaperStatementsN.lean#L35) | [E1049_03](../evidence/comparator/replay-35882032091/receipt-E1049_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-chargeceilings"></a>

## Theorem (bounds for two proposed degree savings)

> *For every integer $`N>0`$,
> ``` math
> 41(N^3-N)<39(4N^3-3N^2).
> ```
> For every integer $`N\ge2`$,
> ``` math
> 41(2N^3-N)<39(4N^3-3N^2).
> ```
> Hence the same strict inequalities hold with the left side replaced by $`41E`$ whenever, respectively, $`E\le N^3-N`$ or $`E\le2N^3-N`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.charge_ceilings`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L44)

```lean
theorem charge_ceilings :
    (∀ N : ℤ, 0 < N →
      41 * (N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N : ℤ, 2 ≤ N →
      41 * (2 * N ^ 3 - N) < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N E : ℤ, 0 < N → E ≤ N ^ 3 - N →
      41 * E < 39 * (4 * N ^ 3 - 3 * N ^ 2)) ∧
    (∀ N E : ℤ, 2 ≤ N → E ≤ 2 * N ^ 3 - N →
      41 * E < 39 * (4 * N ^ 3 - 3 * N ^ 2))
```

<a id="long1049-res-chargeceilings-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `charge_ceilings` | [E1049_03/Challenge.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_03/Challenge.lean#L46) | [PaperStatementsK.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_03/PaperStatementsK.lean#L21) | [E1049_03](../evidence/comparator/replay-35882032091/receipt-E1049_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-zudilin-sharp-qorder"></a>

## Theorem (the first nonzero term at every rank)

> *For every rank $`N`$, the normalised Hankel determinant $`V_N^{*}`$ of \[zudilin2016, Sec. 4, (6), p. 6\], evaluated at $`x=z=1`$, has
> ``` math
> \operatorname{ord}_q V_N^{*}=\frac{N(N-1)(2N-1)}{6},
>  \qquad
>  \text{leading coefficient}\quad\frac{(N!)^{2}(N+1)!}{2^{N}} .
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1049.order_zudilinNormalizedHankelDet_all`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L173)

```lean
theorem order_zudilinNormalizedHankelDet_all (N : ℕ) :
    PowerSeries.order (zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞)
```

2. [`ErdosProblems.Erdos1049.coeff_zudilinNormalizedHankelDet_all_rat`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/AllRow/Producer.lean#L199)

```lean
theorem coeff_zudilinNormalizedHankelDet_all_rat (N : ℕ) :
    ((PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (zudilinNormalizedHankelDet N) : ℤ) : ℚ) =
      (N.factorial : ℚ) ^ 2 * ((N + 1).factorial : ℚ) / (2 : ℚ) ^ N
```

<a id="long1049-res-zudilin-sharp-qorder-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `order_zudilinNormalizedHankelDet_all` | [E1049_04/Challenge.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_04/Challenge.lean#L72) | [PaperStatementsG.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_04/PaperStatementsG.lean#L49) | [E1049_04](../evidence/comparator/replay-35882032091/receipt-E1049_04.json) |
| `coeff_zudilinNormalizedHankelDet_all_rat` | [E1049_03/Challenge.lean, line 162](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_03/Challenge.lean#L162) | [AdelicHeightBridge.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_03/AdelicHeightBridge.lean#L62) | [E1049_03](../evidence/comparator/replay-35882032091/receipt-E1049_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-allrowinitial"></a>

## Lemma (a coefficient of each transformed row)

> *For $`m\ge j\ge0`$ one has $`D_jW_m(t)\in q^{E(m,j)}A`$ and
> ``` math
> \bigl[q^{E(m,j)}\bigr]D_jW_m(t)=(-1)^{j}h_{j-t}.
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/AllRowInitialCoefficient.lean#L213)

```lean
theorem all_row_initial (a : ℕ → S) (h : ℕ → ℤ) (hzero : h 0 = 1)
    (hrec : ∀ i : ℕ, h (i + 1) =
      -(∑ s ∈ Finset.range (i + 1),
          PowerSeries.constantCoeff (a (s + 1)) * h (i - s)))
    (m j t : ℕ) (hjm : j ≤ m) :
    (∀ d, d < m * j - j * (j - 1) / 2 →
        PowerSeries.coeff d
          (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) = 0) ∧
      PowerSeries.coeff (m * j - j * (j - 1) / 2)
        (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) =
        (if t ≤ j then (-1 : ℤ) ^ j * h (j - t) else 0)
```

2. [`ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial_reciprocal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/AllRowInitialCoefficient.lean#L242)

```lean
theorem all_row_initial_reciprocal (a : ℕ → S) (m j t : ℕ) (hjm : j ≤ m) :
    (∀ d, d < m * j - j * (j - 1) / 2 →
        PowerSeries.coeff d
          (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) = 0) ∧
      PowerSeries.coeff (m * j - j * (j - 1) / 2)
        (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) =
        (if t ≤ j then (-1 : ℤ) ^ j * paperReciprocal a (j - t) else 0)
```

3. [`ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial_dvd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/AllRowInitialCoefficient.lean#L255)

```lean
theorem all_row_initial_dvd (a : ℕ → S) (m j t : ℕ) (hjm : j ≤ m) :
    (PowerSeries.X : S) ^ (m * j - j * (j - 1) / 2) ∣
      zudilinBackwardShiftApply j m (fun n => paperTail a n t)
```

4. [`ErdosProblems.Erdos1049.PaperCompleteR21.paperE_eq_rowExponent`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/AllRowInitialCoefficient.lean#L116)

```lean
theorem paperE_eq_rowExponent (m j : ℕ) (hjm : j ≤ m) :
    m * j - j * (j - 1) / 2 = rowExponent j (m - j)
```

5. [`ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/AllRowInitialCoefficient.lean#L165)

```lean
theorem paperReciprocal_zero (a : ℕ → S) : paperReciprocal a 0 = 1
```

6. [`ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal_rec`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/AllRowInitialCoefficient.lean#L171)

```lean
theorem paperReciprocal_rec (a : ℕ → S) (i : ℕ) :
    paperReciprocal a (i + 1) =
      -(∑ s ∈ Finset.range (i + 1),
          PowerSeries.constantCoeff (a (s + 1)) * paperReciprocal a (i - s))
```

7. [`ErdosProblems.Erdos1049.PaperCompleteR21.paperRatio_agree`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/AllRowInitialCoefficient.lean#L73)

```lean
theorem paperRatio_agree (a : ℕ → S) (n D K : ℕ) (hDK : D ≤ K) :
    Agree D (paperRatio a n) (finiteRatio a K n)
```

<a id="long1049-res-allrowinitial-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `all_row_initial` | [E1049_04/Challenge.lean, line 132](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_04/Challenge.lean#L132) | [PaperStatementsH.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_04/PaperStatementsH.lean#L20) | [E1049_04](../evidence/comparator/replay-35882032091/receipt-E1049_04.json) |
| `all_row_initial_reciprocal` | [E1049_04/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_04/Challenge.lean#L150) | [PaperStatementsH.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_04/PaperStatementsH.lean#L40) | [E1049_04](../evidence/comparator/replay-35882032091/receipt-E1049_04.json) |
| `all_row_initial_dvd` | [E1049_04/Challenge.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_04/Challenge.lean#L145) | [PaperStatementsH.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_04/PaperStatementsH.lean#L34) | [E1049_04](../evidence/comparator/replay-35882032091/receipt-E1049_04.json) |
| `paperE_eq_rowExponent` | [E1049_04/Challenge.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_04/Challenge.lean#L87) | [PaperStatementsB.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_04/PaperStatementsB.lean#L26) | [E1049_04](../evidence/comparator/replay-35882032091/receipt-E1049_04.json) |
| `paperReciprocal_zero` | [E1049_04/Challenge.lean, line 101](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_04/Challenge.lean#L101) | [PaperStatementsB.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_04/PaperStatementsB.lean#L37) | [E1049_04](../evidence/comparator/replay-35882032091/receipt-E1049_04.json) |
| `paperReciprocal_rec` | [E1049_04/Challenge.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_04/Challenge.lean#L95) | [PaperStatementsB.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_04/PaperStatementsB.lean#L32) | [E1049_04](../evidence/comparator/replay-35882032091/receipt-E1049_04.json) |
| `paperRatio_agree` | [E1049_04/Challenge.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_04/Challenge.lean#L91) | [PaperStatementsB.lean, line 29](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_04/PaperStatementsB.lean#L29) | [E1049_04](../evidence/comparator/replay-35882032091/receipt-E1049_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-thm-geometric-universality"></a>

## Theorem (determinants of geometric moments)

> *Let $`a_k>0`$ satisfy, for fixed constants $`C`$ and $`\kappa`$,
> ``` math
> \frac{a_{k+h}}{a_k}\longrightarrow1\quad(k\to\infty)
>  \text{ for each fixed }h\ge0,
>  \qquad
>  \frac{a_{k+h}}{a_k}\le C(1+h)^\kappa\quad(k,h\ge0).
> ```
> Put $`M_m=\sum_{k\ge0}a_kq^{(m+1)k}`$ and $`D_N=\det(M_{i+j})_{0\le i,j<N}`$. Then
> ``` math
> D_N\sim\mathcal M(q)^3\,q^{B_N}P^{2N}\prod_{k=0}^{N-1}a_k
>  \qquad(N\to\infty).
> ```*

The Lean declaration below states a result at least as strong as this one.

[`ErdosProblems.Erdos1049.PaperCompleteR21.GeometricUniversality.geometric_universality`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/GeometricUniversality.lean#L1324)

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

<a id="long1049-thm-geometric-universality-comparator"></a>

**Comparator:** not yet compared.

<a id="long1049-prop-rogers-factorisation"></a>

## Proposition (the moment weights as a product of two finite sums)

> *For $`r\ge1`$ and $`k\ge0`$ set
> ``` math
> R_k^{(r)}(q)=\sum_{n_1+\cdots+n_r=k}
>  \frac{(q;q)_k}{\prod_{j\le r}(q;q)_{n_j}},
> ```
> the sum being over compositions into $`r`$ nonnegative parts, so that $`R_k^{(r)}`$ is the sum of all $`q`$-multinomial coefficients of degree $`k`$ and length $`r`$, equivalently the multivariate Rogers–Szegő polynomial at unit arguments \[vinroot2010\]. These are polynomial identities in the indeterminate $`q`$; at a prime power, $`r=2`$ gives the Galois number counting the subspaces of a $`k`$-dimensional space over the field of that order, and $`r=3`$ counts the flags $`V_1\subseteq V_2`$ in that space. The source is cited for those identifications; the factorisation below is proved here. Then
> ``` math
> \gamma_k(q)=\frac{R_k^{(2)}(q)R_k^{(3)}(q)}{(q;q)_k}.
> ```
> The product $`R_k^{(2)}R_k^{(3)}`$ lies in $`\mathbb{Z}_{\ge0}[q]`$, has degree $`\lfloor k^2/4\rfloor+\lfloor k^2/3\rfloor`$, and has coefficient sum $`6^k`$. Consequently $`(q;q)_k\gamma_k\in\mathbb{Z}[q]`$, and the weights $`a_k=P^4\gamma_k`$ satisfy
> ``` math
> P^5c_k\le a_k\le P^{-1}c_k
>  \qquad(k\ge0),
> ```
> together with $`a_{k+h}/a_k\le P^{-6}(1+h)^3`$, so the hypotheses of Theorem <a href="#long1049:thm:geometric-universality" data-reference-type="ref" data-reference="long1049:thm:geometric-universality">13</a> hold with $`\kappa=3`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperCompleteR21.RogersFactorisation.rogers_factorisation_proposition`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/RogersFactorisationAnalytic.lean#L1312)

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

<a id="long1049-prop-rogers-factorisation-comparator"></a>

**Comparator:** not yet compared.

<a id="long1049-thm-sharp-fixed-base"></a>

## Theorem (the size of $`V_N^*`$ at a fixed base)

> *Let $`\gamma_{\!E}`$ be Euler’s constant. The product
> ``` math
> \mathcal A(q)=e^{-8\gamma_{\!E}L}
>  \prod_{k\ge0}\left(\frac{a_k}{c_k}\,e^{8L/(k+1)}\right)
> ```
> converges to a positive finite value. With $`K(q)=\mathcal A(q)\mathcal M(q)^3`$,
> ``` math
> V_N^*(q)\sim K(q)\,C_Nq^{B_N}P^{2N}N^{-8L},
> ```
> equivalently
> ``` math
> \log V_N^*(q)=B_N\log q+\log C_N+2N\log P-8L\log N+\log K(q)+o(1).
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/SharpFixedBase.lean#L990)

```lean
theorem sharp_fixed_base {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (γ : ℕ → ℝ)
    (hγ : ∀ w : ℝ, 0 ≤ w → w < 1 →
      HasSum (fun k => γ k * w ^ k) (actualGeneratingFunction q w)) :
    HasProd (sharpFactor q γ) (∏' k : ℕ, sharpFactor q γ k) ∧
    0 < sharpA q γ ∧
    Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
        (sharpK q γ * leadC N * q ^ orderB N * qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * lambertL q))) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => Real.log (actualMomentHankel q N).det -
        ((orderB N : ℝ) * Real.log q + Real.log (leadC N) +
          2 * (N : ℝ) * Real.log (qPochhammerInfinity q q) - 8 * lambertL q * Real.log N +
          Real.log (sharpK q γ))) atTop (𝓝 0)
```

<a id="long1049-thm-sharp-fixed-base-comparator"></a>

**Comparator:** not yet compared.

<a id="long1049-res-finite-pencil"></a>

## Proposition (finite coefficient positivity and pencil roots)

> *For every real $`p>1`$ and $`1\le N\le8`$, $`A_N`$ is positive definite and all roots of $`\det(YA_N-B_N)`$ are real and strictly less than $`F(p)`$. The roots at consecutive ranks $`N,N+1\le8`$ interlace non-strictly.*

The Lean declaration below states a result at least as strong as this one.

[`ErdosProblems.Erdos1049.PaperR20.coefficientPencil_finitePencil`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperR20/FinitePencilProposition.lean#L43)

```lean
theorem coefficientPencil_finitePencil {p : ℝ} (hp : 1 < p) :
    (∀ N : ℕ, N ≤ 8 →
      (coefficientAlphaMatrix p N).PosDef ∧
        (coefficientPencilPoly p N).Splits ∧
        ∀ x : ℝ, (coefficientPencilPoly p N).IsRoot x → x < PaperR16.lambert (1 / p)) ∧
    (∀ N : ℕ, N + 1 ≤ 8 →
      ∃ (large : Fin (N + 1) → ℝ) (small : Fin N → ℝ),
        Antitone large ∧ Antitone small ∧
        (coefficientPencilPoly p (N + 1)).roots = Multiset.map large Finset.univ.val ∧
        (coefficientPencilPoly p N).roots = Multiset.map small Finset.univ.val ∧
        ∀ i : Fin N, small i ≤ large i.castSucc ∧ large i.succ ≤ small i)
```

<a id="long1049-res-finite-pencil-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `coefficientPencil_finitePencil` | [E1049_04/Challenge.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_04/Challenge.lean#L219) | [PaperStructuresO.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_04/PaperStructuresO.lean#L239) | [E1049_04](../evidence/comparator/replay-35882032091/receipt-E1049_04.json) |

Challenge for `coefficientPencil_finitePencil`:

```lean
theorem coefficientPencil_finitePencil {p : ℝ} (hp : 1 < p) :
    (∀ N : ℕ, N ≤ 8 →
      (coefficientAlphaMatrix p N).PosDef ∧
        (coefficientPencilPoly p N).Splits ∧
        ∀ x : ℝ, (coefficientPencilPoly p N).IsRoot x → x < lambert (1 / p)) ∧
    (∀ N : ℕ, N + 1 ≤ 8 →
      ∃ (large : Fin (N + 1) → ℝ) (small : Fin N → ℝ),
        Antitone large ∧ Antitone small ∧
        (coefficientPencilPoly p (N + 1)).roots = Multiset.map large Finset.univ.val ∧
        (coefficientPencilPoly p N).roots = Multiset.map small Finset.univ.val ∧
        ∀ i : Fin N, small i ≤ large i.castSucc ∧ large i.succ ≤ small i) := by sorry
```

<a id="long1049-res-content"></a>

## Theorem (rescaling rows and their determinant)

> *Let $`S`$ be real, let $`(U_n,V_n)`$ and $`(U_m,V_m)`$ be pairs of integers, and let $`c_n,c_m`$ be integers. Then
> ``` math
> L_S(c_nU_n,c_nV_n)=c_nL_S(U_n,V_n),
> ```
> ``` math
> \Delta\bigl(c_n(U_n,V_n),c_m(U_m,V_m)\bigr)
>  =c_nc_m\Delta\bigl((U_n,V_n),(U_m,V_m)\bigr),
> ```
> and consequently
> ``` math
> \left|\Delta\bigl(c_n(U_n,V_n),c_m(U_m,V_m)\bigr)\right|
>  =|c_n|\,|c_m|\,
>    \left|\Delta\bigl((U_n,V_n),(U_m,V_m)\bigr)\right|.
> ```
> In particular $`c_nc_m`$ divides the scaled determinant. Multiplication by these scalars therefore introduces a divisor whose absolute value is exactly the factor multiplying the determinant’s absolute value.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.integer_scalar_content`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L59)

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

<a id="long1049-res-content-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `integer_scalar_content` | [E1049_04/Challenge.lean, line 242](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_04/Challenge.lean#L242) | [PaperStatementsN.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_04/PaperStatementsN.lean#L47) | [E1049_04](../evidence/comparator/replay-35882032091/receipt-E1049_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-endpoints"></a>

## Theorem (endpoint residues)

> *Let $`P=\sum_ip_iX^i\in\mathbb{Z}[X]`$ and let $`W\ge0`$. Then
> ``` math
> H_W(P)\equiv p_0\,2^W\pmod 3,\qquad
>  H_W(P)\equiv p_W\,3^W\pmod 2.
> ```
> Consequently a unit constant coefficient prevents divisibility by $`3`$, and a unit coefficient at index $`W`$ prevents divisibility by $`2`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.endpoint_residues`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L74)

```lean
theorem endpoint_residues (W : ℕ) (P : Polynomial ℤ) :
    (homEvalThreeTwo W P : ZMod 3) = (P.coeff 0 : ZMod 3) * 2 ^ W ∧
    (homEvalThreeTwo W P : ZMod 2) = (P.coeff W : ZMod 2) * 3 ^ W ∧
    ((P.coeff 0 = 1 ∨ P.coeff 0 = -1) →
      ¬ (3 : ℤ) ∣ homEvalThreeTwo W P) ∧
    ((P.coeff W = 1 ∨ P.coeff W = -1) →
      ¬ (2 : ℤ) ∣ homEvalThreeTwo W P)
```

<a id="long1049-res-endpoints-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `endpoint_residues` | [E1049_05/Challenge.lean, line 98](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L98) | [PaperStatementsM.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsM.lean#L19) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-commonmult"></a>

## Proposition (common divisor)

> *Let $`U,V\in\mathbb{Z}[X]`$ and let $`W\ge0`$. If $`U`$ has unit top endpoint, $`V`$ has unit constant endpoint, and an integer $`c`$ divides both $`H_W(U)`$ and $`H_W(V)`$, then
> ``` math
> 2\nmid c\qquad\text{and}\qquad 3\nmid c.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.commonMultiplier_not_two_not_three_of_endpoint_units`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L398)

```lean
theorem commonMultiplier_not_two_not_three_of_endpoint_units
    (c : ℤ) (W : ℕ) (U V : Polynomial ℤ)
    (hUtop : U.coeff W = 1 ∨ U.coeff W = -1)
    (hVconst : V.coeff 0 = 1 ∨ V.coeff 0 = -1)
    (hcU : c ∣ homEvalThreeTwo W U)
    (hcV : c ∣ homEvalThreeTwo W V) :
    (¬ (2 : ℤ) ∣ c) ∧ (¬ (3 : ℤ) ∣ c)
```

<a id="long1049-res-commonmult-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `commonMultiplier_not_two_not_three_of_endpoint_units` | [E1049_05/Challenge.lean, line 142](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L142) | [PaperStatementsF.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsF.lean#L23) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-nomult"></a>

## Corollary (limits of rescaling and common-divisor cancellation at $`3/2`$)

> *Under the endpoint hypotheses of Proposition <a href="#long1049:res:commonmult" data-reference-type="ref" data-reference="long1049:res:commonmult">21</a>, every common divisor of the unscaled evaluations $`H_W(U)`$ and $`H_W(V)`$ is coprime to $`6`$. Multiplying two integer rows by nonzero integers $`c_n,c_m`$ multiplies their determinant by $`c_nc_m`$ and its absolute value by $`|c_nc_m|`$. Cancelling this introduced scalar factor therefore leaves the original comparison between divisor and determinant size unchanged.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.endpoint_scalar_content_exclusion`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L220)

```lean
theorem endpoint_scalar_content_exclusion (W : ℕ) (U V : Polynomial ℤ)
    (hU : U.coeff W = 1 ∨ U.coeff W = -1)
    (hV : V.coeff 0 = 1 ∨ V.coeff 0 = -1) :
    (∀ c U₀ V₀ : ℤ,
      homEvalThreeTwo W U = c * U₀ →
      homEvalThreeTwo W V = c * V₀ →
      ¬ (2 : ℤ) ∣ c ∧ ¬ (3 : ℤ) ∣ c) ∧
    (∀ c : ℤ, c ∣ homEvalThreeTwo W U → c ∣ homEvalThreeTwo W V →
      ¬ (2 : ℤ) ∣ c ∧ ¬ (3 : ℤ) ∣ c)
```

<a id="long1049-res-nomult-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `endpoint_scalar_content_exclusion` | [E1049_05/Challenge.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L107) | [PaperStatementsM.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsM.lean#L27) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-cyclounit"></a>

## Proposition (coprimality of homogenised cyclotomic values)

> *Let $`a>b\ge1`$ with $`\gcd(a,b)=1`$ and let $`m\ge1`$. Then $`\gcd(\Phi_m(a,b),ab)=1`$. In particular $`\gcd(\Phi_m(3,2),6)=1`$ for every $`m`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.cyclotomicHomEval_isCoprime_mul`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/ZudilinConeArithmetic.lean#L302)

```lean
theorem cyclotomicHomEval_isCoprime_mul
    {a b m : ℕ} (hm : 0 < m) (hab : a.Coprime b) :
    IsCoprime
      (homEval a b (Nat.totient m) (Polynomial.cyclotomic m ℤ))
      ((a * b : ℕ) : ℤ)
```

<a id="long1049-res-cyclounit-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cyclotomicHomEval_isCoprime_mul` | [E1049_05/Challenge.lean, line 151](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L151) | [PaperStatementsF.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsF.lean#L31) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-jetkernel"></a>

## Theorem (equal residues for two subset sums)

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

[`ErdosProblems.Erdos1049.PaperR7.fourJet_paper_statement`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L248)

```lean
theorem fourJet_paper_statement {M R S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ) :
    Fintype.card (FourJetSignature R S) = (3 ^ R) ^ 2 * (2 ^ S) ^ 2 ∧
    (Fintype.card (FourJetSignature R S) < 2 ^ M → PaperJetWitness R S W forms) ∧
    (0 < R → 4 * R + 2 * S ≤ M → PaperJetWitness R S W forms)
```

<a id="long1049-res-jetkernel-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `fourJet_paper_statement` | [E1049_05/Challenge.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L118) | [PaperStatementsM.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsM.lean#L37) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-rankfortyone"></a>

## Corollary (the exact count at depth $`41`$)

> *Let $`T>0`$. At modulus $`3^{R}`$ with $`R=41T`$, any family of $`M\ge130T+2S`$ integral polynomial pairs has two distinct binary selectors with the same residue vector. For $`T=1`$ the coefficient $`130`$ is exact for this counting argument:
> ``` math
> 2^{129+2S}<\bigl| (\mathbb{Z}/3^{41}\mathbb{Z})^2\times
>                        (\mathbb{Z}/2^S\mathbb{Z})^2\bigr|.
> ```
> No exact-optimality assertion is made here for $`T>1`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.rank_fortyone`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L149)

```lean
theorem rank_fortyone {M T S W : ℕ}
    (forms : Fin M → Polynomial ℤ × Polynomial ℤ)
    (hT : 0 < T) (hM : 130 * T + 2 * S ≤ M) :
    (∃ s t : Fin M → Bool, s ≠ t ∧
      selectedFourJetSum (41 * T) S W forms s =
        selectedFourJetSum (41 * T) S W forms t) ∧
      2 ^ (129 + 2 * S) < Fintype.card (FourJetSignature 41 S)
```

<a id="long1049-res-rankfortyone-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rank_fortyone` | [E1049_05/Challenge.lean, line 125](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L125) | [PaperStatementsM.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsM.lean#L43) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-boundedfibre"></a>

## Theorem (equal residues with different values)

> *Let $`A`$ and $`B`$ be finite sets, let $`f:A\to B`$, and let $`g:A\to C`$ be any map into a set $`C`$. Suppose every fibre of $`g`$ has at most $`k`$ elements. If
> ``` math
> |B|k<|A|,
> ```
> then there exist distinct $`x,y\in A`$ such that
> ``` math
> f(x)=f(y)\qquad\hbox{and}\qquad g(x)\ne g(y).
> ```
> Thus, when $`f`$ records the four residues and $`g`$ records the real remainder, a bound on the multiplicities of equal remainders guarantees a pair with equal residues and different remainders.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.exists_ne_map_eq_map_ne_of_card_mul_lt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/AdelicHeightBridge.lean#L1832)

```lean
theorem exists_ne_map_eq_map_ne_of_card_mul_lt {α β γ : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : α → γ) (k : ℕ)
    (hg : ∀ x : α, (Finset.univ.filter fun y => g y = g x).card ≤ k)
    (hcard : Fintype.card β * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧ g x ≠ g y
```

<a id="long1049-res-boundedfibre-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_ne_map_eq_map_ne_of_card_mul_lt` | [E1049_03/Challenge.lean, line 224](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_03/Challenge.lean#L224) | [AdelicHeightBridge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_03/AdelicHeightBridge.lean#L147) | [E1049_03](../evidence/comparator/replay-35882032091/receipt-E1049_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-plucker-collapse"></a>

## Theorem (vanishing minors and a residue count)

> *Let $`R_0`$ be a commutative ring and let $`w_n=(A_n,B_n)\in R_0^2`$. Suppose that each row is unimodular, meaning that $`u_nA_n+v_nB_n=1`$ for some $`u_n,v_n\in R_0`$, and that every adjacent minor vanishes:
> ``` math
> A_nB_{n+1}-B_nA_{n+1}=0\qquad(n\ge0).
> ```
> Then every pairwise minor $`A_iB_j-B_iA_j`$ vanishes. In particular, take $`R_0=\mathbb{Z}/(2^S3^R)\mathbb{Z}`$ with $`R>0`$. If $`S+2R\le k`$, there are two distinct binary selectors $`s,t\in\{0,1\}^{k}`$ such that
> ``` math
> \sum_{i<k}s_iw_i=\sum_{i<k}t_iw_i.
> ```
> Thus $`S+2R`$ rows suffice. The ambient two-coordinate argument gives the sufficient bound $`2S+4R`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.plucker_paper_statement`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L269)

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

<a id="long1049-res-plucker-collapse-comparator"></a>

**Comparator:** not yet compared.

<a id="long1049-res-scalar"></a>

## Theorem (a restriction on the two scalar exponents)

> *Let $`C_1>0`$. If $`C_0\le0`$ or $`2C_0\le C_1`$, then
> ``` math
> C_0\log 3-C_1\log 2<0.
> ```
> In the positive branch $`C_0>0`$ and $`2C_0\le C_1`$, the stronger estimate is
> ``` math
> C_0\log3-C_1\log2< -\frac{17}{41}C_0\log2.
> ```*

The Lean declaration below states a result at least as strong as this one.

[`ErdosProblems.Erdos1049.PaperR7.scalar_margin`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L177)

```lean
theorem scalar_margin {C0 C1 : ℝ} (hC1 : 0 < C1)
    (hs : C0 ≤ 0 ∨ 2 * C0 ≤ C1) :
    C0 * Real.log 3 - C1 * Real.log 2 < 0 ∧
      (0 < C0 → 2 * C0 ≤ C1 →
        C0 * Real.log 3 - C1 * Real.log 2 < -((17 : ℝ) / 41) * C0 * Real.log 2)
```

<a id="long1049-res-scalar-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `scalar_margin` | [E1049_05/Challenge.lean, line 172](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L172) | [PaperStatementsK.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsK.lean#L37) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-corridorbound"></a>

## Theorem (a necessary inequality for clearing)

> *If $`(a,b,N,K,Q,D)`$ satisfies the clearing conditions, then
> ``` math
> b^{\,N+K+1}<a\,(N+K).
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.coordinatewiseCorridor_implies_pow_lt_linear`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L121)

```lean
theorem coordinatewiseCorridor_implies_pow_lt_linear
    {a b N K Q digit : ℕ}
    (h : CoordinatewiseCorridor a b N K Q digit) :
    b ^ (N + K + 1) < a * (N + K)
```

<a id="long1049-res-corridorbound-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `coordinatewiseCorridor_implies_pow_lt_linear` | [E1049_05/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L184) | [PaperStatementsB.lean, line 53](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsB.lean#L53) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-exp"></a>

## Proposition

> *For every natural number $`x\ge2`$ we have $`3x<2^{\,x+1}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.three_mul_lt_two_pow_succ`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L142)

```lean
theorem three_mul_lt_two_pow_succ {x : ℕ} (hx : 2 ≤ x) :
    3 * x < 2 ^ (x + 1)
```

<a id="long1049-res-exp-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `three_mul_lt_two_pow_succ` | [E1049_05/Challenge.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L195) | [PaperStatementsB.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsB.lean#L62) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-nocorridor"></a>

## Theorem (failure of the stated clearing conditions at $`3/2`$)

> *For all $`N\ge1`$ and $`K\ge1`$ and all natural $`Q,D`$, the tuple $`(3,2,N,K,Q,D)`$ does not satisfy the clearing conditions.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.threeHalves_no_coordinatewiseCorridor`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L155)

```lean
theorem threeHalves_no_coordinatewiseCorridor
    {N K Q digit : ℕ} (hN : 1 ≤ N) (hK : 1 ≤ K) :
    ¬ CoordinatewiseCorridor 3 2 N K Q digit
```

<a id="long1049-res-nocorridor-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `threeHalves_no_coordinatewiseCorridor` | [E1049_05/Challenge.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L220) | [RationalBaseBarrier.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/RationalBaseBarrier.lean#L37) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-tailrec"></a>

## Theorem (recurrence for the scaled remainder)

> *Let $`r,s,B,\xi\in\mathbb{Q}`$ with $`r\ne0`$, let $`c:\mathbb{N}\to\mathbb{Q}`$, and let $`P_N`$ and $`U_N`$ be as in <a href="#long1049:eq:tailstate" data-reference-type="eqref" data-reference="long1049:eq:tailstate">[long1049:eq:tailstate]</a>. Then for every $`N`$,
> ``` math
> U_{N+1}=r\,U_N-B\,c(N+1)\,s^{\,N+1}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.rationalBaseClearedTailQ_succ`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L187)

```lean
theorem rationalBaseClearedTailQ_succ
    {r s B F : ℚ} {coeff : ℕ → ℚ} (hr : r ≠ 0) (N : ℕ) :
    rationalBaseClearedTailQ r s B F coeff (N + 1) =
      r * rationalBaseClearedTailQ r s B F coeff N -
        B * coeff (N + 1) * s ^ (N + 1)
```

<a id="long1049-res-tailrec-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rationalBaseClearedTailQ_succ` | [E1049_05/Challenge.lean, line 213](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L213) | [RationalBaseBarrier.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/RationalBaseBarrier.lean#L19) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-forcing"></a>

## Theorem (the forcing term)

> *Let $`s,B`$ be natural numbers and $`c:\mathbb{N}\to\mathbb{N}`$.*
> 
> 1.  *If $`s\ge2`$, $`B\ge1`$ and $`c(N+1)\ge1`$, then $`2^{\,N+1}\le B\,c(N+1)\,s^{\,N+1}`$.*
> 
> 2.  *If $`s=1`$, then $`B\,c(N+1)\,s^{\,N+1}=B\,c(N+1)`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.forcing_term`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L186)

```lean
theorem forcing_term (B : ℕ) (c : ℕ → ℕ) (N : ℕ) :
    (∀ s : ℕ, 2 ≤ s → 1 ≤ B → 1 ≤ c (N + 1) →
      2 ^ (N + 1) ≤ rationalBaseForcingNat s B c N) ∧
      rationalBaseForcingNat 1 B c N = B * c (N + 1)
```

<a id="long1049-res-forcing-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `forcing_term` | [E1049_05/Challenge.lean, line 166](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L166) | [PaperStatementsK.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsK.lean#L27) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-sevenhalves"></a>

## Theorem (the $`7/2`$ height condition)

> *``` math
> \frac{\log 7}{\log(7/2)}
>  <
>  \left(\frac12+\frac1{\pi^2}\right)^{-1}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.sevenHalves_archimedean_height_condition`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/RationalBaseLambert.lean#L83)

```lean
theorem sevenHalves_archimedean_height_condition :
    Real.log 7 / Real.log ((7 : ℝ) / 2) <
      ((1 : ℝ) / 2 + 1 / Real.pi ^ 2)⁻¹
```

<a id="long1049-res-sevenhalves-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `sevenHalves_archimedean_height_condition` | [E1049_05/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L190) | [PaperStatementsB.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsB.lean#L58) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-pade"></a>

## Proposition (exponent model: summand bound and exact gap)

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
> 1.  *if $`0\le k\le n`$, then $`\widetilde{P}(n,k)\le\widetilde{E}_n`$, and the gap factors as $`\widetilde{E}_n-\widetilde{P}(n,k)=(n-k)(3n-k-1)`$;*
> 
> 2.  *$`\widetilde{E}_n-\widetilde{Q}(n,m)=2\bigl(n+m(m-1)\bigr)`$ identically;*
> 
> 3.  *if $`n\ge0`$ and $`m\ge1`$, then $`\widetilde{Q}(n,m)\le\widetilde{E}_n`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperR7.pade_summand_bound_and_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperFiniteAssembliesR7.lean#L201)

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

<a id="long1049-res-pade-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `pade_summand_bound_and_gap` | [E1049_05/Challenge.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L239) | [PaperStatementsN.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStatementsN.lean#L52) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long1049-res-tail-lattice"></a>

## Proposition (the prefix lattice of the tails)

> *Every $`Q_m`$ is coprime to $`ab`$, and $`b`$ divides every $`P_m`$. For every prefix containing $`m=0`$ and $`m=1`$,
> ``` math
> \operatorname{span}_{\mathbb{Z}}\{(Q_m,P_m):0\le m<M\}=\mathbb{Z}\times b\mathbb{Z}
>  \qquad(M\ge2),
> ```
> so the Smith invariants are $`1,b`$, the gcd of the $`2\times2`$ minors is $`b`$, and the image modulo $`D`$ has cardinality $`D^2/\gcd(b,D)`$. Multiplying an individual tail by a nonzero rational weight leaves its primitive row unchanged up to sign.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperCompleteR21.TailLattice.tail_prefix_lattice`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/TailPrefixLattice.lean#L475)

```lean
theorem tail_prefix_lattice (a b : ℕ) (hb : 1 ≤ b) (hba : b < a) (hab : Nat.Coprime a b) :
    (∀ m, 0 < tailQ a b m ∧ Int.gcd (tailQ a b m) (tailP a b m) = 1) ∧
    (∀ m, IsCoprime (tailQ a b m) ((a : ℤ) * b)) ∧
    (∀ m, (b : ℤ) ∣ tailP a b m) ∧
    (∀ M, 2 ≤ M →
      tailPrefixLattice a b M = (⊤ : Submodule ℤ ℤ).prod (Submodule.span ℤ {(b : ℤ)}) ∧
      (∃ snf : Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) 2,
          snf.a = ![1, (b : ℤ)]) ∧
      (∀ n, Nonempty (Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) n) → n = 2) ∧
      (∀ snf : Module.Basis.SmithNormalForm (tailPrefixLattice a b M) (Fin 2) 2,
          snf.a 0 ∣ snf.a 1 → IsUnit (snf.a 0) ∧ Associated (snf.a 1) (b : ℤ)) ∧
      (Finset.univ : Finset (Fin M × Fin M)).gcd
          (fun ij => tailMinor a b ij.1 ij.2) = (b : ℤ) ∧
      (∀ D : ℕ, 1 ≤ D →
        (rowModD D '' (tailPrefixLattice a b M : Set (ℤ × ℤ))).ncard = D ^ 2 / Nat.gcd b D)) ∧
    (∀ m (w : ℚ), w ≠ 0 → ∀ (c : ℚ) (A B : ℤ), c ≠ 0 →
      (A : ℚ) = c * (w * tailQ a b m) → (B : ℚ) = c * (w * tailP a b m) →
      (∃ k : ℤ, k ≠ 0 ∧ (A, B) = k • tailRow a b m) ∧
      ((A / (Int.gcd A B : ℤ), B / (Int.gcd A B : ℤ)) = tailRow a b m ∨
        (A / (Int.gcd A B : ℤ), B / (Int.gcd A B : ℤ)) = -tailRow a b m))
```

<a id="long1049-res-tail-lattice-comparator"></a>

**Comparator:** not yet compared.

<a id="long1049-res-nomahler"></a>

## Proposition (no finite simultaneous $`2/3`$-system)

> *Let
> ``` math
> \mathcal L(z)=\sum_{n\ge1}\frac{z^n}{1-z^n}.
> ```
> There is no finite-dimensional $`\mathbb{Q}(z)`$-vector space that contains $`\mathcal L`$ and is stable under both $`z\mapsto z^2`$ and $`z\mapsto z^3`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1049.PaperCompleteR21.no_finite_simultaneous_two_three_system_unconditional`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos1049/PaperCompleteR21/SimultaneousMahlerSystemUnconditional.lean#L298)

```lean
theorem no_finite_simultaneous_two_three_system_unconditional :
    ¬ ∃ V : Submodule (RatFunc ℚ) ℚ⸨X⸩,
        Module.Finite (RatFunc ℚ) V ∧
        divisorLambert ∈ V ∧
        (∀ f ∈ V, subs 2 f ∈ V) ∧ (∀ f ∈ V, subs 3 f ∈ V)
```

<a id="long1049-res-nomahler-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `no_finite_simultaneous_two_three_system_unconditional` | [E1049_05/Challenge.lean, line 286](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1049_05/Challenge.lean#L286) | [PaperStructuresL.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1049_05/PaperStructuresL.lean#L23) | [E1049_05](../evidence/comparator/replay-35882032091/receipt-E1049_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
