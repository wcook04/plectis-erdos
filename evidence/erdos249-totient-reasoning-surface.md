# Formal evidence: The Binary Totient Series

This record belongs to the paper [erdos249-totient-reasoning-surface.pdf](../paper/249/erdos249-totient-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`e6c2d8f77ac2`](https://github.com/wcook04/plectis-erdos/tree/e6c2d8f77ac24753c5216a49f4daf7f7388b309f) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35882032091](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35882032091) at corpus commit [`a2faa350b45a`](https://github.com/wcook04/plectis-erdos-lean/tree/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3) (tag `paper-evidence-2026-09-23`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 195 results: 191 with a Lean proof of the whole statement, 4 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 190 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="thm-denom"></a>

## Theorem (Denominator exclusion from a fixed Farey window)

> *If $`S \in \mathbb{Q}`$ then its reduced denominator exceeds $`Q_0 := 79\,639\,646\,646\,701\,375\,323\,355\,774\,875\,831\,053 \approx 7.96 \times 10^{34}`$. Equivalently, $`S`$ differs from every rational number whose reduced denominator is at most $`Q_0`$. The bound is sharp for this window: $`q = Q_0 + 1`$ is the exact first failing denominator. It is the denominator of the mediant of two explicit unimodular Farey neighbours. <span class="sans-serif">\[bounded\]</span> <span class="sans-serif">\[Lean\]</span> [`Erdos249257.tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18384) [`Erdos249257.gap_check_window_1_240_first_failure`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GapFareyBound.lean#L225)*

The Lean declarations below together state this result.

1. [`Erdos249257.tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L18384)

```lean
theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ)
```

2. [`GapFareyBound.gap_check_window_1_240_first_failure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GapFareyBound.lean#L225)

```lean
theorem gap_check_window_1_240_first_failure :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054
```

where [`IsFirstGapFailure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GapFareyBound.lean#L44) is

```lean
def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)
```

<a id="thm-denom-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053` | [E249_01/Challenge.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L44) | [PaperStatementsAI.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAI.lean#L57) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `gap_check_window_1_240_first_failure` | [E249_01/Challenge.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L56) | [PaperStatementsAK.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAK.lean#L118) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-deposits"></a>

## Proposition (Finite certificate computations)

> *$`\mathcal{C}`$ has been verified at: the $`28`$ diagonal instances of the least-common-multiple diagonal through $`t = 64`$ ([`Erdos249257.certifiedKill_diagonal_all_imported_through_t64`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/DiagonalPincerCertificatesT64.lean#L1967), endpoint [`Erdos249257.certifiedKill_diagonal_t64`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/DiagonalPincerCertificatesT64.lean#L1928)); all shifts $`h \in [1,16]`$ simultaneously at $`(N,L) = (14,9)`$, by `decide` ([`Erdos249257.certifiedKill_all_upto_sixteen`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L574)); and eight further period examples at $`N = 300`$. These are historical subsets of the examples. The supplied source also proves a complete diagonal band for $`1\le t\le82`$, with no omitted scales ([`exists_diagonalKill_le_82`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Skip/LadderT67.lean#L71264)). This is bounded coverage, not a cofinal diagonal family. Note the quantifier order: the simultaneous small-shift example uses one pair $`N,L`$ for every $`1\le h\le16`$. In symbols, it proves $`\exists N\,\exists L\,\forall h\,(1\le h\le16\Rightarrow\mathcal C(h,N,L))`$. In contrast, $`\mathrm{Sep}`$ requires arbitrarily large $`N`$ for each positive $`h`$; neither the shift range nor the basepoint threshold is bounded. <span class="sans-serif">\[fixed\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state this result.

1. [`Erdos249257.TotientTailPeriodKiller.certifiedKill_diagonal_all_imported_through_t64`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/DiagonalPincerCertificatesT64.lean#L1967)

```lean
theorem certifiedKill_diagonal_all_imported_through_t64 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT64 t)
```

2. [`Erdos249257.TotientTailPeriodKiller.certifiedKill_diagonal_t64`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/DiagonalPincerCertificatesT64.lean#L1928)

```lean
theorem certifiedKill_diagonal_t64 :
    certifiedKill (periodLcm 64) (periodLcm 64) 93
```

3. [`Erdos249257.TotientTailPeriodKiller.certifiedKill_all_upto_sixteen`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CarrySurvivorExtinction.lean#L574)

```lean
theorem certifiedKill_all_upto_sixteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9
```

4. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_67_300`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L471)

```lean
theorem certifiedKill_67_300 : certifiedKill 67 300 11
```

5. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_81_300`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L474)

```lean
theorem certifiedKill_81_300 : certifiedKill 81 300 13
```

6. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_97_300`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L477)

```lean
theorem certifiedKill_97_300 : certifiedKill 97 300 13
```

7. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_101_300`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L480)

```lean
theorem certifiedKill_101_300 : certifiedKill 101 300 11
```

8. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_121_300`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L483)

```lean
theorem certifiedKill_121_300 : certifiedKill 121 300 10
```

9. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_125_300`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L486)

```lean
theorem certifiedKill_125_300 : certifiedKill 125 300 18
```

10. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_127_300`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L490)

```lean
theorem certifiedKill_127_300 : certifiedKill 127 300 11
```

11. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_128_300`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L493)

```lean
theorem certifiedKill_128_300 : certifiedKill 128 300 11
```

12. [`ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Skip/LadderT67.lean#L71264)

```lean
theorem exists_diagonalKill_le_82 (t : ℕ) (ht : t ≤ 82) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L
```

<a id="prop-deposits-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `certifiedKill_diagonal_all_imported_through_t64` | [E249_01/Challenge.lean, line 153](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L153) | [PaperStatementsAT.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAT.lean#L122) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `certifiedKill_diagonal_t64` | [E249_01/Challenge.lean, line 210](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L210) | [PaperStructuresN.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStructuresN.lean#L42) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `certifiedKill_all_upto_sixteen` | [E249_01/Challenge.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L91) | [PaperStatementsAD.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAD.lean#L27) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `certifiedKill_67_300` | [E249_01/Challenge.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L187) | [PaperStatementsAU.lean, line 589](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L589) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `certifiedKill_81_300` | [E249_01/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L190) | [PaperStatementsAU.lean, line 591](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L591) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `certifiedKill_97_300` | [E249_01/Challenge.lean, line 193](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L193) | [PaperStatementsAU.lean, line 593](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L593) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `certifiedKill_101_300` | [E249_01/Challenge.lean, line 172](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L172) | [PaperStatementsAU.lean, line 579](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L579) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `certifiedKill_121_300` | [E249_01/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L175) | [PaperStatementsAU.lean, line 581](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L581) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `certifiedKill_125_300` | [E249_01/Challenge.lean, line 178](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L178) | [PaperStatementsAU.lean, line 583](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L583) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `certifiedKill_127_300` | [E249_01/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L181) | [PaperStatementsAU.lean, line 585](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L585) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `certifiedKill_128_300` | [E249_01/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L184) | [PaperStatementsAU.lean, line 587](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L587) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `exists_diagonalKill_le_82` | [E249_01/Challenge.lean, line 201](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L201) | [PaperStatementsAU.lean, line 599](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L599) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sign"></a>

## Proposition (Positivity does not exclude an integer)

> *Put $`H_a=\operatorname{lcm}(1,\ldots,2^a)`$. For every $`a\ge8`$ and $`J\ge0`$ with $`J+(a+6)<2\cdot2^a`$,
> ``` math
> R_{2H_a+J}-R_{H_a+J}>0.
> ```
> This needs no irrationality hypothesis ([`Erdos257PeriodNoncollapse.actualLcmTailDiff_shift_pos`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSign.lean#L39), [`Erdos257PeriodNoncollapse.actualLcmTailOrbit_pos`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSign.lean#L144)). If this difference is an integer and $`K\ge0`$ satisfies
> ``` math
> J+K+(a+6)<2\cdot2^a,\qquad 2H_a+J+K+2<2^K,
> ```
> then
> ``` math
> D(H_a,H_a+J,K)\bmod2^K
>    =2^K-\bigl(R_{2H_a+J+K}-R_{H_a+J+K}\bigr)
> ```
> lies strictly between $`2^K-(2H_a+J+K+2)`$ and $`2^K`$ ([`Erdos257PeriodNoncollapse.actualLcm_integral_forces_topEdgeResidue`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSign.lean#L211)). The later tail difference is a positive integer. Its negative, not the carry itself, is the representative near zero. Thus positivity locates the residue near the upper endpoint; it does not establish the central-residue inequalities. Both restrictions on $`K`$ are part of this conclusion. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state this result.

1. [`Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailDiff_shift_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientActualLcmOrbitSign.lean#L39)

```lean
theorem actualLcmTailDiff_shift_pos
    {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 <
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J)
```

2. [`Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcm_integral_forces_topEdgeResidue`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientActualLcmOrbitSign.lean#L211)

```lean
theorem actualLcm_integral_forces_topEdgeResidue
    {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J))
    (hroom :
      ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
        (2 : ℤ) ^ K) :
    let H
```

3. [`Erdos249257.TotientTailPeriodKiller.carryOrbit_eq_tail_diff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CarrySurvivorExtinction.lean#L393)

```lean
lemma carryOrbit_eq_tail_diff {h N : ℕ} {d : ℤ}
    (hd : (d : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N d i : ℝ) = totientTail (N + i + h) - totientTail (N + i)
```

<a id="prop-sign-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `actualLcmTailDiff_shift_pos` | [E249_01/Challenge.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L228) | [PaperStatementsA.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L21) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `actualLcm_integral_forces_topEdgeResidue` | [E249_01/Challenge.lean, line 236](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L236) | [PaperStatementsA.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L30) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `carryOrbit_eq_tail_diff` | [E249_01/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L255) | [PaperStatementsA.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L50) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-rank"></a>

## Proposition (Rationality forces unbounded carry rank)

> *If $`S`$ is rational then, for every $`e`$, the carry sections $`n\mapsto u_{2^jn+r}`$ with $`1\le j\le e`$ and $`0\le r<2^j`$ span a rational vector space of dimension at least $`2^{e}-1`$ ([`Erdos249257.not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientCarryKernelRigidity.lean#L300)). The lower bound holds at every depth. It comes from the linear independence of the $`2^e+1`$ retained dyadic totient sections for $`e\ge1`$, proved using the Chinese remainder theorem and Dirichlet’s theorem ([`Erdos249257.linearIndependent_canonicalTotientKernelFamily`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L935)), so the full family spans an infinite-dimensional space ([`Erdos249257.not_finiteDimensional_span_fullTotientKernel`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L1145)), the case $`k=2`$ of Coons’s non-regularity theorem (§<a href="#sec:mahler-defect" data-reference-type="ref" data-reference="sec:mahler-defect">10.8</a>). <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declaration below states this result.

[`Erdos249257.not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientCarryKernelRigidity.lean#L300)

```lean
theorem not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e)))
```

<a id="prop-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `not_irrational_totientSeries_implies_unbounded_carryRank_unconditional` | [E249_32/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_32/Challenge.lean#L94) | [CarryRankFrontier.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_32/CarryRankFrontier.lean#L44) | [E249_32](../evidence/comparator/replay-35882032091/receipt-E249_32.json) |

Challenge for `not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`:

```lean
theorem not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e))) := by sorry
```

<a id="prop-period-not-rank"></a>

## Proposition (Periodicity modulo an integer does not bound rational rank)

> *If $`S`$ is rational, the same carry $`u`$ has unbounded rational section rank and one eventual period modulo $`v`$ valid for all its dyadic sections. More precisely, there are $`h\ge1`$ and $`N_0`$ such that, for every $`j,r\ge0`$ and $`n\ge N_0`$,
> ``` math
> u_{2^j(n+h)+r}\equiv u_{2^jn+r}\pmod v.
> ```
> The rank and periodicity assertions hold together ([`Erdos257PeriodNoncollapse.not_irrational_totientSeries_implies_mod_period_and_unbounded_rank`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailCarryPeriod.lean#L224)). This conditional theorem alone is not a counterexample to a general periodicity-to-rank implication: its antecedent is not established. The separate $`5/4`$ control supplies a concrete counterexample to the generic rationality-driven rank ceiling; see the detailed comparison in Section <a href="#sec:mahler-defect" data-reference-type="ref" data-reference="sec:mahler-defect">10.8</a>. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declaration below states this result.

[`Erdos249257.not_irrational_totientSeries_implies_mod_period_and_unbounded_rank`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientTailCarryPeriod.lean#L224)

```lean
theorem not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u
```

<a id="prop-period-not-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `not_irrational_totientSeries_implies_mod_period_and_unbounded_rank` | [E249_32/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_32/Challenge.lean#L113) | [CarryRankFrontier.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_32/CarryRankFrontier.lean#L65) | [E249_32](../evidence/comparator/replay-35882032091/receipt-E249_32.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-iffs"></a>

## Proposition (Equivalent certificate conditions)

> *Put $`H_t=\operatorname{lcm}(1,\ldots,t)`$. Several variations of Definition <a href="#defn:sep" data-reference-type="ref" data-reference="defn:sep">2</a> are equivalent to $`S\notin\mathbb Q`$. One may allow a positive multiple of each prescribed shift, still requiring certificates beyond every basepoint threshold (Theorem <a href="#catalogue:cert:b2" data-reference-type="ref" data-reference="catalogue:cert:b2">99</a>; [`periodMultipleKillSupply_iff_irrational`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L432)). Alternatively, one may use the original quantified condition ([`irrational_totient_series_iff_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmConeFlatness.lean#L412)) or restrict to $`h=N=H_t`$ at arbitrarily large $`t`$ (Theorem <a href="#catalogue:cert:b3" data-reference-type="ref" data-reference="catalogue:cert:b3">100</a>; [`irrational_totient_series_iff_lcm_diagonal_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmConeFlatness.lean#L426)). Replacing the symmetric residue test by
> ``` math
> N+L+2\le D(h,N,L)\bmod2^L\le2^L-(N+h+L+2)
> ```
> also gives equivalent quantified conditions, including its restriction to $`h=N=H_t`$ at arbitrarily large $`t`$ ([`Erdos257PeriodNoncollapse.CofinalDirectedLcmCertificateSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailCarryPeriod.lean#L866)). Finally, the counted phase-separation condition in Proposition <a href="#prop:b2" data-reference-type="ref" data-reference="prop:b2">16</a>(b) is equivalent to irrationality ([`Erdos249257.dtwWindowSeparatedPairs_iff_irrational_totient_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/PivotAntiReconstruction.lean#L1765)). These equivalences change the form of the arithmetic question, not its logical strength. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PeriodMultipleEscape.periodMultipleKillSupply_iff_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L432)

```lean
theorem periodMultipleKillSupply_iff_irrational :
    PeriodMultipleKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L412)

```lean
theorem irrational_totient_series_iff_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ,
        ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L
```

3. [`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_lcm_diagonal_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L426)

```lean
theorem irrational_totient_series_iff_lcm_diagonal_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
        certifiedKill (periodLcm t) (periodLcm t) L
```

4. [`Erdos249257.irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientTailCarryPeriod.lean#L875)

```lean
theorem irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      CofinalDirectedLcmCertificateSupply
```

5. [`Erdos249257.TotientTailPeriodKiller.dtwWindowSeparatedPairs_iff_irrational_totient_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/PivotAntiReconstruction.lean#L1765)

```lean
theorem dtwWindowSeparatedPairs_iff_irrational_totient_series :
    DTWWindowSeparatedPairs ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="prop-iffs-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `periodMultipleKillSupply_iff_irrational` | [E249_01/Challenge.lean, line 196](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L196) | [PaperStatementsAU.lean, line 595](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L595) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `irrational_totient_series_iff_certificate_supply` | [E249_01/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L100) | [PaperStatementsAD.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAD.lean#L46) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `irrational_totient_series_iff_lcm_diagonal_certificate_supply` | [E249_01/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L260) | [PaperStatementsA.lean, line 66](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L66) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply` | [E249_01/Challenge.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L158) | [PaperStatementsAT.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAT.lean#L128) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `dtwWindowSeparatedPairs_iff_irrational_totient_series` | [E249_01/Challenge.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L95) | [PaperStatementsAD.lean, line 33](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAD.lean#L33) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-parity"></a>

## Proposition (A rational sequence preserving size bounds, parity and aperiodicity)

> *There is $`c : \mathbb{N}\to \mathbb{N}`$ with $`c(n) \le 6`$ and $`c(n) \le n`$ for all $`n`$, $`c(n) \equiv \varphi(n) \pmod 2`$ for *every* $`n`$, and $`c`$ not eventually periodic; indeed for every $`N, G, K`$ there are $`K`$ explicit carry pulses beyond $`N`$, pairwise separated by more than $`G`$; and yet $`\sum_n c(n)/2^{n} = 3/2 \in \mathbb{Q}`$ ([`Erdos257PeriodNoncollapse.exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientParityCoboundaryCountermodel.lean#L637); sum at `:359`, aperiodicity at `:487`, parity match at `:194`; `#print axioms` clean). <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state this result.

1. [`Erdos249257.TotientParityCoboundaryCountermodel.exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L637)

```lean
theorem exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel :
    ∃ c : ℕ → ℕ,
      (∀ N G K, ∃ k,
        N < 2 ^ (k + 3) ∧
        ∀ i : ℕ, i < K →
          2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
          c (2 ^ (k + i + 3)) = 6 ∧
          c (2 ^ (k + i + 3) + 1) = 0) ∧
      (∀ n, c n ≤ 6) ∧
      (∀ n, c n ≤ n) ∧
      (∀ n, c n % 2 = Nat.totient n % 2) ∧
      (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n) ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n)
```

2. [`Erdos249257.TotientParityCoboundaryCountermodel.tsum_parityCoboundaryWeight_eq_three_halves`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L359)

```lean
theorem tsum_parityCoboundaryWeight_eq_three_halves :
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) = 3 / 2
```

<a id="prop-parity-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel` | [E249_01/Challenge.lean, line 270](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L270) | [PaperStatementsAG.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAG.lean#L43) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |
| `tsum_parityCoboundaryWeight_eq_three_halves` | [E249_02/Challenge.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L65) | [PaperStatementsAG.lean, line 48](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAG.lean#L48) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-gsound"></a>

## Lemma (A residue certificate excludes an integral tail difference)

> *Let $`c:\mathbb{N}\to\mathbb{N}`$ satisfy $`c(n)\le n`$ for all $`n`$. For $`h,N,L\in\mathbb{N}`$, $`\mathcal C_c(h,N,L) \Rightarrow R^{c}_{N+h} - R^{c}_{N} \notin \mathbb{Z}`$. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.certificate_sound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/GenericTailCertificates.lean#L66)

```lean
theorem certificate_sound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (h N L : ℕ) (hcert : certificate c h N L) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_difference`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/GenericTailCertificates.lean#L48)

```lean
theorem scaled_difference (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    (2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ) =
      binaryCoeffTail c (N + h + L) - binaryCoeffTail c (N + L)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.truncation_error_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/GenericTailCertificates.lean#L55)

```lean
theorem truncation_error_bound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    |(2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ)| ≤ (N : ℝ) + h + L + 2
```

<a id="lem-gsound-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `certificate_sound` | [E249_02/Challenge.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L95) | [PaperStatementsAW.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L30) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `scaled_difference` | [E249_02/Challenge.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L107) | [PaperStatementsAW.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L40) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `truncation_error_bound` | [E249_02/Challenge.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L118) | [PaperStatementsAW.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L49) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-gperiod"></a>

## Lemma (Generic tail-period law)

> *Let $`c:\mathbb{N}\to\mathbb{N}`$ satisfy $`c(n)\le n`$ for all $`n`$. If $`T_c = p/(2^{e}m)`$ with $`p\in\mathbb{Z}`$, $`e\ge0`$ and $`m`$ a positive odd integer, and if $`h\ge1`$ satisfies $`m\mid 2^h-1`$, then $`R^{c}_{N+h} - R^{c}_{N} \in \mathbb{Z}`$ for every $`N \ge e`$. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.generic_tail_period`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/GenericTailCertificates.lean#L98)

```lean
theorem generic_tail_period (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (p : ℤ) (e m h N : ℕ) (hm : 0 < m) (hN : e ≤ N)
    (hdvd : m ∣ 2 ^ h - 1)
    (hS : binaryCoeffSeries c = (p : ℝ) / ((2 : ℝ) ^ e * m)) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∈ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_tail_split`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/GenericTailCertificates.lean#L33)

```lean
theorem scaled_tail_split (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (N L : ℕ) :
    (2 : ℝ) ^ L * binaryCoeffTail c N =
      (windowPrefix c N L : ℝ) + binaryCoeffTail c (N + L)
```

<a id="lem-gperiod-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `generic_tail_period` | [E249_02/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L100) | [PaperStatementsAW.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L34) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `scaled_tail_split` | [E249_02/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L113) | [PaperStatementsAW.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L45) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-gamma"></a>

## Theorem (A rational sequence agreeing with any finite totient prefix)

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
> *Hence for every $`B`$ there is a coefficient sequence in the same class, agreeing with $`\varphi`$ on all of $`[1,B]`$, whose quantified condition is false. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodel.lean#L15)

```lean
theorem gamma_le (B P n : ℕ) : gamma B P n ≤ n
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_prefix`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodel.lean#L21)

```lean
theorem gamma_prefix (B P n : ℕ) (hn : n ≤ B) : gamma B P n = Nat.totient n
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.discrepancy_prefix`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodel.lean#L24)

```lean
theorem discrepancy_prefix (B P h N L : ℕ) (hB : N + h + L ≤ B) :
    GenericTailCertificates.discrepancy (gamma B P) h N L =
      GenericTailCertificates.discrepancy Nat.totient h N L
```

4. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodel.lean#L108)

```lean
theorem exact_series (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = 2 -
      (∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℝ) / 2 ^ n) -
      1 / ((2 : ℝ) ^ P - 1)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.value_cast`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L31)

```lean
theorem value_cast (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = (value B P : ℝ)
```

6. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_denominator`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L39)

```lean
theorem exact_denominator (B P : ℕ) (hBP : B < P) :
    ∃ e ≤ B, (value B P).den = 2 ^ e * (2 ^ P - 1)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.no_certificate_after_prefix`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L51)

```lean
theorem no_certificate_after_prefix (B P : ℕ) (hBP : B < P) :
    ∀ N : ℕ, B ≤ N → ∀ L : ℕ, ¬ GenericTailCertificates.certificate (gamma B P) P N L
```

8. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_not_separation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L69)

```lean
theorem gamma_not_separation (B P : ℕ) (hBP : B < P) : ¬ separation (gamma B P)
```

<a id="thm-gamma-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `gamma_le` | [E249_02/Challenge.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L140) | [PaperStatementsAE.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L129) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `gamma_prefix` | [E249_02/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L146) | [PaperStatementsAE.lean, line 133](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L133) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `discrepancy_prefix` | [E249_02/Challenge.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L131) | [PaperStatementsAE.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L122) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `exact_series` | [E249_02/Challenge.lean, line 85](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L85) | [PaperStatementsAW.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L22) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `value_cast` | [E249_02/Challenge.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L91) | [PaperStatementsAW.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAW.lean#L27) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `exact_denominator` | [E249_02/Challenge.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L136) | [PaperStatementsAE.lean, line 126](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L126) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `no_certificate_after_prefix` | [E249_02/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L149) | [PaperStatementsAE.lean, line 135](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L135) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `gamma_not_separation` | [E249_02/Challenge.lean, line 143](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L143) | [PaperStatementsAE.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L131) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |

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

## Corollary (The limit of a finite-prefix argument)

> *No proof rule uniform over all $`c:\mathbb{N}\to\mathbb{N}`$ with $`c(n)\le n`$ can establish $`\mathrm{Sep}`$ from a single fixed prefix $`\{c(n):n\le B\}`$: Theorem <a href="#thm:gamma" data-reference-type="ref" data-reference="thm:gamma">13</a> supplies a rational countermodel with that same prefix. This does *not* invalidate an argument that uses the fixed arithmetic sequence $`\varphi`$ together with compatible information at arbitrarily large horizons; the theorem gives a different $`\gamma_B`$ for each $`B`$, not one sequence agreeing with $`\varphi`$ at every $`B`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.no_uniform_prefix_rule`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L74)

```lean
theorem no_uniform_prefix_rule (B : ℕ) :
    ¬ (∀ c : ℕ → ℕ, (∀ n, c n ≤ n) → (∀ n, n ≤ B → c n = Nat.totient n) → separation c)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_not_separation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FinitePrefixCountermodelEndpoint.lean#L69)

```lean
theorem gamma_not_separation (B P : ℕ) (hBP : B < P) : ¬ separation (gamma B P)
```

<a id="cor-b1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `no_uniform_prefix_rule` | [E249_02/Challenge.lean, line 153](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L153) | [PaperStatementsAE.lean, line 138](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L138) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |
| `gamma_not_separation` | [E249_02/Challenge.lean, line 143](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L143) | [PaperStatementsAE.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAE.lean#L131) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b2"></a>

## Proposition (Three particular equivalences)

> 1.  **Certificate completeness.* The complete residue tests considered here are equivalent to the corresponding nonintegrality assertions. Rewriting the quantified condition using one of these equivalences does not weaken it ([`periodMultipleKillSupply_iff_irrational`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L432), forward at `:132`, converse at `:143`).*
> 
> 2.  **A selectable two-point sample.* The condition is as follows. For every $`h\ge1`$ and $`X_0`$, choose $`X,L\in\mathbb{N}`$ with $`X\ge\max(X_0,1)`$ and $`16(2X+h+L+2)\le2^L`$, a nonempty set $`T\subseteq[X,2X)\cap\mathbb{N}`$, a set $`P\subseteq T\times T`$ of ordered pairs, and a real number $`\delta\ge0`$. With $`E_N=\exp(2\pi iD(h,N,L)/2^L)`$, require
>     ``` math
>     |E_i-E_j|\ge\delta\quad((i,j)\in P),\qquad
>        \frac{2|T|^2}{5}\le |P|\delta^2.
>     ```
>     This condition is equivalent to irrationality. For the converse, irrationality and the doubling map allow $`T=\{N,N+1\}`$ and $`P=\{(N,N+1),(N+1,N)\}`$ at arbitrarily large $`N`$, with $`\delta=9/10`$. The numerical requirement is then $`8/5\le2(9/10)^2`$. The freedom to select $`T`$ matters: this is not an estimate on a sample prescribed in advance, such as all prime positions.*
> 
>     *Formal sources: [`Erdos249257.dtwWindowSeparatedPairs_iff_irrational_totient_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/PivotAntiReconstruction.lean#L1765)*
> 
> 3.  **Four integral tail differences.* For $`H\ge0`$ and positive integers $`p,q`$, the conjunction
>     ``` math
>     R_{2kH}-R_{kH}\in\mathbb{Z}\qquad(k\in\{1,p,q,pq\})
>     ```
>     is equivalent to $`R_{2H}-R_H\in\mathbb{Z}`$ alone. The affine transport identity for $`H\mapsto kH`$ preserves integrality, so the three additional conditions add no restriction. Neither $`p`$ nor $`q`$ need be prime ([`Erdos249257.fullTarget_primeAdjunction_diamond_iff_root`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/FullTargetPrimeAdjunctionNoGo.lean#L196)).*
> 
> *These three equivalences explain why these particular reformulations retain the original arithmetic question. They do not rule out useful weaker intermediate lemmas. The full-block and fixed-margin conditions in §<a href="#sec:survivors" data-reference-type="ref" data-reference="sec:survivors">3</a> ask for additional quantitative information that the three arguments above do not supply. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.three_particular_equivalences`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ThreeParticularEquivalences.lean#L33)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.two_point_sample_numerical_requirement`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ThreeParticularEquivalences.lean#L55)

```lean
theorem two_point_sample_numerical_requirement :
    2 * ((2 : ℝ)) ^ 2 / 5 = 8 / 5 ∧ (8 : ℝ) / 5 ≤ 2 * (9 / 10) ^ 2
```

<a id="prop-b2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `three_particular_equivalences` | [E249_03/Challenge.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_03/Challenge.lean#L86) | [PaperStatementsAU.lean, line 439](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_03/PaperStatementsAU.lean#L439) | [E249_03](../evidence/comparator/replay-35882032091/receipt-E249_03.json) |
| `two_point_sample_numerical_requirement` | [E249_03/Challenge.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_03/Challenge.lean#L37) | [PaperStatementsAK.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_03/PaperStatementsAK.lean#L99) | [E249_03](../evidence/comparator/replay-35882032091/receipt-E249_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b4"></a>

## Proposition (Failure of a specified two-adic congruence construction)

> *A certificate requires the residue to lie farther than $`N+h+L+2`$ from either endpoint modulo $`2^L`$. In the specific construction below, a pulse places the residue at $`2^{K-1}`$ modulo $`2^K`$, but the defining congruence is $`p\equiv1+2^{K-1}\pmod{2^K}`$. Hence $`p\ge1+2^{K-1}`$. At $`N=p-K`$, $`h=H`$, and $`L=K`$, the error bound is $`p+H+2>2^{K-1}`$, so the residue does not satisfy the certificate inequalities. This calculation defeats this construction at every depth. It does not prove a corresponding statement for every use of the Chinese Remainder Theorem or every prescribed totient pattern. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span> [`Erdos257PeriodNoncollapse.exists_prime_deltaTotient_twoAdic_pulseBlock`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTwoAdicPulseBlock.lean#L211) [`Erdos257PeriodNoncollapse.windowDiscrepancy_modEq_half_of_twoAdic_pulse`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTwoAdicPulseBlock.lean#L262)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_construction_never_certifies`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseCertificateFailure.lean#L29)

```lean
theorem twoAdic_pulse_construction_never_certifies
    (H K : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, p.Prime ∧ H + K < p ∧ 2 ^ (K - 1) < p ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ¬ certifiedKill H (p - K) K
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_defining_congruence`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseCertificateFailure.lean#L60)

```lean
theorem twoAdic_pulse_defining_congruence (H K B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧ 1 + 2 ^ (K - 1) ≤ p
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.twoAdic_pulse_error_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseCertificateFailure.lean#L85)

```lean
theorem twoAdic_pulse_error_bound (H K p : ℕ) (hKp : K ≤ p)
    (hp : 2 ^ (K - 1) < p) :
    (p - K) + H + K + 2 = p + H + 2 ∧ 2 ^ (K - 1) < p + H + 2
```

<a id="prop-b4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `twoAdic_pulse_construction_never_certifies` | [E249_03/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_03/Challenge.lean#L99) | [PaperStatementsAU.lean, line 482](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_03/PaperStatementsAU.lean#L482) | [E249_03](../evidence/comparator/replay-35882032091/receipt-E249_03.json) |
| `twoAdic_pulse_defining_congruence` | [E249_03/Challenge.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_03/Challenge.lean#L27) | [PaperStatementsAK.lean, line 82](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_03/PaperStatementsAK.lean#L82) | [E249_03](../evidence/comparator/replay-35882032091/receipt-E249_03.json) |
| `twoAdic_pulse_error_bound` | [E249_03/Challenge.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_03/Challenge.lean#L32) | [PaperStatementsAK.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_03/PaperStatementsAK.lean#L86) | [E249_03](../evidence/comparator/replay-35882032091/receipt-E249_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b5"></a>

## Proposition (Information lost by specific carry descriptions)

> 1.  *Fix $`m\ge2`$ and write $`R=\lfloor(m+1)/2\rfloor`$. For $`r=0,\ldots,R`$, let $`c_r`$ vanish except at $`c_r(m)=R-r`$ and $`c_r(m+1)=2r`$. Each sequence satisfies $`0\le c_r(n)\le n`$, has the same binary sum $`R2^{-m}`$, and has the same coefficients and scaled tails before position $`m`$. Its scaled tail at position $`m`$ is $`r`$. The common history therefore does not determine that tail. A finite set of labels that determines the tail for each member of this family must contain at least $`R+1=\lfloor(m+1)/2\rfloor+1`$ elements, one for each value of $`r`$ ([`Erdos249257.balancedPulse_no_autonomous_decoder`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L247)).*
> 
> 2.  *Reduction modulo $`2^L`$ forgets the initial value after the same $`L`$ recurrence steps: two affine binary orbits with different seeds satisfy $`\mathrm{orbit}_u(L) - \mathrm{orbit}_v(L) = 2^{L}(u_0 - v_0)`$, so the endpoint residue mod $`2^{L}`$ is independent of the initial carry ([`Erdos249257.affineBinaryOrbit_mod_twoPow_eq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L307)).*
> 
> 3.  *Fix a precision $`u\ge1`$, a finite list of nonnegative valuations $`\nu_j`$ and odd integers $`a_j`$, and an initial integer $`e_0`$. There are integers $`z_j`$ such that
>     ``` math
>     c_j=2^{\nu_j}(a_j+2^u z_j),\qquad
>        e_{j+1}=2e_j+c_j,\qquad |e_{j+1}|\le2^{\nu_j+u-1}.
>     ```
>     At each step, choose the centred representative of $`2e_j+2^{\nu_j}a_j`$ modulo $`2^{\nu_j+u}`$ ([`Erdos249257.fixedPrecisionTropicalNoGo`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TropicalCurvatureCarry.lean#L137)). The unrestricted integers $`z_j`$ are essential: the assertion does not prescribe the full coefficients $`c_j`$.*
> 
> *These statements exclude decoders using only the specified common history, distinctions using only the endpoint residue, and contradictions using only the stated local symbols. They do not prove that the actual totient expansion cannot be studied by automata. A proposed application must verify that it uses no additional arithmetic information that the comparison families fail to preserve. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_common_history`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L93)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_tail_at`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L30)

```lean
theorem balancedPulse_tail_at (m r : ℕ) (hm : 2 ≤ m)
    (hr : r ≤ balancedPulseRadius m) :
    binaryCoeffTail (balancedPulseCoeff m r) m = (r : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L76)

```lean
theorem balancedPulse_series (m : ℕ) (hm : 2 ≤ m) (r : ℕ)
    (hr : r ≤ balancedPulseRadius m) :
    binaryCoeffSeries (balancedPulseCoeff m r)
      = (balancedPulseRadius m : ℝ) / 2 ^ m
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_label_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L114)

```lean
theorem balancedPulse_label_lower_bound {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ) (decode : Λ → ℕ)
    (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_no_decoder_from_common_state`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L122)

```lean
theorem balancedPulse_no_decoder_from_common_state
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.affineBinaryOrbit_difference_and_reset`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L134)

```lean
theorem affineBinaryOrbit_difference_and_reset (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L = (2 : ℤ) ^ L * (u0 - v0)
      ∧ affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L]
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.fixed_precision_carry_completion`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L146)

```lean
theorem fixed_precision_carry_completion (u : ℕ) (hu : 0 < u)
    (symbols : List VUSymbol) (hodd : ∀ σ ∈ symbols, Odd σ.unit) (e : ℤ) :
    ∃ states : List ℤ,
      VUOrbit u e symbols states ∧
      List.Forall₂ (fun σ e' => |e'| ≤ vuRadius u σ) symbols states
```

<a id="prop-b5-comparator"></a>

**Comparator:** not yet compared.

<a id="prop-b6"></a>

## Proposition (Four limits of particular linear constructions)

> *The following four constructions have different limitations. They must not be read as a claim that every finite family of totient sections is independent: the full family has the explicit relations described in the short paper.*
> 
> 1.  **Dyadic sections and an integer identity.* The retained family of $`2^e+1`$ dyadic sections is linearly independent over $`\mathbb{Q}`$ for $`e\ge1`$ (Proposition <a href="#prop:rank" data-reference-type="ref" data-reference="prop:rank">6</a>). Separately, positive integers $`Q,v`$ and integers $`A,b`$ cannot satisfy
>     ``` math
>     A\ne0,\qquad QvA=b,\qquad |b|<Qv,
>     ```
>     because $`|A|\ge1`$ gives $`|b|\ge Qv`$ ([`Erdos249257.false_of_compressedAdjointCertificate`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L1183)). This elementary incompatibility concerns the displayed requirements; it does not exclude every argument using an adjugate matrix.*
> 
> 2.  **Möbius incidence.* $`U_N(i,j) = \mu((i{+}1)/(j{+}1))`$ when $`(j{+}1) \mid (i{+}1)`$ and $`0`$ otherwise is lower triangular with unit diagonal, so $`\det U_N = 1`$ for every $`N`$. Hence multiplication by $`U_N`$ is injective; the corresponding coefficient transformation cannot create a nonzero vector in its kernel ([`Erdos249257.incidenceMobius_det_eq_one`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/IncidenceQuotientHermitePade.lean#L56), injectivity of the companion map at `:77`).*
> 
> 3.  **Adjugate reconstruction.* Let $`w_i\in\mathbb{Q}`$ and $`x_i\in\mathbb{N}`$ be finite families with $`\sum_i w_i\varphi(x_i)=1`$. Reconstructing each value from two tails and bounding them separately gives the error bound $`\sum_i|w_i|(3x_i+4)`$. It is at least $`3`$, since
>     ``` math
>     1\le\sum_i|w_i|\varphi(x_i)\le\sum_i|w_i|x_i.
>     ```
>     Consequently this particular bound cannot be less than $`1`$, whatever the size of the evaluation matrix ([`Erdos257PeriodNoncollapse.three_le_totientAdjugateTailCost`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailCarryPeriod.lean#L266), closure at `:307`).*
> 
> 4.  **Finite combinations of shifts.* The synthetic sequence in Observation <a href="#prop:B4b-kill" data-reference-type="ref" data-reference="prop:B4b-kill">166</a> has the prescribed differences $`a_{(q-1)H-1}=\varphi(H)`$ for $`2\le q<t`$, where $`H=\operatorname{lcm}(1,\ldots,t)`$. It is of the form $`a_i=2c_i-c_{i+1}`$, and every finite integer combination of its shifts has the same form with a correspondingly shifted state. Thus these linear operations alone do not remove the compatible carry recurrence. Their uniform bounds depend on the absolute coefficient sum, as made explicit in that observation. The construction does not assert that $`a_i`$ equals the actual totient difference at other indices.*
> 
> *A further limitation concerns quotients of the finite sums $`t(Y,r)=\sum_{d=1}^{Y}\mu(d)/(2^d-1)^r`$. For $`e\ge1`$ and $`Y\ge4`$,
> ``` math
> \frac{t(Y,e+2)^2}{t(Y,2e+2)}-(S-\tfrac12)>\frac1{480}.
> ```
> The proof bounds each infinite sum $`\sum_{d\ge1}\mu(d)/(2^d-1)^r`$, $`r\ge3`$, between $`1429/1512`$ and $`1`$, and its truncation error after $`Y\ge4`$ terms by $`1/3584`$. Thus the lower bound holds for every stated pair $`e,Y`$, not just a finite list of computed examples ([`rankOneSubrankQuotient_sub_theta_two_gt`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L238)). These results concern the listed matrices, estimates, and comparison sequence. The fourth item has the explicit construction and source theorem given in Observation <a href="#prop:B4b-kill" data-reference-type="ref" data-reference="prop:B4b-kill">166</a>; it has not been replayed here. A different finite-dimensional argument, or one using further arithmetic assumptions, is not excluded. Proposition <a href="#prop:period-not-rank" data-reference-type="ref" data-reference="prop:period-not-rank">7</a> is conditional on rationality of $`S`$ and is not, by itself, a counterexample. The separate rational $`5/4`$ comparison supplies the counterexample to the generic rank bound. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_retained_dyadic_sections_independent`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L72)

```lean
theorem b6_retained_dyadic_sections_independent (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1
      ∧ LinearIndependent ℚ (canonicalTotientKernelFamily e)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_compressed_adjoint_identity_impossible`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L80)

```lean
theorem b6_compressed_adjoint_identity_impossible
    {Q v : ℕ} (hQ : 0 < Q) (hv : 0 < v) {A b : ℤ}
    (hA : A ≠ 0) (hid : (Q : ℤ) * (v : ℤ) * A = b) :
    ¬ |b| < (Q : ℤ) * (v : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_mobius_incidence_unimodular_and_injective`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L101)

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

4. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_adjugate_tail_cost_floor`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L129)

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

5. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_synthetic_sequence_prescribed_differences`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L165)

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

6. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_synthetic_shift_combinations_same_form`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L199)

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

7. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersennePrefix_eq_icc_sum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L236)

```lean
theorem b6_mobiusMersennePrefix_eq_icc_sum (Y r : ℕ) :
    mobiusMersennePrefix Y r =
      ∑ d ∈ Finset.Icc 1 Y,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / ((2 : ℝ) ^ d - 1) ^ r
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersenne_rung_estimates`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L253)

```lean
theorem b6_mobiusMersenne_rung_estimates {r Y : ℕ} (hr : 3 ≤ r) (hY : 4 ≤ Y) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r
      ∧ mobiusMersenneTheta r < 1
      ∧ |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤ (1 : ℝ) / 3584
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L262)

```lean
theorem b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half :
    mobiusMersenneTheta 2 = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FourLinearConstructionLimits.lean#L270)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `b6_retained_dyadic_sections_independent` | [E249_04/Challenge.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L92) | [PaperStatementsL.lean, line 18](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsL.lean#L18) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `b6_compressed_adjoint_identity_impossible` | [E249_03/Challenge.lean, line 192](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_03/Challenge.lean#L192) | [PaperStatementsG.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_03/PaperStatementsG.lean#L104) | [E249_03](../evidence/comparator/replay-35882032091/receipt-E249_03.json) |
| `b6_mobius_incidence_unimodular_and_injective` | [E249_04/Challenge.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L59) | [PaperStatementsK.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsK.lean#L17) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `b6_adjugate_tail_cost_floor` | [E249_03/Challenge.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_03/Challenge.lean#L182) | [PaperStatementsG.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_03/PaperStatementsG.lean#L95) | [E249_03](../evidence/comparator/replay-35882032091/receipt-E249_03.json) |
| `b6_synthetic_sequence_prescribed_differences` | [E249_03/Challenge.lean, line 254](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_03/Challenge.lean#L254) | [PaperStatementsI.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_03/PaperStatementsI.lean#L99) | [E249_03](../evidence/comparator/replay-35882032091/receipt-E249_03.json) |
| `b6_synthetic_shift_combinations_same_form` | [E249_03/Challenge.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_03/Challenge.lean#L269) | [PaperStatementsI.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_03/PaperStatementsI.lean#L115) | [E249_03](../evidence/comparator/replay-35882032091/receipt-E249_03.json) |
| `b6_mobiusMersennePrefix_eq_icc_sum` | [E249_04/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L111) | [PaperStatementsO.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsO.lean#L23) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `b6_mobiusMersenne_rung_estimates` | [E249_04/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L117) | [PaperStatementsO.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsO.lean#L28) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `b6_mobiusMersenneTheta_two_eq_totientSeries_sub_half` | [E249_04/Challenge.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L45) | [PaperStatementsJ.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsJ.lean#L20) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `b6_rankOneSubrankQuotient_sub_totientSeries_offset_gt` | [E249_03/Challenge.lean, line 198](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_03/Challenge.lean#L198) | [PaperStatementsG.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_03/PaperStatementsG.lean#L109) | [E249_03](../evidence/comparator/replay-35882032091/receipt-E249_03.json) |

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

## Proposition (The coefficient properties of the rational example)

> *The rational sequence in Proposition <a href="#prop:parity" data-reference-type="ref" data-reference="prop:parity">9</a> satisfies uniform boundedness, $`c(n)\le n`$, agreement with $`\varphi(n)`$ modulo $`2`$ at every index, and the stated separated-carry form of aperiodicity. Consequently, those properties alone cannot imply irrationality of a dyadic series. The example does not exclude arguments using further totient identities, including its multiplicative relations. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_rational_parityComparison`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalParityCountermodelProperties.lean#L28)

```lean
theorem exists_rational_parityComparison :
    ∃ c : ℕ → ℕ, ParityComparisonProperties c ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.parityComparisonProperties_do_not_imply_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalParityCountermodelProperties.lean#L37)

```lean
theorem parityComparisonProperties_do_not_imply_irrational :
    ¬ ∀ c : ℕ → ℕ, ParityComparisonProperties c →
        Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n)
```

<a id="prop-b7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_rational_parityComparison` | [E249_04/Challenge.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L139) | [PaperStatementsAJ.lean, line 301](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAJ.lean#L301) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `parityComparisonProperties_do_not_imply_irrational` | [E249_04/Challenge.lean, line 144](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L144) | [PaperStatementsAJ.lean, line 468](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAJ.lean#L468) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-shift"></a>

## Proposition (Digit-shift identity)

> *For every $`N : \mathbb{N}`$,
> ``` math
> 2^{N} \cdot S \;=\; \Phi_N + R_N,
> ```
> where $`\Phi_N := \sum_{n \le N} \varphi(n) \cdot 2^{N-n} \in \mathbb{N}`$ (the integer prefix) and $`R_N := \sum_{j \ge 0} \varphi(N+1+j)/2^{j+1}`$ (the scaled tail, $`{R}`$ in Lean). <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> [`two_pow_mul_totient_series_eq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L150)*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.two_pow_mul_totient_series_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientTailPeriodKiller.lean#L150)

```lean
theorem two_pow_mul_totient_series_eq (N : ℕ) :
    (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (totientPrefix N : ℝ) + totientTail N
```

<a id="prop-shift-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `two_pow_mul_totient_series_eq` | [E249_04/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L159) | [PaperStatementsAD.lean, line 90](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAD.lean#L90) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-farey"></a>

## Lemma (Farey gap, fully general)

> *For integers $`a,b,c,d,r,s`$ with $`b>0`$, $`d>0`$, $`bc-ad=1`$ (i.e. $`a/b`$ and $`c/d`$ are unimodular Farey neighbours), and $`as < rb`$, $`rd < cs`$ (i.e. $`r/s`$ lies strictly between them): $`b+d \le s`$. <span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> [`farey_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GapFareyBound.lean#L51)*

The Lean declaration below states this result.

[`GapFareyBound.farey_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GapFareyBound.lean#L51)

```lean
theorem farey_gap {a b c d r s : ℤ}
    (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1)
    (hleft : a * s < r * b)
    (hright : r * d < c * s) :
    b + d ≤ s
```

<a id="lem-farey-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `farey_gap` | [E249_04/Challenge.lean, line 167](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L167) | [PaperStatementsAK.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L115) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-gapwindow"></a>

## Proposition (The Farey certificate at $`K=240`$)

> *For the window $`(N,K)=(1,240)`$, put
> ``` math
> V=\left(\sum_{r=1}^{240}\varphi(1+r)2^{240-r}\right)\bmod2^{240}.
> ```
> For every $`q : \mathbb{N}`$ with
> ``` math
> 0 < q \;\le\; Q_0 := 79\,639\,646\,646\,701\,375\,323\,355\,774\,875\,831\,053 \;\;(\approx 7.96\times 10^{34}),
> ```
> ``` math
> (q \cdot V) \bmod 2^{240} \;+\; 243\,q \;<\; 2^{240}.
> ```
> This bound is *sharp*: $`q = Q_0+1 = 79\,639\,646\,646\,701\,375\,323\,355\,774\,875\,831\,054`$ is the exact first failing denominator, obtained as the denominator of the mediant of two explicit unimodular Farey neighbours. <span class="sans-serif">\[bounded\]</span> <span class="sans-serif">\[Lean\]</span> [`gap_check_window_1_240_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GapFareyBound.lean#L176) [`gap_check_window_1_240_first_failure`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GapFareyBound.lean#L225)*

The Lean declarations below together state this result.

1. [`Erdos249257.totient_carry_residue_window_1_240_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L18310)

```lean
theorem totient_carry_residue_window_1_240_eq :
    (∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r)) % 2 ^ 240
      = 1299094806818720335611738031537456208600423915562142231419225521361164904
```

2. [`GapFareyBound.gap_check_window_1_240_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GapFareyBound.lean#L176)

```lean
theorem gap_check_window_1_240_le_79639646646701375323355774875831053
    (q : ℕ) (hq : 0 < q) (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904) % 2 ^ 240 + q * 243 < 2 ^ 240
```

3. [`GapFareyBound.gap_check_window_1_240_first_failure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GapFareyBound.lean#L225)

```lean
theorem gap_check_window_1_240_first_failure :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054
```

where [`IsFirstGapFailure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GapFareyBound.lean#L44) is

```lean
def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)
```

<a id="prop-gapwindow-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totient_carry_residue_window_1_240_eq` | [E249_04/Challenge.lean, line 198](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L198) | [PaperStatementsAI.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAI.lean#L37) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `gap_check_window_1_240_le_79639646646701375323355774875831053` | [E249_04/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L175) | [PaperStatementsAK.lean, line 127](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L127) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `gap_check_window_1_240_first_failure` | [E249_01/Challenge.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L56) | [PaperStatementsAK.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAK.lean#L118) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-denom-record"></a>

## Theorem (Denominator exclusion)

> *For every $`p\in\mathbb{Q}`$ whose reduced denominator is at most $`Q_0`$,
> ``` math
> S \;\neq\; p.
> ```
> Equivalently: *if $`S`$ is rational, its reduced denominator exceeds* $`Q_0 \approx 7.96 \times 10^{34}`$. <span class="sans-serif">\[bounded\]</span> <span class="sans-serif">\[Lean\]</span> [`tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18384)*

The Lean declaration below states this result.

[`Erdos249257.tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L18384)

```lean
theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ)
```

<a id="thm-denom-record-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053` | [E249_01/Challenge.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L44) | [PaperStatementsAI.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAI.lean#L57) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-coprime"></a>

## Proposition (Fair-coin coprimality form)

> *Let $`X,Y`$ be independent random variables with $`\Pr(X=n)=\Pr(Y=n)=2^{-n}`$ for $`n \ge 1`$ (independent fair-coin waiting times). Then
> ``` math
> S \;=\; \tfrac12 \;+\; \Pr\bigl(\gcd(X,Y)=1\bigr)
> \;=\; \tfrac12 \;+\; \sum_{\substack{a,b\ge 1\\ \gcd(a,b)=1}} 2^{-(a+b)}.
> ```
> Equivalently, on the visible lattice: summing $`2^{-(a+b)}`$ over the half-open coprime pairs ($`a\ge1`$, $`b\ge0`$, $`\gcd(a,b)=1`$) recovers $`\sum_n \varphi(n)/2^n`$ exactly, with no boundary correction, because the visible-point count on the half-open antidiagonal at height $`n`$ equals $`\varphi(n)`$ for every $`n`$, including $`n=0,1`$. <span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> [`tsum_visible_coprime_pairs_eq_totient_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18544) [`totient_series_eq_half_add_visible_coprime_pairs`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18557)*

The Lean declarations below together state this result.

1. [`Erdos249257.tsum_visible_coprime_pairs_eq_totient_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L18544)

```lean
theorem tsum_visible_coprime_pairs_eq_totient_series :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n
```

2. [`Erdos249257.totient_series_eq_half_add_visible_coprime_pairs`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L18557)

```lean
theorem totient_series_eq_half_add_visible_coprime_pairs :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = 1 / 2 + ∑' p : ℕ × ℕ, (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
```

<a id="prop-coprime-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_visible_coprime_pairs_eq_totient_series` | [E249_04/Challenge.lean, line 216](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L216) | [PaperStatementsAI.lean, line 61](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAI.lean#L61) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `totient_series_eq_half_add_visible_coprime_pairs` | [E249_04/Challenge.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L203) | [PaperStatementsAI.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAI.lean#L46) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-gcdlayer"></a>

## Proposition (The gcd-layer normalisation)

> *For independent fair-coin waiting times as above, $`\sum_{g\ge1}\Pr(\gcd(X,Y)=g)=1`$ exactly; and for every $`d>0`$, $`\Pr(d\mid X \wedge d\mid Y) = 1/(2^d-1)^2`$. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> [`tsum_pos_coprime_inv_mersenne_eq_one`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L349) [`tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L266)*

The Lean declarations below together state this result.

1. [`GeometricCoprimality.tsum_gcd_layer_pos_coprime_half_eq_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GeometricCoprimality.lean#L480)

```lean
theorem tsum_gcd_layer_pos_coprime_half_eq_one :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = 1
```

2. [`GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GcdMomentCalculus.lean#L266)

```lean
theorem tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2
```

<a id="prop-gcdlayer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_gcd_layer_pos_coprime_half_eq_one` | [E249_04/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L186) | [PaperStatementsAK.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L156) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq` | [E249_04/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L180) | [PaperStatementsAK.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L145) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-denomcoprime"></a>

## Theorem (Denominator exclusion for the coprimality-probability form)

> *Let
> ``` math
> Q_1 := \left\lfloor \frac{Q_0}{2} \right\rfloor = 39\,819\,823\,323\,350\,687\,661\,677\,887\,437\,915\,526.
> ```
> For every $`a\in\mathbb{Z}`$, $`d\in\mathbb{N}`$ with $`0<d\le Q_1`$: the visible coprime-pair probability $`\Pr(\gcd(X,Y)=1)`$ is not equal to $`a/d`$. <span class="sans-serif">\[bounded\]</span> <span class="sans-serif">\[Lean\]</span> [`tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18572)*

The Lean declaration below states this result.

[`Erdos249257.tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L18572)

```lean
theorem tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 39819823323350687661677887437915526 →
      (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
        ≠ (a : ℝ) / (d : ℝ)
```

<a id="thm-denomcoprime-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526` | [E249_04/Challenge.lean, line 222](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L222) | [PaperStatementsAI.lean, line 66](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAI.lean#L66) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-denommobsq"></a>

## Theorem (Denominator exclusion for the Möbius-square form)

> *With $`Q_1`$ as in Theorem <a href="#thm:denomcoprime" data-reference-type="ref" data-reference="thm:denomcoprime">42</a>: for every $`a\in\mathbb{Z}`$, $`d\in\mathbb{N}`$ with $`0<d\le Q_1`$, the signed series $`T := \sum_{m\ge1} \mu(m)/(2^m-1)^2 = S - \tfrac12`$ (see §<a href="#ssec:mobius" data-reference-type="ref" data-reference="ssec:mobius">5.5</a>) is not equal to $`a/d`$. <span class="sans-serif">\[bounded\]</span> <span class="sans-serif">\[Lean\]</span> [`tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18487)*

The Lean declaration below states this result.

[`Erdos249257.tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L18487)

```lean
theorem tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 39819823323350687661677887437915526 →
      (∑' k : ℕ+, ((ArithmeticFunction.moebius (k : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (k : ℕ) - 1) ^ 2)
        ≠ (a : ℝ) / (d : ℝ)
```

<a id="thm-denommobsq-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526` | [E249_04/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L209) | [PaperStatementsAI.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAI.lean#L51) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-mobsq"></a>

## Proposition (Möbius-square reduction)

> *``` math
> S \;=\; \sum_{n\ge1}\frac{\varphi(n)}{2^n} \;=\; \frac12 \;+\; \sum_{d\ge1}\frac{\mu(d)}{(2^d-1)^2},
> ```
> where $`\mu`$ is the Möbius function, so $`\mu(d)\in\{-1,0,1\}`$ for every $`d`$. Consequently *Erdős \#249 $`\iff`$ $`T:=\sum_{d\ge1}\mu(d)/(2^d-1)^2 \notin \mathbb{Q}`$*, since adding a rational number does not change irrationality. <span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> [`totientSeries_eq_pnat_half_pow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L72) [`tsum_totient_half_pow_eq_half_add_moebius_sq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneLambertLadder.lean#L665)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.mobius_square_reduction`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/MobiusSquareReduction.lean#L10)

```lean
theorem mobius_square_reduction :
    totientSeries = (1 : ℝ) / 2 +
      ∑' d : ℕ+, (ArithmeticFunction.moebius (d : ℕ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.irrational_totient_iff_mobius_square`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/MobiusSquareReduction.lean#L17)

```lean
theorem irrational_totient_iff_mobius_square :
    Irrational totientSeries ↔
      Irrational (∑' d : ℕ+, (ArithmeticFunction.moebius (d : ℕ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.moebius_three_values`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/MobiusSquareReduction.lean#L25)

```lean
theorem moebius_three_values (d : ℕ) :
    ArithmeticFunction.moebius d = -1 ∨ ArithmeticFunction.moebius d = 0 ∨
      ArithmeticFunction.moebius d = 1
```

<a id="prop-mobsq-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mobius_square_reduction` | [E249_04/Challenge.lean, line 242](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L242) | [PaperStatementsAY.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAY.lean#L65) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `irrational_totient_iff_mobius_square` | [E249_04/Challenge.lean, line 236](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L236) | [PaperStatementsAY.lean, line 60](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAY.lean#L60) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `moebius_three_values` | [E249_04/Challenge.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L134) | [PaperStatementsAJ.lean, line 116](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAJ.lean#L116) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-lambertengine"></a>

## Proposition (The squared-Lambert identity)

> *For $`w:\mathbb{N}\to\mathbb{R}`$ with $`|w(d)|\le d`$ for all $`d>0`$, and $`0\le r<1`$:
> ``` math
> \sum_{d\ge1} w(d)\left(\frac{r^d}{1-r^d}\right)^2 \;=\; \sum_{n\ge1}\left(\sum_{e\mid n} w(e)\Bigl(\tfrac{n}{e}-1\Bigr)\right) r^n.
> ```
> <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> [`tsum_lambert_linear_weight_sq_pure`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L105)*

The Lean declaration below states this result.

[`GcdMomentCalculus.tsum_lambert_linear_weight_sq_pure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GcdMomentCalculus.lean#L105)

```lean
theorem tsum_lambert_linear_weight_sq_pure
    (w : ℕ → ℝ) (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * ((((n : ℕ) / e : ℕ) : ℝ) - 1))
          * r ^ (n : ℕ)
```

<a id="prop-lambertengine-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_lambert_linear_weight_sq_pure` | [E249_05/Challenge.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L54) | [PaperStatementsAK.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAK.lean#L134) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-zetaq"></a>

## Proposition (The divisor-sum identity)

> *``` math
> \sum_{d\ge1} \frac{1}{(2^d-1)^2} \;=\; \sum_{n\ge1} \frac{\sigma(n)-\tau(n)}{2^n} \;=\; \zeta_q(2)-\zeta_q(1) \text{ at } q=\tfrac12,
> ```
> where $`\sigma`$ is the sum-of-divisors function and $`\tau`$ the number-of-divisors function. The *identity* is machine-checked (<span class="sans-serif">\[Lean\]</span>). With $`\zeta_q(s)=\sum_{n\ge1}n^{s-1}q^n/(1-q^n)`$, Postelmans and Van Assche prove that $`1,\zeta_q(1),\zeta_q(2)`$ are linearly independent over $`\mathbb{Q}`$ for $`q=1/p`$ with an integer $`p\ge2`$ \[postelmans-vanassche, Theorem 1.3, p. 3\]; at $`q=\tfrac12`$ this gives the irrationality of the *value* $`\zeta_q(2)-\zeta_q(1)`$ (<span class="sans-serif">\[Cited\]</span>, *not* formalised in this corpus). Two irrational numbers can have a rational difference, so the separate irrationality of the two values would not suffice. <span class="sans-serif">\[n/a\]</span> [`tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L216)*

The Lean proof assumes the linear independence theorem of Postelmans and Van Assche, stated in Lean as `PostelmansVanAssche.q_Pade_linear_independence`; that input is not proved in Lean.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.divisor_sum_identity`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquaredMersenneDivisorIdentities.lean#L36)

```lean
theorem divisor_sum_identity :
    ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          (((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℝ)
            - ((ArithmeticFunction.sigma 0 (n : ℕ) : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.qZeta`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L17)

```lean
def qZeta (q : ℝ) (s : ℕ) : ℝ :=
  ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ (s - 1) * (q ^ (n : ℕ) / (1 - q ^ (n : ℕ)))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.qZeta_half_two_sub_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L81)

```lean
theorem qZeta_half_two_sub_one :
    qZeta ((1 : ℝ) / 2) 2 - qZeta ((1 : ℝ) / 2) 1
      = ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_qZeta_half_difference_of_linearIndependent`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L143)

```lean
theorem irrational_qZeta_half_difference_of_linearIndependent
    (hli : ∀ a b c : ℚ,
      (a : ℝ) * 1 + (b : ℝ) * qZeta ((1 : ℝ) / 2) 1
        + (c : ℝ) * qZeta ((1 : ℝ) / 2) 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    Irrational (qZeta ((1 : ℝ) / 2) 2 - qZeta ((1 : ℝ) / 2) 1)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_irrational_pair_with_rational_difference`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L125)

```lean
theorem exists_irrational_pair_with_rational_difference :
    ∃ x y : ℝ, Irrational x ∧ Irrational y ∧ x ≠ y ∧ ¬ Irrational (x - y)
```

<a id="prop-zetaq-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="prop-pillai"></a>

## Proposition (The gcd-moment identity)

> *``` math
> \sum_{d\ge1} \frac{\varphi(d)}{(2^d-1)^2} \;=\; \sum_{n\ge1} \bigl(P(n)-n\bigr)\cdot 2^{-n} \;=\; \mathbb{E}[\gcd(X,Y)],
> ```
> where $`P(n) := \sum_{e\mid n}\varphi(e)\cdot(n/e) = (\varphi * \mathrm{Id})(n)`$ is Pillai’s gcd-sum function $`P(n)=\sum_{k\le n}\gcd(k,n)`$ \[toth-gcd, §1, (1)–(2)\] and $`X,Y`$ are the independent fair-coin waiting times of Proposition <a href="#prop:coprime" data-reference-type="ref" data-reference="prop:coprime">40</a>. The identity itself is machine-checked (<span class="sans-serif">\[Lean\]</span>); irrationality of $`\mathbb{E}[\gcd(X,Y)]`$ is not proved here. This is a different series from $`S`$. <span class="sans-serif">\[n/a\]</span> [`tsum_totient_div_mersenne_sq_eq_gcd_moment_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L235)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.gcd_moment_identity_three_members`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L334)

```lean
theorem gcd_moment_identity_three_members :
    (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' n : ℕ+, (((pillaiP (n : ℕ) : ℕ) : ℝ) - ((n : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ))
      ∧ (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
            then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L307)

```lean
theorem tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
        then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_gcd_Icc_eq_pillaiP`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L77)

```lean
theorem sum_gcd_Icc_eq_pillaiP (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, Nat.gcd k n = pillaiP n
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.pillaiP_eq_totient_mul_id`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L67)

```lean
theorem pillaiP_eq_totient_mul_id (n : ℕ) :
    (totientArith * ArithmeticFunction.id) n = pillaiP n
```

5. [`GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GcdMomentCalculus.lean#L235)

```lean
theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ)
```

<a id="prop-pillai-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `gcd_moment_identity_three_members` | [E249_05/Challenge.lean, line 137](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L137) | [PaperStatementsAE.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L218) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq` | [E249_05/Challenge.lean, line 154](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L154) | [PaperStatementsAE.lean, line 335](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L335) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `sum_gcd_Icc_eq_pillaiP` | [E249_05/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L150) | [PaperStatementsAE.lean, line 295](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L295) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `pillaiP_eq_totient_mul_id` | [E249_05/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L146) | [PaperStatementsAE.lean, line 263](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L263) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `tsum_totient_div_mersenne_sq_eq_gcd_moment_series` | [E249_05/Challenge.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L62) | [PaperStatementsAK.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAK.lean#L150) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a9"></a>

## Theorem (Rationality gives an eventual tail period)

> *If $`S=a/(2^cv)`$ with $`a\in\mathbb Z`$, $`c\in\mathbb N`$ and $`v`$ a positive odd integer, then
> ``` math
> R_{N+h}-R_N\in\mathbb Z\qquad(N\ge c),\qquad h=\varphi(v)>0.
> ```
> Euler’s theorem gives $`v\mid2^h-1`$, and the prefix-tail identity then makes $`2^N(2^h-1)S`$ integral. Thus rationality supplies a positive shift for which all sufficiently late tail differences are integral.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`eventual_period_of_not_irrational`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L358)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR20.specified_euler_tail_period`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/SpecifiedTailPeriod.lean#L44)

```lean
theorem specified_euler_tail_period
    (a : ℤ) (c v : ℕ) (hv : 0 < v) (hodd : Odd v)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      (a : ℝ) / ((2 : ℝ) ^ c * (v : ℝ))) :
    0 < Nat.totient v ∧ ∀ N : ℕ, c ≤ N →
      totientTail (N + Nat.totient v) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ)
```

<a id="catalogue-cert-a9-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `specified_euler_tail_period` | [E249_05/Challenge.lean, line 166](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L166) | [PaperStatementsAX.lean, line 256](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAX.lean#L256) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d5"></a>

## Theorem (Rationality forces unbounded carry rank)

> *If $`S\in\mathbb Q`$, there are an integer $`v>0`$ and an integer sequence $`u`$ such that
> ``` math
> u(N+1)=2u(N)-v\varphi(N+1),\qquad u(N)/2^N\longrightarrow0,
> ```
> and, for every $`e\ge0`$, the sequences $`n\mapsto u(2^jn+r)`$ with $`1\le j\le e`$ and $`0\le r<2^j`$ span a space of $`\mathbb Q`$-dimension at least $`2^e-1`$.*
> 
> *The recurrence is the one obtained from the scaled tails after clearing a hypothetical denominator of $`S`$. The formal term *tempered* means exactly $`u(N)/2^N\to0`$ here, not a separate assumption of subexponential growth. This rank lower bound is a necessary consequence of rationality, not a contradiction. An upper bound using additional properties of the actual totient coefficients would be needed; the later rational comparison rules out such a bound for arbitrary rational coefficient series.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientCarryKernelRigidity.lean#L300)*

The Lean declaration below states this result.

[`Erdos249257.not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientCarryKernelRigidity.lean#L300)

```lean
theorem not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e)))
```

<a id="catalogue-cert-d5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `not_irrational_totientSeries_implies_unbounded_carryRank_unconditional` | [E249_32/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_32/Challenge.lean#L94) | [CarryRankFrontier.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_32/CarryRankFrontier.lean#L44) | [E249_32](../evidence/comparator/replay-35882032091/receipt-E249_32.json) |

Challenge for `not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`:

```lean
theorem not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e))) := by sorry
```

<a id="catalogue-cert-d4"></a>

## Theorem (Independence of the retained dyadic sections)

> *For every integer $`e\ge0`$, the family
> ``` math
> \varphi(n),\quad\varphi(2n),\quad
>  \varphi(2^jn+r)\quad(1\le j\le e,\ 0<r<2^j,\ r\text{ odd})
> ```
> is linearly independent over $`\mathbb Q`$ and has $`2^e+1`$ members. At $`e=0`$ this family still contains $`\varphi(2n)`$; it is not the full level-zero truncation, which consists only of $`\varphi(n)`$. For $`e\ge1`$ it is the basis of the full truncated dyadic family.*
> 
> *The proof separates one section at a time: the Chinese remainder theorem forces suitable prime divisors in the other affine arguments, while Dirichlet’s theorem makes the selected argument prime. This proves independence, not just the displayed cardinality. In particular, the span of all dyadic sections is infinite-dimensional; that conclusion alone says nothing about rationality of their weighted sum.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`card_totientCanonicalIndex`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L61) [`linearIndependent_canonicalTotientKernelFamily`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L935)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR8.displayed_canonical_and_full_dyadic`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR8/FullKernelAssemblies.lean#L177)

```lean
theorem displayed_canonical_and_full_dyadic :
    (∀ e : ℕ, Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 ∧
      LinearIndependent ℚ (canonicalTotientKernelFamily e)) ∧
    (∃ b : Module.Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)),
      ∀ i, (b i : ℕ → ℚ) = oddCoreTotientKernelFamily i) ∧
    (∀ e : ℕ, 1 ≤ e → Module.finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1) ∧
    Module.finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily 2 0))) = 1
```

<a id="catalogue-cert-d4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `displayed_canonical_and_full_dyadic` | [E249_05/Challenge.lean, line 217](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L217) | [CompleteKernelBases.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/CompleteKernelBases.lean#L71) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a8"></a>

## Proposition (Denominator divisibility forces tail integrality)

> *If $`S=a/q`$ in lowest terms with $`q>0`$ and $`q\mid2^N(2^h-1)`$, then $`R_{N+h}-R_N\in\mathbb Z`$. Indeed, the prefix identity expresses that difference as $`2^N(2^h-1)S`$ minus an integer. This is the contradiction used by a nonintegrality certificate to exclude the rational value $`a/q`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`tail_diff_int_of_den_dvd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L327)*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.tail_diff_int_of_den_dvd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientTailPeriodKiller.lean#L327)

```lean
theorem tail_diff_int_of_den_dvd (r : ℚ)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (r : ℝ))
    (h N : ℕ) (hdvd : (r.den : ℕ) ∣ 2 ^ N * (2 ^ h - 1)) :
    totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)
```

<a id="catalogue-cert-a8-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tail_diff_int_of_den_dvd` | [E249_05/Challenge.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L233) | [PaperStatementsAD.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAD.lean#L80) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-b5"></a>

## Proposition (A cyclotomic factor remains after cancellation)

> *If $`r`$ is squarefree, then
> ``` math
> \gcd\bigl(|P_r(2)|,|\Phi_r(2)|\bigr)=1,
>  \qquad |\Phi_r(2)|\mid\operatorname{den}(b_r).
> ```
> Here $`\Phi_r`$ is the $`r`$-th cyclotomic polynomial. Proposition <a href="#catalogue:mob:b4" data-reference-type="ref" data-reference="catalogue:mob:b4">91</a> gives $`P_r\equiv\mu(r)\pmod{\Phi_r}`$, and $`\mu(r)=\pm1`$ because $`r`$ is squarefree. This proves that the indicated cyclotomic factor cannot cancel from $`b_r`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`mobiusNumerator_gcd_cyclotomicValue`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CyclotomicProjectionOfShadow.lean#L350) [`cyclotomicValue_dvd_baseMobiusShadow_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CyclotomicProjectionOfShadow.lean#L389)*

The Lean declarations below together state this result.

1. [`Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_eval_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RepunitMobiusNumerator.lean#L445)

```lean
theorem mobiusNumeratorPolynomial_eval_two {r : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      RadicalMobiusShadow.mobiusNumerator r
```

2. [`Erdos249257.CyclotomicProjectionOfShadow.mobiusNumerator_gcd_cyclotomicValue`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CyclotomicProjectionOfShadow.lean#L350)

```lean
theorem mobiusNumerator_gcd_cyclotomicValue
    {r : ℕ} (hr : Squarefree r) :
    Nat.gcd
      (RadicalMobiusShadow.mobiusNumerator r).natAbs
      (cyclotomicValue r) = 1
```

3. [`Erdos249257.CyclotomicProjectionOfShadow.cyclotomicValue_dvd_baseMobiusShadow_den`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CyclotomicProjectionOfShadow.lean#L389)

```lean
theorem cyclotomicValue_dvd_baseMobiusShadow_den
    {r : ℕ} (hr : Squarefree r) :
    cyclotomicValue r ∣ (RadicalMobiusShadow.baseMobiusShadow r).den
```

<a id="catalogue-mob-b5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mobiusNumeratorPolynomial_eval_two` | [E249_05/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L272) | [PaperStatementsAQ.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAQ.lean#L58) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `mobiusNumerator_gcd_cyclotomicValue` | [E249_05/Challenge.lean, line 265](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L265) | [PaperStatementsAQ.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAQ.lean#L46) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `cyclotomicValue_dvd_baseMobiusShadow_den` | [E249_05/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L260) | [PaperStatementsAQ.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAQ.lean#L42) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Challenge for `mobiusNumeratorPolynomial_eval_two`:

```lean
theorem mobiusNumeratorPolynomial_eval_two {r : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      mobiusNumerator r := by sorry
```

Challenge for `mobiusNumerator_gcd_cyclotomicValue`:

```lean
theorem mobiusNumerator_gcd_cyclotomicValue
    {r : ℕ} (hr : Squarefree r) :
    Nat.gcd
      (mobiusNumerator r).natAbs
      (cyclotomicValue r) = 1 := by sorry
```

Challenge for `cyclotomicValue_dvd_baseMobiusShadow_den`:

```lean
theorem cyclotomicValue_dvd_baseMobiusShadow_den
    {r : ℕ} (hr : Squarefree r) :
    cyclotomicValue r ∣ (baseMobiusShadow r).den := by sorry
```

<a id="catalogue-mob-b6"></a>

## Proposition (Primes in the upper half remain after cancellation)

> *For $`t\ge5`$ the whole product
> ``` math
> \prod_{p\in\mathcal P_t}(2^p-1)
>        \ \mid\ \operatorname{den}(H_t\beta_{H_t})
> ```
> remains after cancellation. More generally, the source gives the same product-divisibility conclusion for a multiplier coprime to that product; it also supplies a sufficient condition on the multiplier’s prime factors. For the multiplier $`H_t/r_t`$, those prime factors are at most $`t`$, and the LCM result above follows.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`upperHalfPrimes`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L914) [`upperHalfChannel_product_dvd_den_of_scale_primeFactors_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L809) [`lcmHeight_upperHalf_product_dvd_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L983)*

The Lean declarations below together state this result.

1. [`Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmHeight_upperHalf_product_dvd_den`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L983)

```lean
theorem lcmHeight_upperHalf_product_dvd_den
    {t : ℕ} (ht : 5 ≤ t) :
    (∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p) ∣
      ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den
```

2. [`Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfChannel_product_dvd_den_of_coprime_scale`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L795)

```lean
theorem upperHalfChannel_product_dvd_den_of_coprime_scale
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hscale : Nat.Coprime
      (∏ p ∈ P, RadicalMobiusShadow.mersenne p) h) :
    (∏ p ∈ P, RadicalMobiusShadow.mersenne p) ∣
      (Rat.divInt ((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r)
        (RadicalMobiusShadow.mersenne r : ℤ)).den
```

3. [`Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfChannel_product_dvd_den_of_scale_primeFactors_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L809)

```lean
theorem upperHalfChannel_product_dvd_den_of_scale_primeFactors_le
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hhcut : ∀ q : ℕ, q.Prime → q ∣ h → q ≤ t) :
    (∏ p ∈ P, RadicalMobiusShadow.mersenne p) ∣
      (Rat.divInt ((h : ℤ) * RadicalMobiusShadow.mobiusNumerator r)
        (RadicalMobiusShadow.mersenne r : ℤ)).den
```

<a id="catalogue-mob-b6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lcmHeight_upperHalf_product_dvd_den` | [E249_05/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L81) | [PaperStatementsAE.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L83) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `upperHalfChannel_product_dvd_den_of_coprime_scale` | [E249_05/Challenge.lean, line 88](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L88) | [PaperStatementsAE.lean, line 89](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L89) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `upperHalfChannel_product_dvd_den_of_scale_primeFactors_le` | [E249_05/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L100) | [PaperStatementsAE.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L100) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Challenge for `lcmHeight_upperHalf_product_dvd_den`:

```lean
theorem lcmHeight_upperHalf_product_dvd_den
    {t : ℕ} (ht : 5 ≤ t) :
    (∏ p ∈ upperHalfPrimes t, mersenne p) ∣
      ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den := by sorry
```

Challenge for `upperHalfChannel_product_dvd_den_of_coprime_scale`:

```lean
theorem upperHalfChannel_product_dvd_den_of_coprime_scale
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hscale : Nat.Coprime
      (∏ p ∈ P, mersenne p) h) :
    (∏ p ∈ P, mersenne p) ∣
      (Rat.divInt ((h : ℤ) * mobiusNumerator r)
        (mersenne r : ℤ)).den := by sorry
```

Challenge for `upperHalfChannel_product_dvd_den_of_scale_primeFactors_le`:

```lean
theorem upperHalfChannel_product_dvd_den_of_scale_primeFactors_le
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hhcut : ∀ q : ℕ, q.Prime → q ∣ h → q ≤ t) :
    (∏ p ∈ P, mersenne p) ∣
      (Rat.divInt ((h : ℤ) * mobiusNumerator r)
        (mersenne r : ℤ)).den := by sorry
```

<a id="catalogue-mob-b7a"></a>

## Proposition (A lower bound for the reduced denominator)

> *For every integer $`t\ge5`$,
> ``` math
> 2^{\lfloor t/2\rfloor}
>  \le \prod_{p\in\mathcal P_t}(2^p-1)
>  \le \operatorname{den}(H_t\beta_{H_t}).
> ```
> Bertrand’s postulate supplies a prime in $`\mathcal P_t`$; its factor is at least $`2^{\lfloor t/2\rfloor}`$. Proposition <a href="#catalogue:mob:b6" data-reference-type="ref" data-reference="catalogue:mob:b6">57</a> then gives the second inequality. The complementary term in the real tail decomposition can still cancel this rational contribution, so denominator growth alone does not prove irrationality of $`S`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`upperHalfMersenneProduct_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowDenominatorGrowth.lean#L60)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR20.upper_half_product_denominator_bounds`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/DenominatorBounds.lean#L10)

```lean
theorem upper_half_product_denominator_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ (∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p) ∧
    (∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p) ≤
      ((lcmHeight t : ℚ) * RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den
```

<a id="catalogue-mob-b7a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `upper_half_product_denominator_bounds` | [E249_05/Challenge.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L131) | [PaperStatementsAE.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L159) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Challenge for `upper_half_product_denominator_bounds`:

```lean
theorem upper_half_product_denominator_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ (∏ p ∈ upperHalfPrimes t, mersenne p) ∧
    (∏ p ∈ upperHalfPrimes t, mersenne p) ≤
      ((lcmHeight t : ℚ) * numericMobiusShadow (lcmHeight t)).den := by sorry
```

<a id="catalogue-mob-b7b"></a>

## Proposition (The exact reduced denominator)

> *At every integer scale $`t\ge0`$,
> ``` math
> \operatorname{den}(H_t\beta_{H_t})
>  =\frac{2^{r_t}-1}
>  {\gcd\!\left(2^{r_t}-1,
>        \dfrac{H_t}{r_t}
>        \prod_{\substack{p\mid r_t\\p\ \mathrm{odd\ prime}}}(p^2-1)\right)}.
> ```
> The product is $`1`$ when there is no odd prime divisor. This gives the exact cancellation, including the multiplier $`H_t/r_t`$, rather than merely a lower bound for the denominator. For example, $`H_5=60`$ and $`r_5=30`$, and the denominator is $`(2^{30}-1)/3`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`lcmHeight_scaledMobiusShadow_den_exact`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowDenominatorGrowth.lean#L147)*

The Lean declarations below together state this result.

1. [`Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_exact`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MersenneShadowDenominatorGrowth.lean#L147)

```lean
theorem lcmHeight_scaledMobiusShadow_den_exact (t : ℕ) :
    ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den =
      RadicalMobiusShadow.mersenne (lcmRadical t) /
        Nat.gcd (RadicalMobiusShadow.mersenne (lcmRadical t))
          (lcmScale t *
            (CyclicTensorMobiusShadow.oddJordanScalar (lcmRadical t)).natAbs)
```

2. [`Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_five_scaledMobiusShadow_den_exact`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MersenneShadowDenominatorGrowth.lean#L187)

```lean
theorem lcmHeight_five_scaledMobiusShadow_den_exact :
    ((lcmHeight 5 : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight 5)).den =
      RadicalMobiusShadow.mersenne 30 / 3
```

<a id="catalogue-mob-b7b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lcmHeight_scaledMobiusShadow_den_exact` | [E249_05/Challenge.lean, line 292](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L292) | [PaperStatementsAR.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAR.lean#L21) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `lcmHeight_five_scaledMobiusShadow_den_exact` | [E249_05/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L111) | [PaperStatementsAE.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L110) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Challenge for `lcmHeight_scaledMobiusShadow_den_exact`:

```lean
theorem lcmHeight_scaledMobiusShadow_den_exact (t : ℕ) :
    ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den =
      mersenne (lcmRadical t) /
        Nat.gcd (mersenne (lcmRadical t))
          (lcmScale t *
            (oddJordanScalar (lcmRadical t)).natAbs) := by sorry
```

Challenge for `lcmHeight_five_scaledMobiusShadow_den_exact`:

```lean
theorem lcmHeight_five_scaledMobiusShadow_den_exact :
    ((lcmHeight 5 : ℚ) *
        numericMobiusShadow (lcmHeight 5)).den =
      mersenne 30 / 3 := by sorry
```

<a id="catalogue-mob-d3"></a>

## Proposition (Nonvanishing of a signed dyadic sum)

> *Let $`I`$ be finite, let $`u_i\in\mathbb Z`$ and $`e_i\in\mathbb N`$, and suppose that $`m\in I`$ is the unique index with maximal exponent $`e_m`$. If $`u_m`$ is odd, then
> ``` math
> 2^{e_m}\sum_{i\in I}\frac{u_i}{2^{e_i}}
>        =\sum_{i\in I}u_i2^{e_m-e_i}\equiv1\pmod2.
> ```
> Indeed, every summand other than $`u_m`$ is even. The sum is therefore nonzero. In the determinant application, the rectangular Cauchy–Binet formula produces such finite signed sums from truncated moments. The result tests a specified configuration; it does not show that a suitable maximal-exponent term exists at arbitrarily large scales.*
> 
> *<span class="sans-serif">\[bounded\]</span> [`scaled_dyadic_sum_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SignedQMomentObstruction.lean#L96) [`det_mul_rectangular`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SignedQMomentObstruction.lean#L29)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_clearing`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/SignedDyadicClearing.lean#L8)

```lean
theorem signed_dyadic_clearing {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α)
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (2 : ℚ) ^ e m * (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) =
      ((∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i) : ℤ) : ℚ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_sum_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/SignedDyadicClearing.lean#L28)

```lean
theorem signed_dyadic_sum_ne_zero {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) ≠ 0
```

3. [`Erdos249257.SignedQMomentObstruction.scaled_dyadic_sum_odd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/SignedQMomentObstruction.lean#L78)

```lean
theorem scaled_dyadic_sum_odd {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) % 2 = 1
```

<a id="catalogue-mob-d3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `signed_dyadic_clearing` | [E249_05/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L117) | [PaperStatementsAE.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L145) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `signed_dyadic_sum_ne_zero` | [E249_05/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L124) | [PaperStatementsAE.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L152) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `scaled_dyadic_sum_odd` | [E249_06/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L81) | [PaperStatementsAF.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAF.lean#L30) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a11"></a>

## Proposition (Small certificates)

> *For each integer $`1\le h\le8`$, the finite test $`\mathcal C(h,12,16)`$ holds. Each discrepancy uses two 16-term windows. Across all eight shifts, only the 24 distinct totient values at $`13\le n\le36`$ are needed, since the windows overlap. The source verifies the eight integer residue inequalities by exact computation.*
> 
> *Consequently, if $`a/b`$ is a reduced fraction with $`b>0`$ and $`b\mid2^{12}(2^h-1)`$ for at least one $`1\le h\le8`$, then $`S\ne a/b`$. This follows from Propositions <a href="#catalogue:cert:a6" data-reference-type="ref" data-reference="catalogue:cert:a6">69</a> and <a href="#catalogue:cert:a8" data-reference-type="ref" data-reference="catalogue:cert:a8">55</a>.*
> 
> *<span class="sans-serif">\[fixed\]</span> [`certifiedKill_all_small`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L404) [`totient_series_ne_rat_of_den_dvd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L416)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.small_certificate_windows`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L33)

```lean
theorem small_certificate_windows :
    certificateWindowIndices 8 12 16 = Finset.Icc 13 36 ∧
      (certificateWindowIndices 8 12 16).card = 24
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.small_certificates_and_exclusions`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L45)

```lean
theorem small_certificates_and_exclusions :
    (∀ h ∈ Finset.Icc 1 8, certifiedKill h 12 16) ∧
    (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 8 → r.den ∣ 2 ^ 12 * (2 ^ h - 1) →
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ))
```

<a id="catalogue-cert-a11-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `small_certificate_windows` | [E249_06/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L110) | [PaperStatementsG.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsG.lean#L58) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `small_certificates_and_exclusions` | [E249_06/Challenge.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L136) | [PaperStatementsI.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsI.lean#L92) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a12"></a>

## Proposition (A common certificate for sixteen shifts)

> *For each integer $`1\le h\le16`$, one has $`\mathcal C(h,14,9)`$. The common basepoint is $`14`$ and the depth is $`9`$; these parameters have different roles. The two windows for each shift use only the 25 distinct totient values at $`15\le n\le39`$ across the whole family. Thus $`S\ne a/b`$ for every reduced fraction with $`b>0`$ such that $`b\mid2^{14}(2^h-1)`$ for at least one $`1\le h\le16`$.*
> 
> *<span class="sans-serif">\[fixed\]</span> [`totient_series_ne_rat_of_den_dvd_pow_two_mul_mersenne_upto_sixteen`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18890)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificate_windows`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L39)

```lean
theorem sixteen_certificate_windows :
    certificateWindowIndices 16 14 9 = Finset.Icc 15 39 ∧
      (certificateWindowIndices 16 14 9).card = 25
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificates_and_exclusions`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L51)

```lean
theorem sixteen_certificates_and_exclusions :
    (∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9) ∧
    (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 16 → r.den ∣ 2 ^ 14 * (2 ^ h - 1) →
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ))
```

<a id="catalogue-cert-a12-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `sixteen_certificate_windows` | [E249_06/Challenge.lean, line 105](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L105) | [PaperStatementsG.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsG.lean#L54) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `sixteen_certificates_and_exclusions` | [E249_06/Challenge.lean, line 130](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L130) | [PaperStatementsI.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsI.lean#L87) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b11"></a>

## Proposition (Historical diagonal examples and the complete band through 82)

> *Let $`H_t=\operatorname{lcm}(1,\ldots,t)`$ and let
> ``` math
> P(t)\quad:\Longleftrightarrow\quad \exists L,\ \mathcal{C}(H_t,H_t,L).
> ```
> The checked certificate table proves $`P(t)`$ at 28 explicit indices, ending at $`t=64`$. For the initial indices
> ``` math
> t=1,2,3,4,5,7,8,9,11,13,16,17,\ldots,
> ```
> the corresponding depths begin $`6,5,7,7,9,14,15,14,21,22,23,26,\ldots`$. Each entry is a finite kernel computation on explicit totient values. The factorisations use checked prime-power blocks and Lucas primality certificates. Thus the table proves a finite list of instances of $`P(t)`$; it does not prove that $`P(t)`$ holds for infinitely many $`t`$.*
> 
> *<span class="sans-serif">\[fixed\]</span> [`certifiedKill_diagonal_all_imported`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/DiagonalPincerCertificates.lean#L2870) [`diagonalPincerKillDepth`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/DiagonalPincerCertificates.lean#L2854) [`certifiedKill_diagonal_t64`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/DiagonalPincerCertificateT64Endpoint.lean#L1928)*
> 
> *The historical 28 examples are now a strict subset of the aggregate theorem $`\forall t\le82,\ P(t)`$. That theorem closes the finite interval without holes but supplies neither $`P(83)`$ nor a cofinal family.*
> 
> *<span class="sans-serif">\[bounded\]</span> [`ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Skip/LadderT67.lean#L71264)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.historical_table_size_and_initial_depths`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L57)

```lean
theorem historical_table_size_and_initial_depths :
    diagonalPincerCertificateScalesThroughT64.length = 28 ∧
    diagonalPincerCertificateScalesThroughT64.Nodup ∧
    diagonalPincerCertificateScalesThroughT64.getLast? = some 64 ∧
    ([1,2,3,4,5,7,8,9,11,13,16,17].map diagonalPincerKillDepthThroughT64) =
      [6,5,7,7,9,14,15,14,21,22,23,26]
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.historical_table_and_complete_band`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L64)

```lean
theorem historical_table_and_complete_band :
    (∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT64 t)) ∧
    (∀ t : ℕ, t ≤ 82 → ∃ L, certifiedKill (periodLcm t) (periodLcm t) L)
```

<a id="catalogue-cert-b11-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `historical_table_size_and_initial_depths` | [E249_06/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L97) | [PaperStatementsG.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsG.lean#L47) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `historical_table_and_complete_band` | [E249_06/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L124) | [PaperStatementsI.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsI.lean#L80) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a2"></a>

## Proposition (The prefix-tail identity)

> *For every $`N\in\mathbb N`$,
> ``` math
> 2^NS=\Phi_N+R_N,
>  \qquad \Phi_N=\sum_{n\le N}\varphi(n)2^{N-n}\in\mathbb Z.
> ```
> Thus $`R_N`$ and $`2^NS`$ have the same fractional part. Subtracting the identities at $`N+h`$ and $`N`$ gives the tail-difference congruence used in the irrationality criterion.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`two_pow_mul_totient_series_eq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L150)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.prefix_fractional_part`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/TailDepthCorrespondence.lean#L8)

```lean
theorem prefix_fractional_part (N : ℕ) :
    Int.fract ((2 : ℝ)^N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2^n)) =
      Int.fract (totientTail N)
```

2. [`Erdos249257.TotientTailPeriodKiller.two_pow_mul_totient_series_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientTailPeriodKiller.lean#L150)

```lean
theorem two_pow_mul_totient_series_eq (N : ℕ) :
    (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (totientPrefix N : ℝ) + totientTail N
```

3. [`Erdos249257.TotientTailPeriodKiller.tail_diff_mem_int_iff_scaled_series_mem_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L327)

```lean
theorem tail_diff_mem_int_iff_scaled_series_mem_int (h N : ℕ) :
    (totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ↔
    ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      ∈ Set.range ((↑) : ℤ → ℝ))
```

<a id="catalogue-cert-a2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `prefix_fractional_part` | [E249_06/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L180) | [PaperStatementsAT.lean, line 237](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L237) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `two_pow_mul_totient_series_eq` | [E249_04/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L159) | [PaperStatementsAD.lean, line 90](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAD.lean#L90) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `tail_diff_mem_int_iff_scaled_series_mem_int` | [E249_06/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L156) | [PaperStatementsAD.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAD.lean#L77) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a5"></a>

## Lemma (The necessary depth inequality)

> *For $`h,N,L\in\mathbb{N}`$, the condition $`\mathcal C(h,N,L)`$ implies
> ``` math
> 2(N+h+L+2)<2^L.
> ```
> Indeed, its lower residue bound must be smaller than its upper bound. Thus $`L>1+\log_2(N+h+L+2)`$ whenever a certificate holds. In particular, a fixed depth cannot accommodate unbounded $`N+h`$. This is a necessary depth bound, not an upper bound for finding a certificate.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`certifiedKill_depth_floor`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L79)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.certificate_logarithmic_depth`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/TailDepthCorrespondence.lean#L20)

```lean
theorem certificate_logarithmic_depth {h N L : ℕ} (hc : certifiedKill h N L) :
    1 + Real.logb 2 ((N : ℝ)+h+L+2) < L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.fixed_depth_bounds_indices`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/TailDepthCorrespondence.lean#L30)

```lean
theorem fixed_depth_bounds_indices {h N L : ℕ} (hc : certifiedKill h N L) :
    N + h < 2^L
```

3. [`Erdos249257.TotientTailPeriodKiller.certifiedKill_depth_floor`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientTailPeriodKiller.lean#L79)

```lean
theorem certifiedKill_depth_floor {h N L : ℕ} (hcert : certifiedKill h N L) :
    (2 * (N + h + L + 2) : ℤ) < 2 ^ L
```

<a id="catalogue-cert-a5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `certificate_logarithmic_depth` | [E249_06/Challenge.lean, line 172](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L172) | [PaperStatementsAT.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L181) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `fixed_depth_bounds_indices` | [E249_06/Challenge.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L176) | [PaperStatementsAT.lean, line 206](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L206) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `certifiedKill_depth_floor` | [E249_06/Challenge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L147) | [PaperStatementsAD.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAD.lean#L51) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a6"></a>

## Proposition (A certificate implies nonintegrality)

> *For all $`h,N,L\in\mathbb N`$,
> ``` math
> \mathcal C(h,N,L)\ \Longrightarrow\ R_{N+h}-R_N\notin\mathbb Z.
> ```
> The scaled truncation error satisfies $`|2^L(R_{N+h}-R_N)-D(h,N,L)|\le N+h+L+2`$. If the tail difference were integral, $`D(h,N,L)`$ would therefore lie within that distance of a multiple of $`2^L`$, contrary to the two strict residue inequalities.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`tail_diff_notMem_int_of_certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L262)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.totient_scaled_truncation_error`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/TailDepthCorrespondence.lean#L13)

```lean
theorem totient_scaled_truncation_error (h N L : ℕ) :
    |(2 : ℝ)^L * (totientTail (N+h) - totientTail N) -
      (windowDiscrepancy h N L : ℝ)| ≤ (N : ℝ)+h+L+2
```

2. [`Erdos249257.TotientTailPeriodKiller.tail_diff_notMem_int_of_certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientTailPeriodKiller.lean#L262)

```lean
theorem tail_diff_notMem_int_of_certifiedKill {h N L : ℕ} (hcert : certifiedKill h N L) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="catalogue-cert-a6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totient_scaled_truncation_error` | [E249_06/Challenge.lean, line 185](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L185) | [PaperStatementsAT.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L247) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `tail_diff_notMem_int_of_certifiedKill` | [E249_06/Challenge.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L163) | [PaperStatementsAD.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAD.lean#L83) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a7"></a>

## Theorem (Nonintegrality gives a certificate at some depth)

> *For every $`h,N\in\mathbb N`$,
> ``` math
> (\exists L\in\mathbb N,\ \mathcal C(h,N,L))
>  \quad\Longleftrightarrow\quad R_{N+h}-R_N\notin\mathbb Z.
> ```
> For the converse to Proposition <a href="#catalogue:cert:a6" data-reference-type="ref" data-reference="catalogue:cert:a6">69</a>, fix a positive distance from the nonintegral tail difference to the nearest integer. The normalised error $`(N+h+L+2)/2^L`$ tends to zero, so a sufficiently large truncation preserves that distance. This is a pointwise equivalence; irrationality requires the stated quantifiers over the shift and basepoint.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`exists_certifiedKill_iff_tail_diff_notMem_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmConeFlatness.lean#L316)*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.exists_certifiedKill_iff_tail_diff_notMem_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L316)

```lean
theorem exists_certifiedKill_iff_tail_diff_notMem_int (h N : ℕ) :
    (∃ L, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="catalogue-cert-a7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_certifiedKill_iff_tail_diff_notMem_int` | [E249_06/Challenge.lean, line 151](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L151) | [PaperStatementsAD.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAD.lean#L58) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-c1"></a>

## Proposition (The Farey gap lemma)

> *Let $`a,b,c,d,r,s\in\mathbb Z`$, with $`b,d>0`$ and $`bc-ad=1`$. If
> ``` math
> as<rb\quad\hbox{and}\quad rd<cs,
> ```
> then $`b+d\le s`$. The two cross-products $`rb-as`$ and $`cs-rd`$ are positive integers, and
> ``` math
> s=d(rb-as)+b(cs-rd)\ge d+b.
> ```
> In particular, a rational $`r/s`$ strictly between the Farey neighbours $`a/b`$ and $`c/d`$, with positive denominator, has denominator at least $`b+d`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`farey_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GapFareyBound.lean#L51)*

The Lean declaration below states this result.

[`GapFareyBound.farey_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GapFareyBound.lean#L51)

```lean
theorem farey_gap {a b c d r s : ℤ}
    (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1)
    (hleft : a * s < r * b)
    (hright : r * d < c * s) :
    b + d ≤ s
```

<a id="catalogue-cert-c1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `farey_gap` | [E249_04/Challenge.lean, line 167](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L167) | [PaperStatementsAK.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L115) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d1"></a>

## Proposition (An irrationality criterion from rational approximations)

> *Let $`x\in\mathbb R`$ and let $`u_k=p_k/q_k\in\mathbb Q`$ be in lowest terms, with $`q_k>0`$. If $`u_k\ne x`$ for every sufficiently large $`k`$ and $`q_k|x-u_k|\to0`$, then $`x`$ is irrational. Indeed, if $`x=a/b`$ with $`a\in\mathbb Z`$ and $`b\ge1`$, a nonzero integer numerator gives $`q_k|x-u_k|=|a q_k-b p_k|/b\ge1/b`$, a contradiction. This elementary criterion requires both nonvanishing and the scaled error estimate. Convergence $`u_k\to x`$ alone is insufficient, and the approximants need not be continued-fraction convergents.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`irrational_of_den_mul_abs_sub_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5371)*

The Lean declaration below states this result.

[`Erdos249257.irrational_of_den_mul_abs_sub_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L5371)

```lean
theorem irrational_of_den_mul_abs_sub_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in atTop, ((u k : ℝ)) ≠ x)
    (h0 : Tendsto (fun k => ((u k).den : ℝ) * |x - (u k : ℝ)|) atTop (nhds 0)) :
    Irrational x
```

<a id="catalogue-cert-d1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_den_mul_abs_sub_tendsto_zero` | [E249_06/Challenge.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L195) | [PaperStatementsAI.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L17) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d2"></a>

## Proposition (An irrationality criterion from near integers)

> *Let $`\xi\in\mathbb R`$. Suppose that for every integer $`q\ge1`$ there are integers $`m,z`$ with
> ``` math
> 0<|m\xi-z|<1/q.
> ```
> Then $`\xi`$ is irrational: if $`\xi=a/b`$ with $`b\ge1`$, every nonzero such difference is at least $`1/b`$. Restricting the multiplier to powers $`m=b_0^n`$ of a fixed integer base $`b_0\ge2`$ gives a sufficient special case, not a hypothesis satisfied by every irrational number. The strict lower bound excludes exact integer hits; the upper bound must be available for arbitrarily large $`q`$.*
> 
> *For a binary example, form a number by concatenating the blocks $`10`$ at square indices $`k\ge1`$ and $`01`$ at the other indices. Its binary expansion is not eventually periodic, since the block sequence has increasingly long gaps between the square indices, so the number is irrational. There are no three consecutive equal digits. Every fractional part after a binary shift therefore lies in $`[1/8,7/8]`$, and the multiples $`2^n\xi`$ do not approach the integers. This verifies that the restriction to base powers is genuinely stronger. This example is an ordinary mathematical argument, not an additional claim about the linked formalisation.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`irrational_of_int_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6120) [`irrational_of_pow_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6149)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.irrational_of_int_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L6120)

```lean
theorem irrational_of_int_mul_near_int {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

2. [`Erdos249257.irrational_of_pow_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L6149)

```lean
theorem irrational_of_pow_mul_near_int (b : ℕ) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_near_integer_multiples`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NearIntegerIrrationalityCriterion.lean#L16)

```lean
theorem irrational_of_near_integer_multiples {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_near_integer_base_powers`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NearIntegerIrrationalityCriterion.lean#L25)

```lean
theorem irrational_of_near_integer_base_powers (b₀ : ℕ) (hb : 2 ≤ b₀) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b₀ : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b₀ : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_le_abs_int_combination`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L33)

```lean
theorem one_div_den_le_abs_int_combination (p : ℚ) (m z : ℤ)
    (hne : (m : ℝ) * (p : ℝ) - (z : ℝ) ≠ 0) :
    (1 : ℝ) / (p.den : ℝ) ≤ |(m : ℝ) * (p : ℝ) - (z : ℝ)|
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.digit_block`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L393)

```lean
theorem digit_block (j : ℕ) :
    (IsSquare (j + 1) → digit (2 * j) = 1 ∧ digit (2 * j + 1) = 0) ∧
      (¬ IsSquare (j + 1) → digit (2 * j) = 0 ∧ digit (2 * j + 1) = 1)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_eventually_periodic`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L424)

```lean
theorem not_eventually_periodic (N P : ℕ) (hP : 0 < P) :
    ¬ ∀ k, N ≤ k → digit k = digit (k + P)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_xi`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L476)

```lean
theorem irrational_xi : Irrational xi
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.no_three_consecutive_equal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L408)

```lean
theorem no_three_consecutive_equal (n : ℕ) :
    ¬ (digit n = digit (n + 1) ∧ digit (n + 1) = digit (n + 2))
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.fract_two_pow_mul_xi_mem_Icc`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L480)

```lean
theorem fract_two_pow_mul_xi_mem_Icc (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * xi) ∈ Set.Icc (1 / 8 : ℝ) (7 / 8)
```

11. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.fract_mem_Icc_of_no_three_equal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L235)

```lean
theorem fract_mem_Icc_of_no_three_equal {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * tail d 0) ∈ Set.Icc (1 / 8 : ℝ) (7 / 8)
```

12. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_dist_xi`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L486)

```lean
theorem one_div_eight_le_dist_xi (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * xi - (z : ℝ)|
```

13. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_approaches_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L492)

```lean
theorem not_approaches_int {ε : ℝ} (hε : ε ≤ 1 / 8) :
    ¬ ∃ (n : ℕ) (z : ℤ), |(2 : ℝ) ^ n * xi - (z : ℝ)| < ε
```

14. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_near_integer_along_powers_of_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L502)

```lean
theorem not_near_integer_along_powers_of_two :
    ¬ ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
        0 < |(2 : ℝ) ^ n * xi - (z : ℝ)| ∧
          |(2 : ℝ) ^ n * xi - (z : ℝ)| < 1 / (q : ℝ)
```

15. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.exists_irrational_basePower_bounded_away`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L515)

```lean
theorem exists_irrational_basePower_bounded_away :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ (n : ℕ) (z : ℤ), (1 : ℝ) / 8 ≤ |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)|
```

16. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.strict_lower_bound_needed`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L550)

```lean
theorem strict_lower_bound_needed :
    ¬ ∀ ξ : ℝ, (∀ q : ℕ, 0 < q → ∃ m z : ℤ,
        |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) → Irrational ξ
```

17. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.upper_bound_needed_for_every_q`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L566)

```lean
theorem upper_bound_needed_for_every_q (q : ℕ) (hq : 0 < q) :
    ∃ ξ : ℝ, ¬ Irrational ξ ∧ ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)
```

18. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail_mem_Icc`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L123)

```lean
theorem tail_mem_Icc {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    1 / 8 ≤ tail d n ∧ tail d n ≤ 7 / 8
```

19. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_tail_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L269)

```lean
theorem irrational_tail_zero {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2)))
    (hper : ∀ N P : ℕ, 0 < P → ¬ ∀ k, N ≤ k → d k = d (k + P)) :
    Irrational (tail d 0)
```

20. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_abs_sub_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L243)

```lean
theorem one_div_eight_le_abs_sub_int {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * tail d 0 - (z : ℝ)|
```

<a id="catalogue-cert-d2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_int_mul_near_int` | [E249_06/Challenge.lean, line 201](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L201) | [PaperStatementsAI.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L22) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_pow_mul_near_int` | [E249_06/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L207) | [PaperStatementsAI.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L28) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_near_integer_multiples` | [E249_06/Challenge.lean, line 222](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L222) | [PaperStatementsAJ.lean, line 399](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAJ.lean#L399) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_near_integer_base_powers` | [E249_06/Challenge.lean, line 216](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L216) | [PaperStatementsAJ.lean, line 393](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAJ.lean#L393) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `one_div_den_le_abs_int_combination` | [E249_06/Challenge.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L228) | [PaperStatementsAJ.lean, line 449](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAJ.lean#L449) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `digit_block` | [E249_06/Challenge.lean, line 244](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L244) | [PaperStatementsAL.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L22) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `not_eventually_periodic` | [E249_06/Challenge.lean, line 280](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L280) | [PaperStatementsAL.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L51) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_xi` | [E249_06/Challenge.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L269) | [PaperStatementsAL.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L42) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `no_three_consecutive_equal` | [E249_06/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L272) | [PaperStatementsAL.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L44) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `fract_two_pow_mul_xi_mem_Icc` | [E249_06/Challenge.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L259) | [PaperStatementsAL.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L34) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `fract_mem_Icc_of_no_three_equal` | [E249_06/Challenge.lean, line 254](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L254) | [PaperStatementsAL.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L30) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `one_div_eight_le_dist_xi` | [E249_06/Challenge.lean, line 295](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L295) | [PaperStatementsAL.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L63) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `not_approaches_int` | [E249_06/Challenge.lean, line 276](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L276) | [PaperStatementsAL.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L47) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `not_near_integer_along_powers_of_two` | [E249_06/Challenge.lean, line 284](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L284) | [PaperStatementsAL.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L54) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `exists_irrational_basePower_bounded_away` | [E249_06/Challenge.lean, line 249](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L249) | [PaperStatementsAL.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L26) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `strict_lower_bound_needed` | [E249_07/Challenge.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L50) | [PaperStatementsAL.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAL.lean#L71) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `upper_bound_needed_for_every_q` | [E249_07/Challenge.lean, line 60](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L60) | [PaperStatementsAL.lean, line 79](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAL.lean#L79) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `tail_mem_Icc` | [E249_07/Challenge.lean, line 55](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L55) | [PaperStatementsAL.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAL.lean#L75) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `irrational_tail_zero` | [E249_06/Challenge.lean, line 263](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L263) | [PaperStatementsAL.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L37) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `one_div_eight_le_abs_sub_int` | [E249_06/Challenge.lean, line 290](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L290) | [PaperStatementsAL.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L59) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d3"></a>

## Proposition (A nonzero evaluation minor gives independence)

> *Let $`I`$ be a finite index set and let $`f_j:\mathbb N\to\mathbb Q`$ for $`j\in I`$. If there are evaluation points $`n_i\in\mathbb N`$ such that
> ``` math
> \det\bigl(f_j(n_i)\bigr)_{i,j\in I}\ne0,
> ```
> then the family $`(f_j)_{j\in I}`$ is linearly independent over $`\mathbb Q`$. A relation among the functions, evaluated at the $`n_i`$, gives a vector in the kernel of this nonsingular matrix, so all coefficients vanish. Finiteness is required to form the displayed determinant. In the totient application the arithmetic work is to construct these evaluation points; the implication itself is ordinary linear algebra.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`SeparatedMinorCertificate`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L83) [`linearIndependent_of_separatedMinorCertificate`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L91)*

The Lean declaration below states this result.

[`Erdos249257.linearIndependent_of_separatedMinorCertificate`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientMahlerDefect.lean#L91)

```lean
theorem linearIndependent_of_separatedMinorCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (family : ι → ℕ → ℚ)
    (cert : SeparatedMinorCertificate family) :
    LinearIndependent ℚ family
```

<a id="catalogue-cert-d3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `linearIndependent_of_separatedMinorCertificate` | [E249_07/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L76) | [PaperStructuresP.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStructuresP.lean#L36) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d9"></a>

## Proposition (The gap between distinct rational numbers)

> *If $`a/b<c/d`$ are reduced rational numbers with $`b,d>0`$, then
> ``` math
> \frac cd-\frac ab=\frac{bc-ad}{bd}\ge\frac1{bd}.
> ```
> The numerator $`bc-ad`$ is a positive integer. Thus an upper bound on a positive rational error gives a lower bound on the product of the reduced denominators. A large denominator in an unreduced displayed expression need not be the reduced denominator appearing in this conclusion.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`positive_rational_difference_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/PrimitiveRationalGapSupply.lean#L31)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.rational_difference_exact`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/RationalSpacingCorrespondence.lean#L6)

```lean
theorem rational_difference_exact (u v : ℚ) :
    (v : ℝ) - u =
      ((v.num * (u.den : ℤ) - u.num * (v.den : ℤ) : ℤ) : ℝ) /
        ((v.den : ℝ) * u.den)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.rational_cross_numerator_positive`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/RationalSpacingCorrespondence.lean#L17)

```lean
theorem rational_cross_numerator_positive {u v : ℚ} (h : u < v) :
    1 ≤ v.num * (u.den : ℤ) - u.num * (v.den : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.rational_error_denominator_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/RationalSpacingCorrespondence.lean#L27)

```lean
theorem rational_error_denominator_bound {u v : ℚ} {ε : ℝ}
    (h : u < v) (he : (v : ℝ) - u ≤ ε) :
    1 / ((u.den : ℝ) * ε) ≤ v.den
```

4. [`Erdos249257.positive_rational_difference_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/PrimitiveRationalGapSupply.lean#L31)

```lean
theorem positive_rational_difference_lower_bound
    {whole pfx : ℚ} (hpositive : pfx < whole) :
    (1 : ℝ) /
        (((whole.den * pfx.den : ℕ) : ℝ)) ≤
      (whole : ℝ) - (pfx : ℝ)
```

<a id="catalogue-cert-d9-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rational_difference_exact` | [E249_07/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L96) | [PaperStatementsAJ.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAJ.lean#L131) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `rational_cross_numerator_positive` | [E249_07/Challenge.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L92) | [PaperStatementsAJ.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAJ.lean#L128) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `rational_error_denominator_bound` | [E249_07/Challenge.lean, line 102](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L102) | [PaperStatementsAJ.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAJ.lean#L136) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `positive_rational_difference_lower_bound` | [E249_07/Challenge.lean, line 85](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L85) | [PaperStatementsAJ.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAJ.lean#L115) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a1a"></a>

## Proposition (The Möbius identity for $`S`$)

> *The absolutely convergent series satisfy
> ``` math
> S=\sum_{n\ge1}\frac{\varphi(n)}{2^n}
>   =\sum_{d\ge1}\frac{\mu(d)2^d}{(2^d-1)^2}
>   =\frac12+\sum_{d\ge1}\frac{\mu(d)}{(2^d-1)^2}.
> ```
> For the first rearrangement use $`\varphi(n)=\sum_{d\mid n}\mu(d)n/d`$. For the second use $`2^d=(2^d-1)+1`$ and the classical identity $`\sum_{d\ge1}\mu(d)/(2^d-1)=1/2`$. These are identities of values, not transfers of irrationality from a Lambert series with a different weight.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`tsum_totient_half_pow_eq_half_add_moebius_sq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneLambertLadder.lean#L665) [`totientSeries_eq_pnat_half_pow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L72) [`mobius_square_series_eq_partial_add_tail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SquaredMersenneDiagonalEnclosure.lean#L94)*

The Lean declarations below together state this result.

1. [`MersenneLambertLadder.tsum_moebius_lambert_sq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/MersenneLambertLadder.lean#L491)

```lean
theorem tsum_moebius_lambert_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * r ^ (n : ℕ)
```

2. [`Erdos249257.totient_series_eq_half_add_moebius_mersenne_square`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L18454)

```lean
theorem totient_series_eq_half_add_moebius_mersenne_square :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = 1 / 2 + ∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

<a id="catalogue-mob-a1a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_moebius_lambert_sq` | [E249_07/Challenge.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L122) | [PaperStatementsAP.lean, line 16](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAP.lean#L16) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `totient_series_eq_half_add_moebius_mersenne_square` | [E249_07/Challenge.lean, line 112](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L112) | [PaperStatementsAI.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAI.lean#L41) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a1b"></a>

## Corollary (An equivalent irrationality question)

> *Subtracting the rational number $`1/2`$ gives
> ``` math
> S\notin\mathbb Q
>  \quad\Longleftrightarrow\quad
>  \sum_{d\ge1}\frac{\mu(d)}{(2^d-1)^2}\notin\mathbb Q.
> ```
> This is the same irrationality question in a different series representation. The notation $`L_2(\mu)`$ for the right-hand series is introduced in Definition <a href="#catalogue:mob:a3" data-reference-type="ref" data-reference="catalogue:mob:a3">80</a>.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`tsum_totient_half_pow_eq_half_add_moebius_sq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneLambertLadder.lean#L665)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR7.irrational_totient_iff_moebius_square`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR7/ArithmeticAssemblies.lean#L40)

```lean
theorem irrational_totient_iff_moebius_square :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) ↔
      Irrational (∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2)
```

<a id="catalogue-mob-a1b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totient_iff_moebius_square` | [E249_07/Challenge.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L131) | [PaperStatementsH.lean, line 16](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsH.lean#L16) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a2"></a>

## Proposition (The squared-Lambert identity)

> *Let $`w:\mathbb N\to\mathbb R`$ satisfy $`|w(d)|\le d`$ for $`d\ge1`$, and let $`0\le r<1`$. Then
> ``` math
> \sum_{d\ge1}w(d)\left(\frac{r^d}{1-r^d}\right)^2
>  =\sum_{n\ge1}\left(\sum_{d\mid n}w(d)\left(\frac nd-1\right)\right)r^n.
> ```
> Expand $`(x/(1-x))^2=\sum_{j\ge1}(j-1)x^j`$ and group terms by $`n=dj`$. Absolute convergence follows from the bound on $`w`$ and geometric decay. The cases $`w=\mu`$, $`w=1`$ and $`w=\varphi`$ give the next three series; the same algebra applies to each, but their arithmetic values differ.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`tsum_lambert_linear_weight_sq_pure`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L105)*

The Lean declaration below states this result.

[`GcdMomentCalculus.tsum_lambert_linear_weight_sq_pure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GcdMomentCalculus.lean#L105)

```lean
theorem tsum_lambert_linear_weight_sq_pure
    (w : ℕ → ℝ) (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * ((((n : ℕ) / e : ℕ) : ℝ) - 1))
          * r ^ (n : ℕ)
```

<a id="catalogue-mob-a2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_lambert_linear_weight_sq_pure` | [E249_05/Challenge.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L54) | [PaperStatementsAK.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAK.lean#L134) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a4"></a>

## Proposition (Weight one and divisor sums)

> *$`\sum_{d:\mathbb{N}^+}' 1/(2^d-1)^2 = \sum_{n:\mathbb{N}^+}' \big(\sigma(n)-\tau(n)\big)\cdot(1/2)^n = \zeta_q(2) - \zeta_q(1)`$ at $`q=1/2`$. The displayed identity is formalised. Irrationality of its value follows from the cited linear independence result of Postelmans and Van Assche, as explained in Proposition <a href="#prop:zetaq" data-reference-type="ref" data-reference="prop:zetaq">48</a>; that literature result is not formalised here. Replacing the weight $`1`$ by $`\mu`$ changes the value to that of Definition <a href="#catalogue:mob:a3" data-reference-type="ref" data-reference="catalogue:mob:a3">80</a>. Observation <a href="#catalogue:mob:a6" data-reference-type="ref" data-reference="catalogue:mob:a6">83</a> compares the two choices of weight.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L216)*

The Lean proof assumes the linear independence theorem of Postelmans and Van Assche, stated in Lean as `PostelmansVanAssche.q_Pade_linear_independence`; that input is not proved in Lean.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.divisor_sum_identity`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquaredMersenneDivisorIdentities.lean#L36)

```lean
theorem divisor_sum_identity :
    ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          (((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℝ)
            - ((ArithmeticFunction.sigma 0 (n : ℕ) : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.qZeta`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L17)

```lean
def qZeta (q : ℝ) (s : ℕ) : ℝ :=
  ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ (s - 1) * (q ^ (n : ℕ) / (1 - q ^ (n : ℕ)))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.qZeta_half_two_sub_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L81)

```lean
theorem qZeta_half_two_sub_one :
    qZeta ((1 : ℝ) / 2) 2 - qZeta ((1 : ℝ) / 2) 1
      = ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_qZeta_half_difference_of_linearIndependent`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L143)

```lean
theorem irrational_qZeta_half_difference_of_linearIndependent
    (hli : ∀ a b c : ℚ,
      (a : ℝ) * 1 + (b : ℝ) * qZeta ((1 : ℝ) / 2) 1
        + (c : ℝ) * qZeta ((1 : ℝ) / 2) 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    Irrational (qZeta ((1 : ℝ) / 2) 2 - qZeta ((1 : ℝ) / 2) 1)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.moebius_weight_value`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquaredMersenneDivisorIdentities.lean#L98)

```lean
theorem moebius_weight_value :
    ∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
        / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)) - 1 / 2
```

<a id="catalogue-mob-a4-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="catalogue-mob-a5"></a>

## Proposition (Totient weight and gcd moments)

> *$`\sum_{d:\mathbb{N}^+}' \varphi(d)/(2^d-1)^2 = \sum_{n:\mathbb{N}^+}' (P(n)-n)\cdot(1/2)^n`$, where $`P = \varphi * \mathrm{Id}`$ (Pillai’s gcd-sum function). It also equals $`\mathbb E[\gcd(X,Y)]`$ when $`X,Y`$ are independent and $`\mathbb P(X=n)=\mathbb P(Y=n)=2^{-n}`$ for $`n\ge1`$; see Proposition <a href="#prop:pillai" data-reference-type="ref" data-reference="prop:pillai">49</a>. This is a different weighted series. Its rationality is not settled by the identities proved here.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`tsum_totient_div_mersenne_sq_eq_gcd_moment_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L235)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.gcd_moment_identity_three_members`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L334)

```lean
theorem gcd_moment_identity_three_members :
    (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' n : ℕ+, (((pillaiP (n : ℕ) : ℕ) : ℝ) - ((n : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ))
      ∧ (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
            then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L307)

```lean
theorem tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
        then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.pillaiP_eq_totient_mul_id`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L67)

```lean
theorem pillaiP_eq_totient_mul_id (n : ℕ) :
    (totientArith * ArithmeticFunction.id) n = pillaiP n
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_gcd_Icc_eq_pillaiP`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L77)

```lean
theorem sum_gcd_Icc_eq_pillaiP (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, Nat.gcd k n = pillaiP n
```

5. [`GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GcdMomentCalculus.lean#L235)

```lean
theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ)
```

<a id="catalogue-mob-a5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `gcd_moment_identity_three_members` | [E249_05/Challenge.lean, line 137](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L137) | [PaperStatementsAE.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L218) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq` | [E249_05/Challenge.lean, line 154](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L154) | [PaperStatementsAE.lean, line 335](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L335) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `pillaiP_eq_totient_mul_id` | [E249_05/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L146) | [PaperStatementsAE.lean, line 263](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L263) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `sum_gcd_Icc_eq_pillaiP` | [E249_05/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L150) | [PaperStatementsAE.lean, line 295](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L295) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `tsum_totient_div_mersenne_sq_eq_gcd_moment_series` | [E249_05/Challenge.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L62) | [PaperStatementsAK.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAK.lean#L150) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a7"></a>

## Proposition (The weight of pairs divisible by a fixed integer)

> *Let $`X,Y`$ be independent random variables with $`\mathbb P(X=n)=\mathbb P(Y=n)=2^{-n}`$ for $`n\ge1`$. For every $`d\ge1`$,
> ``` math
> \mathbb P(d\mid X,\ d\mid Y)=\frac1{(2^d-1)^2}.
> ```
> This follows by multiplying the two geometric sums $`\sum_{k\ge1}2^{-dk}=1/(2^d-1)`$. It explains the squared denominator in the preceding Möbius identity.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L266)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.pair_divisibility_mass`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquaredMersenneDivisorIdentities.lean#L62)

```lean
theorem pair_divisibility_mass (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_geometric_multiples`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquaredMersenneDivisorIdentities.lean#L79)

```lean
theorem tsum_geometric_multiples (d : ℕ) (hd : 0 < d) :
    ∑' k : ℕ, ((1 : ℝ) / 2) ^ (d * (k + 1)) = 1 / ((2 : ℝ) ^ d - 1)
```

3. [`GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GcdMomentCalculus.lean#L266)

```lean
theorem tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2
```

<a id="catalogue-mob-a7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `pair_divisibility_mass` | [E249_07/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L146) | [PaperStatementsAE.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAE.lean#L283) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `tsum_geometric_multiples` | [E249_07/Challenge.lean, line 164](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L164) | [PaperStatementsAE.lean, line 357](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAE.lean#L357) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq` | [E249_04/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L180) | [PaperStatementsAK.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L145) | [E249_04](../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a8"></a>

## Proposition (The sum over coprime directions)

> *The sum over positive coprime pairs satisfies
> ``` math
> \sum_{\substack{a,b\ge1\\\gcd(a,b)=1}}
>                   \frac1{2^{a+b}-1}=1.
> ```
> To see the normalisation, write every pair of positive integers uniquely as $`(ka,kb)`$ with $`\gcd(a,b)=1`$, and sum $`2^{-k(a+b)}`$ over $`k\ge1`$. The total is $`(\sum_{n\ge1}2^{-n})^2=1`$. This base-two normalisation is used in Proposition <a href="#catalogue:mob:a9a" data-reference-type="ref" data-reference="catalogue:mob:a9a">86</a>.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`tsum_pos_coprime_inv_mersenne_eq_one`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L349)*

The Lean declaration below states this result.

[`GcdMomentCalculus.tsum_pos_coprime_inv_mersenne_eq_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GcdMomentCalculus.lean#L349)

```lean
theorem tsum_pos_coprime_inv_mersenne_eq_one :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1
```

<a id="catalogue-mob-a8-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_pos_coprime_inv_mersenne_eq_one` | [E249_07/Challenge.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L176) | [PaperStatementsAK.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAK.lean#L139) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a9a"></a>

## Proposition (A Stern–Brocot recursion with stopping)

> *For positive integers $`a,b`$, put
> ``` math
> M(a,b)=\frac1{(2^a-1)(2^b-1)}.
> ```
> Then
> ``` math
> M(a,b)=\frac1{2^{a+b}-1}+M(a+b,b)+M(a,a+b).
> ```
> Multiplication by the common denominator proves the identity. At the root $`(1,1)`$, the three terms on the right are each $`1/3`$, and $`M(1,1)=1`$.*
> 
> *The first term is a mass retained at the current node, not passed to either child. Thus the probabilistic interpretation is a branching process with stopping: after division by $`M(a,b)`$, the stopping and two transition probabilities are, respectively,
> ``` math
> \frac{(2^a-1)(2^b-1)}{2^{a+b}-1},\qquad
>  \frac{2^a-1}{2^{a+b}-1},\qquad
>  \frac{2^b-1}{2^{a+b}-1}.
> ```
> They sum to one. The stopping probability is at least $`1/3`$, which gives the next proposition’s geometric error bound. Also $`M(a,b)=\mathbb P(a\mid X)\mathbb P(b\mid Y)`$ for the independent geometric variables used above. The identity does not describe a conservative mass split between the two children alone.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`cylinderMass_split`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L474)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.divisibility_mass`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L42)

```lean
theorem divisibility_mass (a : ℕ) (ha : 0 < a) :
    (∑' k : ℕ, if 0 < k ∧ a ∣ k then ((1 : ℝ) / 2) ^ k else 0)
      = 1 / ((2 : ℝ) ^ a - 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.cylinderMass_eq_divisibility_mass_mul`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L86)

```lean
theorem cylinderMass_eq_divisibility_mass_mul (a b : ℕ+) :
    cylinderMass a b
      = (∑' k : ℕ, if 0 < k ∧ (a : ℕ) ∣ k then ((1 : ℝ) / 2) ^ k else 0)
        * (∑' k : ℕ, if 0 < k ∧ (b : ℕ) ∣ k then ((1 : ℝ) / 2) ^ k else 0)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.cylinder_mediant_split`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L95)

```lean
theorem cylinder_mediant_split (a b : ℕ+) :
    cylinderMass a b
      = 1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + cylinderMass (a + b) b + cylinderMass a (a + b)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.cylinder_root_values`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L103)

```lean
theorem cylinder_root_values :
    cylinderMass 1 1 = 1 ∧
      1 / ((2 : ℝ) ^ (((1 : ℕ+) : ℕ) + ((1 : ℕ+) : ℕ)) - 1) = 1 / 3 ∧
      cylinderMass (1 + 1) 1 = 1 / 3 ∧ cylinderMass 1 (1 + 1) = 1 / 3
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.normalised_split_probabilities`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L117)

```lean
theorem normalised_split_probabilities (a b : ℕ+) :
    (1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)) / cylinderMass a b
        = ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
          / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      ∧ cylinderMass (a + b) b / cylinderMass a b
        = ((2 : ℝ) ^ (a : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      ∧ cylinderMass a (a + b) / cylinderMass a b
        = ((2 : ℝ) ^ (b : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.stopping_transition_probabilities_sum_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L147)

```lean
theorem stopping_transition_probabilities_sum_one (a b : ℕ+) :
    ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
        / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      + ((2 : ℝ) ^ (a : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      + ((2 : ℝ) ^ (b : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) = 1
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.stopping_probability_ge_third`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L162)

```lean
theorem stopping_probability_ge_third (a b : ℕ+) :
    (1 : ℝ) / 3 ≤ ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
      / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
```

<a id="catalogue-mob-a9a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `divisibility_mass` | [E249_07/Challenge.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L141) | [PaperStatementsAE.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAE.lean#L227) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `cylinderMass_eq_divisibility_mass_mul` | [E249_07/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L186) | [PaperStatementsAY.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAY.lean#L74) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `cylinder_mediant_split` | [E249_07/Challenge.lean, line 192](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L192) | [PaperStatementsAY.lean, line 79](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAY.lean#L79) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `cylinder_root_values` | [E249_07/Challenge.lean, line 198](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L198) | [PaperStatementsAY.lean, line 84](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAY.lean#L84) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `normalised_split_probabilities` | [E249_07/Challenge.lean, line 204](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L204) | [PaperStatementsAY.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAY.lean#L110) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `stopping_transition_probabilities_sum_one` | [E249_07/Challenge.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L157) | [PaperStatementsAE.lean, line 305](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAE.lean#L305) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `stopping_probability_ge_third` | [E249_07/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L152) | [PaperStatementsAE.lean, line 301](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAE.lean#L301) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a9b"></a>

## Proposition (Convergence with an explicit error)

> *In the splitting identity of Proposition <a href="#catalogue:mob:a9a" data-reference-type="ref" data-reference="catalogue:mob:a9a">86</a>, the sum of the two child terms is at most $`2/3`$ of the parent term. If $`M_d(a,b)`$ is the sum of the contributions removed during the first $`d`$ levels, then
> ``` math
> |M(a,b)-M_d(a,b)|\le(2/3)^d M(a,b).
> ```
> In particular, $`M_d(a,b)\to M(a,b)`$. This convergence statement is separate from identifying the limit with a sum over any independently defined infinite set of descendants; no additional identification is asserted here.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`sternBrocotDepthMass_error`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L525) [`tendsto_sternBrocotDepthMass`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L560)*

The Lean declarations below together state this result.

1. [`GcdMomentCalculus.cylinderMass_children_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GcdMomentCalculus.lean#L514)

```lean
theorem cylinderMass_children_le (a b : ℕ+) :
    cylinderMass (a + b) b + cylinderMass a (a + b) ≤ (2 / 3) * cylinderMass a b
```

2. [`GcdMomentCalculus.sternBrocotDepthMass_error`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GcdMomentCalculus.lean#L525)

```lean
theorem sternBrocotDepthMass_error (dp : ℕ) :
    ∀ a b : ℕ+,
      0 ≤ cylinderMass a b - sternBrocotDepthMass dp a b
        ∧ cylinderMass a b - sternBrocotDepthMass dp a b
            ≤ (2 / 3 : ℝ) ^ dp * cylinderMass a b
```

3. [`GcdMomentCalculus.tendsto_sternBrocotDepthMass`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GcdMomentCalculus.lean#L560)

```lean
theorem tendsto_sternBrocotDepthMass (a b : ℕ+) :
    Filter.Tendsto (fun dp : ℕ => sternBrocotDepthMass dp a b)
      Filter.atTop (nhds (cylinderMass a b))
```

<a id="catalogue-mob-a9b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cylinderMass_children_le` | [E249_07/Challenge.lean, line 172](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L172) | [PaperStatementsAK.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAK.lean#L129) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `sternBrocotDepthMass_error` | [E249_07/Challenge.lean, line 224](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L224) | [PaperStatementsB.lean, line 15](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsB.lean#L15) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `tendsto_sternBrocotDepthMass` | [E249_07/Challenge.lean, line 231](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L231) | [PaperStatementsB.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsB.lean#L23) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-b1"></a>

## Proposition (A numerator polynomial and its coefficients)

> *For squarefree $`r\ge1`$, the polynomial defined above has coefficients
> ``` math
> [X^k]P_r(X)=
>  \begin{cases}
>  \dfrac r{\gcd(r,k)}\varphi(\gcd(r,k)),&0\le k<r,\\
>  0,&k\ge r.
>  \end{cases}
> ```
> For $`k<r`$, extracting the coefficient gives $`\sum_{d\mid\gcd(r,k)}\mu(d)r/d`$; the usual divisor formula for $`\varphi`$ evaluates this sum. All coefficients in the range $`0\le k<r`$ are positive. Thus a signed sum of geometric polynomials has an explicit positive-coefficient expression. The squarefree hypothesis is retained as in the cited formal statements.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`mobiusNumeratorPolynomial_eq_gcdWord`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RepunitMobiusNumerator.lean#L205) [`mobiusNumeratorPolynomial_coeff`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RepunitMobiusNumerator.lean#L217) [`mobiusNumeratorPolynomial_coeff_pos`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RepunitMobiusNumerator.lean#L234)*

The Lean declarations below together state this result.

1. [`Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_coeff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RepunitMobiusNumerator.lean#L217)

```lean
theorem mobiusNumeratorPolynomial_coeff {r k : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).coeff k =
      if k < r then (gcdWordCoeff r k : ℤ) else 0
```

2. [`Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_coeff_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RepunitMobiusNumerator.lean#L234)

```lean
theorem mobiusNumeratorPolynomial_coeff_pos {r k : ℕ}
    (hr : Squarefree r) (hk : k < r) :
    0 < (mobiusNumeratorPolynomial r).coeff k
```

<a id="catalogue-mob-b1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mobiusNumeratorPolynomial_coeff` | [E249_07/Challenge.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L246) | [PaperStatementsAC.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAC.lean#L36) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `mobiusNumeratorPolynomial_coeff_pos` | [E249_07/Challenge.lean, line 251](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L251) | [PaperStatementsAC.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAC.lean#L40) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-b2"></a>

## Proposition (Evaluation at two)

> *For squarefree $`r\ge1`$, evaluation of $`P_r`$ at two gives the integer
> ``` math
> P_r(2)=\sum_{d\mid r}\mu(d)\frac rd
>                          \frac{2^r-1}{2^d-1}.
> ```
> Each quotient is an integer because $`d\mid r`$. The formal definition sums over subsets of the prime divisors of $`r`$; for squarefree $`r`$ these are exactly its divisors. This identifies the polynomial calculation with the numerator used in $`b_r`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`mobiusNumeratorPolynomial_eval_two`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RepunitMobiusNumerator.lean#L445) [`mobiusNumerator`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RadicalMobiusShadow.lean#L101)*

The Lean declarations below together state this result.

1. [`Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_eval_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/RepunitMobiusNumerator.lean#L445)

```lean
theorem mobiusNumeratorPolynomial_eval_two {r : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      RadicalMobiusShadow.mobiusNumerator r
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.numerator_eval_two_divisors`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/NumeratorEvaluation.lean#L32)

```lean
theorem numerator_eval_two_divisors {r : ℕ} (hr : 0 < r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      ∑ d ∈ r.divisors,
        ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) *
          (((RadicalMobiusShadow.mersenne r /
            RadicalMobiusShadow.mersenne d : ℕ) : ℤ))
```

<a id="catalogue-mob-b2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mobiusNumeratorPolynomial_eval_two` | [E249_05/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L272) | [PaperStatementsAQ.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAQ.lean#L58) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `numerator_eval_two_divisors` | [E249_07/Challenge.lean, line 279](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L279) | [PaperStatementsAQ.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAQ.lean#L63) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Challenge for `mobiusNumeratorPolynomial_eval_two`:

```lean
theorem mobiusNumeratorPolynomial_eval_two {r : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      mobiusNumerator r := by sorry
```

Challenge for `numerator_eval_two_divisors`:

```lean
theorem numerator_eval_two_divisors {r : ℕ} (hr : 0 < r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      ∑ d ∈ r.divisors,
        ArithmeticFunction.moebius d * (((r / d : ℕ) : ℤ)) *
          (((mersenne r /
            mersenne d : ℕ) : ℤ)) := by sorry
```

<a id="catalogue-mob-b3"></a>

## Proposition (Decomposition by the radical)

> *For $`H\ge1`$ and $`r\ge1`$,
> ``` math
> H\beta_H=\frac H{\operatorname{rad}(H)}b_{\operatorname{rad}(H)},
>  \qquad
>  \operatorname{den}(b_r)
>    =\frac{2^r-1}{\gcd(|P_r(2)|,2^r-1)}.
> ```
> The first equality follows from the definition of $`\beta_H`$; the second is ordinary reduction of an integer fraction. Multiplication by $`H/\operatorname{rad}(H)`$ can cause further cancellation. No coprimality assumption is included in either identity.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`scaledMobiusShadow_eq_radicalBase`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RadicalMobiusShadow.lean#L125) [`baseMobiusShadow_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RadicalMobiusShadow.lean#L150)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR20.radical_decomposition`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/RadicalDecomposition.lean#L50)

```lean
theorem radical_decomposition (H r : ℕ) (hH : 0 < H) (hr : 0 < r) :
    (H : ℚ) * numericMobiusShadow H =
      ((H / squarefreeKernel H : ℕ) : ℚ) * baseMobiusShadow (squarefreeKernel H) ∧
    (baseMobiusShadow r).den = mersenne r /
      ((mobiusNumeratorPolynomial r).eval 2).natAbs.gcd (mersenne r)
```

<a id="catalogue-mob-b3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `radical_decomposition` | [E249_07/Challenge.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L287) | [PaperStatementsAQ.lean, line 70](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAQ.lean#L70) | [E249_07](../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-b4"></a>

## Proposition (A cyclotomic congruence)

> *Let $`r`$ be squarefree and $`m\mid r`$. In $`\mathbb Z[X]`$,
> ``` math
> P_r(X)\equiv\mu(m)J_2(r/m)\pmod{\Phi_m(X)},
> ```
> where $`J_2(n)=n^2\prod_{p\mid n}(1-p^{-2})`$ is the second Jordan totient. Evaluation at two gives
> ``` math
> \Phi_m(2)\mid P_r(2)-\mu(m)J_2(r/m).
> ```*
> 
> *<span class="sans-serif">\[uniform\]</span> [`cyclotomic_dvd_mobiusNumeratorPolynomial_sub`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CyclotomicProjectionOfShadow.lean#L299) [`mobiusNumerator_mod_cyclotomicEval`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CyclotomicProjectionOfShadow.lean#L310)*

The Lean declarations below together state this result.

1. [`Erdos249257.CyclotomicProjectionOfShadow.cyclotomic_dvd_mobiusNumeratorPolynomial_sub`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CyclotomicProjectionOfShadow.lean#L299)

```lean
theorem cyclotomic_dvd_mobiusNumeratorPolynomial_sub
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      RepunitMobiusNumerator.mobiusNumeratorPolynomial r -
        Polynomial.C
          (ArithmeticFunction.moebius m * jordanTotientTwo (r / m))
```

2. [`Erdos249257.CyclotomicProjectionOfShadow.mobiusNumerator_mod_cyclotomicEval`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CyclotomicProjectionOfShadow.lean#L310)

```lean
theorem mobiusNumerator_mod_cyclotomicEval
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    cyclotomicEval m ∣
      RadicalMobiusShadow.mobiusNumerator r -
        ArithmeticFunction.moebius m * jordanTotientTwo (r / m)
```

3. [`Erdos249257.CyclotomicProjectionOfShadow.jordanTotientTwo_eq_prod_primeFactors`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CyclotomicProjectionOfShadow.lean#L67)

```lean
theorem jordanTotientTwo_eq_prod_primeFactors
    {n : ℕ} (hn : Squarefree n) :
    jordanTotientTwo n =
      ∏ p ∈ n.primeFactors, ((p : ℤ) ^ 2 - 1)
```

<a id="catalogue-mob-b4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cyclotomic_dvd_mobiusNumeratorPolynomial_sub` | [E249_08/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L63) | [PaperStatementsAC.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAC.lean#L23) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `mobiusNumerator_mod_cyclotomicEval` | [E249_08/Challenge.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L95) | [PaperStatementsAQ.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAQ.lean#L62) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `jordanTotientTwo_eq_prod_primeFactors` | [E249_08/Challenge.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L71) | [PaperStatementsAC.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAC.lean#L30) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `cyclotomic_dvd_mobiusNumeratorPolynomial_sub`:

```lean
theorem cyclotomic_dvd_mobiusNumeratorPolynomial_sub
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial r -
        Polynomial.C
          (ArithmeticFunction.moebius m * jordanTotientTwo (r / m)) := by sorry
```

Challenge for `mobiusNumerator_mod_cyclotomicEval`:

```lean
theorem mobiusNumerator_mod_cyclotomicEval
    {r m : ℕ} (hr : Squarefree r) (hm : m ∣ r) :
    cyclotomicEval m ∣
      mobiusNumerator r -
        ArithmeticFunction.moebius m * jordanTotientTwo (r / m) := by sorry
```

<a id="catalogue-mob-b8a"></a>

## Proposition (Adjoining a prime: new divisors)

> *Let $`r\ge1`$, let $`p\nmid r`$ be prime, and let $`m\mid r`$. Then
> ``` math
> P_{rp}(X)\equiv-P_r(X^p)\pmod{\Phi_{mp}(X)}.
> ```*
> 
> *<span class="sans-serif">\[uniform\]</span> [`cyclotomic_dvd_primeJump_new_fibre`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/PrimePowerJumpDynamics.lean#L281) [`cyclotomic_dvd_primeJump_new_fibre_constant`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/PrimePowerJumpDynamics.lean#L347)*

The Lean declaration below states this result.

[`Erdos249257.PrimePowerJumpDynamics.cyclotomic_dvd_primeJump_new_fibre`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/PrimePowerJumpDynamics.lean#L281)

```lean
theorem cyclotomic_dvd_primeJump_new_fibre
    {r p m : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic (m * p) ℤ ∣
      mobiusNumeratorPolynomial (r * p) +
        Polynomial.expand ℤ p (mobiusNumeratorPolynomial r)
```

<a id="catalogue-mob-b8a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cyclotomic_dvd_primeJump_new_fibre` | [E249_08/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L110) | [PaperStatementsAS.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAS.lean#L21) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-b8b"></a>

## Proposition (Adjoining a prime: existing divisors)

> *Let $`r`$ be squarefree, let $`p\nmid r`$ be prime, and let $`m\mid r`$. For the existing divisors $`m`$, the corresponding identity is
> ``` math
> P_{rp}(X)\equiv(p^2-1)P_r(X)\pmod{\Phi_m(X)}.
> ```*
> 
> *<span class="sans-serif">\[uniform\]</span> [`cyclotomic_dvd_primeJump_old_fibre`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/PrimePowerJumpDynamics.lean#L310)*

The Lean declaration below states this result.

[`Erdos249257.PrimePowerJumpDynamics.cyclotomic_dvd_primeJump_old_fibre`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/PrimePowerJumpDynamics.lean#L310)

```lean
theorem cyclotomic_dvd_primeJump_old_fibre
    {r p m : ℕ} (hr : Squarefree r) (hp : p.Prime)
    (hpr : ¬ p ∣ r) (hm : m ∣ r) :
    Polynomial.cyclotomic m ℤ ∣
      mobiusNumeratorPolynomial (r * p) -
        Polynomial.C ((p : ℤ) ^ 2 - 1) *
          mobiusNumeratorPolynomial r
```

<a id="catalogue-mob-b8b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cyclotomic_dvd_primeJump_old_fibre` | [E249_08/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L117) | [PaperStatementsAS.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAS.lean#L27) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d7"></a>

## Proposition (Lambert-series identities)

> *For an arithmetic function $`f`$ for which the sums converge absolutely, write $`L(f)=\sum_{n\ge1}f(n)/(2^n-1)`$. Expanding each geometric series gives
> ``` math
> L(f)=\sum_{m\ge1}\frac{(f*1)(m)}{2^m}.
> ```
> In particular, if $`\alpha=\varphi*\mu`$, then $`\alpha*1=\varphi`$ and $`L(\alpha)=S`$. The table distinguishes this value from four other Lambert-series values. The identity changes the coefficients and the form of the denominator; it does not transfer an irrationality theorem for one weight to another.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`tsum_totient_div_pow_two_eq_pnat_half_pow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18415)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_eq_divisor_sum_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertDivisorTransform.lean#L42)

```lean
theorem lambertValue_eq_divisor_sum_series (f : ℕ → ℝ)
    (hf : Summable (fun p : ℕ+ × ℕ+ =>
      f (p.1 : ℕ) * ((1 : ℝ) / 2) ^ ((p.1 : ℕ) * (p.2 : ℕ)))) :
    lambertValue f
      = ∑' m : ℕ+, (∑ e ∈ (m : ℕ).divisors, f e) * ((1 : ℝ) / 2) ^ (m : ℕ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.alpha_divisor_sum_eq_totient`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertDivisorTransform.lean#L101)

```lean
theorem alpha_divisor_sum_eq_totient (n : ℕ) :
    ∑ e ∈ n.divisors, ((primWeight e : ℤ) : ℝ) = (Nat.totient n : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_alpha_eq_totientSeries`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertDivisorTransform.lean#L109)

```lean
theorem lambertValue_alpha_eq_totientSeries :
    lambertValue (fun d => ((primWeight d : ℤ) : ℝ))
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n
```

<a id="catalogue-cert-d7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lambertValue_eq_divisor_sum_series` | [E249_08/Challenge.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L145) | [PaperStatementsAE.lean, line 258](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAE.lean#L258) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `alpha_divisor_sum_eq_totient` | [E249_08/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L175) | [PaperStatementsBA.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsBA.lean#L25) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `lambertValue_alpha_eq_totientSeries` | [E249_08/Challenge.lean, line 179](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L179) | [PaperStatementsBA.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsBA.lean#L42) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-e3"></a>

## Proposition (An affine combination annihilates the specified divisor terms)

> *Let $`H\ge1`$ and $`d\mid H`$, with $`d>0`$. The $`d`$th term in the Möbius expansion of $`R_{mH}`$ is $`\mu(d)K_d(mH)`$, where
> ``` math
> K_d(mH)=\frac{mH}{d(2^d-1)}+\frac{2^d}{(2^d-1)^2}.
> ```
> This is affine in $`m`$. Consequently, for any finite family of real coefficients $`c_i`$ and nonnegative integers $`m_i`$ with $`\sum_i c_i=\sum_i c_i m_i=0`$, one has $`\sum_i c_i K_d(m_iH)=0`$.*
> 
> *For the four multipliers $`(1,3,5,15)`$ and coefficients $`(4,-3,-2,1)`$,
> ``` math
> K_d(15H)-3K_d(3H)-2K_d(5H)+4K_d(H)=0.
> ```
> The zeroth and first moments are zero, while the second is $`15^2-3\cdot3^2-2\cdot5^2+4=152`$. Equivalently, $`XY-3X-2Y+4`$ takes the values $`0,0,152`$ at $`(1,1),(3,5),(9,25)`$. This explains the coefficients: they cancel the affine contribution of each divisor of $`H`$, without cancelling a general quadratic function of the multiplier.*
> 
> *For a finite truncation of depth $`L\ge0`$, write
> ``` math
> U=\sum_{j=1}^{L}
>  \bigl(\varphi(15H+j)-3\varphi(3H+j)
>        -2\varphi(5H+j)+4\varphi(H+j)\bigr)2^{L-j}.
> ```
> The difference between $`2^L(R_{15H}-3R_{3H}-2R_{5H}+4R_H)`$ and $`U`$ has absolute value at most $`19H+5L+5`$. Indeed, the error equals
> ``` math
> (R_{15H+L}+4R_{H+L})-(3R_{3H+L}+2R_{5H+L}),
> ```
> and both parenthesised terms lie between $`0`$ and $`19H+5L+5`$ by $`0\le R_n\le n+1`$ for $`n\ge1`$. Thus
> ``` math
> 19H+5L+5<U\bmod2^L<2^L-(19H+5L+5)
> ```
> is sufficient for this four-tail combination to be nonintegral. The bound is derived from these tail enclosures; no optimality for the actual totient tails is asserted. Obtaining such certificates at the required unbounded family of LCM heights remains unproved, as in Theorems <a href="#catalogue:mob:e2" data-reference-type="ref" data-reference="catalogue:mob:e2">111</a> and <a href="#catalogue:cert:b6" data-reference-type="ref" data-reference="catalogue:cert:b6">103</a>.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`oldChannel_affine_moment_annihilation`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/JointExponentTransport.lean#L36) [`joint35_oldChannel_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/JointExponentTransport.lean#L71) [`sharpJoint35ConeRadius`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/JointExponentTransport.lean#L124)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.transportResidueKernel_eq_mobiusTermKernel`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L28)

```lean
theorem transportResidueKernel_eq_mobiusTermKernel {d N : ℕ}
    (hd : 0 < d) (hdN : d ∣ N) :
    transportResidueKernel d N
      = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * mobiusTermKernel d N
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel_affine_in_multiplier`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L47)

```lean
theorem mobiusTermKernel_affine_in_multiplier (d H m : ℕ) :
    mobiusTermKernel d (m * H)
      = (m : ℝ) * ((H : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)))
        + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.joint35ConeWindow_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L99)

```lean
theorem joint35ConeWindow_eq (H L : ℕ) :
    joint35ConeWindow H L
      = ∑ j ∈ Finset.range L,
          ((Nat.totient (15 * H + (j + 1)) : ℤ)
            - 3 * (Nat.totient (3 * H + (j + 1)) : ℤ)
            - 2 * (Nat.totient (5 * H + (j + 1)) : ℤ)
            + 4 * (Nat.totient (H + (j + 1)) : ℤ)) * 2 ^ (L - (j + 1))
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.totientTail_enclosure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L119)

```lean
theorem totientTail_enclosure (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 1
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel_moment_annihilation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L58)

```lean
theorem mobiusTermKernel_moment_annihilation
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (m : ι → ℕ) (d H : ℕ)
    (hzero : ∑ i, c i = 0) (hfirst : ∑ i, c i * (m i : ℝ) = 0) :
    ∑ i, c i * mobiusTermKernel d (m i * H) = 0
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.joint35_mobiusTermKernel_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L76)

```lean
theorem joint35_mobiusTermKernel_zero (d H : ℕ) :
    mobiusTermKernel d (15 * H) - 3 * mobiusTermKernel d (3 * H)
      - 2 * mobiusTermKernel d (5 * H) + 4 * mobiusTermKernel d H = 0
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.joint35_coefficient_moments`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L87)

```lean
theorem joint35_coefficient_moments :
    ((4 : ℝ) + (-3) + (-2) + 1 = 0)
      ∧ ((4 : ℝ) * 1 + (-3) * 3 + (-2) * 5 + 1 * 15 = 0)
      ∧ ((4 : ℝ) * 1 ^ 2 + (-3) * 3 ^ 2 + (-2) * 5 ^ 2 + 1 * 15 ^ 2 = 152)
      ∧ ((1 : ℝ) * 1 - 3 * 1 - 2 * 1 + 4 = 0)
      ∧ ((3 : ℝ) * 5 - 3 * 3 - 2 * 5 + 4 = 0)
      ∧ ((9 : ℝ) * 25 - 3 * 9 - 2 * 25 + 4 = 152)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.joint35_truncation_error`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L132)

```lean
theorem joint35_truncation_error (H L : ℕ) (hH : 1 ≤ H) :
    (2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)
      = (totientTail (15 * H + L) + 4 * totientTail (H + L))
        - (3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L))
    ∧ |(2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)|
      ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)
    ∧ (0 ≤ totientTail (15 * H + L) + 4 * totientTail (H + L)
        ∧ totientTail (15 * H + L) + 4 * totientTail (H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ))
    ∧ (0 ≤ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
        ∧ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ))
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.joint35_nonintegral_of_separated_window`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/AffineDivisorAnnihilation.lean#L183)

```lean
theorem joint35_nonintegral_of_separated_window {H L : ℕ} (hH : 1 ≤ H)
    (hlow : ((19 * H + 5 * L + 5 : ℕ) : ℤ) < joint35ConeWindow H L % 2 ^ L)
    (hhigh : joint35ConeWindow H L % 2 ^ L
      < 2 ^ L - ((19 * H + 5 * L + 5 : ℕ) : ℤ)) :
    (totientTail (15 * H) - 3 * totientTail (3 * H)
      - 2 * totientTail (5 * H) + 4 * totientTail H) ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="catalogue-mob-e3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `transportResidueKernel_eq_mobiusTermKernel` | [E249_08/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L255) | [PaperStatementsBE.lean, line 69](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsBE.lean#L69) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `mobiusTermKernel_affine_in_multiplier` | [E249_08/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L152) | [PaperStatementsAE.lean, line 267](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAE.lean#L267) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `joint35ConeWindow_eq` | [E249_08/Challenge.lean, line 201](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L201) | [PaperStatementsAX.lean, line 369](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAX.lean#L369) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `totientTail_enclosure` | [E249_08/Challenge.lean, line 236](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L236) | [PaperStatementsAX.lean, line 618](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAX.lean#L618) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `mobiusTermKernel_moment_annihilation` | [E249_08/Challenge.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L158) | [PaperStatementsAE.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAE.lean#L272) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `joint35_mobiusTermKernel_zero` | [E249_08/Challenge.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L140) | [PaperStatementsAE.lean, line 254](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAE.lean#L254) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `joint35_coefficient_moments` | [E249_08/Challenge.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L131) | [PaperStatementsAE.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAE.lean#L246) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `joint35_truncation_error` | [E249_08/Challenge.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L218) | [PaperStatementsAX.lean, line 384](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAX.lean#L384) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `joint35_nonintegral_of_separated_window` | [E249_08/Challenge.lean, line 210](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L210) | [PaperStatementsAX.lean, line 377](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAX.lean#L377) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-f1"></a>

## Proposition (The error under composite dilation)

> *For $`A\subseteq\mathbb N`$ and $`n\ge1`$, let $`d_A(n)=\#\{d\ge1:d\mid n,\ d\in A\}`$. If $`a\in A`$ and $`a,x\ge1`$, then
> ``` math
> d_A(ax)=d_A(x)+\mathbf 1_{a\nmid x}
>        +\#\{d\mid ax:d\in A,\ d\nmid x,\ d\ne a\}.
> ```
> Indeed, partition the divisors of $`ax`$ into those already dividing $`x`$, the possible new divisor $`a`$, and all other new divisors. If every element of $`A`$ is prime, the last set is empty, since a prime dividing $`ax`$ but not $`x`$ must equal the prime $`a`$. For composite $`a`$ it can be nonempty: at $`A=\mathbb N`$, $`a=6`$, $`x=1`$, the other new divisors are $`2`$ and $`3`$.*
> 
> *This is an unweighted counting identity. The associated Lambert series satisfies
> ``` math
> \sum_{\substack{a\in A\\a\ge1}}\frac1{2^a-1}
>  =\sum_{n\ge1}\frac{d_A(n)}{2^n}.
> ```
> For the totient series the required divisor-convolution weight is instead $`\alpha=\varphi*\mu`$, since $`\alpha*1=\varphi`$, as in Proposition <a href="#catalogue:cert:d7" data-reference-type="ref" data-reference="catalogue:cert:d7">94</a>. Weighting all divisors by $`\varphi`$ would give $`\sum_{d\mid n}\varphi(d)=n`$, not $`\varphi(n)`$; already at $`n=2`$ these values are $`2`$ and $`1`$. A weighted version must retain the weights of the new divisors, so it cannot be obtained by substituting $`A=\mathbb N`$ in this unweighted formula. Also $`\alpha(p)=p-2`$ for primes $`p`$, so $`\alpha`$ is unbounded and is not a periodic weight.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`supportCoeff_mul_eq_add_defect`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CompositeDilationDefect.lean#L30) [`compositeDilationDefect_eq_zero_of_prime_support`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CompositeDilationDefect.lean#L103) [`supportCoeff_mul_prime_support`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CompositeDilationDefect.lean#L119)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L27)

```lean
theorem composite_dilation_divisor_count (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (ha1 : 1 ≤ a) (hx1 : 1 ≤ x) :
    supportCoeff A (a * x) =
      supportCoeff A x + (if a ∣ x then 0 else 1) +
        compositeDilationDefect A a x
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_eq_zero_of_prime_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L36)

```lean
theorem composite_dilation_defect_eq_zero_of_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hAprime : ∀ d ∈ A, d.Prime) :
    compositeDilationDefect A a x = 0
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_divisor_count_prime_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L42)

```lean
theorem composite_dilation_divisor_count_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hx1 : 1 ≤ x) (hAprime : ∀ d ∈ A, d.Prime) :
    supportCoeff A (a * x) = supportCoeff A x + (if a ∣ x then 0 else 1)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L49)

```lean
theorem composite_dilation_defect_univ_six_one :
    ((6 * 1 : ℕ).divisors.filter
        fun d => (d ∈ (Set.univ : Set ℕ) ∧ ¬ d ∣ 1 ∧ d ≠ 6)) = ({2, 3} : Finset ℕ)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one_card`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L72)

```lean
theorem composite_dilation_defect_univ_six_one_card :
    compositeDilationDefect (Set.univ : Set ℕ) 6 1 = 2
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L83)

```lean
theorem lambert_support_series (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.lambert_support_series_restricted`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L92)

```lean
theorem lambert_support_series_restricted (A : Set ℕ) :
    (∑' a : ℕ, Set.indicator {a ∈ A | 1 ≤ a} (fun a => (1 : ℝ) / ((2 : ℝ) ^ a - 1)) a) =
      ∑' m : ℕ, (supportCoeff A (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_mul_zeta`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L108)

```lean
theorem totient_convolution_weight_mul_zeta (n : ℕ) :
    ∑ e ∈ n.divisors, MersenneLambertLadder.primWeight e = (Nat.totient n : ℤ)
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_totient_ne_totient`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L114)

```lean
theorem sum_divisors_totient_ne_totient :
    (∀ n : ℕ, ∑ d ∈ n.divisors, Nat.totient d = n) ∧
      (∑ d ∈ (2 : ℕ).divisors, Nat.totient d) = 2 ∧ Nat.totient 2 = 1
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_prime`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L120)

```lean
theorem totient_convolution_weight_prime {p : ℕ} (hp : p.Prime) :
    MersenneLambertLadder.primWeight p = (p : ℤ) - 2
```

11. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_unbounded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L125)

```lean
theorem totient_convolution_weight_unbounded :
    ¬ ∃ B : ℕ, ∀ n : ℕ, MersenneLambertLadder.primWeight n ≤ (B : ℤ)
```

12. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_not_periodic`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CompositeDilationIdentity.lean#L131)

```lean
theorem totient_convolution_weight_not_periodic :
    ¬ ∃ p : ℕ, 0 < p ∧
      ∀ n : ℕ, MersenneLambertLadder.primWeight (n + p) =
        MersenneLambertLadder.primWeight n
```

<a id="catalogue-mob-f1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `composite_dilation_divisor_count` | [E249_08/Challenge.lean, line 294](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L294) | [PaperStatementsBD.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsBD.lean#L20) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `composite_dilation_defect_eq_zero_of_prime_support` | [E249_08/Challenge.lean, line 265](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L265) | [PaperStatementsAJ.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAJ.lean#L168) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `composite_dilation_divisor_count_prime_support` | [E249_09/Challenge.lean, line 53](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L53) | [PaperStatementsBD.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsBD.lean#L31) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `composite_dilation_defect_univ_six_one` | [E249_08/Challenge.lean, line 270](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L270) | [PaperStatementsAJ.lean, line 172](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAJ.lean#L172) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `composite_dilation_defect_univ_six_one_card` | [E249_08/Challenge.lean, line 275](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L275) | [PaperStatementsAJ.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAJ.lean#L176) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `lambert_support_series` | [E249_09/Challenge.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L58) | [PaperStatementsBD.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsBD.lean#L35) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `lambert_support_series_restricted` | [E249_09/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L63) | [PaperStatementsBD.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsBD.lean#L39) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `totient_convolution_weight_mul_zeta` | [E249_09/Challenge.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L77) | [PaperStatementsBN.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsBN.lean#L17) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `sum_divisors_totient_ne_totient` | [E249_08/Challenge.lean, line 279](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_08/Challenge.lean#L279) | [PaperStatementsAJ.lean, line 500](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_08/PaperStatementsAJ.lean#L500) | [E249_08](../evidence/comparator/replay-35882032091/receipt-E249_08.json) |
| `totient_convolution_weight_prime` | [E249_09/Challenge.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L87) | [PaperStatementsBN.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsBN.lean#L25) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `totient_convolution_weight_unbounded` | [E249_09/Challenge.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L91) | [PaperStatementsBN.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsBN.lean#L28) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `totient_convolution_weight_not_periodic` | [E249_09/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L81) | [PaperStatementsBN.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsBN.lean#L20) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `totient_convolution_weight_mul_zeta`:

```lean
theorem totient_convolution_weight_mul_zeta (n : ℕ) :
    ∑ e ∈ n.divisors, primWeight e = (Nat.totient n : ℤ) := by sorry
```

Challenge for `totient_convolution_weight_prime`:

```lean
theorem totient_convolution_weight_prime {p : ℕ} (hp : p.Prime) :
    primWeight p = (p : ℤ) - 2 := by sorry
```

Challenge for `totient_convolution_weight_unbounded`:

```lean
theorem totient_convolution_weight_unbounded :
    ¬ ∃ B : ℕ, ∀ n : ℕ, primWeight n ≤ (B : ℤ) := by sorry
```

Challenge for `totient_convolution_weight_not_periodic`:

```lean
theorem totient_convolution_weight_not_periodic :
    ¬ ∃ p : ℕ, 0 < p ∧
      ∀ n : ℕ, primWeight (n + p) =
        primWeight n := by sorry
```

<a id="catalogue-cert-a10"></a>

## Theorem (The quantified certificate condition is equivalent to irrationality)

> *$`\big(\forall h:\mathbb{N},\ 0<h \to \forall N_0:\mathbb{N},\ \exists N\ge N_0,\ \exists L,\ \mathcal{C}(h,N,L)\big) \leftrightarrow S\notin\mathbb Q`$. The quantified-condition side is exactly $`\mathcal{C}(h,N,L)`$ quantified as $`\forall h\ge1\ \forall N_0\ge0\ \exists N\ge N_0\ \exists L`$. The universally quantified assertion remains unproved. The equivalence identifies the finite witnesses that suffice; it does not establish their existence beyond every threshold.*
> 
> *(equivalence proved; supply <span class="sans-serif">\[Open\]</span>) <span class="sans-serif">\[cofinal\]</span> [`irrational_totient_series_iff_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmConeFlatness.lean#L412)*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L412)

```lean
theorem irrational_totient_series_iff_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ,
        ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L
```

<a id="catalogue-cert-a10-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totient_series_iff_certificate_supply` | [E249_01/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L100) | [PaperStatementsAD.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAD.lean#L46) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b2"></a>

## Theorem (It suffices to use multiples of a period)

> *$`\big(\forall h_0>0,\ \forall N_0,\ \exists m>0,\ \exists N\ge N_0,\ \exists L,\ \mathcal{C}(m\cdot h_0, N, L)\big) \to S\notin\mathbb Q`$. The shift may be any positive multiple of a prescribed period. This enlarges the choice of finite witness: Theorem <a href="#catalogue:cert:a10" data-reference-type="ref" data-reference="catalogue:cert:a10">98</a> gives the condition with $`m=1`$. Conversely, rationality would make all such tail differences integral after a fixed starting index. The displayed implication therefore makes this quantified condition equivalent to irrationality; its truth remains unproved.*
> 
> *(implication proved; hypothesis <span class="sans-serif">\[Open\]</span>) <span class="sans-serif">\[cofinal\]</span> [`irrational_totient_series_of_multiple_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L502)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_period_multiple_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L25)

```lean
theorem irrational_of_period_multiple_certificate_supply
    (hsupply : ∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
      ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_at_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L33)

```lean
theorem period_multiple_certificate_at_one {h₀ N L : ℕ}
    (hcert : certifiedKill h₀ N L) : certifiedKill (1 * h₀) N L
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_period_multiple_integrality`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L55)

```lean
theorem rational_forces_period_multiple_integrality
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ m N : ℕ, N₀ ≤ N →
      totientTail (N + m * h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.period_multiple_certificate_supply_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L41)

```lean
theorem period_multiple_certificate_supply_iff :
    (∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
        ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill (m * h₀) N L) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="catalogue-cert-b2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_period_multiple_certificate_supply` | [E249_09/Challenge.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L107) | [PaperStatementsAU.lean, line 166](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L166) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `period_multiple_certificate_at_one` | [E249_09/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L113) | [PaperStatementsAU.lean, line 326](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L326) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `rational_forces_period_multiple_integrality` | [E249_09/Challenge.lean, line 123](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L123) | [PaperStatementsAU.lean, line 372](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L372) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `period_multiple_certificate_supply_iff` | [E249_09/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L117) | [PaperStatementsAU.lean, line 329](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L329) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b3"></a>

## Theorem (The diagonal condition is equivalent to irrationality)

> *$`\big(\forall t_0:\mathbb{N},\ \exists t\ge t_0,\ \exists L,\ \mathcal{C}({H}(t), {H}(t), L)\big) \leftrightarrow S\notin\mathbb Q`$. For a fixed hypothetical rational value, sufficiently large $`t`$ makes both its dyadic denominator and its odd-part period admissible at $`N=h={H}(t)`$. Conversely, irrationality and pointwise completeness supply a witness for every prescribed $`t`$. This is an equivalent condition with one scale parameter; the verified cases $`t\le82`$ do not establish it at arbitrarily large scales.*
> 
> *(equivalence proved; supply <span class="sans-serif">\[Open\]</span>) <span class="sans-serif">\[cofinal\]</span> [`irrational_totient_series_iff_lcm_diagonal_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmConeFlatness.lean#L426)*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_lcm_diagonal_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L426)

```lean
theorem irrational_totient_series_iff_lcm_diagonal_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
        certifiedKill (periodLcm t) (periodLcm t) L
```

<a id="catalogue-cert-b3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totient_series_iff_lcm_diagonal_certificate_supply` | [E249_01/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L260) | [PaperStatementsA.lean, line 66](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L66) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b4"></a>

## Lemma (Nondivisors in a short LCM window)

> *Let $`t\ge1`$ and $`1\le j<2t`$ be integers. If $`j\nmid H(t)`$, then $`j=p^a>t`$ for a prime $`p`$ and an integer $`a\ge1`$. Indeed, a prime-power divisor of $`j`$ must exceed $`t`$, and $`j<2t`$ leaves no room for a cofactor larger than $`1`$. This classifies the exceptional offsets in this short window; it does not bound their contribution to a weighted sum of totient differences.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`eq_prime_pow_of_not_dvd_periodLcm`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmDiagonalReduction.lean#L137)*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.eq_prime_pow_of_not_dvd_periodLcm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmDiagonalReduction.lean#L137)

```lean
theorem eq_prime_pow_of_not_dvd_periodLcm {t j : ℕ} (hj : 0 < j) (hlt : j < 2 * t)
    (hnd : ¬ j ∣ periodLcm t) :
    ∃ p k : ℕ, Nat.Prime p ∧ j = p ^ k ∧ t < j
```

<a id="catalogue-cert-b4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `eq_prime_pow_of_not_dvd_periodLcm` | [E249_09/Challenge.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L155) | [PaperStatementsA.lean, line 66](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsA.lean#L66) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b5"></a>

## Proposition (Totient factorisation on an LCM progression)

> *Let $`t\ge1`$, $`j\ge1`$ and $`q\ge0`$ be integers. Suppose $`j\mid H(t)`$ and every prime divisor of $`j`$ also divides $`H(t)/j`$. Then
> ``` math
> \varphi(qH(t)+j)=\varphi(j)\,
>                  \varphi\bigl(q(H(t)/j)+1\bigr).
> ```
> The two factors in $`qH(t)+j=j\bigl(q(H(t)/j)+1\bigr)`$ are coprime: the second is $`1`$ modulo each prime dividing $`j`$. Totient multiplicativity gives the identity. The extra prime-divisor hypothesis is not automatic from $`j\mid H(t)`$; for example, it fails at $`t=j=2`$, where $`\varphi(H(2)+2)=2`$ but the proposed product would be $`1`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`totient_periodLcm_ray_split`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmDiagonalReduction.lean#L208)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.clean_lcm_ray_factorisation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L67)

```lean
theorem clean_lcm_ray_factorisation (t j q : ℕ) (hdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ (periodLcm t / j)) :
    q * periodLcm t + j = j * (q * (periodLcm t / j) + 1) ∧
    Nat.Coprime j (q * (periodLcm t / j) + 1) ∧
    Nat.totient (q * periodLcm t + j) = Nat.totient j * Nat.totient (q * (periodLcm t / j) + 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.unclean_lcm_ray_counterexample`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L76)

```lean
theorem unclean_lcm_ray_counterexample :
    2 ∣ periodLcm 2 ∧ Nat.totient (periodLcm 2 + 2) = 2 ∧
    Nat.totient 2 * Nat.totient (periodLcm 2 / 2 + 1) = 1 ∧
    ¬ (∀ p : ℕ, Nat.Prime p → p ∣ 2 → p ∣ (periodLcm 2 / 2))
```

<a id="catalogue-cert-b5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `clean_lcm_ray_factorisation` | [E249_09/Challenge.lean, line 196](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L196) | [PaperStatementsAT.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L174) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `unclean_lcm_ray_counterexample` | [E249_09/Challenge.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L233) | [PaperStatementsAT.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L241) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b6"></a>

## Theorem (Rationality forces tail integrality on an LCM grid)

> *If $`S\in\mathbb Q`$, there is $`t_1\in\mathbb N`$ such that for all $`t\ge t_1`$, $`q\ge1`$ and $`m\ge0`$,
> ``` math
> R_{(q+m)H(t)}-R_{qH(t)}\in\mathbb Z.
> ```
> Thus all tails at positive multiples of $`H(t)`$ have the same fractional part once $`t\ge t_1`$. A certificate at one fixed scale does not refute rationality: the threshold $`t_1`$ depends on the hypothetical rational value. At a shift $`mH(t)>0`$ and basepoint $`qH(t)`$, such a certificate excludes rational values whose reduced denominator divides $`2^{qH(t)}(2^{mH(t)}-1)`$. Certificates at arbitrarily large scales, as required in Theorem <a href="#catalogue:cert:b7" data-reference-type="ref" data-reference="catalogue:cert:b7">104</a>, exclude every hypothetical rational value.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`rational_totient_series_forces_lcm_cone_flatness`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19002)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L8)

```lean
theorem lcm_grid_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail ((q + m) * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_fractional_parts`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L15)

```lean
theorem lcm_grid_fractional_parts
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      Int.fract (totientTail ((q + m) * periodLcm t)) =
        Int.fract (totientTail (q * periodLcm t))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.certificate_denominator_exclusion`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L27)

```lean
theorem certificate_denominator_exclusion (r : ℚ) (h N L : ℕ)
    (hcert : certifiedKill h N L) (hden : r.den ∣ 2 ^ N * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_supply_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L40)

```lean
theorem lcm_grid_supply_iff :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
        certifiedKill (m * periodLcm t) (q * periodLcm t) L
```

<a id="catalogue-cert-b6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lcm_grid_flatness` | [E249_09/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L209) | [PaperStatementsAT.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L199) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `lcm_grid_fractional_parts` | [E249_09/Challenge.lean, line 216](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L216) | [PaperStatementsAT.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L207) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `certificate_denominator_exclusion` | [E249_09/Challenge.lean, line 191](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L191) | [PaperStatementsAT.lean, line 167](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L167) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `lcm_grid_supply_iff` | [E249_09/Challenge.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L227) | [PaperStatementsAT.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L220) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b7"></a>

## Theorem (A sufficient nonintegrality condition on the grid)

> *Suppose that for every $`t_0\in\mathbb{N}`$ there are integers $`t\ge t_0`$, $`q\ge1`$, $`m\ge0`$ and $`L\ge0`$ such that
> ``` math
> \mathcal C(mH_t,qH_t,L).
> ```
> Then $`S\notin\mathbb Q`$. Rationality would make the corresponding tail difference integral at every sufficiently large scale, contradicting Proposition <a href="#catalogue:cert:a6" data-reference-type="ref" data-reference="catalogue:cert:a6">69</a>. A successful certificate necessarily has $`m>0`$, since the discrepancy vanishes at shift zero.*
> 
> *The diagonal choice is $`q=m=1`$; consecutive grid points have $`m=1`$, and for $`p\ge2`$ the pair $`(H_t,pH_t)`$ has $`(q,m)=(1,p-1)`$. The diagonal equivalence in Theorem <a href="#catalogue:cert:b3" data-reference-type="ref" data-reference="catalogue:cert:b3">100</a> also gives the converse from irrationality to the displayed quantified condition.*
> 
> *(implication proved; hypothesis <span class="sans-serif">\[Open\]</span>) <span class="sans-serif">\[cofinal\]</span> [`irrational_totient_series_of_lcm_cone_window_kill_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19014)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_supply_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L40)

```lean
theorem lcm_grid_supply_iff :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
        certifiedKill (m * periodLcm t) (q * periodLcm t) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_multiplier_positive`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L50)

```lean
theorem lcm_grid_multiplier_positive (t q m L : ℕ)
    (hc : certifiedKill (m * periodLcm t) (q * periodLcm t) L) : 0 < m
```

<a id="catalogue-cert-b7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lcm_grid_supply_iff` | [E249_09/Challenge.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L227) | [PaperStatementsAT.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L220) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `lcm_grid_multiplier_positive` | [E249_09/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L223) | [PaperStatementsAT.lean, line 215](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L215) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b8"></a>

## Corollary (Equivalent conditions stated without certificates)

> *The series $`S`$ is irrational if and only if
> ``` math
> R_{2H_t}-R_{H_t}\notin\mathbb Z
>  \qquad\text{for arbitrarily large integers }t.
> ```
> Equivalently, for arbitrarily large $`t`$ there are integers $`q\ge1`$ and $`m\ge1`$ with $`R_{(q+m)H_t}-R_{qH_t}\notin\mathbb Z`$. Apply the pointwise equivalence of Theorem <a href="#catalogue:cert:a7" data-reference-type="ref" data-reference="catalogue:cert:a7">70</a> to Theorems <a href="#catalogue:cert:b3" data-reference-type="ref" data-reference="catalogue:cert:b3">100</a> and <a href="#catalogue:cert:b7" data-reference-type="ref" data-reference="catalogue:cert:b7">104</a>, respectively. These are equivalent statements of the irrationality question; the required unbounded sets of scales are not established.*
> 
> *(implication proved; hypothesis <span class="sans-serif">\[Open\]</span>) <span class="sans-serif">\[cofinal\]</span> [`irrational_totient_series_of_lcm_diagonal_nonintegrality_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19034) [`irrational_totient_series_of_lcm_cone_nonintegrality_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19046)*

The Lean declarations below together state this result.

1. [`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_all_tail_diffs_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L386)

```lean
theorem irrational_totient_series_iff_all_tail_diffs_nonintegral :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`Erdos249257.TotientTailPeriodKiller.periodLcm_diagonal_kill_iff_tail_diff_notMem_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L439)

```lean
theorem periodLcm_diagonal_kill_iff_tail_diff_notMem_int (t : ℕ) :
    (∃ L, certifiedKill (periodLcm t) (periodLcm t) L) ↔
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)
```

3. [`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L451)

```lean
theorem irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

4. [`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonintegrality_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L462)

```lean
theorem irrational_totient_series_of_lcm_cone_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m : ℕ, 0 < q ∧
      totientTail (q * periodLcm t + m * periodLcm t) - totientTail (q * periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="catalogue-cert-b8-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totient_series_iff_all_tail_diffs_nonintegral` | [E249_09/Challenge.lean, line 249](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L249) | [PaperStatementsAD.lean, line 70](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAD.lean#L70) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `periodLcm_diagonal_kill_iff_tail_diff_notMem_int` | [E249_09/Challenge.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L174) | [PaperStatementsA.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsA.lean#L95) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `irrational_totient_series_of_lcm_diagonal_nonintegrality_supply` | [E249_09/Challenge.lean, line 167](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L167) | [PaperStatementsA.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsA.lean#L87) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `irrational_totient_series_of_lcm_cone_nonintegrality_supply` | [E249_09/Challenge.lean, line 160](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L160) | [PaperStatementsA.lean, line 79](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsA.lean#L79) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b9a"></a>

## Proposition (Soundness of a second-difference certificate)

> *Let $`h,N,L\in\mathbb N`$. If
> ``` math
> \begin{aligned}
>  2(N+2h+L+2)
>  &<\bigl(D(h,N+h,L)-D(h,N,L)\bigr)\bmod2^L\\
>  &<2^L-2(N+2h+L+2),
> \end{aligned}
> ```
> then $`R_{N+2h}-2R_{N+h}+R_N\notin\mathbb Z`$. The numerator is the second difference of the finite windows. Subtracting the two tail identities leaves an error of absolute value at most $`2(N+2h+L+2)`$, which explains the radius in the hypothesis. At $`(h,N)=(1,8)`$, the first-difference test holds at depth $`8`$, whereas the second-difference test fails at every depth $`L\le8`$ and holds at $`L=9`$. A historical probe over $`t\le20`$ reported that the first-difference test was at least as shallow in $`30`$ of $`40`$ sampled cases. This finite comparison is not a uniform ordering of the depths.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`second_diff_notMem_int_of_certifiedRank2Kill`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmConeFlatness.lean#L493) (the certified $`(1,8)`$ comparison: [`totient_tail_rank_two_kill_sound_but_not_shallower_cell`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19090)).*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_tail_diff_scaled_sub_window_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L65)

```lean
theorem abs_tail_diff_scaled_sub_window_le (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + h) - totientTail N) -
        ((windowDiscrepancy h N L : ℤ) : ℝ)| ≤ (N : ℝ) + h + L + 2
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.second_difference_error_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L104)

```lean
theorem second_difference_error_bound (h N L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N) -
        ((windowDiscrepancy h (N + h) L - windowDiscrepancy h N L : ℤ) : ℝ)| ≤
      2 * ((N : ℝ) + 2 * h + L + 2)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.second_difference_certificate_sound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L121)

```lean
theorem second_difference_certificate_sound {h N L : ℕ}
    (hlow : 2 * ((N : ℤ) + 2 * h + L + 2) <
      (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L)
    (hhigh : (windowDiscrepancy h (N + h) L - windowDiscrepancy h N L) % 2 ^ L <
      2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)) :
    totientTail (N + 2 * h) - 2 * totientTail (N + h) + totientTail N ∉
      Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.second_difference_cell_one_eight`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PeriodMultipleAndSecondDifference.lean#L136)

```lean
theorem second_difference_cell_one_eight :
    certifiedKill 1 8 8 ∧
      (∀ L : ℕ, L ≤ 8 → ¬ certifiedRank2Kill 1 8 L) ∧
      certifiedRank2Kill 1 8 9
```

<a id="catalogue-cert-b9a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `abs_tail_diff_scaled_sub_window_le` | [E249_09/Challenge.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L239) | [PaperStatementsAT.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L246) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `second_difference_error_bound` | [E249_09/Challenge.lean, line 144](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L144) | [PaperStatementsAU.lean, line 414](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L414) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `second_difference_certificate_sound` | [E249_09/Challenge.lean, line 135](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L135) | [PaperStatementsAU.lean, line 406](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L406) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `second_difference_cell_one_eight` | [E249_09/Challenge.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L129) | [PaperStatementsAU.lean, line 401](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAU.lean#L401) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b10a"></a>

## Theorem (A finite-grid condition gives a nonintegral pair)

> *Let $`Q\subseteq\mathbb N_{>0}`$ be finite and nonempty. Suppose that $`B_q<2^L`$ for every $`q\in Q`$ and that
> ``` math
> \forall q_i\in Q\ \exists q_j\in Q,\qquad
>  B_{q_j}<(A_{q_i}-A_{q_j})\bmod2^L.
> ```
> Then $`R_{q_jH}-R_{q_iH}\notin\mathbb Z`$ for some $`q_i,q_j\in Q`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`exists_nonintegral_pair_of_coneNonflatCert`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmConeNonflat.lean#L126)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L12)

```lean
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L36)

```lean
theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="catalogue-cert-b10a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paperGridNumerator_eq` | [E249_09/Challenge.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L287) | [PaperStatementsAX.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L238) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_grid_nonintegral_pair` | [E249_09/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L272) | [PaperStatementsAX.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L223) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b10b"></a>

## Theorem (A sufficient quantified finite-grid condition)

> *Suppose that for every $`t_0`$ there are $`t\ge t_0`$, a depth $`L`$, and a finite nonempty $`Q\subseteq\mathbb N_{>0}`$ such that, with $`H=H_t`$, all the hypotheses of Theorem <a href="#catalogue:cert:b10a" data-reference-type="ref" data-reference="catalogue:cert:b10a">107</a> hold. Then $`S\notin\mathbb Q`$. Indeed, rationality would make all tail differences on every sufficiently large LCM grid integral, whereas the finite-grid theorem supplies a nonintegral pair on such a grid. The example above verifies one grid; it does not establish the quantified hypothesis.*
> 
> *(implication proved; hypothesis <span class="sans-serif">\[Open\]</span>) <span class="sans-serif">\[cofinal\]</span> [`irrational_totient_series_of_lcm_cone_nonflat_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19140)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L12)

```lean
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_supply_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L49)

```lean
theorem finite_grid_supply_irrational
    (hs : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, ∃ Q : Finset ℕ,
      Q.Nonempty ∧ (∀ q ∈ Q, 0 < q) ∧
      (∀ q ∈ Q, (q * periodLcm t + L + 2 : ℤ) < 2 ^ L) ∧
      paperGridCertificate (periodLcm t) L Q) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="catalogue-cert-b10b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paperGridNumerator_eq` | [E249_09/Challenge.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L287) | [PaperStatementsAX.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L238) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_grid_supply_irrational` | [E249_09/Challenge.lean, line 279](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L279) | [PaperStatementsAX.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L229) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b12"></a>

## Proposition (A finite carry test implies nonintegrality)

> *For each integer $`z`$ with $`|z|\le N+h+1`$, define
> ``` math
> c_z(0)=z,\qquad
>  c_z(i+1)=2c_z(i)-\bigl(\varphi(N+h+i+1)-\varphi(N+i+1)\bigr).
> ```
> Suppose that for every such $`z`$ there is an $`i\le K`$ with
> ``` math
> |c_z(i)|\ge N+i+h+2.
> ```
> Then $`R_{N+h}-R_N\notin\mathbb Z`$. Indeed, an integral value of the tail difference would be one of the $`2(N+h+1)+1`$ initial candidates. Its recurrence would satisfy $`c_z(i)=R_{N+h+i}-R_{N+i}`$ and hence $`|c_z(i)|<N+i+h+2`$ at every step, contrary to the finite test. The excluded strip is open: equality at its boundary already suffices. This proposition proves soundness for a specified $`h,N,K`$; an irrationality argument still needs the quantified family of tests.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`survivorKill`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L412) [`tail_diff_notMem_int_of_survivorKill`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L428)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_test_sound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L8)

```lean
theorem finite_carry_test_sound (h N K : ℕ)
    (htest : ∀ z : ℤ, |z| ≤ (N + h + 1 : ℤ) →
      ∃ i : ℕ, i ≤ K ∧ (N + i + h + 2 : ℤ) ≤ |carryOrbit h N z i|) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_candidate_count`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L22)

```lean
theorem finite_carry_candidate_count (h N : ℕ) :
    (Finset.Icc (-(N + h + 1 : ℤ)) (N + h + 1)).card = 2 * (N + h + 1) + 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_true_orbit`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L27)

```lean
theorem finite_carry_true_orbit (h N : ℕ) (z : ℤ)
    (hz : (z : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N z i : ℝ) = totientTail (N + i + h) - totientTail (N + i) ∧
    |carryOrbit h N z i| < (N + i + h + 2 : ℤ)
```

<a id="catalogue-cert-b12-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `finite_carry_test_sound` | [E249_09/Challenge.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L203) | [PaperStatementsAT.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L182) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_carry_candidate_count` | [E249_09/Challenge.lean, line 294](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L294) | [PaperStatementsAJ.lean, line 121](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAJ.lean#L121) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_carry_true_orbit` | [E249_10/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L80) | [PaperStatementsAT.lean, line 160](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L160) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-e1"></a>

## Theorem (The block norm condition implies irrationality)

> *Suppose that for every integer $`h\ge1`$ and every threshold $`X_0\in\mathbb{N}`$ there are $`X,L\in\mathbb{N}`$ with
> ``` math
> X\ge\max(X_0,1),\qquad 16(2X+h+L+2)\le2^L,
> ```
> and
> ``` math
> \left\lVert\sum_{X\le N<2X}E(h,N,L)\right\rVert\le\frac{21}{25}X.
> ```
> Then $`S\notin\mathbb Q`$. Indeed, the norm bound implies the real-part bound $`\operatorname{Re}\sum E(h,N,L)\le(9/10)X`$. Under the displayed size condition, this latter bound already gives a finite residue certificate, by $`\cos(\pi/8)>9/10`$ and averaging. The argument uses this specific numerical gap; an unspecified saving below $`X`$ is not the stated hypothesis.*
> 
> *(conditional theorem proved; hypothesis <span class="sans-serif">\[Open\]</span>) <span class="sans-serif">\[cofinal\]</span> [`irrational_totient_series_of_first_harmonic_norm_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/FirstHarmonicPivot.lean#L83) [`exists_certifiedKill_of_first_harmonic_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/FirstHarmonicGap.lean#L128)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_first_harmonic_norm_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L71)

```lean
theorem irrational_of_first_harmonic_norm_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X L : ℕ,
      max X₀ 1 ≤ X ∧ 16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.first_harmonic_re_bound_of_norm_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L40)

```lean
theorem first_harmonic_re_bound_of_norm_bound {h X L : ℕ}
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_real_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L54)

```lean
theorem exists_certificate_of_first_harmonic_real_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hre : (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certificate_of_first_harmonic_norm_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L61)

```lean
theorem exists_certificate_of_first_harmonic_norm_bound {h X L : ℕ} (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.nine_tenths_lt_cos_pi_div_eight`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L28)

```lean
theorem nine_tenths_lt_cos_pi_div_eight : (9 / 10 : ℝ) < Real.cos (Real.pi / 8)
```

<a id="catalogue-mob-e1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_first_harmonic_norm_gap` | [E249_10/Challenge.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L136) | [PaperStatementsAT.lean, line 578](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L578) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `first_harmonic_re_bound_of_norm_bound` | [E249_10/Challenge.lean, line 98](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L98) | [PaperStatementsAT.lean, line 476](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L476) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `exists_certificate_of_first_harmonic_real_bound` | [E249_10/Challenge.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L92) | [PaperStatementsAT.lean, line 382](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L382) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `exists_certificate_of_first_harmonic_norm_bound` | [E249_10/Challenge.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L86) | [PaperStatementsAT.lean, line 377](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L377) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `nine_tenths_lt_cos_pi_div_eight` | [E249_10/Challenge.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L157) | [PaperStatementsAJ.lean, line 447](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAJ.lean#L447) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-e2"></a>

## Theorem (A four-tail residue criterion)

> *For nonnegative integers $`H,p,L`$, define the four-tail combination, its finite numerator and its error bound by
> ``` math
> \begin{aligned}
>  J(H,p)&=R_{2pH}-R_{pH}-pR_{2H}+pR_H,\\
>  W(H,p,L)&=D(pH,pH,L)-pD(H,H,L),\\
>  B(H,p,L)&=3pH+(p+1)(L+2).
> \end{aligned}
> ```
> Then
> ``` math
> |2^LJ(H,p)-W(H,p,L)|\le B(H,p,L).
> ```
> Consequently the finite condition
> ``` math
> B(H,p,L)<W(H,p,L)\bmod2^L<2^L-B(H,p,L)
> ```
> implies $`J(H,p)\notin\mathbb Z`$. If, for every $`t_0\in\mathbb N`$, there are $`t\ge t_0`$, $`p\ge1`$ and $`L\ge0`$ satisfying this condition with $`H=H(t)`$, then $`S\notin\mathbb Q`$. Rationality would instead make both diagonal differences in $`J(H(t),p)`$ integral for every sufficiently large $`t`$.*
> 
> *The error bound groups the remainder as
> ``` math
> (R_{2pH+L}+pR_{H+L})-(R_{pH+L}+pR_{2H+L}).
> ```
> Each parenthesis is nonnegative and at most $`B(H,p,L)`$, by $`0\le R_n\le n+2`$. Their difference therefore has absolute value at most $`B(H,p,L)`$. This proves the bound without asserting optimality for the actual totient tails. Primality of $`p`$ is not required by the criterion; a prime $`p`$ is useful when comparing consecutive LCM heights. The checked instance is $`(H,p,L)=(12,5,15)`$, for which $`W(H,p,L)\bmod2^L=18834`$ and $`B(H,p,L)=282`$.*
> 
> *(conditional theorem + <span class="sans-serif">\[Cert\]</span> witness; supply <span class="sans-serif">\[Open\]</span>) <span class="sans-serif">\[cofinal\]</span> [`irrational_totient_series_of_primeJumpSharpKill_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/PrimeJumpWindow.lean#L193) [`primeJumpSharpKill_twelve_five`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/PrimeJumpWindow.lean#L186)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.four_tail_combination_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L103)

```lean
theorem four_tail_combination_eq (H p : ℕ) :
    primeJumpTailCommutator H p =
      totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.four_tail_window_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L93)

```lean
theorem four_tail_window_eq (H p L : ℕ) :
    windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L =
      primeJumpWindowCommutator H p L
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.windowDiscrepancy_diagonal_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L81)

```lean
theorem windowDiscrepancy_diagonal_eq (M L : ℕ) :
    windowDiscrepancy M M L =
      (windowNumerator (2 * M) L : ℤ) - (windowNumerator M L : ℤ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.four_tail_error_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L113)

```lean
theorem four_tail_error_bound (H p L : ℕ) :
    |(2 : ℝ) ^ L * (totientTail (2 * p * H) - totientTail (p * H)
          - p * totientTail (2 * H) + p * totientTail H)
        - ((windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L : ℤ) : ℝ)|
      ≤ ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℝ)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.totientTail_bounds`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L129)

```lean
theorem totientTail_bounds (n : ℕ) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 2
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.four_tail_criterion_sound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L152)

```lean
theorem four_tail_criterion_sound {H p L : ℕ}
    (hlow : ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ) <
      (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L)
    (hhigh : (windowDiscrepancy (p * H) (p * H) L - p * windowDiscrepancy H H L) % 2 ^ L <
      2 ^ L - ((3 * p * H + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    totientTail (2 * p * H) - totientTail (p * H)
        - p * totientTail (2 * H) + p * totientTail H ∉ Set.range ((↑) : ℤ → ℝ)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_four_tail_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L169)

```lean
theorem irrational_of_four_tail_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ p L : ℕ, 1 ≤ p ∧
      ((3 * p * periodLcm t + (p + 1) * (L + 2) : ℕ) : ℤ) <
        (windowDiscrepancy (p * periodLcm t) (p * periodLcm t) L
          - p * windowDiscrepancy (periodLcm t) (periodLcm t) L) % 2 ^ L ∧
      (windowDiscrepancy (p * periodLcm t) (p * periodLcm t) L
          - p * windowDiscrepancy (periodLcm t) (periodLcm t) L) % 2 ^ L <
        2 ^ L - ((3 * p * periodLcm t + (p + 1) * (L + 2) : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_four_tail_diagonals_integral`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L135)

```lean
theorem rational_forces_four_tail_diagonals_integral
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ p : ℕ, 0 < p →
      (totientTail (2 * periodLcm t) - totientTail (periodLcm t) ∈
          Set.range ((↑) : ℤ → ℝ)) ∧
        (totientTail (2 * (p * periodLcm t)) - totientTail (p * periodLcm t) ∈
          Set.range ((↑) : ℤ → ℝ))
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.four_tail_checked_instance`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/HarmonicGapAndFourTail.lean#L187)

```lean
theorem four_tail_checked_instance :
    (windowDiscrepancy (5 * 12) (5 * 12) 15
        - ((5 : ℕ) : ℤ) * windowDiscrepancy 12 12 15) % 2 ^ 15 = 18834 ∧
      (3 * 5 * 12 + (5 + 1) * (15 + 2) : ℕ) = 282
```

<a id="catalogue-mob-e2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `four_tail_combination_eq` | [E249_10/Challenge.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L109) | [PaperStatementsAT.lean, line 501](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L501) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `four_tail_window_eq` | [E249_10/Challenge.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L131) | [PaperStatementsAT.lean, line 520](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L520) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `windowDiscrepancy_diagonal_eq` | [E249_10/Challenge.lean, line 178](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L178) | [PaperStatementsAU.lean, line 572](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAU.lean#L572) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `four_tail_error_bound` | [E249_10/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L124) | [PaperStatementsAT.lean, line 514](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L514) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `totientTail_bounds` | [E249_10/Challenge.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L174) | [PaperStatementsAU.lean, line 504](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAU.lean#L504) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `four_tail_criterion_sound` | [E249_10/Challenge.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L115) | [PaperStatementsAT.lean, line 506](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L506) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `irrational_of_four_tail_supply` | [E249_10/Challenge.lean, line 143](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L143) | [PaperStatementsAT.lean, line 584](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L584) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `rational_forces_four_tail_diagonals_integral` | [E249_10/Challenge.lean, line 165](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L165) | [PaperStatementsAU.lean, line 366](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAU.lean#L366) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |
| `four_tail_checked_instance` | [E249_10/Challenge.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L103) | [PaperStatementsAT.lean, line 496](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L496) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ni-01"></a>

## Proposition (An equivalent diagonal nonintegrality condition)

> *The following statements are equivalent:
> ``` math
> S\notin\mathbb Q
>  \quad\Longleftrightarrow\quad
>  \forall a_0\in\mathbb N\ \exists a\ge a_0,\ \Omega_a\notin\mathbb Z.
> ```
> This is an exact reformulation of irrationality, not a weaker theorem about a finite set of scales. The later sufficient conditions seek a finite inequality that establishes the right-hand side.*
> 
> *(equivalence) [`irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitNonintegrality.lean#L37)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.irrational_iff_diagonal_orbit_nonintegrality`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L29)

```lean
theorem irrational_iff_diagonal_orbit_nonintegrality :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
        totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) ∉
          Set.range ((↑) : ℤ → ℝ)
```

<a id="prop-ni-01-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_iff_diagonal_orbit_nonintegrality` | [E249_11/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L76) | [PaperStatementsAT.lean, line 580](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAT.lean#L580) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ar-07"></a>

## Proposition (A sufficient short-window condition)

> *Suppose that for every $`a_0\in\mathbb N`$ there are $`a\ge a_0`$ and $`L<2\cdot2^a`$ with $`\mathcal C(H_{2^a},H_{2^a},L)`$. Then $`S\notin\mathbb Q`$. Writing out the certificate, the required inequality is
> ``` math
> 2H_{2^a}+L+2
>  <D(H_{2^a},H_{2^a},L)\bmod2^L
>  <2^L-(2H_{2^a}+L+2).
> ```
> It places the residue away from both endpoints of the modulus interval. The examples at $`a=4,6`$ establish the bounded statement in Proposition <a href="#prop:SK-02" data-reference-type="ref" data-reference="prop:SK-02">118</a>, not the condition for every threshold. Pointwise completeness allows a sufficiently large depth but does not supply a depth below $`2\cdot2^a`$.*
> 
> *<span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Open\]</span> \
> [`PowerTwoActualLcmShortArithmeticKillSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2107)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_short_window_diagonal_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L56)

```lean
theorem irrational_of_short_window_diagonal_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.diagonal_certificate_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L40)

```lean
theorem diagonal_certificate_unfolded (a L : ℕ) :
    certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L ↔
      (((2 * periodLcm (2 ^ a) + L + 2 : ℕ) : ℤ) <
          windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L % 2 ^ L ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L % 2 ^ L <
          2 ^ L - ((2 * periodLcm (2 ^ a) + L + 2 : ℕ) : ℤ))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.pointwise_completeness_supplies_some_depth`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L68)

```lean
theorem pointwise_completeness_supplies_some_depth (h N : ℕ)
    (hnon : totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) :
    ∃ L : ℕ, certifiedKill h N L
```

<a id="prop-ar-07-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_short_window_diagonal_supply` | [E249_11/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L97) | [PaperStatementsAU.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAU.lean#L180) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |
| `diagonal_certificate_unfolded` | [E249_11/Challenge.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L56) | [PaperStatementsAT.lean, line 365](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAT.lean#L365) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |
| `pointwise_completeness_supplies_some_depth` | [E249_11/Challenge.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L109) | [PaperStatementsAU.lean, line 329](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAU.lean#L329) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sep-03"></a>

## Proposition (A sufficient approximation condition)

> *Use the prescribed index $`q_a`$ and the error $`\varepsilon_{a,q_a}`$ defined above. Suppose
> ``` math
> \forall a_0\in\mathbb N\ \exists a\ge\max(2,a_0)\ \forall z\in\mathbb Z,
>  \qquad |\Omega_a-z|\ge\frac1{32}+\varepsilon_{a,q_a}.
> ```
> Then $`S\notin\mathbb Q`$. The estimate $`|\Omega_a-\rho_{a,q_a}|<\varepsilon_{a,q_a}`$ implies $`|\rho_{a,q_a}-z|>1/32`$ for every integer $`z`$, and hence the finite residue separation used by the linked implication. This is a fixed separation condition along an unbounded family of LCM scales. It is not an irrationality-measure theorem for arbitrary rational approximants, and nonintegrality alone does not give the stated margin. The depth is prescribed, not an additional free witness.*
> 
> *<span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Open\]</span> \
> [`irrational_totientSeries_of_actualLcmOrbitSeparationSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSeparation.lean#L305)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_diagonal_orbit_separation_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L145)

```lean
theorem irrational_of_diagonal_orbit_separation_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a : ℕ, max 2 a₀ ≤ a ∧ ∀ z : ℤ,
      (1 : ℝ) / 32 +
          ((2 * periodLcm (2 ^ a) + 2 * prescribedOddIndex a + 3 : ℕ) : ℝ) /
            (2 : ℝ) ^ (2 * prescribedOddIndex a + 1) ≤
        |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) - (z : ℝ)|) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.oddGuarded_depth_eq_prescribed`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L80)

```lean
theorem oddGuarded_depth_eq_prescribed (a : ℕ) :
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * prescribedOddIndex a + 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_orbit_sub_rawApprox_lt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L98)

```lean
theorem abs_orbit_sub_rawApprox_lt (a q : ℕ) :
    |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) -
        ((windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
            diagonalWindowIncrement (2 ^ a) (2 * q + 2) : ℤ) : ℝ) / (2 : ℝ) ^ (2 * q + 1)| <
      ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.rawApprox_separation_of_orbit_separation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L112)

```lean
theorem rawApprox_separation_of_orbit_separation {a q : ℕ}
    (hsep : ∀ z : ℤ,
      (1 : ℝ) / 32 + ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1) ≤
        |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) - (z : ℝ)|)
    (z : ℤ) :
    (1 : ℝ) / 32 <
      |((windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
            diagonalWindowIncrement (2 ^ a) (2 * q + 2) : ℤ) : ℝ) / (2 : ℝ) ^ (2 * q + 1) -
        (z : ℝ)|
```

<a id="prop-sep-03-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_diagonal_orbit_separation_supply` | [E249_11/Challenge.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L83) | [PaperStatementsAT.lean, line 601](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAT.lean#L601) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |
| `oddGuarded_depth_eq_prescribed` | [E249_11/Challenge.lean, line 261](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L261) | [PaperStatementsAX.lean, line 278](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAX.lean#L278) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |
| `abs_orbit_sub_rawApprox_lt` | [E249_11/Challenge.lean, line 254](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L254) | [PaperStatementsAX.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAX.lean#L141) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |
| `rawApprox_separation_of_orbit_separation` | [E249_11/Challenge.lean, line 265](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L265) | [PaperStatementsAX.lean, line 374](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAX.lean#L374) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-04"></a>

## Proposition (A sufficient upper-endpoint separation)

> *Let $`a,J,K,m\in\mathbb N`$, $`a\ge8`$, and $`H=H(2^a)`$. Assume
> ``` math
> J+K+(a+6)<2\cdot2^a.
> ```
> Define the finite condition
> ``` math
> \begin{aligned}
>  \mathcal G_a(J,K,m)\quad:\Longleftrightarrow\quad
>  &m\le K,\qquad 2H+J+K+2<2^m,\\
>  &D(H,H+J,K)\bmod2^m\le2^m-(2H+J+K+2).
>  \end{aligned}
> ```
> Then $`\mathcal G_a(J,K,m)`$ implies $`R_{2H+J}-R_{H+J}\notin\mathbb Z`$. In particular, irrationality follows if for every $`a_0`$ there are $`a\ge\max(a_0,8)`$ and $`K,m`$ satisfying $`K+(a+6)<2\cdot2^a`$ and $`\mathcal G_a(0,K,m)`$.*
> 
> *The sign theorem forces an integral tail to give a residue in the upper endpoint interval. This one-sided test excludes that interval; it does not require a lower residue bound. Both the sign-range hypothesis and the strict modulus bound are essential premises of this implication. The required unbounded family is not established.*
> 
> *(implication; quantified hypothesis <span class="sans-serif">\[Open\]</span>) [`PowerTwoActualLcmTopEdgeResidueGapSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1325)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.upper_endpoint_condition_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L29)

```lean
theorem upper_endpoint_condition_iff (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.upper_endpoint_gap_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L38)

```lean
theorem upper_endpoint_gap_nonintegral {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a J K m) :
    totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J) ∉
      Set.range ((↑) : ℤ → ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.integral_tail_forces_upper_endpoint_residue`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L50)

```lean
theorem integral_tail_forces_upper_endpoint_residue {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ K)
    {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J)) :
    (2 : ℤ) ^ K - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ K ∧
      windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ K <
        (2 : ℤ) ^ K
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_upper_endpoint_gap_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L66)

```lean
theorem irrational_of_upper_endpoint_gap_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
      K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="prop-te-04-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `upper_endpoint_condition_iff` | [E249_11/Challenge.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L114) | [PaperStatementsAU.lean, line 523](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAU.lean#L523) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |
| `upper_endpoint_gap_nonintegral` | [E249_11/Challenge.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L122) | [PaperStatementsAU.lean, line 532](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAU.lean#L532) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |
| `integral_tail_forces_upper_endpoint_residue` | [E249_11/Challenge.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L64) | [PaperStatementsAT.lean, line 567](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAT.lean#L567) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |
| `irrational_of_upper_endpoint_gap_supply` | [E249_11/Challenge.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L103) | [PaperStatementsAU.lean, line 193](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAU.lean#L193) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-05"></a>

## Proposition (Relations among the sufficient conditions)

> *The sufficient conditions do not form a single linear chain. The proved implications are
> ``` math
> \begin{aligned}
>  \text{guarded odd-prefix band}
>  &\ \Longleftrightarrow\ \text{guarded centred-magnitude bound},\\
>  \text{guarded centred-magnitude bound}
>  &\ \Longrightarrow\ \text{flexible centred-magnitude bound},\\
>  \text{flexible centred-magnitude bound}
>  &\ \Longrightarrow\ \text{adjacent-suffix band}
>    \ \Longrightarrow\ \text{upper-endpoint test}.
>  \end{aligned}
> ```
> There is also a separate sufficient argument: terminal dominance and flexible centred magnitude each imply the two-sided exclusion in Proposition <a href="#prop:TE-06" data-reference-type="ref" data-reference="prop:TE-06">117</a>, which implies diagonal nonintegrality. These statements refer to the quantified versions, with the bounds on $`a,q`$ and the depth retained. The detailed conditions and sources appear in Proposition <a href="#prop:te-chain" data-reference-type="ref" data-reference="prop:te-chain">226</a>. No reverse implication between terminal dominance and flexible magnitude is asserted, and none of the required unbounded families is proved here.*
> 
> *(implications; hypotheses <span class="sans-serif">\[Open\]</span>) [`powerTwoActualLcmTopEdgeResidueGapSupply_of_adjacentSuffixMidband`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2108)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.te_chain_relations`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L80)

```lean
theorem te_chain_relations :
    (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoAdjacentSuffixMidbandSupply) ∧
      (PowerTwoAdjacentSuffixMidbandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        PowerTwoActualLcmOrbitNonintegralitySupply)
```

<a id="prop-te-05-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `te_chain_relations` | [E249_11/Challenge.lean, line 276](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_11/Challenge.lean#L276) | [PaperStatementsAX.lean, line 447](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_11/PaperStatementsAX.lean#L447) | [E249_11](../evidence/comparator/replay-35882032091/receipt-E249_11.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-06"></a>

## Proposition (An exact endpoint formula)

> *Let $`a,q\in\mathbb N`$, $`a\ge8`$, and $`H=H(2^a)`$. Assume
> ``` math
> 2q+2+(a+6)<2\cdot2^a,\qquad 2(H+q+2)\le4^q.
> ```
> If $`z\in\mathbb Z`$ and $`z=\Omega_a`$, then
> ``` math
> 2u_{a,q}=\delta_{2^a}(2q+2)-c_{H,H,z}(2q+1).
> ```
> Consequently either of the inequalities
> ``` math
> \begin{aligned}
>  2u_{a,q}&\le\delta_{2^a}(2q+2)-(2H+2q+3),\\
>  \delta_{2^a}(2q+2)&\le2u_{a,q}
>  \end{aligned}
> ```
> is sufficient for $`\Omega_a\notin\mathbb Z`$. Under integrality the recurrence equals a positive tail difference strictly smaller than $`2H+2q+3`$, and the identity rules out both displayed inequalities. The identity is exact; the resulting nonintegrality criterion is only sufficient. Its converse is not asserted.*
> 
> *[`two_mul_actualOddHalfCenteredLift_eq_terminal_sub_trueCarry`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1678)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.endpoint_identity`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L142)

```lean
theorem endpoint_identity {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    2 * actualOddHalfCenteredLift a q =
      diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
        carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.integral_carry_strictly_between`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L158)

```lean
theorem integral_carry_strictly_between {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    0 < carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) ∧
      carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) <
        ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.endpoint_criterion_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L187)

```lean
theorem endpoint_criterion_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hesc : 2 * actualOddHalfCenteredLift a q ≤
          diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
            ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ) ∨
        diagonalWindowIncrement (2 ^ a) (2 * q + 2) ≤
          2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) ∉
      Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.oddHalfCenteredLift_spec`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L116)

```lean
theorem oddHalfCenteredLift_spec {a : ℕ} (q : ℕ) (ha : 2 ≤ a) :
    Even (windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
        diagonalWindowIncrement (2 ^ a) (2 * q + 2)) ∧
      Int.ModEq ((4 : ℤ) ^ q) (actualOddHalfCenteredLift a q)
        ((windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 2)) / 2) ∧
      -((4 : ℤ) ^ q) < 2 * actualOddHalfCenteredLift a q ∧
      2 * actualOddHalfCenteredLift a q ≤ (4 : ℤ) ^ q
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.centeredLift_range`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeStaircaseConditions.lean#L106)

```lean
theorem centeredLift_range {A M : ℤ} (hM : 0 < M) :
    -M < 2 * actualCenteredLift A M ∧ 2 * actualCenteredLift A M ≤ M
```

<a id="prop-te-06-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `endpoint_identity` | [E249_12/Challenge.lean, line 123](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L123) | [PaperStatementsAX.lean, line 300](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAX.lean#L300) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `integral_carry_strictly_between` | [E249_12/Challenge.lean, line 82](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L82) | [PaperStatementsAT.lean, line 548](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAT.lean#L548) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `endpoint_criterion_nonintegral` | [E249_12/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L111) | [PaperStatementsAX.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAX.lean#L287) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `oddHalfCenteredLift_spec` | [E249_12/Challenge.lean, line 133](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L133) | [PaperStatementsAX.lean, line 388](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAX.lean#L388) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `centeredLift_range` | [E249_12/Challenge.lean, line 148](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L148) | [PaperStatementsAY.lean, line 70](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAY.lean#L70) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sk-02"></a>

## Proposition (A sufficient extension of the examples through exponent 6)

> *The supplied finite result is
> ``` math
> \forall a_0\le6\ \exists a,L\in\mathbb N,\qquad
>  a\ge a_0,\quad L<2\cdot2^a,\quad
>  \mathcal C(H_{2^a},H_{2^a},L).
> ```
> The witnesses at $`(a,L)=(4,23)`$ and $`(6,93)`$ give this bounded family. A witness with $`a\ge7`$ would extend the verified range, but any finite extension would still leave the assertion for arbitrarily large thresholds in Proposition <a href="#prop:AR-07" data-reference-type="ref" data-reference="prop:AR-07">113</a> unproved.*
> 
> *<span class="sans-serif">\[bounded\]</span> <span class="sans-serif">\[Lean (finite prefix only)\]</span> \
> [`powerTwoActualLcmShortArithmeticKillSupply_through_six`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmShortKill.lean#L54)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_through_six`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L161)

```lean
theorem short_window_diagonal_through_six (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.short_window_diagonal_witnesses`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmDiagonalConditions.lean#L169)

```lean
theorem short_window_diagonal_witnesses :
    certifiedKill (periodLcm (2 ^ 4)) (periodLcm (2 ^ 4)) 23 ∧ (23 : ℕ) < 2 * 2 ^ 4 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ∧ (93 : ℕ) < 2 * 2 ^ 6
```

<a id="prop-sk-02-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `short_window_diagonal_through_six` | [E249_12/Challenge.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L174) | [PaperStatementsAU.lean, line 437](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAU.lean#L437) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `short_window_diagonal_witnesses` | [E249_12/Challenge.lean, line 179](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L179) | [PaperStatementsAU.lean, line 443](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAU.lean#L443) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-fr-01"></a>

## Proposition (A sufficient extremal-order condition)

> *Let $`H\ge1`$ and $`j\ge0`$. If
> ``` math
> \varphi(2H+j)<\min\{\varphi(H+j),\varphi(3H+j)\},
> ```
> then
> ``` math
> \varphi(3H+j)-2\varphi(2H+j)+\varphi(H+j)>0.
> ```
> If instead the middle value is strictly larger than both outer values, the displayed second difference is negative. In each case the claim follows by adding the two strict differences. No lower bound on their sizes is needed.*
> 
> *For $`H=H_{2^a}`$, this reduces nonvanishing of one second difference to an ordering of three totient values. For a prescribed $`j`$, the remaining question is whether either strict ordering occurs for arbitrarily large $`a`$. The elementary implication does not establish those occurrences. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`MiddleRankTotientExtremal`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientFixedRankLcmAsymptotic.lean#L267)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L27)

```lean
theorem extremal_order_curvature_pos {H j : ℕ} (hH : 1 ≤ H)
    (hmin : Nat.totient (2 * H + j) < min (Nat.totient (H + j)) (Nat.totient (3 * H + j))) :
    0 < (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_neg`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L36)

```lean
theorem extremal_order_curvature_neg {H j : ℕ} (hH : 1 ≤ H)
    (hleft : Nat.totient (H + j) < Nat.totient (2 * H + j))
    (hright : Nat.totient (3 * H + j) < Nat.totient (2 * H + j)) :
    (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) < 0
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L45)

```lean
theorem extremal_order_curvature_ne_zero {H j : ℕ} (hH : 1 ≤ H)
    (hextremal : MiddleRankTotientExtremal H j) :
    (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) ≠ 0
```

<a id="prop-fr-01-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `extremal_order_curvature_pos` | [E249_12/Challenge.lean, line 211](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L211) | [PaperStatementsAJ.lean, line 309](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L309) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `extremal_order_curvature_neg` | [E249_12/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L205) | [PaperStatementsAJ.lean, line 304](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L304) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `extremal_order_curvature_ne_zero` | [E249_12/Challenge.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L200) | [PaperStatementsAJ.lean, line 300](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L300) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-06"></a>

## Proposition (A directed certificate condition)

> *For fixed $`h,N\in\mathbb{N}`$, a depth $`L\in\mathbb{N}`$ satisfying
> ``` math
> N+L+2\ \le\ D(h,N,L)\bmod2^L
>  \ \le\ 2^L-(N+h+L+2)
> ```
> exists if and only if $`R_{N+h}-R_N\notin\mathbb Z`$. The endpoint inequalities are non-strict.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L59)

```lean
theorem directed_certificate_iff (h N : ℕ) :
    (∃ L : ℕ,
        ((N : ℤ) + L + 2) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
          windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
            (2 : ℤ) ^ L - ((N : ℤ) + h + L + 2)) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_example`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L71)

```lean
theorem directed_certificate_example :
    periodLcm 3 = 6 ∧
      windowDiscrepancy 6 6 6 = 270 ∧
      windowDiscrepancy 6 6 6 % (2 : ℤ) ^ 6 = 14 ∧
      directedCertifiedKill 6 6 6 ∧
      (∀ L : ℕ, L ≤ 6 → ¬ certifiedKill 6 6 L) ∧
      certifiedKill 6 6 7
```

<a id="prop-cp-06-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `directed_certificate_iff` | [E249_12/Challenge.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L74) | [PaperStatementsAT.lean, line 373](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAT.lean#L373) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `directed_certificate_example` | [E249_12/Challenge.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L65) | [PaperStatementsAT.lean, line 365](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAT.lean#L365) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-07"></a>

## Proposition (A sufficient condition at the prescribed mod-four pulses)

> *Suppose that for every positive integer $`h`$ and every $`B\in\mathbb N`$ there are a prime $`p>B`$ and $`K\in\mathbb N`$ such that
> ``` math
> \varphi(p+4h)-\varphi(p)\equiv2\pmod4
> ```
> and every integer $`z`$ with $`|z|\le p+4h+1`$ and $`z\equiv2\pmod4`$ has an index $`0\le i\le K`$ satisfying
> ``` math
> |c_{4h,p,z}(i)|\ge p+i+4h+2.
> ```
> Then $`S\notin\mathbb Q`$. Under a hypothetical eventual period $`h`$, the proved congruence argument at a sufficiently large such prime forces $`R_{p+4h}-R_p`$ to be an integer in the tested residue class. The finite test excludes every candidate in that class, a contradiction.*
> 
> *The mod-four congruence is supplied by Proposition <a href="#prop:CP-05-inv" data-reference-type="ref" data-reference="prop:CP-05-inv">142</a>; exclusion at the same prime is not. Restricting to $`2\pmod4`$ retains one residue class out of four, not necessarily exactly one quarter of the candidates in a finite interval. The quantifier over every bound $`B`$ cannot be replaced by one fixed prime for each $`h`$.*
> 
> *<span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`irrational_totientSeries_of_cofinal_modFourPulseSurvivorKill`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailCarryPeriod.lean#L1066)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_modFour_pulse_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L105)

```lean
theorem irrational_of_modFour_pulse_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] ∧
      ∃ K : ℕ, ∀ z : ℤ, |z| ≤ ((p + 4 * h + 1 : ℕ) : ℤ) → z ≡ (2 : ℤ) [ZMOD 4] →
        ∃ i : ℕ, i ≤ K ∧
          ((p + i + 4 * h + 2 : ℕ) : ℤ) ≤ |carryOrbit (4 * h) p z i|) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.rational_forces_pulse_class_integrality`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L88)

```lean
theorem rational_forces_pulse_class_integrality
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ B : ℕ, ∀ p : ℕ, B < p →
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] →
      ∃ z : ℤ, (z : ℝ) = totientTail (p + 4 * h) - totientTail p ∧
        z ≡ (2 : ℤ) [ZMOD 4]
```

<a id="prop-cp-07-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_modFour_pulse_supply` | [E249_12/Challenge.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L157) | [PaperStatementsAU.lean, line 153](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAU.lean#L153) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `rational_forces_pulse_class_integrality` | [E249_12/Challenge.lean, line 166](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L166) | [PaperStatementsAU.lean, line 374](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAU.lean#L374) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-a10"></a>

## Proposition (The full quantified condition)

> *``` math
> \big(\forall h\ge 1,\ \forall N_0,\ \exists N\ge N_0,\ \exists L,\ \mathcal{C}\ h\ N\ L\big)
> \iff S\notin\mathbb Q.
> ```
> This is exactly the quantifier structure $`\forall h\ge1\ \forall N_0\ \exists N\ge N_0\ \exists L\ \mathcal{C}(h,N,L)`$. The quantified condition is not supplied here. The equivalence specifies exactly what a residue-based proof would need beyond the finite examples. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span> (equivalence; supply <span class="sans-serif">\[Open\]</span>) \
> [`irrational_totient_series_iff_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmConeFlatness.lean#L412)*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L412)

```lean
theorem irrational_totient_series_iff_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ,
        ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L
```

<a id="prop-a10-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totient_series_iff_certificate_supply` | [E249_01/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L100) | [PaperStatementsAD.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsAD.lean#L46) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b3"></a>

## Proposition (One diagonal parameter suffices)

> *The following condition is equivalent to irrationality:
> ``` math
> \bigl(\forall t_0\in\mathbb N\ \exists t\ge t_0\ \exists L\ge0,
>        \ \mathcal C(H(t),H(t),L)\bigr)
>  \quad\Longleftrightarrow\quad S\notin\mathbb Q.
> ```
> For a hypothetical rational value, let $`h_0`$ and $`N_0`$ be its eventual tail period and starting index. Taking $`t\ge\max(h_0,N_0)`$ ensures $`h_0\mid H(t)`$ and $`H(t)\ge N_0`$. The corresponding diagonal difference is then integral, contradicting a certificate at that scale. Conversely, irrationality and pointwise completeness provide a witness at every prescribed $`t`$. The reduction uses one scale parameter; it neither establishes the certificate condition nor makes one fixed scale sufficient for all rational values.*
> 
> *<span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span> (equivalence; supply <span class="sans-serif">\[Open\]</span>) \
> [`irrational_totient_series_iff_lcm_diagonal_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmConeFlatness.lean#L426)*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_lcm_diagonal_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/LcmConeFlatness.lean#L426)

```lean
theorem irrational_totient_series_iff_lcm_diagonal_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
        certifiedKill (periodLcm t) (periodLcm t) L
```

<a id="prop-b3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totient_series_iff_lcm_diagonal_certificate_supply` | [E249_01/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_01/Challenge.lean#L260) | [PaperStatementsA.lean, line 66](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L66) | [E249_01](../evidence/comparator/replay-35882032091/receipt-E249_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b7-60c3ed"></a>

## Proposition (A sufficient condition on the LCM grid)

> *``` math
> \big(\forall t_0,\ \exists t\ge t_0,\ \exists q\,m\,L,\ 0<q \wedge \mathcal{C}(m\cdot{H}\,t)(q\cdot{H}\,t)\ L\big)
> \implies S\notin\mathbb Q.
> ```
> One residue certificate *anywhere* on the two-multiplier LCM cone, at arbitrarily large $`t`$, suffices; the diagonal choice $`q=m=1`$ recovers Proposition <a href="#prop:B3" data-reference-type="ref" data-reference="prop:B3">123</a>. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean (implication; premise unproved)\]</span> \
> [`irrational_totient_series_of_lcm_cone_window_kill_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19014)*

The Lean declaration below states this result.

[`Erdos249257.irrational_totient_series_of_lcm_cone_window_kill_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L19014)

```lean
theorem irrational_totient_series_of_lcm_cone_window_kill_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
      TotientTailPeriodKiller.certifiedKill
        (m * TotientTailPeriodKiller.periodLcm t)
        (q * TotientTailPeriodKiller.periodLcm t) L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
```

<a id="prop-b7-60c3ed-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totient_series_of_lcm_cone_window_kill_supply` | [E249_12/Challenge.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L239) | [PaperStatementsC.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsC.lean#L21) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

Challenge for `irrational_totient_series_of_lcm_cone_window_kill_supply`:

```lean
theorem irrational_totient_series_of_lcm_cone_window_kill_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
      certifiedKill
        (m * periodLcm t)
        (q * periodLcm t) L) :
    Irrational (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) := by sorry
```

<a id="prop-b10"></a>

## Proposition (A finite-grid certificate condition)

> *Let $`H,L\in\mathbb N`$ and let $`Q\subseteq\mathbb N_{>0}`$ be finite and nonempty. Define $`A_q=\sum_{j=1}^{L}\varphi(qH+j)2^{L-j}`$ and $`B_q=qH+L+2`$. If $`B_q<2^L`$ for every $`q\in Q`$ and
> ``` math
> \forall q_i\in Q\ \exists q_j\in Q,\qquad
>  B_{q_j}<(A_{q_i}-A_{q_j})\bmod2^L,
> ```
> then $`R_{q_jH}-R_{q_iH}\notin\mathbb Z`$ for some $`q_i,q_j\in Q`$. Such a test at $`H=H_t`$ for arbitrarily large $`t`$ implies $`S\notin\mathbb Q`$. Neither $`|Q|\ge3`$ nor compatibility of every pair is a hypothesis. The proof, by choosing a minimum tail in the finite set, is given in Theorem <a href="#catalogue:cert:b10a" data-reference-type="ref" data-reference="catalogue:cert:b10a">107</a>. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean (implication; premise unproved)\]</span> \
> [`irrational_totient_series_of_lcm_cone_nonflat_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19140)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L12)

```lean
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L36)

```lean
theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_supply_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L49)

```lean
theorem finite_grid_supply_irrational
    (hs : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, ∃ Q : Finset ℕ,
      Q.Nonempty ∧ (∀ q ∈ Q, 0 < q) ∧
      (∀ q ∈ Q, (q * periodLcm t + L + 2 : ℤ) < 2 ^ L) ∧
      paperGridCertificate (periodLcm t) L Q) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="prop-b10-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paperGridNumerator_eq` | [E249_09/Challenge.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L287) | [PaperStatementsAX.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L238) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_grid_nonintegral_pair` | [E249_09/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L272) | [PaperStatementsAX.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L223) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_grid_supply_irrational` | [E249_09/Challenge.lean, line 279](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L279) | [PaperStatementsAX.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L229) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-c2sup"></a>

## Proposition (Unbounded Farey bounds imply irrationality)

> *The Farey-gap denominator bound at window $`K`$ is currently $`\sim 7.96\times10^{34}`$ at $`K=240`$ (Prop. <a href="#prop:C2-inv" data-reference-type="ref" data-reference="prop:C2-inv">150</a>). If
> ``` math
> \sup_K\, (b+d)(K) = \infty
> ```
> (that is, the proved exclusion bounds are arbitrarily large), then \#249 follows via the denominator-exclusion implication, without assuming the certificate supply in Proposition <a href="#prop:A10" data-reference-type="ref" data-reference="prop:A10">122</a>. No unboundedness claim is proved or attempted in the record. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Open\]</span> \
> [`gap_check_window_1_240_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GapFareyBound.lean#L176)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.gapCertificate_window_1_240`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyGapDenominatorExclusion.lean#L41)

```lean
theorem gapCertificate_window_1_240 (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    GapCertificate 1 240 q
```

where [`GapCertificate`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyGapDenominatorExclusion.lean#L15) is

```lean
def GapCertificate (N K q : ℕ) : Prop :=
  (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K))
      % 2 ^ K + q * (N + K + 2) < 2 ^ K
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_fareyGapExclusionUnbounded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyGapDenominatorExclusion.lean#L29)

```lean
theorem irrational_totientSeries_of_fareyGapExclusionUnbounded
    (hsup : FareyGapExclusionUnbounded) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.gapFareyBound_window_1_240`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyGapDenominatorExclusion.lean#L51)

```lean
theorem gapFareyBound_window_1_240 (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904)
        % 2 ^ 240 + q * 243 < 2 ^ 240
```

<a id="prop-c2sup-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `gapCertificate_window_1_240` | [E249_12/Challenge.lean, line 216](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L216) | [PaperStatementsAJ.lean, line 330](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L330) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `irrational_totientSeries_of_fareyGapExclusionUnbounded` | [E249_12/Challenge.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L227) | [PaperStatementsAJ.lean, line 408](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L408) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `gapFareyBound_window_1_240` | [E249_12/Challenge.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L221) | [PaperStatementsAJ.lean, line 349](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L349) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-d5cons"></a>

## Proposition (The lower bound and a false proposed upper bound)

> *By Prop. <a href="#prop:D4-inv" data-reference-type="ref" data-reference="prop:D4-inv">149</a>, the canonical dyadic totient-kernel family is unconditionally $`(2^e+1)`$-dimensional at every level $`e\ge1`$. Rationality of $`S`$ forces an associated tempered carry orbit with $`\mathbb Q`$-rank $`\ge 2^e-1`$ at every level (Prop. <a href="#prop:CP-02" data-reference-type="ref" data-reference="prop:CP-02">141</a>). An upper bound independent of $`e`$ for these same carry ranks would contradict the lower bound. More generally, a bound $`g(e)`$ with $`g(e)<2^e-1`$ at some level $`e\ge1`$ would suffice, provided it applies to the actual carry under the hypothetical rationality of $`S`$. A bound that merely grows with $`e`$ need not contradict anything. The generic assertion for arbitrary rational coefficient series is false: the $`5/4`$ comparison sequence in Section <a href="#sec:mahler-defect" data-reference-type="ref" data-reference="sec:mahler-defect">10.8</a> has an integer carry satisfying the growth condition and the same rank lower bound. The incompatible integer identity and the finite-shift counterexample (Observation <a href="#prop:B4b-kill" data-reference-type="ref" data-reference="prop:B4b-kill">166</a>) remain separate counterexample results. None is a generic rationality-driven rank ceiling. The evidence label below applies to the proved rank floor and counterexample results, not to the counterfactual upper bound. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientCarryKernelRigidity.lean#L300)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.rank_floor_and_false_proposed_carryRank_ceiling`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GenericCarryRankCeilingCounterexample.lean#L143)

```lean
theorem rank_floor_and_false_proposed_carryRank_ceiling :
    (∀ e : ℕ, 1 ≤ e →
        finrank ℚ
            (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)))
          = 2 ^ e + 1)
      ∧ (¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) →
          ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
            IsTemperedBinaryOrbit Nat.totient v u
              ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                  finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e))))
      ∧ (∀ g : ℕ → ℕ,
          (∀ v : ℕ, ∀ u : ℕ → ℤ, 0 < v →
              IsTemperedBinaryOrbit Nat.totient v u →
              ∀ e : ℕ,
                finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e)))
                  ≤ g e) →
          (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1) →
          Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ ((∀ n : ℕ, ParityPerturbedRationalControl.control n ≤ n)
          ∧ binaryCoeffSeries ParityPerturbedRationalControl.control = 5 / 4
          ∧ ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
              IsTemperedBinaryOrbit ParityPerturbedRationalControl.control v u
                ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                    finrank ℚ
                      (Submodule.span ℚ
                        (Set.range (canonicalCarryKernelFamily u e))))
      ∧ ¬ ∃ g : ℕ → ℕ,
          (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1)
            ∧ ∀ (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ),
                (∀ n : ℕ, c n ≤ n) →
                ¬ Irrational (binaryCoeffSeries c) →
                0 < v →
                IsTemperedBinaryOrbit c v u →
                ∀ e : ℕ,
                  finrank ℚ
                      (Submodule.span ℚ
                        (Set.range (canonicalCarryKernelFamily u e)))
                    ≤ g e
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.fiveQuarter_comparison_rational_with_carryRank_floor`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GenericCarryRankCeilingCounterexample.lean#L64)

```lean
theorem fiveQuarter_comparison_rational_with_carryRank_floor :
    (∀ n : ℕ, ParityPerturbedRationalControl.control n ≤ n)
      ∧ (∀ n : ℕ, n % 2 = 1 →
          ParityPerturbedRationalControl.control n = Nat.totient n)
      ∧ (∀ n : ℕ,
          |(ParityPerturbedRationalControl.control n : ℤ) - Nat.totient n| ≤ 2)
      ∧ binaryCoeffSeries ParityPerturbedRationalControl.control = 5 / 4
      ∧ ¬ Irrational (binaryCoeffSeries ParityPerturbedRationalControl.control)
      ∧ ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
          IsTemperedBinaryOrbit ParityPerturbedRationalControl.control v u
            ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                finrank ℚ
                  (Submodule.span ℚ
                    (Set.range (canonicalCarryKernelFamily u e)))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.no_generic_rationality_carryRank_ceiling`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GenericCarryRankCeilingCounterexample.lean#L100)

```lean
theorem no_generic_rationality_carryRank_ceiling :
    ¬ ∃ g : ℕ → ℕ,
        (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1)
          ∧ ∀ (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ),
              (∀ n : ℕ, c n ≤ n) →
              ¬ Irrational (binaryCoeffSeries c) →
              0 < v →
              IsTemperedBinaryOrbit c v u →
              ∀ e : ℕ,
                finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e)))
                  ≤ g e
```

<a id="prop-d5cons-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rank_floor_and_false_proposed_carryRank_ceiling` | [E249_13/Challenge.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_13/Challenge.lean#L109) | [PaperStatementsF.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_13/PaperStatementsF.lean#L25) | [E249_13](../evidence/comparator/replay-35882032091/receipt-E249_13.json) |
| `fiveQuarter_comparison_rational_with_carryRank_floor` | [E249_13/Challenge.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_13/Challenge.lean#L74) | [PaperStatementsE.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_13/PaperStatementsE.lean#L23) | [E249_13](../evidence/comparator/replay-35882032091/receipt-E249_13.json) |
| `no_generic_rationality_carryRank_ceiling` | [E249_12/Challenge.lean, line 271](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L271) | [PaperStatementsBH.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsBH.lean#L28) | [E249_12](../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `rank_floor_and_false_proposed_carryRank_ceiling`:

```lean
theorem rank_floor_and_false_proposed_carryRank_ceiling :
    (∀ e : ℕ, 1 ≤ e →
        finrank ℚ
            (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)))
          = 2 ^ e + 1)
      ∧ (¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) →
          ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
            IsTemperedBinaryOrbit Nat.totient v u
              ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                  finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e))))
      ∧ (∀ g : ℕ → ℕ,
          (∀ v : ℕ, ∀ u : ℕ → ℤ, 0 < v →
              IsTemperedBinaryOrbit Nat.totient v u →
              ∀ e : ℕ,
                finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e)))
                  ≤ g e) →
          (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1) →
          Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ ((∀ n : ℕ, control n ≤ n)
          ∧ binaryCoeffSeries control = 5 / 4
          ∧ ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
              IsTemperedBinaryOrbit control v u
                ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                    finrank ℚ
                      (Submodule.span ℚ
                        (Set.range (canonicalCarryKernelFamily u e))))
      ∧ ¬ ∃ g : ℕ → ℕ,
          (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1)
            ∧ ∀ (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ),
                (∀ n : ℕ, c n ≤ n) →
                ¬ Irrational (binaryCoeffSeries c) →
                0 < v →
                IsTemperedBinaryOrbit c v u →
                ∀ e : ℕ,
                  finrank ℚ
                      (Submodule.span ℚ
                        (Set.range (canonicalCarryKernelFamily u e)))
                    ≤ g e := by sorry
```

Challenge for `fiveQuarter_comparison_rational_with_carryRank_floor`:

```lean
theorem fiveQuarter_comparison_rational_with_carryRank_floor :
    (∀ n : ℕ, control n ≤ n)
      ∧ (∀ n : ℕ, n % 2 = 1 →
          control n = Nat.totient n)
      ∧ (∀ n : ℕ,
          |(control n : ℤ) - Nat.totient n| ≤ 2)
      ∧ binaryCoeffSeries control = 5 / 4
      ∧ ¬ Irrational (binaryCoeffSeries control)
      ∧ ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
          IsTemperedBinaryOrbit control v u
            ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                finrank ℚ
                  (Submodule.span ℚ
                    (Set.range (canonicalCarryKernelFamily u e))) := by sorry
```

<a id="prop-b12cons"></a>

## Proposition (Soundness of the finite carry test)

> *For fixed $`h,N,K\in\mathbb N`$, use the integer recurrences $`c_{h,N,z}`$ defined above. Test each of the $`2(N+h+1)+1`$ candidates $`z\in\mathbb Z`$ with $`|z|\le N+h+1`$. If every candidate has some $`i\le K`$ for which
> ``` math
> |c_{h,N,z}(i)|\ge N+i+h+2,
> ```
> then $`R_{N+h}-R_N\notin\mathbb Z`$. An integral tail difference would give one of the initial candidates and would remain in the *open* strip $`|c_{h,N,z}(i)|<N+i+h+2`$ at every step. Equality at a boundary already excludes a candidate. This is the soundness implication for a specified finite test; no bound for a successful search depth is asserted.*
> 
> *<span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`tail_diff_notMem_int_of_survivorKill`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L428)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_test_sound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L8)

```lean
theorem finite_carry_test_sound (h N K : ℕ)
    (htest : ∀ z : ℤ, |z| ≤ (N + h + 1 : ℤ) →
      ∃ i : ℕ, i ≤ K ∧ (N + i + h + 2 : ℤ) ≤ |carryOrbit h N z i|) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_candidate_count`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L22)

```lean
theorem finite_carry_candidate_count (h N : ℕ) :
    (Finset.Icc (-(N + h + 1 : ℤ)) (N + h + 1)).card = 2 * (N + h + 1) + 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_true_orbit`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L27)

```lean
theorem finite_carry_true_orbit (h N : ℕ) (z : ℤ)
    (hz : (z : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N z i : ℝ) = totientTail (N + i + h) - totientTail (N + i) ∧
    |carryOrbit h N z i| < (N + i + h + 2 : ℤ)
```

<a id="prop-b12cons-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `finite_carry_test_sound` | [E249_09/Challenge.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L203) | [PaperStatementsAT.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L182) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_carry_candidate_count` | [E249_09/Challenge.lean, line 294](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L294) | [PaperStatementsAJ.lean, line 121](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAJ.lean#L121) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_carry_true_orbit` | [E249_10/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L80) | [PaperStatementsAT.lean, line 160](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L160) | [E249_10](../evidence/comparator/replay-35882032091/receipt-E249_10.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ar-04-inv"></a>

## Proposition (The exact totient difference on an LCM progression)

> *Put $`H=H(t)`$. For every $`j\ge0`$, the arithmetic expression in the linked source equals $`\delta_t(j)=\varphi(2H+j)-\varphi(H+j)`$. For a divisor $`j\mid H`$, this assertion contains a useful product formula, not merely a change of notation. Set
> ``` math
> a=H/j,\qquad g_1=\gcd(j,a+1),\qquad g_2=\gcd(j,2a+1).
> ```
> Then
> ``` math
> \delta_t(j)=\varphi(j)\left(
>  \frac{g_2\varphi(2a+1)}{\varphi(g_2)}
>  -\frac{g_1\varphi(a+1)}{\varphi(g_1)}\right).
> ```
> Here $`j\ge1`$ because $`H>0`$, so both denominators are nonzero. The identity follows from $`\varphi(jx)=\varphi(j)\varphi(x)\gcd(j,x)/\varphi(\gcd(j,x))`$, which retains all primes shared by $`j`$ and $`x`$. If every prime dividing $`j`$ also divides $`a`$, then $`g_1=g_2=1`$, and the formula reduces to $`\varphi(j)\bigl(\varphi(2a+1)-\varphi(a+1)\bigr)`$. For example, at $`H=j=2`$ the two gcds are $`g_1=2`$ and $`g_2=1`$; the exact difference is $`\varphi(6)-\varphi(4)=0`$, whereas discarding the gcd factors would give $`1`$. For $`j\nmid H`$, the source retains the literal totient difference. Thus no coprimality assumption is imposed on the full expression.*
> 
> *<span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`lcmRayArithmeticLetter_eq_deltaTotient`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitArithmetic.lean#L298)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRayArithmeticLetter_eq_totient_difference`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L56)

```lean
theorem lcmRayArithmeticLetter_eq_totient_difference (t j : ℕ) :
    lcmRayArithmeticLetter t j
      = (Nat.totient (2 * periodLcm t + j) : ℤ)
        - (Nat.totient (periodLcm t + j) : ℤ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_mul_eq_totient_mul_gcd_div_totient_gcd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L70)

```lean
theorem totient_mul_eq_totient_mul_gcd_div_totient_gcd {j x : ℕ} (hj : 0 < j)
    (hx : 0 < x) :
    (Nat.totient (j * x) : ℚ)
      = (Nat.totient j : ℚ) * (Nat.totient x : ℚ) * (Nat.gcd j x : ℚ)
          / (Nat.totient (Nat.gcd j x) : ℚ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_denominators_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L86)

```lean
theorem lcmRay_divisor_denominators_pos {t j : ℕ} (hjdvd : j ∣ periodLcm t) :
    0 < j
      ∧ 0 < Nat.totient (Nat.gcd j (periodLcm t / j + 1))
      ∧ 0 < Nat.totient (Nat.gcd j (2 * (periodLcm t / j) + 1))
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_product_formula`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L104)

```lean
theorem lcmRay_divisor_product_formula {t j : ℕ} (hjdvd : j ∣ periodLcm t) :
    ((Nat.totient (2 * periodLcm t + j) : ℚ)
        - (Nat.totient (periodLcm t + j) : ℚ))
      = (Nat.totient j : ℚ) *
          ((Nat.gcd j (2 * (periodLcm t / j) + 1) : ℚ)
                * (Nat.totient (2 * (periodLcm t / j) + 1) : ℚ)
                / (Nat.totient (Nat.gcd j (2 * (periodLcm t / j) + 1)) : ℚ)
            - (Nat.gcd j (periodLcm t / j + 1) : ℚ)
                * (Nat.totient (periodLcm t / j + 1) : ℚ)
                / (Nat.totient (Nat.gcd j (periodLcm t / j + 1)) : ℚ))
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_clean_formula`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L156)

```lean
theorem lcmRay_divisor_clean_formula {t j : ℕ} (hjdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ periodLcm t / j) :
    Nat.gcd j (periodLcm t / j + 1) = 1
      ∧ Nat.gcd j (2 * (periodLcm t / j) + 1) = 1
      ∧ (Nat.totient (2 * periodLcm t + j) : ℤ)
            - (Nat.totient (periodLcm t + j) : ℤ)
          = (Nat.totient j : ℤ)
              * ((Nat.totient (2 * (periodLcm t / j) + 1) : ℤ)
                  - (Nat.totient (periodLcm t / j + 1) : ℤ))
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_nondivisor_literal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L144)

```lean
theorem lcmRay_nondivisor_literal {t j : ℕ} (hjdvd : ¬ j ∣ periodLcm t) :
    lcmRayArithmeticLetter t j
      = (Nat.totient (2 * periodLcm t + j) : ℤ)
        - (Nat.totient (periodLcm t + j) : ℤ) ∧
      lcmRayArithmeticLetter t j = deltaTotient (periodLcm t) (periodLcm t + j)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_gcd_example`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L180)

```lean
theorem lcmRay_divisor_gcd_example :
    periodLcm 2 = 2
      ∧ Nat.gcd 2 (periodLcm 2 / 2 + 1) = 2
      ∧ Nat.gcd 2 (2 * (periodLcm 2 / 2) + 1) = 1
      ∧ (Nat.totient (2 * periodLcm 2 + 2) : ℤ)
            - (Nat.totient (periodLcm 2 + 2) : ℤ) = 0
      ∧ (Nat.totient 2 : ℤ)
            * ((Nat.totient (2 * (periodLcm 2 / 2) + 1) : ℤ)
                - (Nat.totient (periodLcm 2 / 2 + 1) : ℤ)) = 1
```

<a id="prop-ar-04-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lcmRayArithmeticLetter_eq_totient_difference` | [E249_14/Challenge.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L74) | [PaperStatementsAU.lean, line 193](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L193) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `totient_mul_eq_totient_mul_gcd_div_totient_gcd` | [E249_14/Challenge.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L44) | [PaperStatementsAK.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAK.lean#L50) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `lcmRay_divisor_denominators_pos` | [E249_14/Challenge.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L91) | [PaperStatementsAU.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L212) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `lcmRay_divisor_product_formula` | [E249_14/Challenge.lean, line 108](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L108) | [PaperStatementsAU.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L229) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `lcmRay_divisor_clean_formula` | [E249_14/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L80) | [PaperStatementsAU.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L200) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `lcmRay_nondivisor_literal` | [E249_14/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L120) | [PaperStatementsAU.lean, line 242](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L242) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `lcmRay_divisor_gcd_example` | [E249_14/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L97) | [PaperStatementsAU.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L219) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ar-03-inv"></a>

## Proposition (A lower bound for the totient of a rough integer)

> *Let $`a\ge8`$, set $`t=2^a`$, and let $`n>0`$ be an integer all of whose prime factors exceed $`t`$. If $`n<2^{2t}`$, then $`n`$ has fewer than $`t/4`$ distinct prime factors and
> ``` math
> \varphi(n)>\frac34 n.
> ```
> If $`n`$ has $`r`$ distinct prime factors, then $`n\ge t^r=2^{ar}`$, so $`ar<2t`$ and $`r<t/4`$ because $`a\ge8`$. For the second, use $`\varphi(n)/n=\prod_{p\mid n}(1-1/p)\ge1-\sum_{p\mid n}1/p>3/4`$. These are bounds for rough integers in the stated size range; they are not pointwise bounds for arbitrary totient values.*
> 
> *<span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`three_quarters_mul_lt_totient_of_rough_lt_two_pow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitArithmetic.lean#L768)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.rough_integer_prime_count_and_totient_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L215)

```lean
theorem rough_integer_prime_count_and_totient_bound {a n : ℕ} (ha : 8 ≤ a)
    (hnPos : 0 < n) (hrough : ∀ r : ℕ, Nat.Prime r → r ∣ n → 2 ^ a < r)
    (hnPow : n < 2 ^ (2 * 2 ^ a)) :
    n.primeFactors.card < 2 ^ a / 4
      ∧ (3 / 4 : ℚ) * (n : ℚ) < (Nat.totient n : ℚ)
```

<a id="prop-ar-03-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rough_integer_prime_count_and_totient_bound` | [E249_14/Challenge.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L200) | [PaperStatementsAJ.lean, line 491](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAJ.lean#L491) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ar-05-inv"></a>

## Proposition (Positivity of the short-window differences)

> *For $`a\ge8`$ and $`1\le j<2\cdot2^a`$,
> ``` math
> \delta_{2^a}(j)=\varphi(2H_{2^a}+j)-\varphi(H_{2^a}+j)>0.
> ```
> The proof treats divisor offsets and the exceptional prime-power offsets separately, using multiplicativity and the rough-integer estimate of Proposition <a href="#prop:AR-03-inv" data-reference-type="ref" data-reference="prop:AR-03-inv">130</a>. No rationality hypothesis is used. Positivity of these finitely many coefficients contributes to the later sign theorem; a bound for the remaining infinite tail is still needed to obtain that theorem.*
> 
> *<span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`lcmRayArithmeticLetter_pos_of_lt_two_mul`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1703)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_totient_difference_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L229)

```lean
theorem shortWindow_totient_difference_pos {a j : ℕ} (ha : 8 ≤ a)
    (hjpos : 0 < j) (hjlt : j < 2 * 2 ^ a) :
    0 < (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
          - (Nat.totient (periodLcm (2 ^ a) + j) : ℤ)
```

<a id="prop-ar-05-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `shortWindow_totient_difference_pos` | [E249_14/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L146) | [PaperStatementsAU.lean, line 421](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L421) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ar-06-inv"></a>

## Proposition (The accumulated sum is the discrepancy)

> *For all $`t,L\in\mathbb N`$, the weighted diagonal sum is exactly
> ``` math
> \sum_{j=1}^{L}\delta_t(j)2^{L-j}=D(H(t),H(t),L).
> ```
> Thus its two-sided residue inequality is precisely $`\mathcal C(H(t),H(t),L)`$. The equality follows term by term from the definition of $`\delta_t`$. A separate restriction on $`L`$, when present, remains part of the hypothesis; this identity does not supply such a restricted-depth witness.*
> 
> *<span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`lcmDiagonalArithmeticKill_iff_certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2045)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.weighted_shortWindow_sum_eq_windowDiscrepancy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L241)

```lean
theorem weighted_shortWindow_sum_eq_windowDiscrepancy (t L : ℕ) :
    (∑ r ∈ Finset.range L,
        ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
            - (Nat.totient (periodLcm t + (r + 1)) : ℤ)) * 2 ^ (L - 1 - r))
      = windowDiscrepancy (periodLcm t) (periodLcm t) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.weighted_shortWindow_band_iff_certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L262)

```lean
theorem weighted_shortWindow_band_iff_certifiedKill (t L : ℕ) :
    ((2 * (periodLcm t : ℤ) + L + 2 <
          (∑ r ∈ Finset.range L,
              ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
                  - (Nat.totient (periodLcm t + (r + 1)) : ℤ))
                * 2 ^ (L - 1 - r)) % 2 ^ L)
        ∧ (∑ r ∈ Finset.range L,
              ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
                  - (Nat.totient (periodLcm t + (r + 1)) : ℤ))
                * 2 ^ (L - 1 - r)) % 2 ^ L
            < 2 ^ L - (2 * (periodLcm t : ℤ) + L + 2))
      ↔ certifiedKill (periodLcm t) (periodLcm t) L
```

<a id="prop-ar-06-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `weighted_shortWindow_sum_eq_windowDiscrepancy` | [E249_14/Challenge.lean, line 173](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L173) | [PaperStatementsAU.lean, line 548](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L548) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `weighted_shortWindow_band_iff_certifiedKill` | [E249_14/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L159) | [PaperStatementsAU.lean, line 533](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L533) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sep-01-inv"></a>

## Proposition (A global-to-local identity)

> *``` math
> \Omega_a \;=\; 2^H(2^H-1)\Big(\textstyle\sum_n' \varphi(n)/2^n\Big) - \big(\Phi_{2H}-\Phi_H\big),\quad H={H}(2^a).
> ```
> Thus a separation estimate for $`\Omega_a`$ is an estimate for this integer translate of a multiple of $`S`$. The identity does not require other rational-approximation arguments to use this particular translate. <span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSeparation.lean#L68)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_global_to_local`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L24)

```lean
theorem actualLcmTailOrbit_global_to_local (a : ℕ) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      = (2 : ℝ) ^ periodLcm (2 ^ a) * ((2 : ℝ) ^ periodLcm (2 ^ a) - 1)
            * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
          - ((totientPrefix (2 * periodLcm (2 ^ a)) : ℝ)
              - (totientPrefix (periodLcm (2 ^ a)) : ℝ))
```

<a id="prop-sep-01-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `actualLcmTailOrbit_global_to_local` | [E249_14/Challenge.lean, line 215](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L215) | [PaperStatementsAT.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAT.lean#L264) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sep-02-inv"></a>

## Proposition (A rational approximation with an error bound)

> *For all $`a,q\in\mathbb N`$, with $`H=H_{2^a}`$ and the finite $`\rho_{a,q}`$ defined above,
> ``` math
> |\Omega_a-\rho_{a,q}|<\varepsilon_{a,q}
>      =\frac{2H+2q+3}{2^{2q+1}}.
> ```
> The triangle inequality transfers a separation estimate between the real tail and its rational approximation at the cost of this error. The bound tends to zero with $`q`$ for fixed $`a`$; no assertion of optimality is made. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`abs_actualLcmTailOrbit_sub_rawApprox_lt`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSeparation.lean#L141)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L39)

```lean
theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit (a q : ℕ) :
    |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)))
        - actualLcmRawApprox a q|
      < ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.tendsto_actualLcmRawErrorRadius_atTop_nhds_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L49)

```lean
theorem tendsto_actualLcmRawErrorRadius_atTop_nhds_zero (a : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1))
      Filter.atTop (nhds 0)
```

<a id="prop-sep-02-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit` | [E249_14/Challenge.lean, line 285](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L285) | [PaperStatementsAX.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAX.lean#L247) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `tendsto_actualLcmRawErrorRadius_atTop_nhds_zero` | [E249_14/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L152) | [PaperStatementsAU.lean, line 443](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L443) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sgn-01"></a>

## Proposition (Unconditional positivity)

> *For $`a\ge8`$, $`J+(a+6)<2\cdot2^a`$:
> ``` math
> 0 < R_{2H+J} - R_{H+J},\qquad H={H}(2^a),
> ```
> with no irrationality hypothesis; the true, infinite, real translated tail difference is strictly positive throughout almost the entire short window, proved unconditionally from Prop. <a href="#prop:AR-05-inv" data-reference-type="ref" data-reference="prop:AR-05-inv">131</a> plus a directed one-sided tail bound. Any argument about the sign of the actual orbit (not merely its residue mod $`2^L`$) must agree with this; specialised at $`J=0`$ this gives $`0<\Omega_a`$. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`actualLcmTailDiff_shift_pos`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSign.lean#L39)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_tailDiff_shift_pos_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L82)

```lean
theorem actualLcm_tailDiff_shift_pos_paper {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 < totientTail (2 * periodLcm (2 ^ a) + J)
          - totientTail (periodLcm (2 ^ a) + J)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L89)

```lean
theorem actualLcmTailOrbit_pos {a : ℕ} (ha : 8 ≤ a) :
    0 < totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
```

<a id="prop-sgn-01-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `actualLcm_tailDiff_shift_pos_paper` | [E249_14/Challenge.lean, line 250](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L250) | [PaperStatementsAT.lean, line 310](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAT.lean#L310) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `actualLcmTailOrbit_pos` | [E249_14/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L223) | [PaperStatementsAT.lean, line 273](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAT.lean#L273) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sgn-03"></a>

## Proposition (The residue forced by integrality)

> *Let $`a,J,K\in\mathbb N`$, $`a\ge8`$, $`H=H(2^a)`$, and assume
> ``` math
> J+K+(a+6)<2\cdot2^a,\qquad 2H+J+K+2<2^K.
> ```
> If $`R_{2H+J}-R_{H+J}\in\mathbb Z`$, then
> ``` math
> \begin{aligned}
>  D(H,H+J,K)\bmod2^K
>    &=2^K-\bigl(R_{2H+J+K}-R_{H+J+K}\bigr),\\
>  0<R_{2H+J+K}-R_{H+J+K}&<2H+J+K+2.
>  \end{aligned}
> ```
> The later tail difference is a positive integer. Its negative is the representative near zero, while the least nonnegative residue lies near $`2^K`$. Positivity alone therefore does not prove nonintegrality; a separate estimate must exclude this upper interval.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`actualLcm_integral_forces_topEdgeResidue`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSign.lean#L211)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_integral_forces_topEdgeResidue_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L105)

```lean
theorem actualLcm_integral_forces_topEdgeResidue_paper {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ K)
    (hint : ∃ d : ℤ, (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J)
        - totientTail (periodLcm (2 ^ a) + J)) :
    ∃ e : ℤ,
      ((e : ℝ) = totientTail (2 * periodLcm (2 ^ a) + J + K)
          - totientTail (periodLcm (2 ^ a) + J + K))
        ∧ windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K
              % (2 : ℤ) ^ K
            = (2 : ℤ) ^ K - e
        ∧ 0 < e
        ∧ e < ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
        ∧ ((2 : ℤ) ^ K - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
              < windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K
                  % (2 : ℤ) ^ K
            ∧ windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K
                  % (2 : ℤ) ^ K < (2 : ℤ) ^ K)
        ∧ (2 : ℤ) ^ K ∣
            windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K + e
```

<a id="prop-sgn-03-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `actualLcm_integral_forces_topEdgeResidue_paper` | [E249_14/Challenge.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L227) | [PaperStatementsAT.lean, line 286](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAT.lean#L286) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-02-inv"></a>

## Proposition (The penultimate term of a partial divisibility pattern)

> *Let $`a,J,K,m\in\mathbb N`$, $`a\ge8`$, $`H=H_{2^a}`$ and $`B=2H+J+K+2`$. Suppose that
> ``` math
> \begin{gathered}
>  0<m\le K,\qquad J+K+a+6<2\cdot2^a,\\
>  B<2^m,\qquad \delta_{2^a}(J+K)\le2^m-B,\\
>  2^{r+1}\mid\delta_{2^a}(J+K-m+r+1)
>        \quad(0\le r,\ r+1<m).
> \end{gathered}
> ```
> Then
> ``` math
> \delta_{2^a}(J+K-1)=2^{m-1},\qquad 2^m<2B.
> ```
> Indeed, $`B\ge4`$ and $`B<2^m`$ force $`m\ge3`$. The penultimate divisibility, positivity, and the bound $`\delta_{2^a}(J+K-1)<B<2^m`$ leave $`2^{m-1}`$ as its only possible value. Thus the modulus lies in the strict interval $`B<2^m<2B`$; there is at most one possible power of two. The value fixed at $`2^{m-1}`$ is the *penultimate* difference. The terminal difference $`\delta_{2^a}(J+K)`$ instead satisfies the separate upper bound in the hypotheses. These restrictions are necessary for the specified pattern; the proposition does not construct such patterns at arbitrarily large $`a`$. <span class="sans-serif">\[bounded\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`puncturedDyadicStaircase_penultimate_eq_half`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1187)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.penultimate_shortWindow_difference_eq_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L37)

```lean
theorem penultimate_shortWindow_difference_eq_half {a J K m : ℕ} (ha : 8 ≤ a)
    (hmPos : 0 < m) (hmK : m ≤ K)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hroom : ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m)
    (hlast : (Nat.totient (2 * periodLcm (2 ^ a) + (J + K)) : ℤ)
          - (Nat.totient (periodLcm (2 ^ a) + (J + K)) : ℤ)
        ≤ (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ))
    (hprefix : ∀ r : ℕ, r + 1 < m →
        (2 : ℤ) ^ (r + 1) ∣
          ((Nat.totient (2 * periodLcm (2 ^ a) + (J + K - m + r + 1)) : ℤ)
            - (Nat.totient (periodLcm (2 ^ a) + (J + K - m + r + 1)) : ℤ))) :
    ((Nat.totient (2 * periodLcm (2 ^ a) + (J + K - 1)) : ℤ)
          - (Nat.totient (periodLcm (2 ^ a) + (J + K - 1)) : ℤ))
        = (2 : ℤ) ^ (m - 1)
      ∧ (2 : ℤ) ^ m < 2 * ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
      ∧ (4 : ℤ) ≤ ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
      ∧ 3 ≤ m
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.dyadicScale_unique_in_open_interval`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L80)

```lean
theorem dyadicScale_unique_in_open_interval {B : ℤ} {m₁ m₂ : ℕ}
    (h₁ : B < (2 : ℤ) ^ m₁) (h₁' : (2 : ℤ) ^ m₁ < 2 * B)
    (h₂ : B < (2 : ℤ) ^ m₂) (h₂' : (2 : ℤ) ^ m₂ < 2 * B) :
    m₁ = m₂
```

<a id="prop-te-02-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `penultimate_shortWindow_difference_eq_half` | [E249_14/Challenge.lean, line 127](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L127) | [PaperStatementsAU.lean, line 278](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L278) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `dyadicScale_unique_in_open_interval` | [E249_14/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L194) | [PaperStatementsAJ.lean, line 278](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAJ.lean#L278) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-03-inv"></a>

## Proposition (An equivalent test using two residue bits)

> *For every $`h,N\in\mathbb N`$, existence of a certificate at some depth is equivalent to the following explicit condition:
> ``` math
> \exists s,b\in\mathbb N,\quad
>  \mathcal C(h,N+s,b+1)\quad\text{or}\quad
>  \begin{cases}
>   N+s+h+b+4<2^b,\\
>   2^b\le D(h,N+s,b+2)\bmod2^{b+2}<3\cdot2^b.
>  \end{cases}
> ```
> The last interval says that the two leading bits are $`01`$ or $`10`$. The proof uses the first successful certificate of depth $`L`$ and may take $`b=\lfloor\log_2(N+h+L+2)\rfloor+1`$. Since $`b`$ depends on that unknown $`L`$, the equivalence is not an a priori bound on the search depth. The proof uses the finite tail recurrence and its size bound; it supplies no totient-specific assertion that a witness exists. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`exists_certifiedKill_iff_guardCylinderWitness`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L844)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_iff_twoBitResidueTest`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L129)

```lean
theorem exists_certifiedKill_iff_twoBitResidueTest (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔
      ∃ s b : ℕ,
        certifiedKill h (N + s) (b + 1) ∨
          (N + s + h + b + 4 < 2 ^ b
            ∧ (2 : ℤ) ^ b ≤ windowDiscrepancy h (N + s) (b + 2) % (2 : ℤ) ^ (b + 2)
            ∧ windowDiscrepancy h (N + s) (b + 2) % (2 : ℤ) ^ (b + 2)
                < 3 * (2 : ℤ) ^ b)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.dyadicMixedGuard_iff_twoBitBand`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L104)

```lean
theorem dyadicMixedGuard_iff_twoBitBand (A : ℤ) (b : ℕ) :
    DyadicMixedGuard A b ↔
      ((2 : ℤ) ^ b ≤ A % (2 : ℤ) ^ (b + 2)
        ∧ A % (2 : ℤ) ^ (b + 2) < 3 * (2 : ℤ) ^ b)
```

<a id="prop-te-03-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_certifiedKill_iff_twoBitResidueTest` | [E249_14/Challenge.lean, line 256](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L256) | [PaperStatementsAT.lean, line 423](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAT.lean#L423) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `dyadicMixedGuard_iff_twoBitBand` | [E249_14/Challenge.lean, line 188](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L188) | [PaperStatementsAJ.lean, line 273](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAJ.lean#L273) | [E249_14](../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-fr-02-inv"></a>

## Proposition (The factor in a second difference)

> *Let $`a\ge4`$ and $`j\ge1`$ be integers with $`j^2\le2^a`$, and put $`H_a=H(2^a)=\operatorname{lcm}(1,\ldots,2^a)`$. Then
> ``` math
> 2\varphi(j)\mid
>  \varphi(3H_a+j)-2\varphi(2H_a+j)+\varphi(H_a+j).
> ```
> To see the factor, set $`A=H_a/j`$. The square bound ensures that $`j\mid H_a`$ and that every prime divisor $`p`$ of $`j`$ also divides $`A`$: indeed, $`pj\le j^2\le2^a`$ implies $`pj\mid H_a`$. Consequently $`\gcd(j,qA+1)=1`$ for $`q=1,2,3`$, and the displayed difference equals
> ``` math
> \varphi(j)\bigl(\varphi(3A+1)-2\varphi(2A+1)+\varphi(A+1)\bigr).
> ```
> Also $`2j\le2^a`$, so $`2j\mid H_a`$ and $`A\ge2`$ is even. The three arguments $`qA+1`$ are therefore odd and greater than two, and all three totients are even. This proves the extra factor of two. The divisibility is a lower bound, not an exact valuation at each LCM height. The different family in Observation <a href="#prop:FR-03-kill" data-reference-type="ref" data-reference="prop:FR-03-kill">159</a> does not satisfy these LCM and square-window hypotheses, so it does not establish sharpness within this restricted family. <span class="sans-serif">\[bounded\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`two_mul_totient_dvd_fixedRankSecondDifference`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientFixedRankLcmAsymptotic.lean#L519)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.two_mul_totient_dvd_totient_second_difference`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L219)

```lean
theorem two_mul_totient_dvd_totient_second_difference {a j : ℕ} (ha : 4 ≤ a)
    (hj : 0 < j) (hsq : j * j ≤ 2 ^ a) :
    (2 * (Nat.totient j : ℤ)) ∣
          ((Nat.totient (3 * periodLcm (2 ^ a) + j) : ℤ)
            - 2 * (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
            + (Nat.totient (periodLcm (2 ^ a) + j) : ℤ))
      ∧ ((Nat.totient (3 * periodLcm (2 ^ a) + j) : ℤ)
            - 2 * (Nat.totient (2 * periodLcm (2 ^ a) + j) : ℤ)
            + (Nat.totient (periodLcm (2 ^ a) + j) : ℤ))
          = (Nat.totient j : ℤ)
              * ((Nat.totient (3 * (periodLcm (2 ^ a) / j) + 1) : ℤ)
                  - 2 * (Nat.totient (2 * (periodLcm (2 ^ a) / j) + 1) : ℤ)
                  + (Nat.totient (periodLcm (2 ^ a) / j + 1) : ℤ))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.fixedRank_cleanWindow_structure`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L169)

```lean
theorem fixedRank_cleanWindow_structure {a j : ℕ} (ha : 4 ≤ a) (hj : 0 < j)
    (hsq : j * j ≤ 2 ^ a) :
    j ∣ periodLcm (2 ^ a)
      ∧ (∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ periodLcm (2 ^ a) / j)
      ∧ 2 * j ≤ 2 ^ a
      ∧ 2 * j ∣ periodLcm (2 ^ a)
      ∧ 2 ≤ periodLcm (2 ^ a) / j
      ∧ Even (periodLcm (2 ^ a) / j)
      ∧ (∀ q : ℕ, 0 < q → q ≤ 3 →
          Nat.gcd j (q * (periodLcm (2 ^ a) / j) + 1) = 1
            ∧ Odd (q * (periodLcm (2 ^ a) / j) + 1)
            ∧ 2 < q * (periodLcm (2 ^ a) / j) + 1
            ∧ Even (Nat.totient (q * (periodLcm (2 ^ a) / j) + 1)))
```

<a id="prop-fr-02-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `two_mul_totient_dvd_totient_second_difference` | [E249_15/Challenge.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L168) | [PaperStatementsAU.lean, line 507](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAU.lean#L507) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `fixedRank_cleanWindow_structure` | [E249_15/Challenge.lean, line 105](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L105) | [PaperStatementsAT.lean, line 507](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L507) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-01-inv"></a>

## Proposition (Carry displacement and tail integrality)

> *For a positive integer $`v`$ and a tempered integral totient carry $`u`$,
> ``` math
> v\mid u(N+k)-u(N)\quad\Longleftrightarrow\quad R_{N+k}-R_N\in\mathbb{Z}.
> ```
> Indeed, temperedness identifies $`u(N)=vR_N`$, so the displacement is $`v(R_{N+k}-R_N)`$. This is a divisibility test for that displacement, not a dimension bound for the carry sections. The same proof works for another coefficient sequence once its tempered carry has been identified with its scaled tail; those hypotheses must be checked in each application. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`carryShift_dvd_iff_tailDiff_mem_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailCarryPeriod.lean#L77)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.carryShift_dvd_iff_tailDiff_integral`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TailCarryPeriodAndRankFloor.lean#L31)

```lean
theorem carryShift_dvd_iff_tailDiff_integral {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    (v : ℤ) ∣ u (N + k) - u N
      ↔ ∃ z : ℤ, (z : ℝ) = totientTail (N + k) - totientTail N
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.temperedCarry_eq_scaledTail_and_shift`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TailCarryPeriodAndRankFloor.lean#L20)

```lean
theorem temperedCarry_eq_scaledTail_and_shift {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    ((u N : ℤ) : ℝ) = (v : ℝ) * totientTail N
      ∧ ((u (N + k) - u N : ℤ) : ℝ)
          = (v : ℝ) * (totientTail (N + k) - totientTail N)
```

<a id="prop-cp-01-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `carryShift_dvd_iff_tailDiff_integral` | [E249_15/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L190) | [PaperStatementsBC.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBC.lean#L21) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `temperedCarry_eq_scaledTail_and_shift` | [E249_15/Challenge.lean, line 196](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L196) | [PaperStatementsBC.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBC.lean#L26) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-02"></a>

## Proposition (A consequence of rationality and its limitation)

> *If $`S\in\mathbb Q`$, there are a positive integer $`v`$ and a tempered integer carry orbit $`u`$ such that its retained sections through every level $`e`$ have rational rank at least $`2^e-1`$. At the same time, those sections are uniformly eventually periodic modulo $`v`$. Periodicity after reduction modulo $`v`$ is a statement in a finite quotient; it is not a rank upper bound over $`\mathbb Q`$. Proposition <a href="#prop:D5cons" data-reference-type="ref" data-reference="prop:D5cons">127</a> gives the lower bound, while the rational comparison sequence explains why a general rank upper bound cannot be deduced from these recurrence assumptions alone. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`not_irrational_totientSeries_implies_mod_period_and_unbounded_rank`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailCarryPeriod.lean#L224)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.rationality_forces_mod_period_and_unbounded_rank`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TailCarryPeriodAndRankFloor.lean#L46)

```lean
theorem rationality_forces_mod_period_and_unbounded_rank
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ, 2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u
```

<a id="prop-cp-02-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rationality_forces_mod_period_and_unbounded_rank` | [E249_15/Challenge.lean, line 225](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L225) | [PaperStatementsBH.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBH.lean#L50) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-05-inv"></a>

## Proposition (A totient difference congruent to two modulo four)

> *For every positive integer $`h`$ and every $`B\in\mathbb N`$, there is a prime $`p>B`$ such that
> ``` math
> \varphi(p+4h)-\varphi(p)\equiv2\pmod4.
> ```
> To construct $`p`$, set $`H=4h`$, choose a prime $`r>H`$ with $`r\equiv1\pmod4`$, and use Dirichlet’s theorem in the progression $`p\equiv3r-H\pmod{4r}`$. This progression is reduced: its residue is odd and is $`-H\not\equiv0\pmod r`$. Then $`p\equiv3\pmod4`$, so $`\varphi(p)=p-1\equiv2\pmod4`$, whereas $`r\mid p+H`$ gives $`4\mid\varphi(p+H)`$. Subtracting gives the stated congruence. This supplies the arithmetic congruence at arbitrarily large primes; the additional finite exclusion in Proposition <a href="#prop:CP-07" data-reference-type="ref" data-reference="prop:CP-07">121</a> remains a separate hypothesis.*
> 
> *<span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`exists_prime_deltaTotient_four_mul_mod_four_two`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailCarryPeriod.lean#L384)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_totient_shift_four_mul_congr_two_mod_four`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L28)

```lean
theorem exists_prime_totient_shift_four_mul_congr_two_mod_four
    (h B : ℕ) (hh : 0 < h) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4]
```

<a id="prop-cp-05-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_prime_totient_shift_four_mul_congr_two_mod_four` | [E249_15/Challenge.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L239) | [PaperStatementsAJ.lean, line 304](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAJ.lean#L304) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ta-inv"></a>

## Proposition (An arbitrarily long zero prefix followed by a two-adic pulse)

> *Let $`K\ge2`$ and $`H>K`$ be integers. For every $`B\in\mathbb N`$ there is a prime $`p>\max(B,H+K)`$ such that
> ``` math
> \begin{aligned}
>  p&\equiv1+2^{K-1}\pmod{2^K},&
>  2^K&\mid\varphi(p+H),\\
>  2^K&\mid\varphi(p-j),&
>  2^K&\mid\varphi(p-j+H)\qquad(1\le j<K).
> \end{aligned}
> ```
> The construction uses $`2K-1`$ distinct auxiliary primes congruent to $`1\pmod{2^K}`$: one for $`p+H`$, and two for each of the $`K-1`$ preceding positions. Choose them larger than $`\max(H+K,2^K)`$. For the first prime impose $`p\equiv-H`$; for the pair at position $`j`$ impose $`p\equiv j`$ and $`p\equiv j-H`$, respectively. These nonzero residues, together with the displayed odd residue modulo $`2^K`$, combine by the Chinese remainder theorem into a reduced progression. Dirichlet’s theorem then supplies arbitrarily large prime values of $`p`$. Each auxiliary prime contributes the required factor $`2^K`$ to the corresponding totient.*
> 
> *Thus the first $`K-1`$ totient differences in the window starting at $`p-K`$ vanish modulo $`2^K`$, while the last is $`2^{K-1}`$ modulo $`2^K`$. Consequently
> ``` math
> D(H,p-K,K)\equiv2^{K-1}\pmod{2^K}.
> ```
> If $`R_{N+H}-R_N\in\mathbb Z`$ for every $`N\ge N_0`$, choose such a prime with $`p\ge N_0+K`$. Iterating the carry recurrence from $`p-K`$ then gives
> ``` math
> R_{p+H}-R_p\in\mathbb Z,\qquad
>  R_{p+H}-R_p\equiv2^{K-1}\pmod{2^K}.
> ```
> The initial integer is multiplied by $`2^K`$ and disappears only after reduction modulo $`2^K`$. This does not bound its higher quotient. The condition $`H>K`$ is part of the construction; it does not provide arbitrarily large $`K`$ for one fixed shift $`H`$.*
> 
> *<span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`exists_prime_totient_twoAdic_pulse_divisors`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTwoAdicPulseBlock.lean#L54)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_pulse_block`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L81)

```lean
theorem exists_prime_twoAdic_pulse_block (K H B : ℕ) (hK : 2 ≤ K) (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ H + K < p ∧ p.Prime ∧
      p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K] ∧
      2 ^ K ∣ Nat.totient (p + H) ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        2 ^ K ∣ Nat.totient (p - j) ∧ 2 ^ K ∣ Nat.totient (p - j + H)) ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K]
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.pulse_delta_of_divisor_data`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L41)

```lean
theorem pulse_delta_of_divisor_data {H K p : ℕ} (hK : 2 ≤ K) (hp : p.Prime)
    (hmod : p ≡ 1 + 2 ^ (K - 1) [MOD 2 ^ K])
    (htop : 2 ^ K ∣ Nat.totient (p + H))
    (hlower : ∀ j : ℕ, 1 ≤ j → j < K →
      2 ^ K ∣ Nat.totient (p - j) ∧ 2 ^ K ∣ Nat.totient (p - j + H)) :
    deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      ∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_integral_tailDiff_half_pulse`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L100)

```lean
theorem exists_prime_integral_tailDiff_half_pulse
    {H K N₀ : ℕ} (hK : 2 ≤ K) (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ))
    (B : ℕ) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K]
```

<a id="prop-ta-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_prime_twoAdic_pulse_block` | [E249_15/Challenge.lean, line 93](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L93) | [PaperStatementsAT.lean, line 483](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L483) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `pulse_delta_of_divisor_data` | [E249_15/Challenge.lean, line 130](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L130) | [PaperStatementsAU.lean, line 348](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAU.lean#L348) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `exists_prime_integral_tailDiff_half_pulse` | [E249_15/Challenge.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L83) | [PaperStatementsAT.lean, line 466](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L466) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-mp-01-inv"></a>

## Proposition (A Möbius-inversion formula for the tail)

> *For $`N\in\mathbb N`$ and $`d\ge1`$, let $`r_d(N)=d-(N\bmod d)`$ and $`q_d(N)=\lfloor N/d\rfloor+1`$. Thus $`r_d(N)`$ is the distance to the next strictly larger multiple of $`d`$, so $`1\le r_d(N)\le d`$. Möbius inversion gives
> ``` math
> R_N=\sum_{d\ge1}\mu(d)2^{d-r_d(N)}
>  \left(\frac{q_d(N)}{2^d-1}+\frac{1}{(2^d-1)^2}\right).
> ```
> Indeed, substitute $`\varphi(n)=\sum_{d\mid n}\mu(d)n/d`$ and group by $`d`$. Its multiples after $`N`$ have quotients $`q_d(N)+\ell`$ and forward distances $`r_d(N)+d\ell`$, for $`\ell\ge0`$; summing the two geometric series gives the formula. Absolute convergence justifies the regrouping, since the sum of the absolute divisor contributions at $`n`$ is at most $`\sum_{d\mid n}n/d\le n^2`$, and $`\sum_{n>N}n^2 2^{N-n}<\infty`$. This identity is available for later transformations; it does not assert that every Möbius or Lambert-series argument must use it.*
> 
> *<span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`totientTail_eq_tsum_shiftedMobiusPulse`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientShiftedMobiusPulse.lean#L547)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_spec`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L114)

```lean
theorem forwardMultiple_spec (N : ℕ) {d : ℕ} (hd : 0 < d) :
    forwardMultipleShift N d = d - N % d ∧
      forwardMultipleQuotient N d = N / d + 1 ∧
      1 ≤ forwardMultipleShift N d ∧
      forwardMultipleShift N d ≤ d ∧
      d ∣ N + forwardMultipleShift N d
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.forwardMultipleShift_least`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L125)

```lean
theorem forwardMultipleShift_least (N : ℕ) {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hlt : m < forwardMultipleShift N d) : ¬ d ∣ N + m
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_enumeration`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L139)

```lean
theorem forwardMultiple_enumeration (N : ℕ) {d : ℕ} (hd : 0 < d) (l : ℕ) :
    N + (forwardMultipleShift N d + d * l) =
      d * (forwardMultipleQuotient N d + l)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.totientTail_eq_tsum_mobius_inversion`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L151)

```lean
theorem totientTail_eq_tsum_mobius_inversion (N : ℕ) :
    totientTail N =
      ∑' d : ℕ+,
        (((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) *
            (2 : ℝ) ^ ((d : ℕ) - forwardMultipleShift N (d : ℕ))) *
          (((forwardMultipleQuotient N (d : ℕ) : ℕ) : ℝ) /
              ((2 : ℝ) ^ (d : ℕ) - 1) +
            1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2)
```

<a id="prop-mp-01-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `forwardMultiple_spec` | [E249_15/Challenge.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L264) | [PaperStatementsBA.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBA.lean#L39) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `forwardMultipleShift_least` | [E249_15/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L255) | [PaperStatementsBA.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBA.lean#L32) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `forwardMultiple_enumeration` | [E249_15/Challenge.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L259) | [PaperStatementsBA.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBA.lean#L35) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `totientTail_eq_tsum_mobius_inversion` | [E249_15/Challenge.lean, line 279](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L279) | [PaperStatementsBM.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBM.lean#L21) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sk-01-inv"></a>

## Proposition (Explicit finite examples)

> *The finite certificates $`\mathcal C(H_{16},H_{16},23)`$ and $`\mathcal C(H_{64},H_{64},93)`$ imply $`\Omega_4,\Omega_6\notin\mathbb Z`$. Both satisfy the short-window restriction, since $`23<32`$ and $`93<128`$. They use the pre-existing certificates /. These are two explicit instances of the desired condition, not the start of a proved induction or a claim that no other finite instances can be checked.*
> 
> *<span class="sans-serif">\[fixed\]</span> <span class="sans-serif">\[Cert\]</span> \
> [`actualLcmTailOrbit_four_and_six_notMem_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmShortKill.lean#L35)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_certificates_kill_omega_four_and_six`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L36)

```lean
theorem shortWindow_certificates_kill_omega_four_and_six :
    certifiedKill (periodLcm 16) (periodLcm 16) 23 ∧
      (23 : ℕ) < 32 ∧
      certifiedKill (periodLcm 64) (periodLcm 64) 93 ∧
      (93 : ℕ) < 128 ∧
      actualLcmTailOrbit 4 ∉ Set.range ((↑) : ℤ → ℝ) ∧
      actualLcmTailOrbit 6 ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_inequalities`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L49)

```lean
theorem shortWindow_inequalities :
    (23 : ℕ) < 2 * 2 ^ 4 ∧ (93 : ℕ) < 2 * 2 ^ 6
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_eq_tail_difference`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L27)

```lean
theorem actualLcmTailOrbit_eq_tail_difference (a : ℕ) :
    actualLcmTailOrbit a =
      totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
```

<a id="prop-sk-01-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `shortWindow_certificates_kill_omega_four_and_six` | [E249_15/Challenge.lean, line 153](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L153) | [PaperStatementsAU.lean, line 420](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAU.lean#L420) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `shortWindow_inequalities` | [E249_15/Challenge.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L245) | [PaperStatementsAJ.lean, line 502](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAJ.lean#L502) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `actualLcmTailOrbit_eq_tail_difference` | [E249_15/Challenge.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L67) | [PaperStatementsAT.lean, line 253](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L253) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-a5-inv"></a>

## Proposition (The necessary depth)

> *Every certificate $`\mathcal C(h,N,L)`$ satisfies
> ``` math
> 2(N+h+L+2)<2^L.
> ```
> The two endpoint margins must fit inside an interval of length $`2^L`$. In particular, successful depths grow at least logarithmically with $`N+h`$. This is a necessary lower bound, not an upper bound for the first successful depth. The later two-bit reformulation applies at its stated modulus and does not reverse this implication.*
> 
> *<span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`certifiedKill_depth_floor`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L79)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.certificate_logarithmic_depth`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/TailDepthCorrespondence.lean#L20)

```lean
theorem certificate_logarithmic_depth {h N L : ℕ} (hc : certifiedKill h N L) :
    1 + Real.logb 2 ((N : ℝ)+h+L+2) < L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.fixed_depth_bounds_indices`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/TailDepthCorrespondence.lean#L30)

```lean
theorem fixed_depth_bounds_indices {h N L : ℕ} (hc : certifiedKill h N L) :
    N + h < 2^L
```

3. [`Erdos249257.TotientTailPeriodKiller.certifiedKill_depth_floor`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientTailPeriodKiller.lean#L79)

```lean
theorem certifiedKill_depth_floor {h N L : ℕ} (hcert : certifiedKill h N L) :
    (2 * (N + h + L + 2) : ℤ) < 2 ^ L
```

<a id="prop-a5-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `certificate_logarithmic_depth` | [E249_06/Challenge.lean, line 172](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L172) | [PaperStatementsAT.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L181) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `fixed_depth_bounds_indices` | [E249_06/Challenge.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L176) | [PaperStatementsAT.lean, line 206](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L206) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `certifiedKill_depth_floor` | [E249_06/Challenge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L147) | [PaperStatementsAD.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAD.lean#L51) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-a9-inv"></a>

## Proposition (Rationality gives an eventual tail period)

> *Suppose $`S=a/(2^c v)`$ in lowest terms, where $`a\in\mathbb Z`$, $`c\ge0`$ and $`v\ge1`$ is odd. Take $`h=\varphi(v)`$, including $`h=1`$ when $`v=1`$. Euler’s theorem gives $`v\mid2^h-1`$, so
> ``` math
> 2^N(2^h-1)S\in\mathbb Z\qquad(N\ge c).
> ```
> The identity relating $`S`$ to its scaled tails therefore gives $`R_{N+h}-R_N\in\mathbb Z`$ for every $`N\ge c`$. These are explicit witnesses for the eventual period asserted in Proposition <a href="#prop:A10" data-reference-type="ref" data-reference="prop:A10">122</a>. To use the finite residue test against a hypothetical rational value, one must obtain a nonintegral difference for its period at an index beyond its preperiod. Soundness proves that the quantified certificate condition rules out rationality. Conversely, the prefix-tail identity makes every positive-shift tail difference nonintegral when $`S`$ is irrational, and pointwise completeness (Theorem <a href="#catalogue:cert:a7" data-reference-type="ref" data-reference="catalogue:cert:a7">70</a>) then supplies a depth. Proposition <a href="#prop:AR-06-inv" data-reference-type="ref" data-reference="prop:AR-06-inv">132</a> only identifies the weighted diagonal sum with $`D`$; it is not the completeness argument and supplies no depth bound. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`eventual_period_of_not_irrational`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L358)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.rational_tail_period_explicit_witnesses`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L65)

```lean
theorem rational_tail_period_explicit_witnesses
    (p : ℚ) (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (p : ℝ))
    (c v : ℕ) (hden : p.den = 2 ^ c * v) (hvodd : Odd v) :
    v ∣ 2 ^ Nat.totient v - 1 ∧
      (∀ N : ℕ, c ≤ N →
        ((2 : ℝ) ^ N * ((2 : ℝ) ^ Nat.totient v - 1)) *
            (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ∈
          Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ N : ℕ, c ≤ N →
        totientTail (N + Nat.totient v) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_one_eq_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L56)

```lean
theorem totient_one_eq_one : Nat.totient 1 = 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.eventual_tail_period_of_not_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L111)

```lean
theorem eventual_tail_period_of_not_irrational
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L119)

```lean
theorem irrational_of_certificate_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.tail_diff_notMem_int_of_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L126)

```lean
theorem tail_diff_notMem_int_of_irrational
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
    {h N : ℕ} (hh : 0 < h) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_iff_tail_diff_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L163)

```lean
theorem exists_certifiedKill_iff_tail_diff_nonintegral (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="prop-a9-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rational_tail_period_explicit_witnesses` | [E249_15/Challenge.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L140) | [PaperStatementsAU.lean, line 379](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAU.lean#L379) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `totient_one_eq_one` | [E249_15/Challenge.lean, line 292](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L292) | [PaperStatementsAK.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAK.lean#L56) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `eventual_tail_period_of_not_irrational` | [E249_15/Challenge.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L72) | [PaperStatementsAT.lean, line 399](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L399) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `irrational_of_certificate_supply` | [E249_15/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L120) | [PaperStatementsAT.lean, line 591](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L591) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `tail_diff_notMem_int_of_irrational` | [E249_15/Challenge.lean, line 162](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L162) | [PaperStatementsAU.lean, line 445](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAU.lean#L445) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `exists_certifiedKill_iff_tail_diff_nonintegral` | [E249_15/Challenge.lean, line 78](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L78) | [PaperStatementsAT.lean, line 414](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L414) | [E249_15](../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b6-inv"></a>

## Proposition (Tail integrality on an LCM grid)

> *If $`S\in\mathbb Q`$, there is $`t_1\in\mathbb N`$ such that for all $`t\ge t_1`$, $`q\ge1`$ and $`m\ge0`$,
> ``` math
> R_{(q+m)H(t)}-R_{qH(t)}\in\mathbb Z.
> ```
> The threshold may depend on the hypothetical rational value. A certificate at one fixed scale therefore gives a finite denominator exclusion, not irrationality. Proposition <a href="#prop:B7" data-reference-type="ref" data-reference="prop:B7">124</a> requires certificates at arbitrarily large scales, so that one lies beyond the threshold supplied by any such rational value.*
> 
> *<span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`rational_totient_series_forces_lcm_cone_flatness`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19002)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L8)

```lean
theorem lcm_grid_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail ((q + m) * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.certificate_denominator_exclusion`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L27)

```lean
theorem certificate_denominator_exclusion (r : ℚ) (h N L : ℕ)
    (hcert : certifiedKill h N L) (hden : r.den ∣ 2 ^ N * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_supply_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L40)

```lean
theorem lcm_grid_supply_iff :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m L : ℕ, 0 < q ∧
        certifiedKill (m * periodLcm t) (q * periodLcm t) L
```

<a id="prop-b6-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lcm_grid_flatness` | [E249_09/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L209) | [PaperStatementsAT.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L199) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `certificate_denominator_exclusion` | [E249_09/Challenge.lean, line 191](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L191) | [PaperStatementsAT.lean, line 167](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L167) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `lcm_grid_supply_iff` | [E249_09/Challenge.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L227) | [PaperStatementsAT.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L220) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-d4-inv"></a>

## Proposition (Independence of the retained dyadic family)

> *For every $`e\ge0`$, the auxiliary canonical dyadic family has $`2^e+1`$ indexed sections, and these sections are linearly independent over $`\mathbb Q`$. The CRT–Dirichlet argument is explained in Section <a href="#sec:mahler-defect" data-reference-type="ref" data-reference="sec:mahler-defect">10.8</a>; the declaration below counts its index set. For $`e\ge1`$ the family is a basis for all sections through level $`e`$. At $`e=0`$ the auxiliary family still contains both $`\varphi(n)`$ and $`\varphi(2n)`$, so it is not the actual level-zero truncation, whose dimension is one. No rationality hypothesis on $`S`$ is used.*
> 
> *<span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`card_totientCanonicalIndex`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L61)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.card_canonical_dyadic_index`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CanonicalDyadicSectionRank.lean#L21)

```lean
theorem card_canonical_dyadic_index (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.linearIndependent_canonical_dyadic_family`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CanonicalDyadicSectionRank.lean#L26)

```lean
theorem linearIndependent_canonical_dyadic_family (e : ℕ) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.canonical_family_basis_through_level`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CanonicalDyadicSectionRank.lean#L33)

```lean
theorem canonical_family_basis_through_level (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) =
        Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)) ∧
      finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.canonical_level_zero_channels`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CanonicalDyadicSectionRank.lean#L46)

```lean
theorem canonical_level_zero_channels :
    canonicalTotientKernelFamily 0 (Sum.inl 0) =
        (fun n : ℕ => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily 0 (Sum.inl 1) =
        (fun n : ℕ => (Nat.totient (2 * n) : ℚ)) ∧
      Fintype.card (TotientCanonicalIndex 0) = 2
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.finrank_throughLevel_zero_eq_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CanonicalDyadicSectionRank.lean#L59)

```lean
theorem finrank_throughLevel_zero_eq_one :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1
```

<a id="prop-d4-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `card_canonical_dyadic_index` | [E249_16/Challenge.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L67) | [PaperStatementsBB.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsBB.lean#L56) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `linearIndependent_canonical_dyadic_family` | [E249_16/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L76) | [PaperStatementsBB.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsBB.lean#L68) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `canonical_family_basis_through_level` | [E249_16/Challenge.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L50) | [PaperStatementsBB.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsBB.lean#L41) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `canonical_level_zero_channels` | [E249_16/Challenge.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L59) | [PaperStatementsBB.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsBB.lean#L49) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `finrank_throughLevel_zero_eq_one` | [E249_16/Challenge.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L71) | [PaperStatementsBB.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsBB.lean#L64) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-c2-inv"></a>

## Proposition (The exact range of the stated Farey-gap inequality)

> *Let $`V`$ be the totient residue at $`(N,K)=(1,240)`$ defined in Section <a href="#ssec:farey" data-reference-type="ref" data-reference="ssec:farey">5.3</a>. For every integer $`q`$ satisfying
> ``` math
> 1\le q\le79639646646701375323355774875831053,
> ```
> one has
> ``` math
> (qV)\bmod2^{240}+243q<2^{240}.
> ```
> The first failure occurs at
> ``` math
> q=79639646646701375323355774875831054,
> ```
> obtained from the stated Farey mediant. Thus the range is exact for this particular inequality. It is not an optimality claim among all denominator-exclusion tests. The preceding range gives the exclusion in Proposition <a href="#prop:C3-inv" data-reference-type="ref" data-reference="prop:C3-inv">151</a>, approximately $`7.96\times10^{34}`$. <span class="sans-serif">\[fixed\]</span> <span class="sans-serif">\[Cert\]</span> \
> [`gap_check_window_1_240_first_failure`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GapFareyBound.lean#L225)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.farey_window_1_240_exact_range`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyExactRangeAndDenominatorExclusion.lean#L26)

```lean
theorem farey_window_1_240_exact_range :
    (∀ q : ℕ, 1 ≤ q → q ≤ 79639646646701375323355774875831053 →
        (q * ((∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r))
              % 2 ^ 240)) % 2 ^ 240 + q * 243 < 2 ^ 240) ∧
      ¬ ((79639646646701375323355774875831054 *
              ((∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r))
                % 2 ^ 240)) % 2 ^ 240
            + 79639646646701375323355774875831054 * 243 < 2 ^ 240)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.farey_window_1_240_range_magnitude`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyExactRangeAndDenominatorExclusion.lean#L39)

```lean
theorem farey_window_1_240_range_magnitude :
    (796 : ℕ) * 10 ^ 32 ≤ 79639646646701375323355774875831053 ∧
      (79639646646701375323355774875831053 : ℕ) < 797 * 10 ^ 32
```

<a id="prop-c2-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `farey_window_1_240_exact_range` | [E249_16/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L104) | [PaperStatementsAJ.lean, line 330](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L330) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `farey_window_1_240_range_magnitude` | [E249_16/Challenge.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L114) | [PaperStatementsAJ.lean, line 339](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L339) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-c3-inv"></a>

## Proposition (The resulting denominator exclusion)

> *For every reduced fraction $`a/q`$, with $`a\in\mathbb Z`$ and $`q\ge1`$,
> ``` math
> q\le79639646646701375323355774875831053
>  \quad\Longrightarrow\quad S\ne a/q.
> ```
> This is an unconditional finite denominator exclusion. It does not assume certificates at arbitrarily large scales, as required by Proposition <a href="#prop:A10" data-reference-type="ref" data-reference="prop:A10">122</a>. Conversely, excluding this finite range does not rule out rational values with larger reduced denominators. <span class="sans-serif">\[fixed\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18384)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_reduced_fraction_of_small_denominator`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyExactRangeAndDenominatorExclusion.lean#L49)

```lean
theorem totient_series_ne_reduced_fraction_of_small_denominator (p : ℚ)
    (hden : p.den ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (p : ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_int_div_of_small_denominator`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyExactRangeAndDenominatorExclusion.lean#L57)

```lean
theorem totient_series_ne_int_div_of_small_denominator (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hle : q ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (a : ℝ) / (q : ℝ)
```

<a id="prop-c3-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totient_series_ne_reduced_fraction_of_small_denominator` | [E249_16/Challenge.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L168) | [PaperStatementsAK.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L62) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `totient_series_ne_int_div_of_small_denominator` | [E249_16/Challenge.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L163) | [PaperStatementsAK.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L58) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-d1d2-inv"></a>

## Proposition (Two general irrationality criteria)

> *Let $`x\in\mathbb R`$. One sufficient condition is a sequence of reduced fractions $`u_j=a_j/q_j`$, $`q_j\ge1`$, with $`u_j\ne x`$ for all sufficiently large $`j`$ and
> ``` math
> q_j|x-u_j|\longrightarrow0.
> ```
> Another is that, for every integer $`Q\ge1`$, there exist $`m,z\in\mathbb Z`$ such that
> ``` math
> 0<|mx-z|<1/Q.
> ```
> Indeed, if $`x=a/b`$ is reduced with $`b>0`$, every nonzero error in the first condition is at least $`1/(bq_j)`$, and every nonzero error in the second is at least $`1/b`$. The strict lower bounds exclude exact rational hits. Requiring $`m=b_0^n`$ for a fixed integer base $`b_0\ge2`$ is a stronger sufficient condition, not a reformulation valid for every irrational number. The binary example in Proposition <a href="#catalogue:cert:d2" data-reference-type="ref" data-reference="catalogue:cert:d2">74</a> explains this distinction. The linked declaration proves the first criterion. <span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`irrational_of_den_mul_abs_sub_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5371)*

The Lean declarations below together state a result at least as strong as this one.

1. [`Erdos249257.irrational_of_den_mul_abs_sub_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L5371)

```lean
theorem irrational_of_den_mul_abs_sub_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in atTop, ((u k : ℝ)) ≠ x)
    (h0 : Tendsto (fun k => ((u k).den : ℝ) * |x - (u k : ℝ)|) atTop (nhds 0)) :
    Irrational x
```

2. [`Erdos249257.one_div_den_mul_den_le_abs_sub`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L5342)

```lean
theorem one_div_den_mul_den_le_abs_sub {q r : ℚ} (h : q ≠ r) :
    (1 : ℝ) / ((q.den : ℝ) * (r.den : ℝ)) ≤ |(q : ℝ) - (r : ℝ)|
```

3. [`Erdos249257.irrational_of_int_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L6120)

```lean
theorem irrational_of_int_mul_near_int {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

4. [`Erdos249257.irrational_of_pow_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CertificateKernel.lean#L6149)

```lean
theorem irrational_of_pow_mul_near_int (b : ℕ) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_den_mul_error_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L66)

```lean
theorem irrational_of_den_mul_error_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in Filter.atTop, ((u k : ℚ) : ℝ) ≠ x)
    (h0 : Filter.Tendsto (fun k => ((u k).den : ℝ) * |x - ((u k : ℚ) : ℝ)|)
      Filter.atTop (nhds 0)) :
    Irrational x
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_dirichlet_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L75)

```lean
theorem irrational_of_dirichlet_gap {x : ℝ}
    (h : ∀ Q : ℤ, 1 ≤ Q → ∃ m z : ℤ,
      0 < |(m : ℝ) * x - (z : ℝ)| ∧ |(m : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)) :
    Irrational x
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_mul_den_le_abs_diff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L27)

```lean
theorem one_div_den_mul_den_le_abs_diff {x u : ℚ} (hne : x ≠ u) :
    (1 : ℝ) / ((x.den : ℝ) * (u.den : ℝ)) ≤ |(x : ℝ) - (u : ℝ)|
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_le_abs_int_combination`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L33)

```lean
theorem one_div_den_le_abs_int_combination (p : ℚ) (m z : ℤ)
    (hne : (m : ℝ) * (p : ℝ) - (z : ℝ) ≠ 0) :
    (1 : ℝ) / (p.den : ℝ) ≤ |(m : ℝ) * (p : ℝ) - (z : ℝ)|
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_basePower_dilation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L92)

```lean
theorem irrational_of_basePower_dilation {x : ℝ} (b₀ : ℕ)
    (h : ∀ Q : ℤ, 1 ≤ Q → ∃ n : ℕ, ∃ z : ℤ,
      0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧
        |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)) :
    Irrational x
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.basePower_dilation_not_universal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L529)

```lean
theorem basePower_dilation_not_universal :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ¬ ∀ Q : ℤ, 1 ≤ Q → ∃ (n : ℕ) (z : ℤ),
          0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧
            |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)
```

11. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_xi`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L476)

```lean
theorem irrational_xi : Irrational xi
```

12. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_dist_xi`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L486)

```lean
theorem one_div_eight_le_dist_xi (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * xi - (z : ℝ)|
```

<a id="prop-d1d2-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_den_mul_abs_sub_tendsto_zero` | [E249_06/Challenge.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L195) | [PaperStatementsAI.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L17) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `one_div_den_mul_den_le_abs_sub` | [E249_16/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L199) | [PaperStatementsAI.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAI.lean#L34) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `irrational_of_int_mul_near_int` | [E249_06/Challenge.lean, line 201](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L201) | [PaperStatementsAI.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L22) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_pow_mul_near_int` | [E249_06/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L207) | [PaperStatementsAI.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L28) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_den_mul_error_tendsto_zero` | [E249_16/Challenge.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L134) | [PaperStatementsAJ.lean, line 382](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L382) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `irrational_of_dirichlet_gap` | [E249_16/Challenge.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L141) | [PaperStatementsAJ.lean, line 388](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L388) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `one_div_den_mul_den_le_abs_diff` | [E249_16/Challenge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L147) | [PaperStatementsAJ.lean, line 453](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L453) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `one_div_den_le_abs_int_combination` | [E249_06/Challenge.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L228) | [PaperStatementsAJ.lean, line 449](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAJ.lean#L449) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_basePower_dilation` | [E249_16/Challenge.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L119) | [PaperStatementsAJ.lean, line 367](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L367) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `basePower_dilation_not_universal` | [E249_16/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L207) | [PaperStatementsAL.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAL.lean#L23) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `irrational_xi` | [E249_06/Challenge.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L269) | [PaperStatementsAL.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L42) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `one_div_eight_le_dist_xi` | [E249_06/Challenge.lean, line 295](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L295) | [PaperStatementsAL.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L63) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-d7-inv"></a>

## Proposition (Lambert identities involving $`S`$)

> *For $`L(f)=\sum_{n\ge1}f(n)/(2^n-1)`$, the identities are $`L(\mu)=1/2`$, $`L(\varphi)=2`$, $`L(1)=E`$ and $`L(\varphi*\mu)=S`$. The last identity rewrites the same unknown value; it does not deduce its irrationality from that of $`E`$. The value $`L(\mathrm{Id})=\sum_{m\ge1}\sigma(m)/2^m`$ is transcendental by Nesterenko \[nesterenko1996, Cor. 2, p. 1320\] (cited, not formalised). These examples show that Lambert-series form alone does not determine arithmetic status. The accompanying source reference checks the equality between the two indexing conventions for $`S`$, not every status claim in this paragraph; the individual comparisons are in Proposition <a href="#catalogue:cert:d7" data-reference-type="ref" data-reference="catalogue:cert:d7">94</a> and its table. <span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean, Cited\]</span> \
> [`tsum_totient_div_pow_two_eq_pnat_half_pow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18415)*

The Lean proof assumes Nesterenko's algebraic independence theorem, stated in Lean as `ErdosProblems.Erdos249.PaperCompleteR21.NesterenkoTranscendenceP`; that input is not proved in Lean.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.lambert_ladder_four_values`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L38)

```lean
theorem lambert_ladder_four_values :
    (∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
        / ((2 : ℝ) ^ (d : ℕ) - 1) = 1 / 2) ∧
      (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 2) ∧
      (∑' k : ℕ, (1 : ℝ) / ((2 : ℝ) ^ (k + 1) - 1)
        = ∑' m : ℕ, (((m + 1).divisors.card : ℝ)) / (2 : ℝ) ^ (m + 1)) ∧
      (∑' d : ℕ+, ((MersenneLambertLadder.primWeight (d : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (d : ℕ) - 1)
        = ∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.primWeight_is_totient_conv_moebius`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L53)

```lean
theorem primWeight_is_totient_conv_moebius (n : ℕ) :
    ∑ e ∈ n.divisors, MersenneLambertLadder.primWeight e = (Nat.totient n : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_series_index_bridge'`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L58)

```lean
theorem totient_series_index_bridge' :
    (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.lambert_id_rung_eq_sigma_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L80)

```lean
theorem lambert_id_rung_eq_sigma_series :
    (∑' d : ℕ+, ((d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1))
      = ∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.transcendental_sigma_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L118)

```lean
theorem transcendental_sigma_series (hN : NesterenkoTranscendenceP) :
    Transcendental ℚ
      (∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ))
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.lambert_id_rung_transcendental`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L167)

```lean
theorem lambert_id_rung_transcendental (hN : NesterenkoTranscendenceP) :
    (∑' d : ℕ+, ((d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1))
        = ∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ) ∧
      Transcendental ℚ
        (∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ))
```

<a id="prop-d7-inv-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="prop-d9-inv"></a>

## Proposition (A general rational gap bound)

> *If $`a/b<c/d`$ are reduced fractions with $`b,d>0`$, then
> ``` math
> \frac{1}{bd}\le\frac cd-\frac ab,
> ```
> since $`bc-ad`$ is a positive integer. In particular, if $`S=a/b`$ and $`p_N/q_N<S`$ is a reduced rational approximation with positive error at most $`\varepsilon_N`$, then
> ``` math
> b\ge\frac{1}{q_N\varepsilon_N}.
> ```
> These lower bounds tend to infinity precisely when $`q_N\varepsilon_N\to0`$; a subsequence with this property is enough to contradict a fixed $`b`$. A tail bound by itself does not imply this. For example, the ordinary dyadic prefix has denominator dividing $`2^N`$ and tail at most $`(N+2)2^{-N}`$. Using only these two bounds yields $`b\ge1/(N+2)`$, which is vacuous. The rational-spacing lemma can convert sharper error and denominator information into an exclusion; it does not automatically improve the Farey bound in Proposition <a href="#prop:C2-inv" data-reference-type="ref" data-reference="prop:C2-inv">150</a>. <span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`positive_rational_difference_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/PrimitiveRationalGapSupply.lean#L31)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.rational_gap_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L138)

```lean
theorem rational_gap_lower_bound {lo hi : ℚ} (hlt : lo < hi) :
    (1 : ℝ) / ((hi.den : ℝ) * (lo.den : ℝ)) ≤ (hi : ℝ) - (lo : ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.den_lower_bound_of_positive_error`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L146)

```lean
theorem den_lower_bound_of_positive_error {S u : ℚ} (hlt : u < S) {ε : ℝ}
    (herr : (S : ℝ) - (u : ℝ) ≤ ε) :
    (1 : ℝ) / ((u.den : ℝ) * ε) ≤ (S.den : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.denominator_bound_tendsto_atTop_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L164)

```lean
theorem denominator_bound_tendsto_atTop_iff {f : ℕ → ℝ} (hpos : ∀ N, 0 < f N) :
    Filter.Tendsto (fun N => 1 / f N) Filter.atTop Filter.atTop ↔
      Filter.Tendsto f Filter.atTop (nhds 0)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_den_mul_error_product_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L189)

```lean
theorem irrational_of_den_mul_error_product_tendsto_zero
    {x : ℝ} {u : ℕ → ℚ} {ε : ℕ → ℝ}
    (hne : ∀ j, ((u j : ℚ) : ℝ) ≠ x)
    (herr : ∀ j, |x - ((u j : ℚ) : ℝ)| ≤ ε j)
    (h0 : Filter.Tendsto (fun j => ((u j).den : ℝ) * ε j) Filter.atTop (nhds 0)) :
    Irrational x
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_denominator_bound_vacuous`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L201)

```lean
theorem dyadic_prefix_denominator_bound_vacuous (N : ℕ) :
    (1 : ℝ) / ((2 : ℝ) ^ N * (((N : ℝ) + 2) / (2 : ℝ) ^ N)) = 1 / ((N : ℝ) + 2) ∧
      1 / ((N : ℝ) + 2) ≤ 1
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_den_dvd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicPrefixTailBound.lean#L14)

```lean
theorem dyadic_prefix_den_dvd (N : ℕ) :
    (((totientPrefix N : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den ∣ 2 ^ N
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.totientTail_le_add_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicPrefixTailBound.lean#L22)

```lean
theorem totientTail_le_add_two (N : ℕ) :
    totientTail N ≤ (N : ℝ) + 2
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_tail_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicPrefixTailBound.lean#L28)

```lean
theorem dyadic_prefix_tail_le (N : ℕ) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        - (totientPrefix N : ℝ) / (2 : ℝ) ^ N
      ≤ ((N : ℝ) + 2) / (2 : ℝ) ^ N
```

<a id="prop-d9-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rational_gap_lower_bound` | [E249_16/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L156) | [PaperStatementsAJ.lean, line 493](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L493) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `den_lower_bound_of_positive_error` | [E249_16/Challenge.lean, line 89](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L89) | [PaperStatementsAJ.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L259) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `denominator_bound_tendsto_atTop_iff` | [E249_16/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L94) | [PaperStatementsAJ.lean, line 267](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L267) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `irrational_of_den_mul_error_product_tendsto_zero` | [E249_16/Challenge.lean, line 126](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L126) | [PaperStatementsAJ.lean, line 374](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L374) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `dyadic_prefix_denominator_bound_vacuous` | [E249_16/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L99) | [PaperStatementsAJ.lean, line 289](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L289) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `dyadic_prefix_den_dvd` | [E249_16/Challenge.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L221) | [PaperStatementsAT.lean, line 402](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAT.lean#L402) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `totientTail_le_add_two` | [E249_16/Challenge.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L238) | [PaperStatementsAU.lean, line 517](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAU.lean#L517) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `dyadic_prefix_tail_le` | [E249_16/Challenge.lean, line 225](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L225) | [PaperStatementsAT.lean, line 405](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAT.lean#L405) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b11-inv"></a>

## Proposition (Diagonal certificates through $`82`$)

> *The current aggregate establishes
> ``` math
> \forall t\in\mathbb N,\quad t\le82\ \Longrightarrow\ P\,t,
> ```
> where $`P\,t`$ is the diagonal certificate predicate in Proposition <a href="#prop:B3" data-reference-type="ref" data-reference="prop:B3">123</a>. The earlier aggregate covered 28 explicit cases through $`64`$, including $`1,2,3,4,5,7,8,9,11,13,16,17`$; the later theorem fills the gaps and extends the range through $`82`$. Each instance reduces to exact finite arithmetic with the displayed totient values, using the prime-power factorisations and Lucas primality certificates in the source. This proves neither $`P\,83`$ nor infinitely many instances, and therefore does not establish the quantified conditions in Propositions <a href="#prop:A10" data-reference-type="ref" data-reference="prop:A10">122</a>, <a href="#prop:B3" data-reference-type="ref" data-reference="prop:B3">123</a> and <a href="#prop:B7" data-reference-type="ref" data-reference="prop:B7">124</a>. <span class="sans-serif">\[bounded\]</span> <span class="sans-serif">\[Cert\]</span> \
> [`certifiedKill_diagonal_all_imported`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/DiagonalPincerCertificates.lean#L2870) [`ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/ErdosProblems/Skip/LadderT67.lean#L71264)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.historical_table_size_and_initial_depths`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L57)

```lean
theorem historical_table_size_and_initial_depths :
    diagonalPincerCertificateScalesThroughT64.length = 28 ∧
    diagonalPincerCertificateScalesThroughT64.Nodup ∧
    diagonalPincerCertificateScalesThroughT64.getLast? = some 64 ∧
    ([1,2,3,4,5,7,8,9,11,13,16,17].map diagonalPincerKillDepthThroughT64) =
      [6,5,7,7,9,14,15,14,21,22,23,26]
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.historical_table_and_complete_band`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L64)

```lean
theorem historical_table_and_complete_band :
    (∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT64 t)) ∧
    (∀ t : ℕ, t ≤ 82 → ∃ L, certifiedKill (periodLcm t) (periodLcm t) L)
```

<a id="prop-b11-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `historical_table_size_and_initial_depths` | [E249_06/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L97) | [PaperStatementsG.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsG.lean#L47) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `historical_table_and_complete_band` | [E249_06/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L124) | [PaperStatementsI.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsI.lean#L80) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-c1-inv"></a>

## Proposition (A coprime-pair expression for $`S`$)

> *For $`n\ge0`$, the number of integer pairs $`a\ge1`$, $`b\ge0`$ with $`a+b=n`$ and $`\gcd(a,b)=1`$ is $`\varphi(n)`$, with $`\varphi(0)=0`$. Indeed, $`b=n-a`$ and $`\gcd(a,n-a)=\gcd(a,n)`$. The boundary case $`n=1`$ contributes $`(a,b)=(1,0)`$; it disappears when both coordinates are required to be positive. Consequently,
> ``` math
> \sum_{\substack{a,b\ge1\\\gcd(a,b)=1}}2^{-(a+b)}=S-\frac12.
> ```
> For independent random variables $`X,Y`$ with $`\Pr(X=n)=\Pr(Y=n)=2^{-n}`$, $`n\ge1`$, the left side is $`\Pr(\gcd(X,Y)=1)`$. Thus $`S-1/2`$ has a coprimality-probability interpretation. This identity does not supply an estimate for the binary digits or tail residues used elsewhere in the paper. <span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`tsum_pos_coprime_pair_pow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GeometricCoprimality.lean#L182)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.card_visible_antidiagonal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L218)

```lean
theorem card_visible_antidiagonal (n : ℕ) :
    ((Finset.antidiagonal n).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2).card
      = Nat.totient n
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_zero_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L225)

```lean
theorem totient_zero_eq_zero : Nat.totient 0 = 0
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.visible_antidiagonal_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L228)

```lean
theorem visible_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2)
      = {((1 : ℕ), (0 : ℕ))}
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.positive_antidiagonal_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L234)

```lean
theorem positive_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2) = ∅
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_eq_series_sub_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L241)

```lean
theorem tsum_pos_coprime_pairs_eq_series_sub_half :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then 1 / (2 : ℝ) ^ (q.1 + q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_product_form`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L266)

```lean
theorem tsum_pos_coprime_pairs_product_form :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then (1 / (2 : ℝ) ^ q.1) * (1 / (2 : ℝ) ^ q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2
```

<a id="prop-c1-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `card_visible_antidiagonal` | [E249_16/Challenge.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L83) | [PaperStatementsAJ.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L163) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `totient_zero_eq_zero` | [E249_16/Challenge.lean, line 173](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L173) | [PaperStatementsAK.lean, line 66](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L66) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `visible_antidiagonal_one` | [E249_16/Challenge.lean, line 188](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L188) | [PaperStatementsAK.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L110) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `positive_antidiagonal_one` | [E249_16/Challenge.lean, line 151](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L151) | [PaperStatementsAJ.lean, line 480](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L480) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `tsum_pos_coprime_pairs_eq_series_sub_half` | [E249_16/Challenge.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L176) | [PaperStatementsAK.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L68) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `tsum_pos_coprime_pairs_product_form` | [E249_16/Challenge.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L182) | [PaperStatementsAK.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L73) | [E249_16](../evidence/comparator/replay-35882032091/receipt-E249_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-values-exponents-one-two"></a>

## Theorem

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.mobiusMersenneTheta_one_and_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L23)

```lean
theorem mobiusMersenneTheta_one_and_two :
    mobiusMersenneTheta 1 = 1 / 2 ∧
      mobiusMersenneTheta 2
        = (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n) - 1 / 2
```

<a id="thm-values-exponents-one-two-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mobiusMersenneTheta_one_and_two` | [E249_17/Challenge.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L50) | [PaperStatementsBG.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsBG.lean#L28) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-first-two-summands-give-positive"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_hankel_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L35)

```lean
theorem twoAtom_hankel_gap (r : ℕ) :
    (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2
        - (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      = 4 / (3 : ℝ) ^ (r + 2)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_strict_logConcave`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L43)

```lean
theorem twoAtom_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      < (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2
```

<a id="thm-first-two-summands-give-positive-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `twoAtom_hankel_gap` | [E249_17/Challenge.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L75) | [PaperStatementsAK.lean, line 90](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAK.lean#L90) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `twoAtom_strict_logConcave` | [E249_17/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L81) | [PaperStatementsAK.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAK.lean#L95) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-strict-log-concavity-all-integer"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.theta_strict_logConcave`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L52)

```lean
theorem theta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
      < mobiusMersenneTheta (r + 1) ^ 2
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_det_neg`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L58)

```lean
theorem theta_hankel_det_neg (r : ℕ) (hr : 1 ≤ r) :
    Matrix.det (Matrix.of
        ![![mobiusMersenneTheta r, mobiusMersenneTheta (r + 1)],
          ![mobiusMersenneTheta (r + 1), mobiusMersenneTheta (r + 2)]]) < 0
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_two_neg`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L66)

```lean
theorem theta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
        - mobiusMersenneTheta (r + 1) ^ 2 < 0
```

<a id="thm-strict-log-concavity-all-integer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `theta_strict_logConcave` | [E249_17/Challenge.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L67) | [PaperStatementsBG.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsBG.lean#L42) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `theta_hankel_det_neg` | [E249_17/Challenge.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L56) | [PaperStatementsBG.lean, line 33](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsBG.lean#L33) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `theta_hankel_two_neg` | [E249_17/Challenge.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L62) | [PaperStatementsBG.lean, line 38](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsBG.lean#L38) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-binary-carry-criterion"></a>

## Theorem (Integer recurrence criterion for a binary series)

> *Let $`c:\mathbb{N}\to\mathbb{N}`$ satisfy $`c(n)\le n`$. Then $`\sum_{n\ge1}c(n)2^{-n}`$ is rational if and only if there are an integer $`v>0`$ and an integer sequence $`u`$ such that
> ``` math
> u(N+1)=2u(N)-v\,c(N+1),\qquad \frac{u(N)}{2^N}\longrightarrow0.
> ```
> For each fixed $`v`$, such a sequence is unique and equals
> ``` math
> u(N)=vR^c_N,\qquad R^c_N=\sum_{j\ge1}\frac{c(N+j)}{2^j}.
> ```
> [`Erdos249257.binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L426) [`Erdos249257.temperedBinaryOrbit_eq_scaledTail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L339) .*

The Lean declarations below together state this result.

1. [`Erdos249257.binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L426)

```lean
theorem binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u
```

2. [`Erdos249257.temperedBinaryOrbit_eq_scaledTail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/GenericTailOrbitRigidity.lean#L339)

```lean
theorem temperedBinaryOrbit_eq_scaledTail
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    {v : ℕ} {u : ℕ → ℤ} (horbit : IsTemperedBinaryOrbit c v u) :
    ∀ N : ℕ, (u N : ℝ) = (v : ℝ) * binaryCoeffTail c N
```

<a id="thm-binary-carry-criterion-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit` | [E257_21/Challenge.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L58) | [PaperStatementsAE.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAE.lean#L45) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `temperedBinaryOrbit_eq_scaledTail` | [E257_21/Challenge.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L64) | [PaperStatementsAE.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAE.lean#L65) | [E257_21](../evidence/comparator/replay-35882032091/receipt-E257_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-uniqueness-under-growth-condition"></a>

## Proposition

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.doubling_tempered_sequence_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L28)

```lean
theorem doubling_tempered_sequence_eq_zero
    (d : ℕ → ℝ) (hrec : ∀ N : ℕ, d (N + 1) = 2 * d N)
    (hlittleO :
      Filter.Tendsto (fun N : ℕ ↦ d N / (2 : ℝ) ^ N) Filter.atTop (nhds 0)) :
    ∀ N : ℕ, d N = 0
```

<a id="prop-uniqueness-under-growth-condition-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `doubling_tempered_sequence_eq_zero` | [E249_17/Challenge.lean, line 135](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L135) | [PaperStatementsAE.lean, line 224](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L224) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-exact-rational-approximation-formula"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_sub_rationalApproximation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L118)

```lean
theorem tailDifference_sub_rationalApproximation (H D : ℕ) :
    totientTail (2 * H) - totientTail H -
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ) +
          (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
            (1 / 2 +
              ∑ d ∈ Finset.Icc 1 D,
                ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
                  (((2 : ℝ) ^ d - 1) ^ 2))) =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
        ∑' k : ℕ,
          ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
            (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_eq_coefficient_mul_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L88)

```lean
theorem tailDifference_eq_coefficient_mul_series (H : ℕ) :
    totientTail (2 * H) - totientTail H =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) +
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_pnat_form`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L99)

```lean
theorem totientSeries_pnat_form :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_eq_half_add_moebius_sq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L106)

```lean
theorem totientSeries_eq_half_add_moebius_sq :
    (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)) =
      1 / 2 +
        ∑' d : ℕ+,
          ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
            (((2 : ℝ) ^ (d : ℕ) - 1) ^ 2)
```

<a id="prop-exact-rational-approximation-formula-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tailDifference_sub_rationalApproximation` | [E249_17/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L223) | [PaperStatementsAX.lean, line 529](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAX.lean#L529) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `tailDifference_eq_coefficient_mul_series` | [E249_17/Challenge.lean, line 216](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L216) | [PaperStatementsAX.lean, line 523](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAX.lean#L523) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `totientSeries_pnat_form` | [E249_17/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L184) | [PaperStatementsAE.lean, line 330](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L330) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `totientSeries_eq_half_add_moebius_sq` | [E249_17/Challenge.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L176) | [PaperStatementsAE.lean, line 323](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L323) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-geometric-tail-bound"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_mobiusSquareTail_le_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L155)

```lean
theorem abs_mobiusSquareTail_le_paper (D : ℕ) :
    |∑' k : ℕ,
        ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
          (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2)| ≤
      4 / (3 * (((2 : ℝ) ^ (D + 1) - 1) ^ 2))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_moebius_cast_le_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L138)

```lean
theorem abs_moebius_cast_le_one (d : ℕ) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenne_geometric_shift`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L144)

```lean
theorem mersenne_geometric_shift (D j : ℕ) :
    (2 : ℝ) ^ j * ((2 : ℝ) ^ (D + 1) - 1) ≤ (2 : ℝ) ^ (D + 1 + j) - 1
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_quarter_geometric`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L149)

```lean
theorem tsum_quarter_geometric : ∑' j : ℕ, ((1 : ℝ) / 4) ^ j = 4 / 3
```

<a id="prop-geometric-tail-bound-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `abs_mobiusSquareTail_le_paper` | [E249_17/Challenge.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L103) | [PaperStatementsAE.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L176) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `abs_moebius_cast_le_one` | [E249_17/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L110) | [PaperStatementsAE.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L182) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `mersenne_geometric_shift` | [E249_17/Challenge.lean, line 142](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L142) | [PaperStatementsAE.lean, line 256](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L256) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `tsum_quarter_geometric` | [E249_17/Challenge.lean, line 202](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L202) | [PaperStatementsAE.lean, line 352](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L352) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sum-over-divisor-indices"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_divisorIndices_mobius`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L68)

```lean
theorem sum_divisorIndices_mobius (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ) =
      (H : ℚ) * (Nat.totient (Nat.gcd H s) : ℚ) / (Nat.gcd H s : ℚ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_moebius_div_eq_totient_div`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L98)

```lean
theorem sum_divisors_moebius_div_eq_totient_div {g : ℕ} (hg : 0 < g) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℚ) / (d : ℚ) =
      (Nat.totient g : ℚ) / (g : ℚ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_divisorIndices_radical_form`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L121)

```lean
theorem sum_divisorIndices_radical_form (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        ArithmeticFunction.moebius d * ((H / d : ℕ) : ℤ) =
      ((H / RadicalMobiusShadow.squarefreeKernel H : ℕ) : ℤ) *
        (RepunitMobiusNumerator.gcdWordCoeff
          (RadicalMobiusShadow.squarefreeKernel H) s : ℤ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.squarefreeKernel_eq_prod_primeFactors`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L117)

```lean
theorem squarefreeKernel_eq_prod_primeFactors (H : ℕ) :
    RadicalMobiusShadow.squarefreeKernel H = ∏ p ∈ H.primeFactors, p
```

<a id="prop-sum-over-divisor-indices-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `sum_divisorIndices_mobius` | [E249_17/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L150) | [PaperStatementsAE.lean, line 298](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L298) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `sum_divisors_moebius_div_eq_totient_div` | [E249_17/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L156) | [PaperStatementsAE.lean, line 303](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L303) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `sum_divisorIndices_radical_form` | [E249_17/Challenge.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L259) | [PaperStatementsAQ.lean, line 85](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAQ.lean#L85) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `squarefreeKernel_eq_prod_primeFactors` | [E249_17/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L146) | [PaperStatementsAE.lean, line 285](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L285) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `sum_divisorIndices_radical_form`:

```lean
theorem sum_divisorIndices_radical_form (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        ArithmeticFunction.moebius d * ((H / d : ℕ) : ℤ) =
      ((H / squarefreeKernel H : ℕ) : ℤ) *
        (gcdWordCoeff
          (squarefreeKernel H) s : ℤ) := by sorry
```

Challenge for `squarefreeKernel_eq_prod_primeFactors`:

```lean
theorem squarefreeKernel_eq_prod_primeFactors (H : ℕ) :
    squarefreeKernel H = ∏ p ∈ H.primeFactors, p := by sorry
```

<a id="prop-divisor-sum-complement"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.totientDifference_eq_divisorPart_add_complement`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L217)

```lean
theorem totientDifference_eq_divisorPart_add_complement (H s : ℕ) (hH : 0 < H) :
    (Nat.totient (2 * H + s) : ℚ) - (Nat.totient (H + s) : ℚ) =
      (H : ℚ) * (Nat.totient (Nat.gcd H s) : ℚ) / (Nat.gcd H s : ℚ) +
        ∑ d ∈ {d ∈ Finset.Icc 1 (2 * H + s) | ¬d ∣ H}, complementSummand d H s
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_eq_mobius_divisor_sum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L134)

```lean
theorem totient_eq_mobius_divisor_sum (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℤ) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ((n / d : ℕ) : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.divisorIndex_endpoint_behaviour`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L141)

```lean
theorem divisorIndex_endpoint_behaviour {d H s : ℕ} (hdH : d ∣ H) :
    (d ∣ 2 * H + s ↔ d ∣ s) ∧ (d ∣ H + s ↔ d ∣ s) ∧
      (ArithmeticFunction.moebius d : ℚ) * ((2 * H + s : ℕ) : ℚ) / (d : ℚ) -
          (ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ) =
        (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_eq_phaseTerm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L159)

```lean
theorem complementSummand_eq_phaseTerm {d H s : ℕ} (hd : 0 < d) (hdH : ¬d ∣ H) :
    complementSummand d H s = ((foreignChannelPhaseTerm d H s : ℤ) : ℚ)
```

<a id="prop-divisor-sum-complement-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totientDifference_eq_divisorPart_add_complement` | [E249_17/Challenge.lean, line 170](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L170) | [PaperStatementsAE.lean, line 318](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L318) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `totient_eq_mobius_divisor_sum` | [E249_17/Challenge.lean, line 189](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L189) | [PaperStatementsAE.lean, line 334](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L334) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `divisorIndex_endpoint_behaviour` | [E249_17/Challenge.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L128) | [PaperStatementsAE.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L218) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `complementSummand_eq_phaseTerm` | [E249_17/Challenge.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L114) | [PaperStatementsAE.lean, line 202](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L202) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-doubling-full-totient-difference"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.totientDifference_doubling_seam`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L262)

```lean
theorem totientDifference_doubling_seam (H r : ℕ) (hH : Even H) :
    (Even r →
        (Nat.totient (4 * H + 2 * r) : ℤ) - (Nat.totient (2 * H + 2 * r) : ℤ) =
          2 * ((Nat.totient (2 * H + r) : ℤ) - (Nat.totient (H + r) : ℤ))) ∧
      (Odd r →
        (Nat.totient (4 * H + 2 * r) : ℤ) - (Nat.totient (2 * H + 2 * r) : ℤ) =
          (Nat.totient (2 * H + r) : ℤ) - (Nat.totient (H + r) : ℤ))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_two_mul_even`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L250)

```lean
theorem totient_two_mul_even {n : ℕ} (hn : Even n) :
    Nat.totient (2 * n) = 2 * Nat.totient n
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_two_mul_odd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L255)

```lean
theorem totient_two_mul_odd {n : ℕ} (hn : Odd n) :
    Nat.totient (2 * n) = Nat.totient n
```

<a id="thm-doubling-full-totient-difference-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totientDifference_doubling_seam` | [E249_17/Challenge.lean, line 161](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L161) | [PaperStatementsAE.lean, line 310](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L310) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `totient_two_mul_even` | [E249_17/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L194) | [PaperStatementsAE.lean, line 338](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L338) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `totient_two_mul_odd` | [E249_17/Challenge.lean, line 198](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L198) | [PaperStatementsAE.lean, line 341](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L341) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-doubling-identity-two-portions-sum"></a>

## Proposition

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_low_double_echo`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L289)

```lean
theorem complementSummand_low_double_echo {d H s : ℕ} (_hH : 0 < H) (_hd : 0 < d)
    (hdH : ¬d ∣ H) (hLow : d ∣ H + s) :
    complementSummand d H s =
        -((ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ)) ∧
      complementSummand d H (2 * s) =
        2 * ((ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ)) ∧
      (d ∣ 2 * H + 2 * s ∧ ¬d ∣ H + 2 * s) ∧
      complementSummand d H (2 * s) = -2 * complementSummand d H s
```

<a id="prop-doubling-identity-two-portions-sum-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `complementSummand_low_double_echo` | [E249_17/Challenge.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L118) | [PaperStatementsAE.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L205) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-positive-coefficients-numerator-polynomial"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eq_gcdWordForm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L67)

```lean
theorem paperNumerator_eq_gcdWordForm {r : ℕ} (hr : Squarefree r) :
    paperNumeratorPolynomial r =
      ∑ k ∈ Finset.range r,
        Polynomial.C (((r / Nat.gcd r k) * Nat.totient (Nat.gcd r k) : ℕ) : ℤ) *
          (Polynomial.X : Polynomial ℤ) ^ k
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L82)

```lean
theorem paperNumerator_coeff_pos {r k : ℕ} (hr : Squarefree r) (hk : k < r) :
    0 < (paperNumeratorPolynomial r).coeff k
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L88)

```lean
theorem paperNumerator_coeff_eq_zero {r k : ℕ} (hr : Squarefree r) (hk : r ≤ k) :
    (paperNumeratorPolynomial r).coeff k = 0
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_eq_gcd_divisor_sum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L94)

```lean
theorem paperNumerator_coeff_eq_gcd_divisor_sum {r k : ℕ} (hr : Squarefree r)
    (hk : k < r) :
    (paperNumeratorPolynomial r).coeff k =
      ∑ d ∈ (Nat.gcd r k).divisors,
        ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumeratorPolynomial_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L57)

```lean
theorem paperNumeratorPolynomial_eq (r : ℕ) :
    paperNumeratorPolynomial r = mobiusNumeratorPolynomial r
```

<a id="thm-positive-coefficients-numerator-polynomial-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paperNumerator_eq_gcdWordForm` | [E249_17/Challenge.lean, line 292](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L292) | [PaperStatementsAO.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAO.lean#L52) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `paperNumerator_coeff_pos` | [E249_17/Challenge.lean, line 288](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L288) | [PaperStatementsAO.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAO.lean#L49) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `paperNumerator_coeff_eq_zero` | [E249_17/Challenge.lean, line 284](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L284) | [PaperStatementsAO.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAO.lean#L46) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `paperNumerator_coeff_eq_gcd_divisor_sum` | [E249_17/Challenge.lean, line 277](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L277) | [PaperStatementsAO.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAO.lean#L40) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `paperNumeratorPolynomial_eq` | [E249_17/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L255) | [PaperStatementsAQ.lean, line 82](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAQ.lean#L82) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-numerator-polynomial-explicit-positive-coefficients"></a>

## Corollary

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L111)

```lean
theorem paperNumerator_eval_two {r : ℕ} (_hr : Squarefree r) :
    (((paperNumeratorPolynomial r).eval 2 : ℤ) : ℚ) =
      ∑ d ∈ r.divisors,
        (ArithmeticFunction.moebius d : ℚ) * ((r / d : ℕ) : ℚ) *
          (((2 : ℚ) ^ r - 1) / ((2 : ℚ) ^ d - 1))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenne_dvd_of_dvd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L106)

```lean
theorem mersenne_dvd_of_dvd {d r : ℕ} (hd : d ∣ r) :
    (2 ^ d - 1 : ℕ) ∣ (2 ^ r - 1 : ℕ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two_primeSubsetForm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L145)

```lean
theorem paperNumerator_eval_two_primeSubsetForm {r : ℕ} (hr : Squarefree r) :
    (paperNumeratorPolynomial r).eval 2 =
      ∑ s ∈ r.primeFactors.powerset,
        (-1 : ℤ) ^ s.card * ((r / s.prod id : ℕ) : ℤ) *
          ((((2 ^ r - 1) / (2 ^ s.prod id - 1) : ℕ)) : ℤ)
```

<a id="cor-numerator-polynomial-explicit-positive-coefficients-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paperNumerator_eval_two` | [E249_18/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L104) | [PaperStatementsAO.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L57) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `mersenne_dvd_of_dvd` | [E249_17/Challenge.lean, line 273](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L273) | [PaperStatementsAO.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAO.lean#L34) | [E249_17](../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `paperNumerator_eval_two_primeSubsetForm` | [E249_18/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L111) | [PaperStatementsAO.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L63) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-geometric-remainder-bound"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenneRemainder_identity_and_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L166)

```lean
theorem mersenneRemainder_identity_and_bound {n : ℕ} (hn : 2 ≤ n) :
    1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n =
        ((1 : ℝ) / 8) ^ n / (1 - ((1 : ℝ) / 2) ^ n) ∧
      1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n ≤
        (4 / 3 : ℝ) * ((1 : ℝ) / 8) ^ n
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.one_sub_half_pow_ge`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L156)

```lean
theorem one_sub_half_pow_ge {n : ℕ} (hn : 2 ≤ n) :
    (3 : ℝ) / 4 ≤ 1 - ((1 : ℝ) / 2) ^ n
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenneRemainderTail_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L208)

```lean
theorem mersenneRemainderTail_le {m : ℕ} (hm : 0 < m) :
    ∑' k : ℕ,
        (1 / ((2 : ℝ) ^ (m + k + 1) - 1) - ((1 : ℝ) / 2) ^ (m + k + 1) -
          ((1 : ℝ) / 4) ^ (m + k + 1)) ≤
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_eighth_pow_tail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L182)

```lean
theorem tsum_eighth_pow_tail (m : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) = (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ m
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.four_thirds_tsum_eighth_pow_tail`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L200)

```lean
theorem four_thirds_tsum_eighth_pow_tail (m : ℕ) :
    (4 / 3 : ℝ) * ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) =
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m
```

<a id="prop-geometric-remainder-bound-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mersenneRemainder_identity_and_bound` | [E249_18/Challenge.lean, line 93](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L93) | [PaperStatementsAO.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L27) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `one_sub_half_pow_ge` | [E249_18/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L100) | [PaperStatementsAO.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L36) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `mersenneRemainderTail_le` | [E249_18/Challenge.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L86) | [PaperStatementsAO.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L21) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `tsum_eighth_pow_tail` | [E249_18/Challenge.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L118) | [PaperStatementsAO.lean, line 69](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L69) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `four_thirds_tsum_eighth_pow_tail` | [E249_18/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L81) | [PaperStatementsAO.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L17) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-squared-distance-phase-one"></a>

## Proposition

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.sum_sq_dist_from_phase_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L31)

```lean
theorem sum_sq_dist_from_phase_one (h L : ℕ) (T : Finset ℕ) :
    ∑ N ∈ T, ‖windowFirstExp h N L - 1‖ ^ 2 =
      2 * (T.card : ℝ) - 2 * ∑ N ∈ T, (windowFirstExp h N L).re
```

<a id="prop-squared-distance-phase-one-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `sum_sq_dist_from_phase_one` | [E249_18/Challenge.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L139) | [PaperStatementsAX.lean, line 513](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAX.lean#L513) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-squared-distance-bound-separated-pairs"></a>

## Lemma

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.card_mul_sq_le_pairwise_energy`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L40)

```lean
theorem card_mul_sq_le_pairwise_energy {α : Type*} [DecidableEq α]
    (T : Finset α) (z : α → ℂ) (P : Finset (α × α)) (δ : ℝ)
    (hP : P ⊆ T.product T) (hδ : 0 ≤ δ)
    (hsep : ∀ p ∈ P, δ ≤ ‖z p.1 - z p.2‖) :
    (P.card : ℝ) * δ ^ 2 ≤ ∑ i ∈ T, ∑ j ∈ T, ‖z i - z j‖ ^ 2
```

<a id="lem-squared-distance-bound-separated-pairs-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `card_mul_sq_le_pairwise_energy` | [E249_18/Challenge.lean, line 161](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L161) | [PaperStatementsAE.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAE.lean#L187) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-divisor-sum"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.divisorChannels_sum_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L69)

```lean
theorem divisorChannels_sum_eq (H : ℕ) (_hH : 0 < H) :
    ∑ d ∈ H.divisors, residueIncrement d H =
      (H : ℝ) *
        ∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.residueOffset_of_dvd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L50)

```lean
theorem residueOffset_of_dvd {d H : ℕ} (_hd : 0 < d) (hdvd : d ∣ H) :
    residueOffset d H = d ∧ residueOffset d (2 * H) = d
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.residueKernel_increment_of_dvd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L58)

```lean
theorem residueKernel_increment_of_dvd {d H : ℕ} (hd : 0 < d) (hdvd : d ∣ H) :
    foreignResidueKernel d (2 * H) - foreignResidueKernel d H =
      (H : ℝ) * ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
        ((d : ℝ) * ((2 : ℝ) ^ d - 1))
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.scaleExplicitShadow_eq_divisorChannels`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L84)

```lean
theorem scaleExplicitShadow_eq_divisorChannels {H : ℕ} (hH : 0 < H) :
    scaleExplicitShadow H =
      (H : ℝ) *
        ∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1))
```

<a id="prop-finite-divisor-sum-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `divisorChannels_sum_eq` | [E249_18/Challenge.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L182) | [PaperStatementsBE.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBE.lean#L34) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `residueOffset_of_dvd` | [E249_18/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L209) | [PaperStatementsBE.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBE.lean#L57) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `residueKernel_increment_of_dvd` | [E249_18/Challenge.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L203) | [PaperStatementsBE.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBE.lean#L52) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `scaleExplicitShadow_eq_divisorChannels` | [E249_18/Challenge.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L168) | [PaperStatementsAE.lean, line 270](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAE.lean#L270) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-separation-larger-than-error-implies"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_not_integral_of_separation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L119)

```lean
theorem tailDifference_not_integral_of_separation {H D : ℕ}
    (hbound :
      |totientTail (2 * H) - totientTail H -
        (scaleExplicitShadow H + projectedForeignDefect H D)| ≤
        foreignComplementBound H D)
    (hsep : ∀ z : ℤ,
      foreignComplementBound H D <
        |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)|) :
    totientTail (2 * H) - totientTail H ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.projectedForeignDefect_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L103)

```lean
theorem projectedForeignDefect_paper (H D : ℕ) :
    projectedForeignDefect H D =
      ∑ d ∈ Finset.Icc 1 D,
        (if d ∣ H then 0
          else foreignResidueKernel d (2 * H) - foreignResidueKernel d H)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.foreignComplementBound_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L110)

```lean
theorem foreignComplementBound_paper (H D : ℕ) :
    foreignComplementBound H D =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
        (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D))
```

<a id="prop-separation-larger-than-error-implies-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tailDifference_not_integral_of_separation` | [E249_18/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L223) | [PaperStatementsBK.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBK.lean#L23) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `projectedForeignDefect_paper` | [E249_18/Challenge.lean, line 196](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L196) | [PaperStatementsBE.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBE.lean#L46) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `foreignComplementBound_paper` | [E249_18/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L190) | [PaperStatementsBE.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBE.lean#L41) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-coprime-pair-counting-totient"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.card_coprime_antidiagonal`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L147)

```lean
theorem card_coprime_antidiagonal (n : ℕ) :
    ((Finset.antidiagonal n).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2)).card = Nat.totient n
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.boundary_pair_at_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L154)

```lean
theorem boundary_pair_at_one :
    (1, 0) ∈ (Finset.antidiagonal 1).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2) ∧
      ((Finset.antidiagonal 1).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2)).card = 1
```

<a id="thm-coprime-pair-counting-totient-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `card_coprime_antidiagonal` | [E249_18/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L156) | [PaperStatementsAE.lean, line 183](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAE.lean#L183) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `boundary_pair_at_one` | [E249_18/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L149) | [PaperStatementsAE.lean, line 177](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAE.lean#L177) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-two-lattice-sums"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_totient_pow_shift`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L27)

```lean
theorem tsum_totient_pow_shift {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, (Nat.totient n : ℝ) * r ^ n)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_halfOpen_sum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L38)

```lean
theorem coprimeLattice_halfOpen_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_positive_sum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L46)

```lean
theorem coprimeLattice_positive_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = (∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)) - r
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_removed_pair`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L53)

```lean
theorem coprimeLattice_removed_pair (a b : ℕ) :
    ((0 < a ∧ Nat.Coprime a b) ∧ ¬ (0 < a ∧ 0 < b ∧ Nat.Coprime a b))
      ↔ (a = 1 ∧ b = 0)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_gcd_layer_total`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L77)

```lean
theorem coprimeLattice_gcd_layer_total {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (r ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = (r / (1 - r)) ^ 2
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_gcd_layer_total_eq_one_iff`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L84)

```lean
theorem coprimeLattice_gcd_layer_total_eq_one_iff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (r ^ (g + 1)) ^ (p.1 + p.2) else 0))
        = 1 ↔ r = 1 / 2
```

<a id="prop-two-lattice-sums-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_totient_pow_shift` | [E249_18/Challenge.lean, line 293](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L293) | [PaperStatementsAK.lean, line 78](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAK.lean#L78) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_halfOpen_sum` | [E249_18/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L255) | [PaperStatementsAJ.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L199) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_positive_sum` | [E249_18/Challenge.lean, line 280](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L280) | [PaperStatementsAJ.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L227) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_removed_pair` | [E249_18/Challenge.lean, line 285](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L285) | [PaperStatementsAJ.lean, line 231](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L231) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_gcd_layer_total` | [E249_18/Challenge.lean, line 237](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L237) | [PaperStatementsAJ.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L184) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_gcd_layer_total_eq_one_iff` | [E249_18/Challenge.lean, line 243](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L243) | [PaperStatementsAJ.lean, line 189](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L189) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-classical-coprime-pair-lambert-identity"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_identity`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L106)

```lean
theorem coprimeLattice_lambert_identity {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          r ^ (p.1 + p.2) / (1 - r ^ (p.1 + p.2)) else 0)
      = (r / (1 - r)) ^ 2
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_rational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L114)

```lean
theorem coprimeLattice_lambert_rational (s : ℚ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ v : ℚ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          (s : ℝ) ^ (p.1 + p.2) / (1 - (s : ℝ) ^ (p.1 + p.2)) else 0)
      = (v : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_half_eq_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L127)

```lean
theorem coprimeLattice_lambert_half_eq_one :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          (1 / 2 : ℝ) ^ (p.1 + p.2) / (1 - (1 / 2 : ℝ) ^ (p.1 + p.2)) else 0) = 1
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_positive_sum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L46)

```lean
theorem coprimeLattice_positive_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = (∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)) - r
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_plain_half_eq_series_sub_half`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L136)

```lean
theorem coprimeLattice_plain_half_eq_series_sub_half :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (1 / 2 : ℝ) ^ (p.1 + p.2) else 0)
        = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 ∧
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2
        ≠ ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_halfOpen_half_eq_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L155)

```lean
theorem coprimeLattice_halfOpen_half_eq_series :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then (1 / 2 : ℝ) ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n
```

<a id="thm-classical-coprime-pair-lambert-identity-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `coprimeLattice_lambert_identity` | [E249_18/Challenge.lean, line 266](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L266) | [PaperStatementsAJ.lean, line 208](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L208) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_lambert_rational` | [E249_18/Challenge.lean, line 273](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L273) | [PaperStatementsAJ.lean, line 214](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L214) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_lambert_half_eq_one` | [E249_18/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L260) | [PaperStatementsAJ.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L203) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_positive_sum` | [E249_18/Challenge.lean, line 280](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L280) | [PaperStatementsAJ.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L227) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_plain_half_eq_series_sub_half` | [E249_19/Challenge.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L92) | [PaperStatementsAJ.lean, line 192](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L192) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `coprimeLattice_halfOpen_half_eq_series` | [E249_18/Challenge.lean, line 249](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L249) | [PaperStatementsAJ.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L194) | [E249_18](../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-nondivisors-short-lcm-window"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.short_lcm_window_nondivisor`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L57)

```lean
theorem short_lcm_window_nondivisor (t j : ℕ) (ht : 1 ≤ t) (hj : 1 ≤ j)
    (hlt : j < 2 * t) (hnd : ¬ j ∣ periodLcm t) :
    ∃ p a : ℕ, Nat.Prime p ∧ 1 ≤ a ∧ j = p ^ a ∧ t < j
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.clean_lcm_ray_factorisation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L67)

```lean
theorem clean_lcm_ray_factorisation (t j q : ℕ) (hdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ (periodLcm t / j)) :
    q * periodLcm t + j = j * (q * (periodLcm t / j) + 1) ∧
    Nat.Coprime j (q * (periodLcm t / j) + 1) ∧
    Nat.totient (q * periodLcm t + j) = Nat.totient j * Nat.totient (q * (periodLcm t / j) + 1)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.unclean_lcm_ray_counterexample`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L76)

```lean
theorem unclean_lcm_ray_counterexample :
    2 ∣ periodLcm 2 ∧ Nat.totient (periodLcm 2 + 2) = 2 ∧
    Nat.totient 2 * Nat.totient (periodLcm 2 / 2 + 1) = 1 ∧
    ¬ (∀ p : ℕ, Nat.Prime p → p ∣ 2 → p ∣ (periodLcm 2 / 2))
```

4. [`Erdos249257.TotientTailPeriodKiller.dvd_periodLcm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/CarrySurvivorExtinction.lean#L525)

```lean
lemma dvd_periodLcm {h t : ℕ} (h1 : 1 ≤ h) (ht : h ≤ t) : h ∣ periodLcm t
```

<a id="thm-nondivisors-short-lcm-window-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `short_lcm_window_nondivisor` | [E249_19/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L175) | [PaperStatementsAT.lean, line 248](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAT.lean#L248) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `clean_lcm_ray_factorisation` | [E249_09/Challenge.lean, line 196](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L196) | [PaperStatementsAT.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L174) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `unclean_lcm_ray_counterexample` | [E249_09/Challenge.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L233) | [PaperStatementsAT.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L241) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `dvd_periodLcm` | [E249_19/Challenge.lean, line 167](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L167) | [PaperStatementsA.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsA.lean#L73) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-unbounded-prime-support-mersenne-factors"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_prime_divisor_order`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L33)

```lean
theorem mersenneLayer_prime_divisor_order {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hdvd : p ∣ 2 ^ q - 1) :
    orderOf ((2 : ℕ) : ZMod p) = q ∧ q ∣ p - 1
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_unbounded_prime_support`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L63)

```lean
theorem mersenneLayer_unbounded_prime_support (B N₀ : ℕ) :
    ∃ q p : ℕ, q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ 2 ^ q - 1 ∧ B < p
```

<a id="thm-unbounded-prime-support-mersenne-factors-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mersenneLayer_prime_divisor_order` | [E249_19/Challenge.lean, line 132](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L132) | [PaperStatementsAJ.lean, line 411](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L411) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `mersenneLayer_unbounded_prime_support` | [E249_19/Challenge.lean, line 137](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L137) | [PaperStatementsAJ.lean, line 415](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L415) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-prime-satisfying-stated-cyclotomic-conditions"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_clean_cyclotomic_anchor_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L73)

```lean
theorem exists_clean_cyclotomic_anchor_paper (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ, q.Prime ∧ p.Prime ∧
      p ∣ ((Polynomial.cyclotomic (h * q) ℤ).eval 2).natAbs ∧
      Nat.Coprime p (h * q) ∧ h * q ∣ p - 1 ∧ N₀ ≤ p - 1
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_layer_prime_order_decomposition_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L84)

```lean
theorem cyclotomic_layer_prime_order_decomposition_paper {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime)
    (hpdvd : p ∣ ((Polynomial.cyclotomic n ℤ).eval 2).natAbs) :
    ∃ a : ℕ, n = p ^ a * orderOf ((2 : ℕ) : ZMod p)
```

<a id="thm-prime-satisfying-stated-cyclotomic-conditions-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_clean_cyclotomic_anchor_paper` | [E249_19/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L120) | [PaperStatementsAJ.lean, line 270](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L270) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `cyclotomic_layer_prime_order_decomposition_paper` | [E249_19/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L104) | [PaperStatementsAJ.lean, line 217](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L217) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-sufficient-order-hypothesis-unbounded-prime"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.boundedDegreeOrderConsumer_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L94)

```lean
theorem boundedDegreeOrderConsumer_unfolded (C : ℕ → ℕ) (m d : ℕ) :
    BoundedDegreeOrderConsumer C m d ↔
      ∀ q p : ℕ, q.Prime → p.Prime → p ∣ C (m * q) →
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.coprime_of_dvd_pow_sub_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L101)

```lean
theorem coprime_of_dvd_pow_sub_one {n p k : ℕ} (hp : 0 < p) (hk : 1 ≤ k)
    (hdvd : n ∣ p ^ k - 1) : Nat.Coprime p n
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.dvd_pow_sub_one_iff_orderOf_dvd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L113)

```lean
theorem dvd_pow_sub_one_iff_orderOf_dvd {n p k : ℕ} (hn : 0 < n) (hp : 0 < p) :
    n ∣ p ^ k - 1 ↔ orderOf ((p : ℕ) : ZMod n) ∣ k
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.boundedOrder_witness_iff_orderOf_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L136)

```lean
theorem boundedOrder_witness_iff_orderOf_le {n p d : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hcop : Nat.Coprime p n) :
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ n ∣ p ^ k - 1) ↔ orderOf ((p : ℕ) : ZMod n) ≤ d
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_index_lt_pow`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L160)

```lean
theorem orderConsumer_index_lt_pow {C : ℕ → ℕ} {m d q p : ℕ}
    (horder : BoundedDegreeOrderConsumer C m d)
    (hq : q.Prime) (hp : p.Prime) (hpC : p ∣ C (m * q)) :
    m * q < p ^ d
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_finite_prime_escape`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L168)

```lean
theorem orderConsumer_finite_prime_escape {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m) (horder : BoundedDegreeOrderConsumer C m d) :
    ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_unbounded_prime_divisors`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L178)

```lean
theorem orderConsumer_unbounded_prime_divisors {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m)
    (hlayer : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q))
    (horder : BoundedDegreeOrderConsumer C m d) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.unbounded_prime_divisors_of_escape_of_nontrivial`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L190)

```lean
theorem unbounded_prime_divisors_of_escape_of_nontrivial {C : ℕ → ℕ} {m : ℕ}
    (hnontrivial : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q → 1 < C (m * q))
    (hescape : FinitePrimeSupportEscape C m) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_orderConsumer_instance`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L212)

```lean
theorem mersenneLayer_orderConsumer_instance :
    BoundedDegreeOrderConsumer (fun n => 2 ^ n - 1) 1 1 ∧
      ∀ q p : ℕ, q.Prime → p.Prime → p ∣ 2 ^ q - 1 →
        orderOf ((p : ℕ) : ZMod q) = 1 ∧ orderOf ((2 : ℕ) : ZMod p) = q
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.eventual_orderConsumer_conclusions`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L232)

```lean
theorem eventual_orderConsumer_conclusions {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m) (horder : EventualBoundedDegreeOrderConsumer C m d) :
    FinitePrimeSupportEscape C m ∧
      (∀ hsupply : PrimeRayLayerSupply C m, UnboundedPrimeDivisorSupply C m)
```

11. [`ErdosProblems.Erdos249.PaperCompleteR21.binaryCyclotomicLayer_eventual_instance`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L241)

```lean
theorem binaryCyclotomicLayer_eventual_instance (m : ℕ) (hm : 0 < m) :
    EventualBoundedDegreeOrderConsumer binaryCyclotomicLayer m 1
```

12. [`ErdosProblems.Erdos249.PaperCompleteR21.binaryCyclotomic_allPrime_form_fails`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L247)

```lean
theorem binaryCyclotomic_allPrime_form_fails :
    ((Polynomial.cyclotomic 6 ℤ).eval 2).natAbs = 3 ∧ ¬ (6 ∣ 3 - 1) ∧
      ¬ BoundedDegreeOrderConsumer binaryCyclotomicLayer 2 1
```

<a id="thm-sufficient-order-hypothesis-unbounded-prime-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `boundedDegreeOrderConsumer_unfolded` | [E249_19/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L81) | [PaperStatementsAJ.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L120) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `coprime_of_dvd_pow_sub_one` | [E249_19/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L100) | [PaperStatementsAJ.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L207) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `dvd_pow_sub_one_iff_orderOf_dvd` | [E249_19/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L110) | [PaperStatementsAJ.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L247) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `boundedOrder_witness_iff_orderOf_le` | [E249_19/Challenge.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L87) | [PaperStatementsAJ.lean, line 125](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L125) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `orderConsumer_index_lt_pow` | [E249_19/Challenge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L147) | [PaperStatementsAJ.lean, line 433](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L433) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `orderConsumer_finite_prime_escape` | [E249_19/Challenge.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L141) | [PaperStatementsAJ.lean, line 428](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L428) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `orderConsumer_unbounded_prime_divisors` | [E249_19/Challenge.lean, line 153](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L153) | [PaperStatementsAJ.lean, line 438](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L438) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `unbounded_prime_divisors_of_escape_of_nontrivial` | [E249_19/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L184) | [PaperStatementsAK.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAK.lean#L100) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `mersenneLayer_orderConsumer_instance` | [E249_19/Challenge.lean, line 126](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L126) | [PaperStatementsAJ.lean, line 406](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L406) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `eventual_orderConsumer_conclusions` | [E249_19/Challenge.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L114) | [PaperStatementsAJ.lean, line 265](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L265) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `binaryCyclotomicLayer_eventual_instance` | [E249_19/Challenge.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L72) | [PaperStatementsAJ.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L113) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `binaryCyclotomic_allPrime_form_fails` | [E249_19/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L76) | [PaperStatementsAJ.lean, line 116](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L116) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-uniform-positive-gap-rank-one"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L238)

```lean
theorem rankOneSubrankQuotient_sub_theta_two_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2
```

2. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersenneTheta_ge_alpha`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L163)

```lean
theorem mobiusMersenneTheta_ge_alpha
    {r : ℕ} (hr : 3 ≤ r) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r
```

3. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersenneTheta_lt_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L196)

```lean
theorem mobiusMersenneTheta_lt_one
    {r : ℕ} (hr : 3 ≤ r) :
    mobiusMersenneTheta r < 1
```

4. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.abs_mobiusMersenneTheta_sub_prefix_le`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L73)

```lean
theorem abs_mobiusMersenneTheta_sub_prefix_le
    {Y r : ℕ} (hY : 4 ≤ Y) (hr : 3 ≤ r) :
    |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤
      (1 : ℝ) / 3584
```

5. [`Erdos249257.SignedQMomentObstruction.mobiusMersenneTheta_two_eq_totient_offset`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/SignedQMomentObstruction.lean#L214)

```lean
theorem mobiusMersenneTheta_two_eq_totient_offset :
    mobiusMersenneTheta 2 =
      (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) *
        ((1 : ℝ) / 2) ^ (n : ℕ)) - 1 / 2
```

6. [`ErdosProblems.Erdos249.PaperCompleteR7.rankOne_denominator_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR7/ShortNoteAssemblies.lean#L58)

```lean
theorem rankOne_denominator_pos {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    0 < mobiusMersennePrefix Y (2 * e + 2)
```

<a id="thm-uniform-positive-gap-rank-one-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rankOneSubrankQuotient_sub_theta_two_gt` | [E249_19/Challenge.lean, line 234](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L234) | [PaperStatementsBG.lean, line 78](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsBG.lean#L78) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `mobiusMersenneTheta_ge_alpha` | [E249_19/Challenge.lean, line 224](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L224) | [PaperStatementsBG.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsBG.lean#L45) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `mobiusMersenneTheta_lt_one` | [E249_19/Challenge.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L229) | [PaperStatementsBG.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsBG.lean#L49) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `abs_mobiusMersenneTheta_sub_prefix_le` | [E249_19/Challenge.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L218) | [PaperStatementsBG.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsBG.lean#L40) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `mobiusMersenneTheta_two_eq_totient_offset` | [E249_19/Challenge.lean, line 198](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L198) | [PaperStatementsAF.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAF.lean#L19) | [E249_19](../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `rankOne_denominator_pos` | [E249_20/Challenge.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_20/Challenge.lean#L37) | [PaperStatementsO.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_20/PaperStatementsO.lean#L39) | [E249_20](../evidence/comparator/replay-35882032091/receipt-E249_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-bound-preserved-positive-normalised-averaging"></a>

## Proposition

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.positive_direct_sum_sub_theta_two_gt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L300)

```lean
theorem positive_direct_sum_sub_theta_two_gt
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (1 : ℝ) / 480 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2
```

2. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.primitive_form_abs_gt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L341)

```lean
theorem primitive_form_abs_gt
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot :
      rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) / 480 <
      |(q : ℝ) * mobiusMersenneTheta 2 - p|
```

<a id="prop-bound-preserved-positive-normalised-averaging-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `positive_direct_sum_sub_theta_two_gt` | [E249_21/Challenge.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L64) | [PaperStatementsBG.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsBG.lean#L52) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `primitive_form_abs_gt` | [E249_21/Challenge.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L77) | [PaperStatementsBG.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsBG.lean#L65) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-concatenation-specified-period-multiples"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_eq_paper_indexed_sum`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L23)

```lean
theorem totientBlock_eq_paper_indexed_sum (a N : ℕ) :
    totientBlock a N
      = ∑ j ∈ Finset.Icc 1 a, (Nat.totient (N + j) : ℤ) * 2 ^ (a - j)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_concatenation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L41)

```lean
theorem totientBlock_concatenation (a b N : ℕ) :
    totientBlock (a + b) N = 2 ^ b * totientBlock a N + totientBlock b (N + a)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_doubling`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L46)

```lean
theorem totientBlock_doubling (h N : ℕ) :
    totientBlock (2 * h) N = 2 ^ h * totientBlock h N + totientBlock h (N + h)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_four_eval`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L53)

```lean
theorem cyclotomic_four_eval (x : ℤ) :
    (Polynomial.cyclotomic 4 ℤ).eval x = x ^ 2 + 1
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_four_two_pow_eq_cyclotomic_two`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L64)

```lean
theorem cyclotomic_four_two_pow_eq_cyclotomic_two (h : ℕ) :
    (Polynomial.cyclotomic 4 ℤ).eval ((2 : ℤ) ^ h) = 2 ^ (2 * h) + 1 ∧
      (Polynomial.cyclotomic 2 ℤ).eval ((2 : ℤ) ^ (2 * h)) = 2 ^ (2 * h) + 1
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_three_two_pow`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L73)

```lean
theorem cyclotomic_three_two_pow (h : ℕ) :
    (Polynomial.cyclotomic 3 ℤ).eval ((2 : ℤ) ^ h) = 2 ^ (2 * h) + 2 ^ h + 1
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.orderOf_two_mod_seven`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L83)

```lean
theorem orderOf_two_mod_seven : orderOf ((2 : ℕ) : ZMod 7) = 3
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.three_not_dvd_two_pow`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L92)

```lean
theorem three_not_dvd_two_pow (j : ℕ) : ¬ (3 ∣ 2 ^ j)
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_three_eval_two_not_dvd_doubling_chain`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L100)

```lean
theorem cyclotomic_three_eval_two_not_dvd_doubling_chain :
    (Polynomial.cyclotomic 3 ℤ).eval 2 = 7 ∧
      orderOf ((2 : ℕ) : ZMod 7) = 3 ∧
      (∀ j : ℕ, ¬ (3 ∣ 2 ^ j)) ∧
      (∀ j : ℕ, ¬ (7 ∣ 2 ^ 2 ^ j - 1))
```

<a id="thm-concatenation-specified-period-multiples-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totientBlock_eq_paper_indexed_sum` | [E249_21/Challenge.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L128) | [PaperStatementsG.lean, line 126](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsG.lean#L126) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `totientBlock_concatenation` | [E249_21/Challenge.lean, line 116](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L116) | [PaperStatementsAJ.lean, line 508](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L508) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `totientBlock_doubling` | [E249_21/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L120) | [PaperStatementsAJ.lean, line 511](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L511) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `cyclotomic_four_eval` | [E249_21/Challenge.lean, line 90](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L90) | [PaperStatementsAJ.lean, line 235](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L235) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `cyclotomic_four_two_pow_eq_cyclotomic_two` | [E249_21/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L94) | [PaperStatementsAJ.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L238) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `cyclotomic_three_two_pow` | [E249_21/Challenge.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L106) | [PaperStatementsAJ.lean, line 253](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L253) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `orderOf_two_mod_seven` | [E249_21/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L110) | [PaperStatementsAJ.lean, line 471](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L471) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `three_not_dvd_two_pow` | [E249_21/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L113) | [PaperStatementsAJ.lean, line 506](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L506) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `cyclotomic_three_eval_two_not_dvd_doubling_chain` | [E249_21/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L99) | [PaperStatementsAJ.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L247) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-hgap-real"></a>

## Theorem (A real-part bound gives a certificate)

> *[`exists_certifiedKill_of_first_harmonic_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/FirstHarmonicGap.lean#L128). <span class="sans-serif">\[Lean\]</span>. <span class="sans-serif">\[uniform\]</span>. . For all $`h,X,L`$ with $`0<X`$ and the room condition $`16(2X{+}h{+}L{+}2)\le 2^L`$, if
> ``` math
> \sum_{N=X}^{2X-1} \operatorname{Re}E(h,N,L) \;\le\; \tfrac{9}{10}\,X ,
> ```
> then $`\exists N\in[X,2X)`$ with $`\mathcal{C}\ h\ N\ L`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.windowFirstCos_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L23)

```lean
theorem windowFirstCos_unfolded (h N L : ℕ) :
    windowFirstCos h N L
      = Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ)))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_real_part_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L34)

```lean
theorem exists_certifiedKill_of_block_real_part_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L
```

<a id="thm-hgap-real-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `windowFirstCos_unfolded` | [E249_21/Challenge.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L220) | [PaperStatementsAU.lean, line 572](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAU.lean#L572) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `exists_certifiedKill_of_block_real_part_bound` | [E249_21/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L175) | [PaperStatementsAT.lean, line 433](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L433) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-hgap-subset"></a>

## Theorem (The same implication for a nonempty subset)

> *[`exists_certifiedKill_of_first_harmonic_gap_subset`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/FirstHarmonicGap.lean#L104). <span class="sans-serif">\[Lean\]</span>. <span class="sans-serif">\[uniform\]</span>. . For any nonempty finite $`T\subseteq\mathbb N`$ with $`T\subset[0,2X)`$ and the same room condition, if
> ``` math
> \sum_{N\in T} \operatorname{Re}E(h,N,L) \;\le\; \tfrac{9}{10}\,|T| ,
> ```
> then $`\exists N\in T`$ with $`\mathcal{C}\ h\ N\ L`$. This generalises Theorem <a href="#thm:hgap-real" data-reference-type="ref" data-reference="thm:hgap-real">216</a>: $`T`$ can be *any* explicitly chosen nonempty finite subset of the dyadic block, not the whole block, and the proof (an averaging pigeonhole, §below) never uses that $`T`$ has positive density or comes from a partition.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_subset_real_part_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L50)

```lean
theorem exists_certifiedKill_of_subset_real_part_bound {h X L : ℕ}
    (T : Finset ℕ)
    (hTlt : ∀ N ∈ T, N < 2 * X)
    (hTne : T.Nonempty)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ T,
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * T.card) :
    ∃ N ∈ T, certifiedKill h N L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.block_real_part_bound_of_subset_form`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L65)

```lean
theorem block_real_part_bound_of_subset_form {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap :
      (∑ N ∈ Finset.Ico X (2 * X),
        Real.cos (2 * Real.pi *
          (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) / ((2 ^ L : ℤ) : ℝ))))
        ≤ (9 / 10 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L
```

<a id="thm-hgap-subset-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_certifiedKill_of_subset_real_part_bound` | [E249_21/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L186) | [PaperStatementsAT.lean, line 443](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L443) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `block_real_part_bound_of_subset_form` | [E249_21/Challenge.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L157) | [PaperStatementsAT.lean, line 319](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L319) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-hgap-norm"></a>

## Theorem (A norm bound gives the real-part criterion)

> *[`exists_certifiedKill_of_first_harmonic_norm_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/FirstHarmonicPivot.lean#L53) and [`irrational_totient_series_of_first_harmonic_norm_gap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/FirstHarmonicPivot.lean#L83). <span class="sans-serif">\[Lean\]</span> for both implications; the hypothesis $`block norm condition`$ is <span class="sans-serif">\[Open\]</span>. The complex norm bound implies the real-part bound ($`|z|\ge\mathrm{Re}(z)`$, and $`21/25 < 9/10`$ absorbs the slack), so it composes through Theorem <a href="#thm:hgap-real" data-reference-type="ref" data-reference="thm:hgap-real">216</a> to the same certificate. Define
> ``` math
> \text{block norm condition} :\Leftrightarrow\;
>   \forall h{>}0\ \forall X_0\ \exists X, L,\ \max(X_0,1)\le X\ \wedge\ 16(2X{+}h{+}L{+}2)\le 2^L\ \wedge
> ```
> ``` math
> \Bigl\|\ \sum_{N=X}^{2X-1}E(h,N,L)\ \Bigr\| \;\le\; \tfrac{21}{25}\,X .
> ```
> . <span class="sans-serif">\[cofinal\]</span> (this is the open target itself). Then
> ``` math
> \text{block norm condition} \;\Longrightarrow\; \mathrm{Irrational}\Bigl(\sum_{n\ge 0}
>   \tfrac{\varphi(n)}{2^n}\Bigr),
> ```
> proved in full, with no further gap, by chaining Theorem <a href="#thm:hgap-norm" data-reference-type="ref" data-reference="thm:hgap-norm">218</a>$`\to`$Theorem <a href="#thm:hgap-real" data-reference-type="ref" data-reference="thm:hgap-real">216</a>$`\to`$ [`irrational_totient_series_of_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L394).*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.blockNormCondition_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L86)

```lean
theorem blockNormCondition_unfolded :
    DTWFirstHarmonicNormGap ↔
      ∀ h : ℕ, 0 < h → ∀ X₀ : ℕ, ∃ X L : ℕ,
        max X₀ 1 ≤ X ∧
        16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
        ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.real_part_bound_of_norm_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L97)

```lean
theorem real_part_bound_of_norm_bound {h X L : ℕ} (hX : (0 : ℝ) ≤ X)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    (21 / 25 : ℝ) < 9 / 10 ∧
      (∑ N ∈ Finset.Ico X (2 * X), windowFirstCos h N L) ≤ (9 / 10 : ℝ) * X
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_of_block_norm_bound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L110)

```lean
theorem exists_certifiedKill_of_block_norm_bound {h X L : ℕ}
    (hX : 0 < X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L)
    (hgap : ‖∑ N ∈ Finset.Ico X (2 * X), windowFirstExp h N L‖ ≤ (21 / 25 : ℝ) * X) :
    ∃ N ∈ Finset.Ico X (2 * X), certifiedKill h N L
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_blockNormCondition`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FirstHarmonicBlockCriteria.lean#L118)

```lean
theorem irrational_of_blockNormCondition (hgap : DTWFirstHarmonicNormGap) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-hgap-norm-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `blockNormCondition_unfolded` | [E249_21/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L149) | [PaperStatementsAT.lean, line 312](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L312) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `real_part_bound_of_norm_bound` | [E249_21/Challenge.lean, line 214](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L214) | [PaperStatementsAU.lean, line 396](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAU.lean#L396) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `exists_certifiedKill_of_block_norm_bound` | [E249_21/Challenge.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L168) | [PaperStatementsAT.lean, line 427](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L427) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `irrational_of_blockNormCondition` | [E249_21/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L199) | [PaperStatementsAT.lean, line 588](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAT.lean#L588) | [E249_21](../evidence/comparator/replay-35882032091/receipt-E249_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-positivity-remaining-residue-inequality"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_corridor_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L39)

```lean
theorem actualLcm_corridor_pos {a : ℕ} (ha : 8 ≤ a) :
    (∀ J : ℕ, J + (a + 6) < 2 * 2 ^ a →
        0 < totientTail (2 * periodLcm (2 ^ a) + J)
              - totientTail (periodLcm (2 ^ a) + J)) ∧
      0 < totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.corridor_letter_pos`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L49)

```lean
theorem corridor_letter_pos {a j : ℕ} (ha : 8 ≤ a) (hj : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    0 < lcmRayArithmeticLetter (2 ^ a) j
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.corridor_height_lt_letter`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L56)

```lean
theorem corridor_height_lt_letter {a j : ℕ} (ha : 8 ≤ a) (hj : 0 < j)
    (hjlt : j < 2 * 2 ^ a) :
    (periodLcm (2 ^ a) : ℤ) < 8 * (2 ^ a : ℤ) * lcmRayArithmeticLetter (2 ^ a) j
```

<a id="thm-positivity-remaining-residue-inequality-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `actualLcm_corridor_pos` | [E249_22/Challenge.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L72) | [PaperStatementsAT.lean, line 271](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAT.lean#L271) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `corridor_letter_pos` | [E249_22/Challenge.lean, line 84](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L84) | [PaperStatementsAT.lean, line 351](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAT.lean#L351) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `corridor_height_lt_letter` | [E249_22/Challenge.lean, line 79](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L79) | [PaperStatementsAT.lean, line 345](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAT.lean#L345) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-proved-implications"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L64)

```lean
theorem topEdgeResidueGap_unfolded (a J K m : ℕ) :
    ActualLcmTopEdgeResidueGap a J K m ↔
      (m ≤ K ∧
        ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_forces_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L75)

```lean
theorem topEdgeResidueGap_forces_nonintegral {a J K m : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a J K m) :
    totientTail (2 * periodLcm (2 ^ a) + J) - totientTail (periodLcm (2 ^ a) + J)
      ∉ Set.range ((↑) : ℤ → ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_orbit_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L83)

```lean
theorem topEdgeResidueGap_orbit_nonintegral {a K m : ℕ} (ha : 8 ≤ a)
    (hshort : K + (a + 6) < 2 * 2 ^ a)
    (hgap : ActualLcmTopEdgeResidueGap a 0 K m) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_topEdgeResidueGapSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L92)

```lean
theorem irrational_of_topEdgeResidueGapSupply
    (hsupply : PowerTwoActualLcmTopEdgeResidueGapSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-proved-implications-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `topEdgeResidueGap_unfolded` | [E249_22/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L113) | [PaperStatementsAU.lean, line 486](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAU.lean#L486) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `topEdgeResidueGap_forces_nonintegral` | [E249_22/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L99) | [PaperStatementsAU.lean, line 470](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAU.lean#L470) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `topEdgeResidueGap_orbit_nonintegral` | [E249_22/Challenge.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L106) | [PaperStatementsAU.lean, line 478](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAU.lean#L478) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `irrational_of_topEdgeResidueGapSupply` | [E249_22/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L94) | [PaperStatementsAU.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAU.lean#L187) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-chain"></a>

## Proposition (Five sufficient conditions)

> *Each of the five conditions below suffices for irrationality. The first four imply the upper-endpoint condition [`PowerTwoActualLcmTopEdgeResidueGapSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1325); the fifth gives nonintegrality directly by the endpoint identity. These are not asserted to form a linear hierarchy. Here $`H=H(2^a)`$, and every condition quantifies over arbitrarily large exponents $`a`$.*
> 
> 1.  *[`ErdosProblems.Erdos249.PaperCompleteR21.PaperAdjacentSuffixMidbandSupply`](https://github.com/wcook04/plectis-erdos/blob/168bf6727758f918a430ef056a1c93d3160b53a6/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L46) (<span class="sans-serif">\[Open\]</span>, <span class="sans-serif">\[cofinal\]</span>):
>     ``` math
>     \forall a_0\ \exists a,m,\ a_0\le a \wedge 8\le a \wedge m{+}1{+}(a{+}6)<2\cdot 2^a \wedge
>           2H{+}m{+}3 < 2^m \wedge
>     ```
>     ``` math
>     2H{+}m{+}2 \le \text{suffix residue}(2^a)\,0\,m \le 2^m - (2H{+}m{+}2)
>     ```
>     (a two-sided band on the adjacent-suffix residue directly, one candidate depth $`m`$).*
> 
> 2.  *[`PowerTwoOddGuardTopEdgeHalfWordBandSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1349) (<span class="sans-serif">\[Open\]</span>, <span class="sans-serif">\[cofinal\]</span>): at the odd guarded depth $`2q{+}1`$, a two-sided band of half-width $`H{+}q{+}2`$ on the half-word residue modulo $`4^q`$. The depth is fixed by the stated guard; it cannot be chosen independently of $`a`$.*
> 
> 3.  *[`PowerTwoActualFinalTopEdgeMagnitudeSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1471) (<span class="sans-serif">\[Open\]</span>, <span class="sans-serif">\[cofinal\]</span>), *proved equivalent* to the previous one via [`topEdgeHalfWordBandSupply_iff_actualFinalCenteredMagnitudeSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1479):
>     ``` math
>     \forall a_0\ \exists a,q,\ \max(14,a_0)\le a \wedge q=q_a
>           \wedge H{+}q{+}2 \le |u_{a,q}| .
>     ```*
> 
> 4.  *[`PowerTwoFlexibleActualTopEdgeMagnitudeSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1927) (<span class="sans-serif">\[Open\]</span>, <span class="sans-serif">\[cofinal\]</span>): the same magnitude bound with the depth restriction relaxed from “canonical guarded” to any odd $`2q{+}1`$ satisfying the half-cell fit $`2(H{+}q{+}2)\le 4^q`$ and the sign-corridor room $`2q{+}2{+}(a{+}6)<2\cdot 2^a`$.*
> 
> 5.  *[`PowerTwoFlexibleActualTerminalDominanceSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1908): under the same bounds as item 4, $`\delta_{2^a}(2q+2)\le2u_{a,q}`$. This is a different one-sided comparison, treated immediately below.*
> 
> *For the first four conditions, the relevant implications into [`PowerTwoActualLcmTopEdgeResidueGapSupply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1325) are as follows: midband $`\to`$ residue-gap at [Lean source](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2109); half-word-band $`\to`$ midband at [Lean source](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2058); final-magnitude $`\Leftrightarrow`$ half-word-band at [Lean source](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1479); flexible-magnitude $`\to`$ midband at [Lean source](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L2008); final-magnitude $`\to`$ flexible-magnitude at [Lean source](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmTopEdgeStaircase.lean#L1993).*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_item_one_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L56)

```lean
theorem paperTeChain_item_one_unfolded :
    PaperAdjacentSuffixMidbandSupply ↔
      ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        m + 1 + (a + 6) < 2 * 2 ^ a ∧
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
          diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_two_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L113)

```lean
theorem teChain_item_two_unfolded :
    PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
          powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
        powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
          (4 : ℤ) ^ q - ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_three_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L124)

```lean
theorem teChain_item_three_unfolded :
    PowerTwoActualFinalTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q|
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_four_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L133)

```lean
theorem teChain_item_four_unfolded :
    PowerTwoFlexibleActualTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q|
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_five_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L142)

```lean
theorem teChain_item_five_unfolded :
    PowerTwoFlexibleActualTerminalDominanceSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
          2 * actualOddHalfCenteredLift a q
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_five_sufficient_for_irrationality`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L214)

```lean
theorem paperTeChain_five_sufficient_for_irrationality :
    (PaperAdjacentSuffixMidbandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_first_four_imply_topEdgeSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L233)

```lean
theorem paperTeChain_first_four_imply_topEdgeSupply :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_fifth_gives_nonintegrality`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L271)

```lean
theorem paperTeChain_fifth_gives_nonintegrality :
    PowerTwoFlexibleActualTerminalDominanceSupply →
      PowerTwoActualLcmOrbitNonintegralitySupply
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_relations`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L254)

```lean
theorem paperTeChain_relations :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply)
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_or_of_paperAdjacentSuffixMidband`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L87)

```lean
theorem topEdgeResidueGap_or_of_paperAdjacentSuffixMidband
    {a m : ℕ}
    (hroom :
      ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m)
    (hlo :
      ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m)
    (hhi :
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)) :
    ActualLcmTopEdgeResidueGap a 0 m m ∨
      ActualLcmTopEdgeResidueGap a 0 (m + 1) m
```

11. [`ErdosProblems.Erdos249.PaperCompleteR21.powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L179)

```lean
theorem powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    PowerTwoActualLcmTopEdgeResidueGapSupply
```

12. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_paperAdjacentSuffixMidbandSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L190)

```lean
theorem irrational_of_paperAdjacentSuffixMidbandSupply
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

13. [`ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L197)

```lean
theorem paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
    (hsupply : PowerTwoOddGuardTopEdgeHalfWordBandSupply) :
    PaperAdjacentSuffixMidbandSupply
```

where [`PaperAdjacentSuffixMidbandSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L46) is

```lean
def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
```

14. [`ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L204)

```lean
theorem paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude
    (hsupply : PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :
    PaperAdjacentSuffixMidbandSupply
```

where [`PaperAdjacentSuffixMidbandSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L46) is

```lean
def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
```

15. [`ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L69)

```lean
theorem paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband
    (hsupply : PowerTwoAdjacentSuffixMidbandSupply) :
    PaperAdjacentSuffixMidbandSupply
```

where [`PaperAdjacentSuffixMidbandSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeChainPaperBand.lean#L46) is

```lean
def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
```

<a id="prop-te-chain-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paperTeChain_item_one_unfolded` | [E249_22/Challenge.lean, line 289](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L289) | [PaperStatementsAX.lean, line 346](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L346) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `teChain_item_two_unfolded` | [E249_23/Challenge.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L238) | [PaperStatementsAX.lean, line 445](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L445) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `teChain_item_three_unfolded` | [E249_23/Challenge.lean, line 231](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L231) | [PaperStatementsAX.lean, line 437](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L437) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `teChain_item_four_unfolded` | [E249_23/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L223) | [PaperStatementsAX.lean, line 428](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L428) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `teChain_item_five_unfolded` | [E249_23/Challenge.lean, line 214](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L214) | [PaperStatementsAX.lean, line 418](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L418) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `paperTeChain_five_sufficient_for_irrationality` | [E249_22/Challenge.lean, line 276](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L276) | [PaperStatementsAX.lean, line 332](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L332) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperTeChain_first_four_imply_topEdgeSupply` | [E249_22/Challenge.lean, line 266](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L266) | [PaperStatementsAX.lean, line 321](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L321) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperTeChain_fifth_gives_nonintegrality` | [E249_22/Challenge.lean, line 261](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L261) | [PaperStatementsAX.lean, line 315](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L315) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperTeChain_relations` | [E249_23/Challenge.lean, line 197](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L197) | [PaperStatementsAX.lean, line 364](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L364) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `topEdgeResidueGap_or_of_paperAdjacentSuffixMidband` | [E249_23/Challenge.lean, line 257](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L257) | [PaperStatementsAX.lean, line 484](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L484) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband` | [E249_23/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L209) | [PaperStatementsAX.lean, line 377](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L377) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `irrational_of_paperAdjacentSuffixMidbandSupply` | [E249_22/Challenge.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L241) | [PaperStatementsAX.lean, line 226](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L226) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand` | [E249_22/Challenge.lean, line 256](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L256) | [PaperStatementsAX.lean, line 309](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L309) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude` | [E249_22/Challenge.lean, line 251](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L251) | [PaperStatementsAX.lean, line 303](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L303) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |
| `paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband` | [E249_22/Challenge.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_22/Challenge.lean#L246) | [PaperStatementsAX.lean, line 297](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_22/PaperStatementsAX.lean#L297) | [E249_22](../evidence/comparator/replay-35882032091/receipt-E249_22.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-proved-implication"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.terminalDominance_orbit_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L217)

```lean
theorem terminalDominance_orbit_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hdom : diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
      2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_terminalDominanceSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L228)

```lean
theorem irrational_of_terminalDominanceSupply
    (hsupply : PowerTwoFlexibleActualTerminalDominanceSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-proved-implication-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `terminalDominance_orbit_nonintegral` | [E249_23/Challenge.lean, line 248](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L248) | [PaperStatementsAX.lean, line 474](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L474) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `irrational_of_terminalDominanceSupply` | [E249_23/Challenge.lean, line 192](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L192) | [PaperStatementsAX.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L245) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sufficient-extension"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_lower_escape_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L236)

```lean
theorem irrational_of_lower_escape_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
      2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
      2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
      2 * actualOddHalfCenteredLift a q ≤
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
          ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.corridor_escape_and_irrational_of_magnitude`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L252)

```lean
theorem corridor_escape_and_irrational_of_magnitude :
    (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_four_unfolded`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L133)

```lean
theorem teChain_item_four_unfolded :
    PowerTwoFlexibleActualTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q|
```

<a id="prop-sufficient-extension-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_lower_escape_supply` | [E249_23/Challenge.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L182) | [PaperStatementsAX.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L221) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `corridor_escape_and_irrational_of_magnitude` | [E249_23/Challenge.lean, line 173](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L173) | [PaperStatementsAX.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L181) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `teChain_item_four_unfolded` | [E249_23/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L223) | [PaperStatementsAX.lean, line 428](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L428) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-separation-rational-approximation"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L276)

```lean
theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form (a q : ℕ) :
    |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)))
        - actualLcmRawApprox a q|
      < (4 * (periodLcm (2 ^ a) : ℝ) + 2 * (2 * (q : ℝ) + 1) + 4) / 2 ^ (2 * q + 2)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.two_pow_odd_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L266)

```lean
theorem two_pow_odd_eq (q : ℕ) : (2 : ℝ) ^ (2 * q + 1) = 2 * (4 : ℝ) ^ q
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawApprox_isRat`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L312)

```lean
theorem actualLcmRawApprox_isRat (a q : ℕ) :
    ∃ v : ℚ, actualLcmRawApprox a q = (v : ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawErrorRadius_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L294)

```lean
theorem actualLcmRawErrorRadius_tendsto_zero (a : ℕ) :
    Filter.Tendsto (fun q : ℕ => actualLcmRawErrorRadius a q) Filter.atTop (nhds 0)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_actualLcmOrbitSeparationSupply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TopEdgeCorridorAndSeparation.lean#L320)

```lean
theorem irrational_of_actualLcmOrbitSeparationSupply
    (hsupply : PowerTwoActualLcmOrbitSeparationSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-separation-rational-approximation-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form` | [E249_23/Challenge.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L163) | [PaperStatementsAX.lean, line 143](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L143) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `two_pow_odd_eq` | [E249_23/Challenge.lean, line 275](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L275) | [PaperStatementsAK.lean, line 102](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAK.lean#L102) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `actualLcmRawApprox_isRat` | [E249_23/Challenge.lean, line 169](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L169) | [PaperStatementsAX.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAX.lean#L158) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `actualLcmRawErrorRadius_tendsto_zero` | [E249_23/Challenge.lean, line 290](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_23/Challenge.lean#L290) | [PaperStatementsAT.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_23/PaperStatementsAT.lean#L260) | [E249_23](../evidence/comparator/replay-35882032091/receipt-E249_23.json) |
| `irrational_of_actualLcmOrbitSeparationSupply` | [E249_24/Challenge.lean, line 88](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L88) | [PaperStatementsAX.lean, line 315](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAX.lean#L315) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-short-window-examples-through-exponent"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_through_six_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L29)

```lean
theorem shortWindowSupply_through_six_paper (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    ∃ a L : ℕ, a₀ ≤ a ∧ L < 2 * 2 ^ a ∧
      certifiedKill (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_single_witness_six_ninetyThree`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L38)

```lean
theorem shortWindowSupply_single_witness_six_ninetyThree (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    a₀ ≤ 6 ∧ (93 : ℕ) < 2 * 2 ^ 6 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_witness_eq_t64_certificate`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L47)

```lean
theorem shortWindowSupply_witness_eq_t64_certificate :
    certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ↔
      certifiedKill (periodLcm 64) (periodLcm 64) 93
```

<a id="thm-short-window-examples-through-exponent-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `shortWindowSupply_through_six_paper` | [E249_24/Challenge.lean, line 108](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L108) | [PaperStatementsAU.lean, line 425](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAU.lean#L425) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `shortWindowSupply_single_witness_six_ninetyThree` | [E249_24/Challenge.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L122) | [PaperStructuresN.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStructuresN.lean#L52) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `shortWindowSupply_witness_eq_t64_certificate` | [E249_24/Challenge.lean, line 127](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L127) | [PaperStructuresN.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStructuresN.lean#L58) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-diagonal-certificate-table"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.diagonalPincerCertificateScales_list`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L22)

```lean
theorem diagonalPincerCertificateScales_list :
    diagonalPincerCertificateScales = [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17]
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.diagonalPincerKillDepth_list`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L26)

```lean
theorem diagonalPincerKillDepth_list :
    diagonalPincerCertificateScales.map diagonalPincerKillDepth =
      [6, 5, 7, 7, 9, 14, 15, 14, 21, 22, 23, 26]
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_diagonal_table`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L33)

```lean
theorem certifiedKill_diagonal_table :
    ∀ t ∈ diagonalPincerCertificateScales,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepth t)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_diagonalKill_on_table`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L40)

```lean
theorem exists_diagonalKill_on_table :
    ∀ t ∈ diagonalPincerCertificateScales,
      ∃ L, certifiedKill (periodLcm t) (periodLcm t) L
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_diagonal_t64_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L46)

```lean
theorem certifiedKill_diagonal_t64_paper :
    certifiedKill (periodLcm 64) (periodLcm 64) 93
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_diagonalKill_le_82_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L52)

```lean
theorem exists_diagonalKill_le_82_paper (t : ℕ) (ht : t ≤ 82) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_seventeen_window_data`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DiagonalCertificateTableScales.lean#L59)

```lean
theorem periodLcm_seventeen_window_data :
    periodLcm 17 = 12252240 ∧ periodLcm 17 + 1 = 12252241 ∧
      2 * periodLcm 17 + 1 = 24504481 ∧ 2 * periodLcm 17 + 26 = 24504506 ∧
      diagonalPincerKillDepth 17 = 26
```

<a id="thm-diagonal-certificate-table-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `diagonalPincerCertificateScales_list` | [E249_24/Challenge.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L136) | [PaperStatementsG.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsG.lean#L106) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `diagonalPincerKillDepth_list` | [E249_24/Challenge.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L140) | [PaperStatementsG.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsG.lean#L109) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `certifiedKill_diagonal_table` | [E249_24/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L150) | [PaperStatementsI.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsI.lean#L152) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `exists_diagonalKill_on_table` | [E249_24/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L159) | [PaperStatementsI.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsI.lean#L163) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `certifiedKill_diagonal_t64_paper` | [E249_24/Challenge.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L118) | [PaperStructuresN.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStructuresN.lean#L47) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `exists_diagonalKill_le_82_paper` | [E249_24/Challenge.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L155) | [PaperStatementsI.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsI.lean#L158) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `periodLcm_seventeen_window_data` | [E249_24/Challenge.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L171) | [PaperStatementsI.lean, line 177](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsI.lean#L177) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sufficient-extension-2"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_logarithmicDepth_diagonal_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L58)

```lean
theorem irrational_of_logarithmicDepth_diagonal_supply
    (hsupply : ∃ C : ℕ, ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
      L ≤ Nat.log2 (4 * periodLcm t) + C ∧
        certifiedKill (periodLcm t) (periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_restrictedDepth_diagonal_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L72)

```lean
theorem irrational_of_restrictedDepth_diagonal_supply (depthBound : ℕ → ℕ → Prop)
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ,
      depthBound t L ∧ certifiedKill (periodLcm t) (periodLcm t) L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="prop-sufficient-extension-2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_logarithmicDepth_diagonal_supply` | [E249_24/Challenge.lean, line 164](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L164) | [PaperStatementsI.lean, line 169](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsI.lean#L169) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `irrational_of_restrictedDepth_diagonal_supply` | [E249_24/Challenge.lean, line 98](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L98) | [PaperStatementsAU.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAU.lean#L184) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-one-common-certificate-sixteen-shifts"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.commonCertificate_sixteen_shifts_basepoint_fourteen`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L85)

```lean
theorem commonCertificate_sixteen_shifts_basepoint_fourteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L91)

```lean
theorem totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne
    (r : ℚ) (h : ℕ) (h1 : 1 ≤ h) (h16 : h ≤ 16)
    (hdvd : (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.commonCertificate_eight_shifts_basepoint_twelve`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ShortWindowSupplyAndSixteenShifts.lean#L98)

```lean
theorem commonCertificate_eight_shifts_basepoint_twelve :
    ∀ h ∈ Finset.Icc 1 8, certifiedKill h 12 16
```

<a id="thm-one-common-certificate-sixteen-shifts-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `commonCertificate_sixteen_shifts_basepoint_fourteen` | [E249_24/Challenge.lean, line 208](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L208) | [PaperStatementsAT.lean, line 350](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L350) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `totientSeries_ne_rat_of_den_dvd_two_pow_fourteen_mul_mersenne` | [E249_24/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L180) | [PaperStatementsAK.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAK.lean#L41) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `commonCertificate_eight_shifts_basepoint_twelve` | [E249_24/Challenge.lean, line 204](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L204) | [PaperStatementsAT.lean, line 347](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L347) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-simultaneous-certificates-unrestricted-depth"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_growingShift_simultaneous_certificate_iff_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SimultaneousShiftCertificateDepth.lean#L131)

```lean
theorem exists_growingShift_simultaneous_certificate_iff_irrational :
    (∃ f : ℕ → ℕ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
        ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, ∀ h ∈ Finset.Icc 1 (f N),
          certifiedKill h N L) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_succ_of_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SimultaneousShiftCertificateDepth.lean#L122)

```lean
theorem exists_simultaneous_depth_succ_of_irrational
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) (N : ℕ) :
    ∃ L, ∀ h ∈ Finset.Icc 1 (N + 1), certifiedKill h N L
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_simultaneous_depth_of_irrational`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/SimultaneousShiftCertificateDepth.lean#L89)

```lean
theorem exists_simultaneous_depth_of_irrational
    (hS : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) (N M : ℕ)
    (hM : 1 ≤ M) :
    ∃ L, ∀ h ∈ Finset.Icc 1 M, certifiedKill h N L
```

<a id="prop-simultaneous-certificates-unrestricted-depth-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_growingShift_simultaneous_certificate_iff_irrational` | [E249_24/Challenge.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L221) | [PaperStatementsAT.lean, line 461](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L461) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `exists_simultaneous_depth_succ_of_irrational` | [E249_24/Challenge.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L247) | [PaperStatementsAT.lean, line 505](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L505) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `exists_simultaneous_depth_of_irrational` | [E249_24/Challenge.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L241) | [PaperStatementsAT.lean, line 500](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L500) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-fixed-farey-bound"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_rational_den_gt_fareyBound`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L23)

```lean
theorem totientSeries_rational_den_gt_fareyBound (q : ℚ)
    (hq : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (q : ℝ)) :
    79639646646701375323355774875831053 < q.den
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.farey_gap_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L31)

```lean
theorem farey_gap_paper {a b c d r s : ℤ} (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1) (hleft : a * s < r * b) (hright : r * d < c * s) :
    b + d ≤ s
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_1_240_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L39)

```lean
theorem gapCheck_window_1_240_paper (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904)
        % 2 ^ 240 + q * 243 < 2 ^ 240
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_1_240_first_failure_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L48)

```lean
theorem gapCheck_window_1_240_first_failure_paper :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054
```

<a id="thm-fixed-farey-bound-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totientSeries_rational_den_gt_fareyBound` | [E249_24/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L186) | [PaperStatementsAK.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAK.lean#L46) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `farey_gap_paper` | [E249_24/Challenge.lean, line 266](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L266) | [PaperStatementsAJ.lean, line 322](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAJ.lean#L322) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `gapCheck_window_1_240_paper` | [E249_24/Challenge.lean, line 277](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L277) | [PaperStatementsAJ.lean, line 348](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAJ.lean#L348) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `gapCheck_window_1_240_first_failure_paper` | [E249_24/Challenge.lean, line 271](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L271) | [PaperStatementsAJ.lean, line 343](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAJ.lean#L343) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sufficient-extension-3"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_unbounded_window_one_gapCheck`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L68)

```lean
theorem irrational_of_unbounded_window_one_gapCheck (g : ℕ → ℕ)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop)
    (hcheck : ∀ K q : ℕ, 0 < q → q ≤ g K →
      (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (1 + r) * 2 ^ (K - r)) % 2 ^ K))
        % 2 ^ K + q * (1 + K + 2) < 2 ^ K) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_one_excludes`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyDenominatorFloorExtension.lean#L58)

```lean
theorem gapCheck_window_one_excludes (K q : ℕ) (hq : 0 < q)
    (hcert : (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (1 + r) * 2 ^ (K - r)) % 2 ^ K))
        % 2 ^ K + q * (1 + K + 2) < 2 ^ K) :
    ∀ a : ℤ, (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (a : ℝ) / (q : ℝ)
```

<a id="prop-sufficient-extension-3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_unbounded_window_one_gapCheck` | [E249_24/Challenge.lean, line 289](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L289) | [PaperStatementsAJ.lean, line 401](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAJ.lean#L401) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `gapCheck_window_one_excludes` | [E249_24/Challenge.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L283) | [PaperStatementsAJ.lean, line 353](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAJ.lean#L353) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-two-adic-congruence-that-does"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_half_pulse_window`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicHalfPulseAndAccumulatedResidue.lean#L26)

```lean
theorem exists_prime_twoAdic_half_pulse_window (H K B : ℕ) (hK : 2 ≤ K)
    (hHK : K < H) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      (∀ j : ℕ, 1 ≤ j → j < K →
        deltaTotient H (p - j) ≡ 0 [ZMOD (2 : ℤ) ^ K]) ∧
      deltaTotient H p ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K] ∧
      windowDiscrepancy H (p - K) K ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K]
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.eventual_integral_tailDiff_twoAdic_half_pulse`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicHalfPulseAndAccumulatedResidue.lean#L41)

```lean
theorem eventual_integral_tailDiff_twoAdic_half_pulse {H K N₀ : ℕ} (hK : 2 ≤ K)
    (hHK : K < H)
    (hint : ∀ N : ℕ, N₀ ≤ N →
      totientTail (N + H) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) :
    ∀ B : ℕ, ∃ p : ℕ, B < p ∧ p.Prime ∧ ∃ z : ℤ,
      (z : ℝ) = totientTail (p + H) - totientTail p ∧
        z ≡ (2 : ℤ) ^ (K - 1) [ZMOD (2 : ℤ) ^ K]
```

<a id="thm-two-adic-congruence-that-does-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_prime_twoAdic_half_pulse_window` | [E249_24/Challenge.lean, line 232](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L232) | [PaperStatementsAT.lean, line 481](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L481) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `eventual_integral_tailDiff_twoAdic_half_pulse` | [E249_24/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L212) | [PaperStatementsAT.lean, line 397](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L397) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sufficient-accumulated-residue-condition"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_accumulated_halfModulus_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicHalfPulseAndAccumulatedResidue.lean#L77)

```lean
theorem irrational_of_accumulated_halfModulus_supply
    (hsupply : ∀ h : ℕ, 1 ≤ h → ∀ N₀ : ℕ, ∃ N L : ℕ, N₀ ≤ N ∧ 1 ≤ L ∧
      windowDiscrepancy h N L ≡ 2 ^ (L - 1) [ZMOD (2 : ℤ) ^ L] ∧
      ((N : ℤ) + h + L + 2) < 2 ^ (L - 1)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_of_halfModulus_residue`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicHalfPulseAndAccumulatedResidue.lean#L53)

```lean
theorem certifiedKill_of_halfModulus_residue {h N L : ℕ} (hL : 1 ≤ L)
    (hcong : windowDiscrepancy h N L ≡ 2 ^ (L - 1) [ZMOD (2 : ℤ) ^ L])
    (hsmall : ((N : ℤ) + h + L + 2) < 2 ^ (L - 1)) :
    certifiedKill h N L
```

<a id="prop-sufficient-accumulated-residue-condition-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_accumulated_halfModulus_supply` | [E249_24/Challenge.lean, line 252](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L252) | [PaperStatementsAT.lean, line 588](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L588) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `certifiedKill_of_halfModulus_residue` | [E249_24/Challenge.lean, line 198](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L198) | [PaperStatementsAT.lean, line 342](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L342) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-arbitrarily-large-prime-power-lcm"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_periodLcm_strict_jump_ge_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L26)

```lean
theorem exists_periodLcm_strict_jump_ge_paper (t₀ : ℕ) :
    ∃ t, t₀ ≤ t ∧ periodLcm t < periodLcm (t + 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_strict_jump_at_prime_pred`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L31)

```lean
theorem periodLcm_strict_jump_at_prime_pred {t₀ p : ℕ} (hp : p.Prime)
    (hpt : t₀ < p) :
    t₀ ≤ p - 1 ∧ periodLcm (p - 1) < periodLcm (p - 1 + 1)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_strict_jump_at_powerTwo_pred`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L46)

```lean
theorem periodLcm_strict_jump_at_powerTwo_pred {a : ℕ} (ha : 1 ≤ a) :
    periodLcm (2 ^ a - 1) < periodLcm (2 ^ a - 1 + 1)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_zero_and_one_eq_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L59)

```lean
theorem periodLcm_zero_and_one_eq_one :
    periodLcm 0 = 1 ∧ periodLcm 1 = 1 ∧ ¬ periodLcm 0 < periodLcm (0 + 1)
```

<a id="thm-arbitrarily-large-prime-power-lcm-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_periodLcm_strict_jump_ge_paper` | [E249_24/Challenge.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L228) | [PaperStatementsAT.lean, line 467](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAT.lean#L467) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `periodLcm_strict_jump_at_prime_pred` | [E249_25/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L76) | [PaperStatementsAU.lean, line 304](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L304) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `periodLcm_strict_jump_at_powerTwo_pred` | [E249_24/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_24/Challenge.lean#L104) | [PaperStatementsAU.lean, line 318](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_24/PaperStatementsAU.lean#L318) | [E249_24](../evidence/comparator/replay-35882032091/receipt-E249_24.json) |
| `periodLcm_zero_and_one_eq_one` | [E249_25/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L81) | [PaperStatementsAU.lean, line 310](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L310) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sufficient-inequality"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_powerTwo_postJump_slack_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L90)

```lean
theorem irrational_of_powerTwo_postJump_slack_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a, max 2 a₀ ≤ a ∧
      0 ≤ canonicalAdjacentSuffixCentralSlack (2 ^ a)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.canonicalAdjacentSuffixCentralSlack_paper_formula`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LcmJumpPositionsAndCentralSlack.lean#L68)

```lean
theorem canonicalAdjacentSuffixCentralSlack_paper_formula (t : ℕ) :
    canonicalAdjacentSuffixCentralSlack t =
      min ((windowDiscrepancy (periodLcm t) (periodLcm t + 1)
                (Nat.log2 (periodLcm t) + 10)
              - windowDiscrepancy (periodLcm t) (periodLcm t)
                (Nat.log2 (periodLcm t) + 10))
            % 2 ^ (Nat.log2 (periodLcm t) + 10)
          - 2 ^ (Nat.log2 (periodLcm t) + 10 - 5))
        (2 ^ (Nat.log2 (periodLcm t) + 10)
            - 2 ^ (Nat.log2 (periodLcm t) + 10 - 5)
          - (windowDiscrepancy (periodLcm t) (periodLcm t + 1)
                 (Nat.log2 (periodLcm t) + 10)
               - windowDiscrepancy (periodLcm t) (periodLcm t)
                 (Nat.log2 (periodLcm t) + 10))
            % 2 ^ (Nat.log2 (periodLcm t) + 10))
```

<a id="prop-sufficient-inequality-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_powerTwo_postJump_slack_supply` | [E249_25/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L146) | [PaperStatementsAX.lean, line 339](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAX.lean#L339) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `canonicalAdjacentSuffixCentralSlack_paper_formula` | [E249_25/Challenge.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L129) | [PaperStatementsAX.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAX.lean#L264) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-certificate-four-tail-combination"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJumpTailCommutator_notMem_int_of_central_window`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L36)

```lean
theorem primeJumpTailCommutator_notMem_int_of_central_window (H p L : ℕ)
    (hleft : (primeJumpSharpRadius H p L) < primeJumpWindowCommutator H p L % 2 ^ L)
    (hright : primeJumpWindowCommutator H p L % 2 ^ L
      < 2 ^ L - primeJumpSharpRadius H p L) :
    primeJumpTailCommutator H p ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_formula`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L31)

```lean
theorem primeJumpSharpRadius_formula (H p L : ℕ) :
    primeJumpSharpRadius H p L = 3 * p * H + (p + 1) * (L + 2)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_saves_pH`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L45)

```lean
theorem primeJumpSharpRadius_saves_pH (H p L : ℕ) :
    (4 * p * H + (p + 1) * (L + 2) : ℤ) - primeJumpSharpRadius H p L = p * H
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_lt_twoCellRadius`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L52)

```lean
theorem primeJumpSharpRadius_lt_twoCellRadius {H p L : ℕ} (hpH : 0 < p * H) :
    primeJumpSharpRadius H p L < (4 * p * H + (p + 1) * (L + 2) : ℤ)
```

<a id="thm-certificate-four-tail-combination-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `primeJumpTailCommutator_notMem_int_of_central_window` | [E249_25/Challenge.lean, line 85](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L85) | [PaperStatementsAU.lean, line 325](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L325) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `primeJumpSharpRadius_formula` | [E249_25/Challenge.lean, line 173](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L173) | [PaperStatementsAJ.lean, line 482](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAJ.lean#L482) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `primeJumpSharpRadius_saves_pH` | [E249_25/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L181) | [PaperStatementsAJ.lean, line 488](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAJ.lean#L488) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `primeJumpSharpRadius_lt_twoCellRadius` | [E249_25/Challenge.lean, line 177](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L177) | [PaperStatementsAJ.lean, line 485](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAJ.lean#L485) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-one-explicit-witness"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.periodLcm_four_eq_twelve`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L62)

```lean
theorem periodLcm_four_eq_twelve : periodLcm 4 = 12
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJump_witness_twelve_five_values`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L68)

```lean
theorem primeJump_witness_twelve_five_values :
    primeJumpWindowCommutator 12 5 15 = 149906 ∧
      primeJumpWindowCommutator 12 5 15 % 32768 = 18834 ∧
      primeJumpSharpRadius 12 5 15 = 282 ∧
      (282 : ℤ) < 18834 ∧ (18834 : ℤ) < 32486
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.primeJumpTailCommutator_twelve_five_notMem_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L76)

```lean
theorem primeJumpTailCommutator_twelve_five_notMem_int :
    primeJumpTailCommutator 12 5 ∉ Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_primeJumpSharp_supply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L81)

```lean
theorem irrational_of_primeJumpSharp_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ p L : ℕ,
      0 < p ∧ primeJumpSharpKill (periodLcm t) p L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-one-explicit-witness-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `periodLcm_four_eq_twelve` | [E249_25/Challenge.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L73) | [PaperStatementsAU.lean, line 297](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L297) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `primeJump_witness_twelve_five_values` | [E249_25/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L96) | [PaperStatementsAU.lean, line 334](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L334) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `primeJumpTailCommutator_twelve_five_notMem_int` | [E249_25/Challenge.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L92) | [PaperStatementsAU.lean, line 331](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L331) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `irrational_of_primeJumpSharp_supply` | [E249_25/Challenge.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L67) | [PaperStatementsAU.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAU.lean#L158) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-denominators-mobius-sums"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.upperHalfMersenneProduct_between_bounds`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L110)

```lean
theorem upperHalfMersenneProduct_between_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ ∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p ∧
      (∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p) ≤
        ((lcmHeight t : ℚ) *
          RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_upperHalf_channel_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L123)

```lean
theorem exists_upperHalf_channel_paper {t : ℕ} (ht : 5 ≤ t) :
    ∃ p ∈ upperHalfPrimes t,
      2 ^ (t / 2) ≤ RadicalMobiusShadow.mersenne p ∧
      RadicalMobiusShadow.mersenne p < 2 ^ t ∧
      RadicalMobiusShadow.mersenne p ∣
        ((lcmHeight t : ℚ) *
          RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_nonempty_paper`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L98)

```lean
theorem upperHalfPrimes_nonempty_paper {t : ℕ} (ht : 2 ≤ t) :
    (upperHalfPrimes t).Nonempty
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_member_bounds`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L103)

```lean
theorem upperHalfPrimes_member_bounds {t p : ℕ} (hp : p ∈ upperHalfPrimes t) :
    t / 2 ≤ p - 1 ∧ p ≤ t
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.upperHalfPrimes_spec`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L94)

```lean
theorem upperHalfPrimes_spec (t : ℕ) :
    upperHalfPrimes t = (Finset.Ioc (t / 2) t).filter Nat.Prime
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmHeight_eq_periodLcm`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L90)

```lean
theorem lcmHeight_eq_periodLcm (t : ℕ) : lcmHeight t = periodLcm t
```

<a id="thm-denominators-mobius-sums-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `upperHalfMersenneProduct_between_bounds` | [E249_25/Challenge.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L218) | [PaperStatementsAY.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAY.lean#L100) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `exists_upperHalf_channel_paper` | [E249_25/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L209) | [PaperStatementsAY.lean, line 70](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAY.lean#L70) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `upperHalfPrimes_nonempty_paper` | [E249_25/Challenge.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L229) | [PaperStatementsAY.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAY.lean#L109) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `upperHalfPrimes_member_bounds` | [E249_25/Challenge.lean, line 225](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L225) | [PaperStatementsAY.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAY.lean#L106) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `upperHalfPrimes_spec` | [E249_25/Challenge.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L233) | [PaperStatementsAY.lean, line 112](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAY.lean#L112) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `lcmHeight_eq_periodLcm` | [E249_25/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L152) | [PaperStatementsAX.lean, line 384](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAX.lean#L384) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `upperHalfMersenneProduct_between_bounds`:

```lean
theorem upperHalfMersenneProduct_between_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ ∏ p ∈ upperHalfPrimes t, mersenne p ∧
      (∏ p ∈ upperHalfPrimes t, mersenne p) ≤
        ((lcmHeight t : ℚ) *
          numericMobiusShadow (lcmHeight t)).den := by sorry
```

Challenge for `exists_upperHalf_channel_paper`:

```lean
theorem exists_upperHalf_channel_paper {t : ℕ} (ht : 5 ≤ t) :
    ∃ p ∈ upperHalfPrimes t,
      2 ^ (t / 2) ≤ mersenne p ∧
      mersenne p < 2 ^ t ∧
      mersenne p ∣
        ((lcmHeight t : ℚ) *
          numericMobiusShadow (lcmHeight t)).den := by sorry
```

<a id="prop-additional-approximation-hypothesis"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_rational_separation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L137)

```lean
theorem irrational_totientSeries_of_rational_separation (u : ℕ → ℚ)
    (hne : ∀ᶠ t in Filter.atTop,
      ((u t : ℝ)) ≠ ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
    (h0 : Filter.Tendsto
      (fun t => ((u t).den : ℝ) *
        |(∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (u t : ℝ)|)
      Filter.atTop (nhds 0)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.den_mul_abs_sub_ge_one_div_den`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/PrimeJumpWitnessAndMersenneChannels.lean#L149)

```lean
theorem den_mul_abs_sub_ge_one_div_den {q u : ℚ} (hqu : q ≠ u) :
    (1 : ℝ) / (q.den : ℝ) ≤ (u.den : ℝ) * |(q : ℝ) - (u : ℝ)|
```

<a id="prop-additional-approximation-hypothesis-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totientSeries_of_rational_separation` | [E249_25/Challenge.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L163) | [PaperStatementsAJ.lean, line 423](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAJ.lean#L423) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `den_mul_abs_sub_ge_one_div_den` | [E249_25/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L159) | [PaperStatementsAJ.lean, line 262](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsAJ.lean#L262) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-rationality-carry-rank"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.retainedSections_basis_and_rank`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L79)

```lean
theorem retainedSections_basis_and_rank (e : ℕ) (he : 1 ≤ e) :
    (∃ b : Module.Basis (TotientCanonicalIndex e) ℚ
        (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))),
        ∀ i, (b i : ℕ → ℚ) = canonicalTotientKernelFamily e i) ∧
      Module.finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)))
        = 2 ^ e + 1
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.completeLevelZeroTruncation_is_totient_and_rank_one`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L93)

```lean
theorem completeLevelZeroTruncation_is_totient_and_rank_one :
    Set.range (totientKernelThroughLevelFamily 0) = {fun n => (Nat.totient n : ℚ)} ∧
      Module.finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_entries`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L33)

```lean
theorem canonicalTotientKernelFamily_entries (e : ℕ) :
    canonicalTotientKernelFamily e (Sum.inl 0) = (fun n => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily e (Sum.inl 1)
        = (fun n => (Nat.totient (2 * n) : ℚ)) ∧
      ∀ (j : Fin e) (r : Fin (2 ^ j.val)),
        canonicalTotientKernelFamily e (Sum.inr ⟨j, r⟩)
          = fun n => (Nat.totient (2 ^ (j.val + 1) * n + (2 * r.val + 1)) : ℚ)
```

<a id="thm-rationality-carry-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `retainedSections_basis_and_rank` | [E249_25/Challenge.lean, line 275](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L275) | [PaperStatementsBB.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsBB.lean#L71) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `completeLevelZeroTruncation_is_totient_and_rank_one` | [E249_25/Challenge.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L269) | [PaperStatementsBB.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsBB.lean#L59) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `canonicalTotientKernelFamily_entries` | [E249_25/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L260) | [PaperStatementsBB.lean, line 24](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsBB.lean#L24) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-rationality-carry-rank-2"></a>

## Theorem

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.rationalValue_integral_carry_and_rank_floor`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L129)

```lean
theorem rationalValue_integral_carry_and_rank_floor
    {v : ℕ} (hv : 0 < v) {p : ℤ}
    (hvS : (v : ℝ) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (p : ℝ)) :
    ∃ u : ℕ → ℤ,
      (∀ N : ℕ, (u N : ℝ) = (v : ℝ) * totientTail N) ∧
      (∀ N : ℕ, u (N + 1) = 2 * u N - (v : ℤ) * (Nat.totient (N + 1) : ℤ)) ∧
      (∀ N : ℕ, 0 ≤ u N ∧ u N ≤ (v : ℤ) * ((N : ℤ) + 2)) ∧
      (∀ e : ℕ, 2 ^ e - 1 ≤
        Module.finrank ℚ
          (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))))
```

<a id="thm-rationality-carry-rank-2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rationalValue_integral_carry_and_rank_floor` | [E249_26/Challenge.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L49) | [PaperStatementsBJ.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsBJ.lean#L20) | [E249_26](../evidence/comparator/replay-35882032091/receipt-E249_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-additional-hypothesis-totient-specific-rank"></a>

## Proposition

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.rationalControl_periodic_with_unbounded_carry_rank`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L238)

```lean
theorem rationalControl_periodic_with_unbounded_carry_rank :
    ∃ c : ℕ → ℕ, (∀ n, c n ≤ n) ∧ binaryCoeffSeries c = 5 / 4 ∧
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
        IsTemperedBinaryOrbit c v u ∧
          CarrySectionsEventuallyPeriodicMod v 2 2 u ∧
          ∀ e : ℕ, 2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.rationality_gives_mod_period_and_unbounded_rank`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L256)

```lean
theorem rationality_gives_mod_period_and_unbounded_rank
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ, 2 ^ e - 1 ≤
          Module.finrank ℚ
            (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u
```

<a id="prop-additional-hypothesis-totient-specific-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rationalControl_periodic_with_unbounded_carry_rank` | [E249_26/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L81) | [PaperStatementsBH.lean, line 38](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsBH.lean#L38) | [E249_26](../evidence/comparator/replay-35882032091/receipt-E249_26.json) |
| `rationality_gives_mod_period_and_unbounded_rank` | [E249_26/Challenge.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L91) | [PaperStatementsBH.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsBH.lean#L57) | [E249_26](../evidence/comparator/replay-35882032091/receipt-E249_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-rational-series-preserving-totient-parity"></a>

## Proposition

The Lean declarations below together state this result.

1. [`Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_six`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L227)

```lean
theorem parityCoboundaryWeight_le_six (n : ℕ) :
    parityCoboundaryWeight n ≤ 6
```

2. [`Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_self`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L155)

```lean
theorem parityCoboundaryWeight_le_self (n : ℕ) :
    parityCoboundaryWeight n ≤ n
```

3. [`Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_mod_two_eq_totient`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L194)

```lean
theorem parityCoboundaryWeight_mod_two_eq_totient (n : ℕ) :
    parityCoboundaryWeight n % 2 = Nat.totient n % 2
```

4. [`Erdos249257.TotientParityCoboundaryCountermodel.exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L457)

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

5. [`Erdos249257.TotientParityCoboundaryCountermodel.tsum_parityCoboundaryWeight_eq_three_halves`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L359)

```lean
theorem tsum_parityCoboundaryWeight_eq_three_halves :
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) = 3 / 2
```

<a id="prop-rational-series-preserving-totient-parity-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `parityCoboundaryWeight_le_six` | [E249_26/Challenge.lean, line 138](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L138) | [PaperStatementsAG.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L42) | [E249_26](../evidence/comparator/replay-35882032091/receipt-E249_26.json) |
| `parityCoboundaryWeight_le_self` | [E249_26/Challenge.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L134) | [PaperStatementsAG.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L39) | [E249_26](../evidence/comparator/replay-35882032091/receipt-E249_26.json) |
| `parityCoboundaryWeight_mod_two_eq_totient` | [E249_26/Challenge.lean, line 142](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L142) | [PaperStatementsAG.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L45) | [E249_26](../evidence/comparator/replay-35882032091/receipt-E249_26.json) |
| `exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs` | [E249_26/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L124) | [PaperStatementsAG.lean, line 16](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAG.lean#L16) | [E249_26](../evidence/comparator/replay-35882032091/receipt-E249_26.json) |
| `tsum_parityCoboundaryWeight_eq_three_halves` | [E249_02/Challenge.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_02/Challenge.lean#L65) | [PaperStatementsAG.lean, line 48](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_02/PaperStatementsAG.lean#L48) | [E249_02](../evidence/comparator/replay-35882032091/receipt-E249_02.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-complement-divisibility-after-multiplication"></a>

## Lemma

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.complementDenominator_dvd_scalar`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ScalarLocalisationAndInversePhaseGauge.lean#L29)

```lean
theorem complementDenominator_dvd_scalar
    (x : ℚ) (c : ℤ) {H : ℕ} (_hHpos : 0 < H) (hH : H ∣ x.den)
    (hscaled : ((c : ℚ) * x).den ∣ H) :
    ((x.den / H : ℕ) : ℤ) ∣ c
```

<a id="lem-complement-divisibility-after-multiplication-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `complementDenominator_dvd_scalar` | [E249_26/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L149) | [PaperStatementsAJ.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAJ.lean#L168) | [E249_26](../evidence/comparator/replay-35882032091/receipt-E249_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-nonvanishing-unique-largest-denominator-exponent"></a>

## Lemma

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_clearing`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/SignedDyadicClearing.lean#L8)

```lean
theorem signed_dyadic_clearing {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α)
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (2 : ℚ) ^ e m * (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) =
      ((∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i) : ℤ) : ℚ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_sum_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/SignedDyadicClearing.lean#L28)

```lean
theorem signed_dyadic_sum_ne_zero {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) ≠ 0
```

3. [`Erdos249257.SignedQMomentObstruction.scaled_dyadic_sum_odd`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/Erdos249257/SignedQMomentObstruction.lean#L78)

```lean
theorem scaled_dyadic_sum_odd {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i)) % 2 = 1
```

<a id="lem-nonvanishing-unique-largest-denominator-exponent-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `signed_dyadic_clearing` | [E249_05/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L117) | [PaperStatementsAE.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L145) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `signed_dyadic_sum_ne_zero` | [E249_05/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L124) | [PaperStatementsAE.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L152) | [E249_05](../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `scaled_dyadic_sum_odd` | [E249_06/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L81) | [PaperStatementsAF.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAF.lean#L30) | [E249_06](../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-nonzero-minor-survives-inverse-phase"></a>

## Proposition

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.inversePhaseGauge_locks_row_and_preserves_minor`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ScalarLocalisationAndInversePhaseGauge.lean#L51)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `inversePhaseGauge_locks_row_and_preserves_minor` | [E249_26/Challenge.lean, line 164](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L164) | [PaperStatementsAY.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsAY.lean#L94) | [E249_26](../evidence/comparator/replay-35882032091/receipt-E249_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-tail-integrality-lcm-grid"></a>

## Proposition

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L8)

```lean
theorem lcm_grid_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail ((q + m) * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ)
```

<a id="prop-tail-integrality-lcm-grid-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lcm_grid_flatness` | [E249_09/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L209) | [PaperStatementsAT.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L199) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-grid-certificate-gives-nonintegral"></a>

## Proposition

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L12)

```lean
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L36)

```lean
theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="prop-finite-grid-certificate-gives-nonintegral-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paperGridNumerator_eq` | [E249_09/Challenge.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L287) | [PaperStatementsAX.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L238) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_grid_nonintegral_pair` | [E249_09/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L272) | [PaperStatementsAX.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L223) | [E249_09](../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-exact-dyadic-rank-infinite-dimensionality"></a>

## Theorem

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_entries`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L33)

```lean
theorem canonicalTotientKernelFamily_entries (e : ℕ) :
    canonicalTotientKernelFamily e (Sum.inl 0) = (fun n => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily e (Sum.inl 1)
        = (fun n => (Nat.totient (2 * n) : ℚ)) ∧
      ∀ (j : Fin e) (r : Fin (2 ^ j.val)),
        canonicalTotientKernelFamily e (Sum.inr ⟨j, r⟩)
          = fun n => (Nat.totient (2 ^ (j.val + 1) * n + (2 * r.val + 1)) : ℚ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.canonicalTotientKernelFamily_independent_card_and_span`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicSectionBasisAndRationalCarry.lean#L53)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `canonicalTotientKernelFamily_entries` | [E249_25/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_25/Challenge.lean#L260) | [PaperStatementsBB.lean, line 24](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_25/PaperStatementsBB.lean#L24) | [E249_25](../evidence/comparator/replay-35882032091/receipt-E249_25.json) |
| `canonicalTotientKernelFamily_independent_card_and_span` | [E249_26/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_26/Challenge.lean#L205) | [PaperStatementsBB.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_26/PaperStatementsBB.lean#L27) | [E249_26](../evidence/comparator/replay-35882032091/receipt-E249_26.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-orbit"></a>

## Lemma (The doubling identity)

> *For all $`N\ge 0`$ and $`h\ge 1`$,
> ``` math
> R_{N+1}=2R_N-\varphi(N+1),
>   \qquad
>   R_{N+h}-R_N \;=\; 2^N\alpha_h-\bigl(\Phi_{N+h}-\Phi_N\bigr),
> ```
> so $`R_{N+h}-R_N \equiv 2^N\alpha_h \pmod 1`$, and consequently the exact first character of the tail difference is the $`\times 2`$ orbit of one real number:
> ``` math
> e(R_{N+h}-R_N)
>   \;=\; e\bigl(2^N\alpha_h\bigr),
>   \qquad e(x):=\exp(2\pi i x).
> ```
> Hence, for fixed $`h`$, the phases $`\{\,R_{N+h}-R_N \bmod 1\,\}_{N\ge 0}`$ are the forward orbit of $`\alpha_h \bmod 1`$ under $`x\mapsto 2x`$.*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_recurrence`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L26)

```lean
theorem orbit_tail_recurrence (N : ℕ) :
    totientTail (N + 1) = 2 * totientTail N - (Nat.totient (N + 1) : ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L32)

```lean
theorem orbit_tail_diff_eq (h N : ℕ) :
    totientTail (N + h) - totientTail N
      = (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        - ((totientPrefix (N + h) : ℝ) - (totientPrefix N : ℝ))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_sub_scaled_is_int`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L41)

```lean
theorem orbit_tail_diff_sub_scaled_is_int (h N : ℕ) :
    ∃ z : ℤ,
      totientTail (N + h) - totientTail N
          - (2 : ℝ) ^ N * (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
        = (z : ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_firstChar_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L53)

```lean
theorem orbit_tail_diff_firstChar_eq (h N : ℕ) :
    Complex.exp
        (((2 * Real.pi * (totientTail (N + h) - totientTail N) : ℝ) : ℂ) * Complex.I)
      = Complex.exp
        (((2 * Real.pi *
            ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
              (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) : ℝ) : ℂ) * Complex.I)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.orbit_tail_diff_fract_eq_doubling_orbit`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L75)

```lean
theorem orbit_tail_diff_fract_eq_doubling_orbit (h N : ℕ) :
    Int.fract (totientTail (N + h) - totientTail N)
      = Int.fract
          ((fun x : ℝ => 2 * x)^[N]
            (((2 : ℝ) ^ h - 1) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)))
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.doublingMap_iterate_apply`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L64)

```lean
theorem doublingMap_iterate_apply (α : ℝ) (N : ℕ) :
    (fun x : ℝ => 2 * x)^[N] α = 2 ^ N * α
```

<a id="lem-orbit-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `orbit_tail_recurrence` | [E249_27/Challenge.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L87) | [PaperStatementsAU.lean, line 299](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAU.lean#L299) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `orbit_tail_diff_eq` | [E249_27/Challenge.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L58) | [PaperStatementsAU.lean, line 274](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAU.lean#L274) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `orbit_tail_diff_sub_scaled_is_int` | [E249_27/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L80) | [PaperStatementsAU.lean, line 293](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAU.lean#L293) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `orbit_tail_diff_firstChar_eq` | [E249_27/Challenge.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L64) | [PaperStatementsAU.lean, line 279](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAU.lean#L279) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `orbit_tail_diff_fract_eq_doubling_orbit` | [E249_27/Challenge.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L73) | [PaperStatementsAU.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAU.lean#L287) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `doublingMap_iterate_apply` | [E249_27/Challenge.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L36) | [PaperStatementsAJ.lean, line 271](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAJ.lean#L271) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-transfer"></a>

## Proposition (Transfer to the doubling orbit)

> *Suppose that
> ``` math
> \forall h\ge 1\ \forall X_0\ \exists X\ge \max(X_0,1):\quad
>   \sum_{N=X}^{2X-1}\cos\bigl(2\pi\,2^{N}\alpha_h\bigr)\;\le\;\tfrac{89}{100}\,X .
> ```
> This hypothesis implies that $`S`$ is irrational.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_block_cosine_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L92)

```lean
theorem irrational_totientSeries_of_block_cosine_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi *
            ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
              (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))))
        ≤ (89 / 100 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="prop-transfer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totientSeries_of_block_cosine_gap` | [E249_27/Challenge.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L40) | [PaperStatementsAJ.lean, line 412](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAJ.lean#L412) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-digitform"></a>

## Corollary (A digit version of the analytic condition)

> *Let $`\rho_h(X)`$ denote the proportion of $`N\in[X,2X)`$ with $`\|2^N\alpha_h\|_{\mathbb{R}/\mathbb{Z}}\ge 1/4`$. If for every $`h\ge 1`$ there are cofinally many $`X`$ with $`\rho_h(X)\ge 11/100`$, then $`S`$ is irrational. For nondyadic $`\alpha_h`$, the condition counted by $`\rho_h(X)`$ is exactly a change between binary digits $`N+1`$ and $`N+2`$. Thus the same sufficient hypothesis asks for at least $`11X/100`$ such changes, counted with $`X\le N<2X`$, on arbitrarily large blocks for every $`h`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_proportion`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L121)

```lean
theorem irrational_totientSeries_of_quarterFarPhase_proportion
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) ≤ quarterFarPhaseProportion h X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.quarterFarFromInt_iff_binaryDigitAt_change`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L146)

```lean
theorem quarterFarFromInt_iff_binaryDigitAt_change {α : ℝ} (hnd : NotDyadicRational α) (N : ℕ) :
    QuarterFarFromInt ((2 : ℝ) ^ N * α) ↔ binaryDigitAt α (N + 1) ≠ binaryDigitAt α (N + 2)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_digitChange_count`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L233)

```lean
theorem irrational_totientSeries_of_digitChange_count
    (hnd : ∀ h : ℕ, 1 ≤ h → NotDyadicRational (totientAlphaShift h))
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤
        ((((Finset.Ico X (2 * X)).filter
            fun N => binaryDigitAt (totientAlphaShift h) (N + 1)
              ≠ binaryDigitAt (totientAlphaShift h) (N + 2)).card : ℕ) : ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_quarterFarPhase_count`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L95)

```lean
theorem irrational_totientSeries_of_quarterFarPhase_count
    (hdense : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (11 / 100 : ℝ) * X ≤ (quarterFarPhaseCount h X : ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.quarterFarFromInt_iff_floor_bounds`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L45)

```lean
theorem quarterFarFromInt_iff_floor_bounds (x : ℝ) :
    QuarterFarFromInt x ↔ (1 / 4 : ℝ) ≤ x - (⌊x⌋ : ℝ) ∧ x - (⌊x⌋ : ℝ) ≤ 3 / 4
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.cos_nonpos_of_quarterFarFromInt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L70)

```lean
theorem cos_nonpos_of_quarterFarFromInt {x : ℝ} (hx : QuarterFarFromInt x) :
    Real.cos (2 * Real.pi * x) ≤ 0
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.tailOrbitFirstExp_re_eq`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/BinaryDigitChangeDensity.lean#L81)

```lean
theorem tailOrbitFirstExp_re_eq (h N : ℕ) :
    (tailOrbitFirstExp h N).re = Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * totientAlphaShift h))
```

<a id="cor-digitform-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_totientSeries_of_quarterFarPhase_proportion` | [E249_27/Challenge.lean, line 127](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L127) | [PaperStatementsAM.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L34) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `quarterFarFromInt_iff_binaryDigitAt_change` | [E249_27/Challenge.lean, line 133](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L133) | [PaperStatementsAM.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L39) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `irrational_totientSeries_of_digitChange_count` | [E249_27/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L111) | [PaperStatementsAM.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L20) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `irrational_totientSeries_of_quarterFarPhase_count` | [E249_27/Challenge.lean, line 121](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L121) | [PaperStatementsAM.lean, line 29](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L29) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `quarterFarFromInt_iff_floor_bounds` | [E249_27/Challenge.lean, line 137](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L137) | [PaperStatementsAM.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L43) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `cos_nonpos_of_quarterFarFromInt` | [E249_27/Challenge.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L107) | [PaperStatementsAM.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAM.lean#L17) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `tailOrbitFirstExp_re_eq` | [E249_27/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L152) | [PaperStatementsBL.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsBL.lean#L20) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-lacunary"></a>

## Theorem (The block norm condition is stronger in the class $`0\le c(n)\le n`$)

> *Let $`c(n)=1`$ if $`n=k!`$ for some $`k\ge 1`$ and $`c(n)=0`$ otherwise, so $`0\le c(n)\le n`$ for all $`n\ge 1`$, and let $`\beta=\sum_{n\ge1}c(n)/2^{n}
> =\sum_{k\ge 1}2^{-k!}`$. Then $`\beta`$ is irrational, and for every $`h\ge 1`$ and every $`X\ge 81(h+5)`$,
> ``` math
> \sum_{N=X}^{2X-1}\cos\bigl(2\pi\,2^{N}(2^{h}-1)\beta\bigr) \;>\; \tfrac{9}{10}X .
> ```
> Consequently the block norm condition fails for $`\beta`$ at every sufficiently large scale, for every admissible truncation depth, even though $`\beta`$ is irrational. Thus irrationality, nonnegative integer coefficients and the bound $`c(n)\le n`$ do not imply the block gap. A proof for $`S`$ needs an additional property not shared by this example; the comparison does not specify which additional property will suffice.*

The Lean declarations below together state a result at least as strong as this one.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.lacCoef_bounds`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L68)

```lean
theorem lacCoef_bounds {n : ℕ} (hn : 1 ≤ n) : 0 ≤ lacCoef n ∧ lacCoef n ≤ (n : ℤ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.lacBeta_eq_factorial_series`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L88)

```lean
theorem lacBeta_eq_factorial_series : lacBeta = ∑' k : ℕ, (1 : ℝ) / 2 ^ ((k + 1)!)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_lacBeta`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L121)

```lean
theorem irrational_lacBeta : Irrational lacBeta
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_cos_gap`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L333)

```lean
theorem lacunary_block_cos_gap {h X : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X) :
    (9 / 10 : ℝ) * X
      < ∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi * ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) * lacBeta))
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.lacunary_block_norm_fails`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L587)

```lean
theorem lacunary_block_norm_fails {h X L : ℕ} (hh : 1 ≤ h) (hX : 81 * (h + 5) ≤ X)
    (hroom : 16 * (2 * X + h + L + 2) ≤ 2 ^ L) :
    (21 / 25 : ℝ) * X < ‖∑ N ∈ Finset.Ico X (2 * X), lacFirstExp h N L‖
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.cos_pi_div_eight_gt`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/LacunaryFactorialBlockNorm.lean#L317)

```lean
theorem cos_pi_div_eight_gt : (9238 / 10000 : ℝ) < Real.cos (Real.pi / 8)
```

<a id="thm-lacunary-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `lacCoef_bounds` | [E249_27/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L184) | [PaperStatementsAN.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L23) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `lacBeta_eq_factorial_series` | [E249_27/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L181) | [PaperStatementsAN.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L21) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `irrational_lacBeta` | [E249_27/Challenge.lean, line 178](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L178) | [PaperStatementsAN.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L19) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `lacunary_block_cos_gap` | [E249_27/Challenge.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L187) | [PaperStatementsAN.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L25) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `lacunary_block_norm_fails` | [E249_27/Challenge.lean, line 193](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L193) | [PaperStatementsAN.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L30) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |
| `cos_pi_div_eight_gt` | [E249_27/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_27/Challenge.lean#L175) | [PaperStatementsAN.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_27/PaperStatementsAN.lean#L17) | [E249_27](../evidence/comparator/replay-35882032091/receipt-E249_27.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-dickman"></a>

## Proposition (A one-sided bound for the unassigned terms)

> *Fix $`h,s`$ and choose the admissible depth $`L`$ minimally for each large $`X`$. Put $`t=L-s+1=O_{h,s}(\log X)`$ and $`y_X=4\sqrt X+2t/\sqrt X`$. If $`n=N+t`$ is unassigned, then its largest prime factor satisfies $`P(n)\le y_X`$. Consequently
> ``` math
> \begin{aligned}
>  \#\{N\in[X,2X):N\notin\mathcal A\}
>  &\le \Psi(2X+t-1,y_X)-\Psi(X+t-1,y_X)\\
>  &=\bigl(1-\log2+o(1)\bigr)X<\tfrac8{25}X
> \end{aligned}
> ```
> for all sufficiently large $`X`$. Here $`\Psi(x,y)`$ counts the positive integers at most $`x`$ whose prime factors are all at most $`y`$. This is an upper bound for the unassigned count, not an asymptotic equality for that count.*

The Lean declaration below states a result at least as strong as this one.

[`ErdosProblems.Erdos249.PaperCompleteR21.prop_dickman`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/UnassignedSmoothCount.lean#L556)

```lean
theorem prop_dickman (h s : ℕ) :
    (∀ X, AdmissibleDepth h s X (minimalDepth h s X) ∧
        ∀ L, AdmissibleDepth h s X L → minimalDepth h s X ≤ L) ∧
    (∀ X, minimalOffset h s X ≤ h + Nat.log 2 X + 11) ∧
    (∀ X N, 0 < X → N ∈ Ico X (2 * X) → N ∉ pivotSupplierBases X (minimalDepth h s X) s →
      ∀ hn : 1 < N + minimalOffset h s X,
        (((N + minimalOffset h s X).primeFactors.max'
            (Nat.nonempty_primeFactors.mpr hn) : ℕ) : ℝ) ≤ minimalCut h s X) ∧
    (∀ X, 0 < X →
      ((((Ico X (2 * X)).filter
          (fun N => N ∉ pivotSupplierBases X (minimalDepth h s X) s)).card : ℕ) : ℝ)
        ≤ (smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) ∧
    Tendsto (fun X : ℕ =>
        ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) / X)
      atTop (𝓝 (1 - Real.log 2)) ∧
    (∀ᶠ X : ℕ in atTop,
      ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) < 8 / 25 * X ∧
      ((((Ico X (2 * X)).filter
          (fun N => N ∉ pivotSupplierBases X (minimalDepth h s X) s)).card : ℕ) : ℝ)
        < 8 / 25 * X)
```

<a id="prop-dickman-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `prop_dickman` | [E249_28/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_28/Challenge.lean#L96) | [PaperStructuresQ.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_28/PaperStructuresQ.lean#L20) | [E249_28](../evidence/comparator/replay-35882032091/receipt-E249_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-badcof"></a>

## Proposition (The excluded-cofactor estimate)

> *Fix $`h,s`$ and use the minimal admissible depth $`L`$, as in Proposition <a href="#prop:dickman" data-reference-type="ref" data-reference="prop:dickman">276</a>; thus $`t=L-s+1=O_{h,s}(\log X)`$. For $`\eta\in(0,1)`$ let $`B(\eta)=\{m\ge1:\varphi(m)<\eta m\}`$, with natural density $`D(\eta)`$; by Schoenberg’s theorem $`D`$ exists, is continuous, and $`D(0+)=0`$ \[schoenberg1928, §17, p. 193\], in the framework of \[schoenberg1936, Theorem 1, pp. 318–319, and §8, p. 323\] <span class="sans-serif">\[Cited\]</span>. Then
> ``` math
> \#\{N\in\mathcal A:m_N\in B(\eta)\}
>   \;\le\;\bigl(D(\eta)+o(1)\bigr)X ,
> ```
> so a single choice of $`\eta`$ with $`D(\eta)<1/200`$ meets the $`\tfrac{1}{100}X`$ budget for all large $`X`$. This choice fixes $`\eta`$ before $`X_0`$, as required. It supplies only the excluded-cofactor bound: the mean and mean-subtracted estimates must still hold for this same $`\eta`$, and do not follow from making $`\eta`$ smaller.*

The Lean proof assumes the prime number theorem, stated in Lean as `ErdosProblems.Erdos251.PaperR11.PrimeSource.PrimeNumberTheorem`; that input is not proved in Lean.

[`ErdosProblems.Erdos249.PaperCompleteR21.prop_badcof`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExcludedCofactorEstimate.lean#L654)

```lean
theorem prop_badcof (hPNT : ErdosProblems.Erdos251.PaperR11.PrimeSource.PrimeNumberTheorem)
    (h s : ℕ) (η D : ℝ) (hD : HasNaturalDensity (excludedCofactorSet η) D) :
    (∀ X : ℕ, minimalOffset h s X ≤ h + Nat.log 2 X + 11) ∧
    (∀ X : ℕ, (pivotSupplierBases X (minimalDepth h s X) s).filter
        (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)
      = pivotBadBases X (minimalDepth h s X) s η) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        ≤ (D + ε) * X) ∧
    (D < 1 / 200 → ∀ᶠ X : ℕ in atTop,
      ((((pivotSupplierBases X (minimalDepth h s X) s).filter
          (fun N => pivotCofactor N (minimalDepth h s X) s ∈ excludedCofactorSet η)).card
            : ℕ) : ℝ)
        < (1 / 100 : ℝ) * X ∧
      ‖pivotBadContribution h X (minimalDepth h s X) s η‖ ≤ (1 / 100 : ℝ) * X)
```

<a id="prop-badcof-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="prop-route4"></a>

## Proposition

> *$`\mathcal{C}(h,N,h)`$ holds whenever $`\bigl\|2^{N+h}S-2^{N}S\bigr\|_{\mathbb{R}/\mathbb{Z}}>2(N+2h+2)/2^{h}`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_of_fullDepth_phase_separation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L130)

```lean
theorem certifiedKill_of_fullDepth_phase_separation (h N : ℕ)
    (hsep : ∀ k : ℤ,
      2 * ((N : ℝ) + 2 * h + 2) / 2 ^ h <
        |(2 : ℝ) ^ (N + h) * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
            - (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - (k : ℝ)|) :
    certifiedKill h N h
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.bracket_of_two_sided_separation`](https://github.com/wcook04/plectis-erdos/blob/e6c2d8f77ac24753c5216a49f4daf7f7388b309f/lean/ErdosProblems/Erdos249/PaperCompleteR21/DoublingOrbitTransferAndFullDepthPhase.lean#L119)

```lean
theorem bracket_of_two_sided_separation
    {c P m δ : ℝ} (_hc : 0 < c) (_hm0 : 0 ≤ m) (_hmP : m < P)
    (hδ : |δ| < c) (h1 : 2 * c < |m + δ|) (h2 : 2 * c < |m + δ - P|) :
    c < m ∧ m < P - c
```

<a id="prop-route4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `certifiedKill_of_fullDepth_phase_separation` | [E249_28/Challenge.lean, line 142](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_28/Challenge.lean#L142) | [PaperStatementsAT.lean, line 343](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_28/PaperStatementsAT.lean#L343) | [E249_28](../evidence/comparator/replay-35882032091/receipt-E249_28.json) |
| `bracket_of_two_sided_separation` | [E249_28/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_28/Challenge.lean#L124) | [PaperStatementsAJ.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_28/PaperStatementsAJ.lean#L157) | [E249_28](../evidence/comparator/replay-35882032091/receipt-E249_28.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
