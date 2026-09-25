# Formal evidence: The Binary Totient Series, Section 1

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="thm-denom"></a>

## Theorem 1.3 (Denominator exclusion from a fixed Farey window), page 5

> *If $`S \in \mathbb{Q}`$ then its reduced denominator exceeds $`Q_0 := 79\,639\,646\,646\,701\,375\,323\,355\,774\,875\,831\,053 \approx 7.96 \times 10^{34}`$. Equivalently, $`S`$ differs from every rational number whose reduced denominator is at most $`Q_0`$. The bound is sharp for this window: $`q = Q_0 + 1`$ is the exact first failing denominator. It is the denominator of the mediant of two explicit unimodular Farey neighbours.*

The Lean declarations below together state this result.

1. [`Erdos249257.tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CertificateKernel.lean#L18384)

```lean
theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ)
```

2. [`GapFareyBound.gap_check_window_1_240_first_failure`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GapFareyBound.lean#L225)

```lean
theorem gap_check_window_1_240_first_failure :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054
```

where [`IsFirstGapFailure`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/GapFareyBound.lean#L44) is

```lean
def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)
```

<a id="thm-denom-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L44) (E249_01, line 44), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAI.lean#L57) (PaperStatementsAI.lean, line 57), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `gap_check_window_1_240_first_failure`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L56) (E249_01, line 56), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAK.lean#L118) (PaperStatementsAK.lean, line 118), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-deposits"></a>

## Proposition 1.4 (Finite certificate computations), page 5

> *$`\mathcal{C}`$ has been verified at: the $`28`$ diagonal instances of the least-common-multiple diagonal through $`t = 64`$; all shifts $`h \in [1,16]`$ simultaneously at $`(N,L) = (14,9)`$, by `decide`; and eight further period examples at $`N = 300`$. These are historical subsets of the examples. The supplied source also proves a complete diagonal band for $`1\le t\le82`$, with no omitted scales. This is bounded coverage, not a cofinal diagonal family. Note the quantifier order: the simultaneous small-shift example uses one pair $`N,L`$ for every $`1\le h\le16`$. In symbols, it proves $`\exists N\,\exists L\,\forall h\,(1\le h\le16\Rightarrow\mathcal C(h,N,L))`$. In contrast, $`\mathrm{Sep}`$ requires arbitrarily large $`N`$ for each positive $`h`$; neither the shift range nor the basepoint threshold is bounded.*

The Lean declarations below together state this result.

1. [`Erdos249257.TotientTailPeriodKiller.certifiedKill_diagonal_all_imported_through_t64`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/DiagonalPincerCertificatesT64.lean#L1967)

```lean
theorem certifiedKill_diagonal_all_imported_through_t64 :
    ∀ t ∈ diagonalPincerCertificateScalesThroughT64,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepthThroughT64 t)
```

2. [`Erdos249257.TotientTailPeriodKiller.certifiedKill_diagonal_t64`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/DiagonalPincerCertificatesT64.lean#L1928)

```lean
theorem certifiedKill_diagonal_t64 :
    certifiedKill (periodLcm 64) (periodLcm 64) 93
```

3. [`Erdos249257.TotientTailPeriodKiller.certifiedKill_all_upto_sixteen`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CarrySurvivorExtinction.lean#L574)

```lean
theorem certifiedKill_all_upto_sixteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9
```

4. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_67_300`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L471)

```lean
theorem certifiedKill_67_300 : certifiedKill 67 300 11
```

where [`certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientTailPeriodKiller.lean#L72) is

```lean
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
```

5. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_81_300`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L474)

```lean
theorem certifiedKill_81_300 : certifiedKill 81 300 13
```

where [`certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientTailPeriodKiller.lean#L72) is

```lean
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
```

6. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_97_300`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L477)

```lean
theorem certifiedKill_97_300 : certifiedKill 97 300 13
```

where [`certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientTailPeriodKiller.lean#L72) is

```lean
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
```

7. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_101_300`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L480)

```lean
theorem certifiedKill_101_300 : certifiedKill 101 300 11
```

where [`certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientTailPeriodKiller.lean#L72) is

```lean
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
```

8. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_121_300`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L483)

```lean
theorem certifiedKill_121_300 : certifiedKill 121 300 10
```

where [`certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientTailPeriodKiller.lean#L72) is

```lean
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
```

9. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_125_300`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L486)

```lean
theorem certifiedKill_125_300 : certifiedKill 125 300 18
```

where [`certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientTailPeriodKiller.lean#L72) is

```lean
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
```

10. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_127_300`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L490)

```lean
theorem certifiedKill_127_300 : certifiedKill 127 300 11
```

where [`certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientTailPeriodKiller.lean#L72) is

```lean
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
```

11. [`ErdosProblems.Erdos249.PeriodMultipleEscape.certifiedKill_128_300`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L493)

```lean
theorem certifiedKill_128_300 : certifiedKill 128 300 11
```

where [`certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientTailPeriodKiller.lean#L72) is

```lean
def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
```

12. [`ErdosProblems.Skip.LadderT67.exists_diagonalKill_le_82`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Skip/LadderT67.lean#L71264)

```lean
theorem exists_diagonalKill_le_82 (t : ℕ) (ht : t ≤ 82) :
    ∃ L, certifiedKill (periodLcm t) (periodLcm t) L
```

<a id="prop-deposits-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `certifiedKill_diagonal_all_imported_through_t64`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L153) (E249_01, line 153), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAT.lean#L122) (PaperStatementsAT.lean, line 122), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `certifiedKill_diagonal_t64`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L210) (E249_01, line 210), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStructuresN.lean#L42) (PaperStructuresN.lean, line 42), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `certifiedKill_all_upto_sixteen`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L91) (E249_01, line 91), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAD.lean#L27) (PaperStatementsAD.lean, line 27), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `certifiedKill_67_300`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L187) (E249_01, line 187), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L589) (PaperStatementsAU.lean, line 589), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `certifiedKill_81_300`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L190) (E249_01, line 190), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L591) (PaperStatementsAU.lean, line 591), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `certifiedKill_97_300`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L193) (E249_01, line 193), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L593) (PaperStatementsAU.lean, line 593), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `certifiedKill_101_300`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L172) (E249_01, line 172), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L579) (PaperStatementsAU.lean, line 579), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `certifiedKill_121_300`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L175) (E249_01, line 175), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L581) (PaperStatementsAU.lean, line 581), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `certifiedKill_125_300`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L178) (E249_01, line 178), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L583) (PaperStatementsAU.lean, line 583), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `certifiedKill_127_300`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L181) (E249_01, line 181), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L585) (PaperStatementsAU.lean, line 585), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `certifiedKill_128_300`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L184) (E249_01, line 184), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L587) (PaperStatementsAU.lean, line 587), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `exists_diagonalKill_le_82`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L201) (E249_01, line 201), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L599) (PaperStatementsAU.lean, line 599), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sign"></a>

## Proposition 1.5 (Positivity does not exclude an integer), page 5

> *Put $`H_a=\operatorname{lcm}(1,\ldots,2^a)`$. For every $`a\ge8`$ and $`J\ge0`$ with $`J+(a+6)<2\cdot2^a`$,
> ``` math
> R_{2H_a+J}-R_{H_a+J}>0.
> ```
> This needs no irrationality hypothesis. If this difference is an integer and $`K\ge0`$ satisfies
> ``` math
> J+K+(a+6)<2\cdot2^a,\qquad 2H_a+J+K+2<2^K,
> ```
> then
> ``` math
> D(H_a,H_a+J,K)\bmod2^K
>    =2^K-\bigl(R_{2H_a+J+K}-R_{H_a+J+K}\bigr)
> ```
> lies strictly between $`2^K-(2H_a+J+K+2)`$ and $`2^K`$. The later tail difference is a positive integer. Its negative, not the carry itself, is the representative near zero. Thus positivity locates the residue near the upper endpoint; it does not establish the central-residue inequalities. Both restrictions on $`K`$ are part of this conclusion.*

The Lean declarations below together state this result.

1. [`Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailDiff_shift_pos`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientActualLcmOrbitSign.lean#L39)

```lean
theorem actualLcmTailDiff_shift_pos
    {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 <
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J)
```

2. [`Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcm_integral_forces_topEdgeResidue`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientActualLcmOrbitSign.lean#L211)

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
    let H := periodLcm (2 ^ a)
    let e := carryOrbit H (H + J) d K
    let P := (2 : ℤ) ^ K
    let B := ((2 * H + J + K + 2 : ℕ) : ℤ)
    windowDiscrepancy H (H + J) K % P = P - e ∧
      P - B < windowDiscrepancy H (H + J) K % P ∧
      windowDiscrepancy H (H + J) K % P < P
```

3. [`Erdos249257.TotientTailPeriodKiller.carryOrbit_eq_tail_diff`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/CarrySurvivorExtinction.lean#L393)

```lean
lemma carryOrbit_eq_tail_diff {h N : ℕ} {d : ℤ}
    (hd : (d : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N d i : ℝ) = totientTail (N + i + h) - totientTail (N + i)
```

<a id="prop-sign-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `actualLcmTailDiff_shift_pos`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L228) (E249_01, line 228), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L21) (PaperStatementsA.lean, line 21), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `actualLcm_integral_forces_topEdgeResidue`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L236) (E249_01, line 236), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L30) (PaperStatementsA.lean, line 30), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `carryOrbit_eq_tail_diff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L255) (E249_01, line 255), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L50) (PaperStatementsA.lean, line 50), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-rank"></a>

## Proposition 1.6 (Rationality forces unbounded carry rank), page 6

> *If $`S`$ is rational then, for every $`e`$, the carry sections $`n\mapsto u_{2^jn+r}`$ with $`1\le j\le e`$ and $`0\le r<2^j`$ span a rational vector space of dimension at least $`2^{e}-1`$. The lower bound holds at every depth. It comes from the linear independence of the $`2^e+1`$ retained dyadic totient sections for $`e\ge1`$, proved using the Chinese remainder theorem and Dirichlet’s theorem, so the full family spans an infinite-dimensional space, the case $`k=2`$ of Coons’s non-regularity theorem (§10.8).*

The Lean declaration below states this result.

[`Erdos249257.not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientCarryKernelRigidity.lean#L300)

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

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_32/Challenge.lean#L94) (E249_32, line 94), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_32/CarryRankFrontier.lean#L44) (CarryRankFrontier.lean, line 44), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_32.json) (E249_32)

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

## Proposition 1.7 (Periodicity modulo an integer does not bound rational rank), page 6

> *If $`S`$ is rational, the same carry $`u`$ has unbounded rational section rank and one eventual period modulo $`v`$ valid for all its dyadic sections. More precisely, there are $`h\ge1`$ and $`N_0`$ such that, for every $`j,r\ge0`$ and $`n\ge N_0`$,
> ``` math
> u_{2^j(n+h)+r}\equiv u_{2^jn+r}\pmod v.
> ```
> The rank and periodicity assertions hold together. This conditional theorem alone is not a counterexample to a general periodicity-to-rank implication: its antecedent is not established. The separate $`5/4`$ control supplies a concrete counterexample to the generic rationality-driven rank ceiling; see the detailed comparison in Section 10.8.*

The Lean declaration below states this result.

[`Erdos249257.not_irrational_totientSeries_implies_mod_period_and_unbounded_rank`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientTailCarryPeriod.lean#L224)

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

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `not_irrational_totientSeries_implies_mod_period_and_unbounded_rank`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_32/Challenge.lean#L113) (E249_32, line 113), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_32/CarryRankFrontier.lean#L65) (CarryRankFrontier.lean, line 65), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_32.json) (E249_32)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-iffs"></a>

## Proposition 1.8 (Equivalent certificate conditions), page 6

> *Put $`H_t=\operatorname{lcm}(1,\ldots,t)`$. Several variations of Definition 1.2 are equivalent to $`S\notin\mathbb Q`$. One may allow a positive multiple of each prescribed shift, still requiring certificates beyond every basepoint threshold (Theorem 6.48). Alternatively, one may use the original quantified condition or restrict to $`h=N=H_t`$ at arbitrarily large $`t`$ (Theorem 6.49). Replacing the symmetric residue test by
> ``` math
> N+L+2\le D(h,N,L)\bmod2^L\le2^L-(N+h+L+2)
> ```
> also gives equivalent quantified conditions, including its restriction to $`h=N=H_t`$ at arbitrarily large $`t`$. Finally, the counted phase-separation condition in Proposition 2.7(b) is equivalent to irrationality. These equivalences change the form of the arithmetic question, not its logical strength.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PeriodMultipleEscape.periodMultipleKillSupply_iff_irrational`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/ErdosProblems/Erdos249/PeriodMultipleEscape.lean#L432)

```lean
theorem periodMultipleKillSupply_iff_irrational :
    PeriodMultipleKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/LcmConeFlatness.lean#L412)

```lean
theorem irrational_totient_series_iff_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ,
        ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L
```

3. [`Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_lcm_diagonal_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/LcmConeFlatness.lean#L426)

```lean
theorem irrational_totient_series_iff_lcm_diagonal_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
        certifiedKill (periodLcm t) (periodLcm t) L
```

4. [`Erdos249257.irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientTailCarryPeriod.lean#L875)

```lean
theorem irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      CofinalDirectedLcmCertificateSupply
```

5. [`Erdos249257.TotientTailPeriodKiller.dtwWindowSeparatedPairs_iff_irrational_totient_series`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/PivotAntiReconstruction.lean#L1765)

```lean
theorem dtwWindowSeparatedPairs_iff_irrational_totient_series :
    DTWWindowSeparatedPairs ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="prop-iffs-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `periodMultipleKillSupply_iff_irrational`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L196) (E249_01, line 196), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAU.lean#L595) (PaperStatementsAU.lean, line 595), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `irrational_totient_series_iff_certificate_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L100) (E249_01, line 100), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAD.lean#L46) (PaperStatementsAD.lean, line 46), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `irrational_totient_series_iff_lcm_diagonal_certificate_supply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L260) (E249_01, line 260), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsA.lean#L66) (PaperStatementsA.lean, line 66), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `irrational_totientSeries_iff_cofinalDirectedLcmCertificateSupply`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L158) (E249_01, line 158), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAT.lean#L128) (PaperStatementsAT.lean, line 128), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `dtwWindowSeparatedPairs_iff_irrational_totient_series`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L95) (E249_01, line 95), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAD.lean#L33) (PaperStatementsAD.lean, line 33), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-parity"></a>

## Proposition 1.9 (A rational sequence preserving size bounds, parity and aperiodicity), page 6

> *There is $`c : \mathbb{N}\to \mathbb{N}`$ with $`c(n) \le 6`$ and $`c(n) \le n`$ for all $`n`$, $`c(n) \equiv \varphi(n) \pmod 2`$ for *every* $`n`$, and $`c`$ not eventually periodic; indeed for every $`N, G, K`$ there are $`K`$ explicit carry pulses beyond $`N`$, pairwise separated by more than $`G`$; and yet $`\sum_n c(n)/2^{n} = 3/2 \in \mathbb{Q}`$.*

The Lean declarations below together state this result.

1. [`Erdos249257.TotientParityCoboundaryCountermodel.exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L637)

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

2. [`Erdos249257.TotientParityCoboundaryCountermodel.tsum_parityCoboundaryWeight_eq_three_halves`](https://github.com/wcook04/plectis-erdos/blob/be89e72217ec9c5f05aa5ec7b915c1ebf0816fdd/lean/Erdos249257/TotientParityCoboundaryCountermodel.lean#L359)

```lean
theorem tsum_parityCoboundaryWeight_eq_three_halves :
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) = 3 / 2
```

<a id="prop-parity-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L270) (E249_01, line 270), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAG.lean#L43) (PaperStatementsAG.lean, line 43), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)
- `tsum_parityCoboundaryWeight_eq_three_halves`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_02/Challenge.lean#L65) (E249_02, line 65), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_02/PaperStatementsAG.lean#L48) (PaperStatementsAG.lean, line 48), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_02.json) (E249_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
