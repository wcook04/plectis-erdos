# Formal evidence: Reciprocal Mersenne Subseries, Section 11

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="lem-odometer"></a>

## Lemma 11.2 (Divisor-residue form of the short-window phase), page 117

> *For all $`M,L\ge 1`$,
> ``` math
> \Theta_L(M)\ =\ \sum_{d\ge 2}\ \sum_{\substack{1\le i\le L\\ i\,\equiv\,-M\ (\mathrm{mod}\ d)}} 2^{-i}
> \ =\ \sum_{d\ge 2}\ 2^{-i_d(M)}\cdot\frac{1-2^{-d\,m_d}}{1-2^{-d}},
> ```
> where $`i_d(M)\in[1,d]`$ is the least $`i\ge1`$ with $`d\mid M+i`$ (so $`i_d(M)`$ depends only on $`M \bmod d`$), $`m_d := \#\{1\le i\le L: d\mid M+i\}`$, and terms with $`i_d(M)>L`$ are empty. In particular, for every integer $`D\ge M+L`$,
> ``` math
> \Theta_L(M)\ =\ \sum_{d=2}^{D}\ \sum_{i=1}^{L} 2^{-i}\,\mathbf 1_{d\mid M+i},
> ```
> and the right-hand side, with an arbitrary integer $`x\ge0`$ in place of $`M`$, depends on $`x`$ only through its residues modulo the integers $`d`$ with $`2\le d\le D`$. The cutoff $`D`$ has to be fixed before the argument varies: at $`(M,L)=(1,1)`$ the cutoff is $`M+L=2`$, the integers $`1`$ and $`3`$ have the same residue modulo every $`d`$ with $`2\le d\le 2`$, and yet $`\Theta_1(1)=1/2`$ while $`\Theta_1(3)=1`$.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones, with the residue condition $i\equiv-M\pmod d$ written as $d\mid M+i$. They define $i_d(M)=d-(M\bmod d)$ and prove that it is the least $i\ge1$ with $d\mid M+i$, lies in $[1,d]$ and depends only on $M\bmod d$.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_tsum_divisorResidue`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L417)

```lean
theorem theta_eq_tsum_divisorResidue (M L : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L) :
    Theta L M
      = ∑' d : ℕ,
          ∑ i ∈ (Finset.Icc 1 L).filter (fun i => (d + 2) ∣ M + i), (1 / 2 : ℚ) ^ i
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_tsum_geometricForm`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L442)

```lean
theorem theta_eq_tsum_geometricForm (M L : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) :
    Theta L M
      = ∑' d : ℕ,
          (1 / 2 : ℚ) ^ (iLeast (d + 2) M)
            * (1 - (1 / 2 : ℚ) ^ ((d + 2) * mCount (d + 2) M L))
            / (1 - (1 / 2 : ℚ) ^ (d + 2))
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_divisorResidueSum`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L368)

```lean
theorem theta_eq_divisorResidueSum (M L D : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (hD : M + L ≤ D) :
    Theta L M
      = ∑ d ∈ Finset.Icc 2 D,
          ∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ M + i), (1 / 2 : ℚ) ^ i
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_geometricForm`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L378)

```lean
theorem theta_eq_geometricForm (M L D : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (hD : M + L ≤ D) :
    Theta L M
      = ∑ d ∈ Finset.Icc 2 D,
          (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
            / (1 - (1 / 2 : ℚ) ^ d)
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.residue_condition_iff`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L116)

```lean
theorem residue_condition_iff (d M i : ℕ) :
    ((i : ℤ) ≡ -(M : ℤ) [ZMOD (d : ℤ)]) ↔ d ∣ M + i
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.card_divisors_sub_one`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L303)

```lean
theorem card_divisors_sub_one (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card - 1 : ℕ) = (n.divisors.filter (fun d => 2 ≤ d)).card
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast_mem_Icc`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L132)

```lean
theorem iLeast_mem_Icc (d M : ℕ) (hd : 1 ≤ d) : 1 ≤ iLeast d M ∧ iLeast d M ≤ d
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.dvd_add_iLeast`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L138)

```lean
theorem dvd_add_iLeast (d M : ℕ) (hd : 1 ≤ d) : d ∣ M + iLeast d M
```

9. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.not_dvd_of_lt_iLeast`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L147)

```lean
theorem not_dvd_of_lt_iLeast (d M i : ℕ) (hd : 1 ≤ d) (hi : 1 ≤ i)
    (hlt : i < iLeast d M) : ¬ d ∣ M + i
```

10. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast_congr`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L160)

```lean
theorem iLeast_congr (d M M' : ℕ) (h : M % d = M' % d) : iLeast d M = iLeast d M'
```

11. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.mCount_eq_zero_of_lt_iLeast`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L278)

```lean
theorem mCount_eq_zero_of_lt_iLeast (d M L : ℕ) (hd : 1 ≤ d) (h : L < iLeast d M) :
    mCount d M L = 0
```

12. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.geometric_term_eq_zero_of_lt_iLeast`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L293)

```lean
theorem geometric_term_eq_zero_of_lt_iLeast (d M L : ℕ) (hd : 1 ≤ d)
    (h : L < iLeast d M) :
    (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
        / (1 - (1 / 2 : ℚ) ^ d) = 0
```

13. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_Psi`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L339)

```lean
theorem theta_eq_Psi (M L D : ℕ) (hM : 1 ≤ M) (hD : M + L ≤ D) :
    Theta L M = Psi L D M
```

14. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.Psi_eq_of_residues_eq`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L467)

```lean
theorem Psi_eq_of_residues_eq (L D x y : ℕ) (h : ∀ d ∈ Finset.Icc 2 D, x % d = y % d) :
    Psi L D x = Psi L D y
```

15. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_one_one`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L523)

```lean
theorem theta_one_one : Theta 1 1 = 1 / 2
```

16. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_one_three`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L528)

```lean
theorem theta_one_three : Theta 1 3 = 1
```

17. [`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.residue_cutoff_reading_fails`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/ShortWindowDivisorPhase.lean#L538)

```lean
theorem residue_cutoff_reading_fails :
    (∀ d ∈ Finset.Icc 2 (1 + 1), (1 : ℕ) % d = 3 % d) ∧ Theta 1 1 ≠ Theta 1 3
```

<a id="lem-odometer-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `theta_eq_tsum_divisorResidue`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L103) (E257_45, line 103), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L140) (PaperStatementsAA.lean, line 140), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `theta_eq_tsum_geometricForm`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L109) (E257_45, line 109), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L145) (PaperStatementsAA.lean, line 145), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `theta_eq_divisorResidueSum`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L88) (E257_45, line 88), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L127) (PaperStatementsAA.lean, line 127), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `theta_eq_geometricForm`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L95) (E257_45, line 95), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L133) (PaperStatementsAA.lean, line 133), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `residue_condition_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L76) (E257_45, line 76), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L118) (PaperStatementsAA.lean, line 118), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `card_divisors_sub_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L49) (E257_45, line 49), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L98) (PaperStatementsAA.lean, line 98), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `iLeast_mem_Icc`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L65) (E257_45, line 65), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L110) (PaperStatementsAA.lean, line 110), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `dvd_add_iLeast`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L53) (E257_45, line 53), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L101) (PaperStatementsAA.lean, line 101), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `not_dvd_of_lt_iLeast`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L72) (E257_45, line 72), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L115) (PaperStatementsAA.lean, line 115), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `iLeast_congr`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L62) (E257_45, line 62), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L108) (PaperStatementsAA.lean, line 108), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `mCount_eq_zero_of_lt_iLeast`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L68) (E257_45, line 68), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L112) (PaperStatementsAA.lean, line 112), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `geometric_term_eq_zero_of_lt_iLeast`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L56) (E257_45, line 56), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L103) (PaperStatementsAA.lean, line 103), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `theta_eq_Psi`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L84) (E257_45, line 84), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L124) (PaperStatementsAA.lean, line 124), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `Psi_eq_of_residues_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L45) (E257_45, line 45), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L95) (PaperStatementsAA.lean, line 95), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `theta_one_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L117) (E257_45, line 117), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L152) (PaperStatementsAA.lean, line 152), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `theta_one_three`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L120) (E257_45, line 120), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L154) (PaperStatementsAA.lean, line 154), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `residue_cutoff_reading_fails`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L80) (E257_45, line 80), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsAA.lean#L121) (PaperStatementsAA.lean, line 121), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-sqwitness"></a>

## Lemma 11.3 (The terminal bound at square depths), page 124

> *Let $`A\subseteq\mathbb{N}`$ with $`1\notin A`$ and $`X_{A}(2)=1/2`$. Then for every $`k\ge1`$,
> ``` math
> \bigl(\ensuremath{\operatorname{ihc}}\ A\ (k^{2}-1)\ :\ \mathbb{R}\bigr)
> \ =\ \mathtt{binaryCoeffTail}\ (c_{A})\ (k^{2})
> \ \le\ 2k+4\ =\ \ensuremath{B}\ (k^{2}).
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_square_depth_terminal_bound`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquareDepthAndHalfMembershipEquivalences.lean#L27)

```lean
theorem paper_square_depth_terminal_bound (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2) (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k ^ 2 - 1) : ℝ) = binaryCoeffTail (supportCoeff A) (k ^ 2) ∧
      binaryCoeffTail (supportCoeff A) (k ^ 2) ≤ 2 * (k : ℝ) + 4 ∧
      (halfStripBound (k ^ 2) : ℝ) = 2 * (k : ℝ) + 4
```

2. [`ErdosProblems.Erdos257.PaperCompleteR20.square_depth_witness`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR20/CarryCollapseCorrespondence.lean#L8)

```lean
theorem square_depth_witness (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k^2-1) : ℝ) = binaryCoeffTail (supportCoeff A) (k^2) ∧
    binaryCoeffTail (supportCoeff A) (k^2) ≤ 2*(k : ℝ)+4 ∧
    (halfStripBound (k^2) : ℝ) = 2*(k : ℝ)+4
```

<a id="lem-sqwitness-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_square_depth_terminal_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L146) (E257_45, line 146), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsL.lean#L52) (PaperStatementsL.lean, line 52), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)
- `square_depth_witness`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_03/Challenge.lean#L136) (E257_03, line 136), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_03/PaperStatementsL.lean#L28) (PaperStatementsL.lean, line 28), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_03.json) (E257_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-squarefree"></a>

## Proposition 11.4 (Squarefree support: a limit of the certificate method, not an open value), page 126

> *Let $`A=\{n\ge2:n\text{ is squarefree}\}`$. Then
> ``` math
> c_{A}(n)=2^{\omega(n)}-1,
> ```
> which is odd for every $`n\ge2`$. Consequently neither the digitwise nor the carry-aware divisibility-first block-certificate schema has an instance at any even base.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_squarefree_support_engine_ceiling`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/SquarefreeSupportEngineCeiling.lean#L20)

```lean
theorem paper_squarefree_support_engine_ceiling :
    (squarefreeSupport = {d : ℕ | 2 ≤ d ∧ Squarefree d}) ∧
      (∀ n : ℕ, n ≠ 0 →
        Erdos249257.supportCoeff squarefreeSupport n
          = 2 ^ n.primeFactors.card - 1) ∧
      (∀ n : ℕ, 2 ≤ n → Odd (Erdos249257.supportCoeff squarefreeSupport n)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
              Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (K - r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < Erdos249257.supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (∀ r ∈ Finset.Icc 1 K,
              b ^ r ∣ Erdos249257.supportCoeff squarefreeSupport (N + r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              Erdos249257.supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < Erdos249257.supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L))
```

<a id="prop-squarefree-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_squarefree_support_engine_ceiling`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_45/Challenge.lean#L162) (E257_45, line 162), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_45/PaperStatementsBF.lean#L21) (PaperStatementsBF.lean, line 21), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_45.json) (E257_45)

Challenge for `paper_squarefree_support_engine_ceiling`:

```lean
theorem paper_squarefree_support_engine_ceiling :
    (squarefreeSupport = {d : ℕ | 2 ≤ d ∧ Squarefree d}) ∧
      (∀ n : ℕ, n ≠ 0 →
        supportCoeff squarefreeSupport n
          = 2 ^ n.primeFactors.card - 1) ∧
      (∀ n : ℕ, 2 ≤ n → Odd (supportCoeff squarefreeSupport n)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (b ^ K ∣ ∑ r ∈ Finset.Icc 1 K,
              supportCoeff squarefreeSupport (N + r) * b ^ (K - r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) ∧
      (∀ b : ℕ, 2 ≤ b → 2 ∣ b →
        ¬ (∀ q : ℕ, 0 < q → ∃ N K L C : ℕ, K ≤ L ∧
            (∀ r ∈ Finset.Icc 1 K,
              b ^ r ∣ supportCoeff squarefreeSupport (N + r)) ∧
            (∑ r ∈ Finset.Icc (K + 1) L,
              supportCoeff squarefreeSupport (N + r) * b ^ (L - r) ≤ C) ∧
            (∃ t : ℕ, 0 < supportCoeff squarefreeSupport (N + L + 1 + t)) ∧
            q * (C + (N + L + 2)) < b ^ L)) := by sorry
```
