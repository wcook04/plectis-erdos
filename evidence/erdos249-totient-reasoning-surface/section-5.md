# Formal evidence: The Binary Totient Series, Section 5

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="prop-shift"></a>

## Proposition 5.3 (Digit-shift identity), page 18

> *For every $`N : \mathbb{N}`$,
> ``` math
> 2^{N} \cdot S \;=\; \Phi_N + R_N,
> ```
> where $`\Phi_N := \sum_{n \le N} \varphi(n) \cdot 2^{N-n} \in \mathbb{N}`$ (the integer prefix) and $`R_N := \sum_{j \ge 0} \varphi(N+1+j)/2^{j+1}`$ (the scaled tail, $`{R}`$ in Lean).*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.two_pow_mul_totient_series_eq`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/TotientTailPeriodKiller.lean#L150)

```lean
theorem two_pow_mul_totient_series_eq (N : ℕ) :
    (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (totientPrefix N : ℝ) + totientTail N
```

<a id="prop-shift-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `two_pow_mul_totient_series_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L220) (E249_04, line 220), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAD.lean#L90) (PaperStatementsAD.lean, line 90), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-farey"></a>

## Lemma 5.4 (Farey gap, fully general), page 18

> *For integers $`a,b,c,d,r,s`$ with $`b>0`$, $`d>0`$, $`bc-ad=1`$ (i.e. $`a/b`$ and $`c/d`$ are unimodular Farey neighbours), and $`as < rb`$, $`rd < cs`$ (i.e. $`r/s`$ lies strictly between them): $`b+d \le s`$.*

The Lean declaration below states this result.

[`GapFareyBound.farey_gap`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/GapFareyBound.lean#L51)

```lean
theorem farey_gap {a b c d r s : ℤ}
    (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1)
    (hleft : a * s < r * b)
    (hright : r * d < c * s) :
    b + d ≤ s
```

<a id="lem-farey-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `farey_gap`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L228) (E249_04, line 228), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L115) (PaperStatementsAK.lean, line 115), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-gapwindow"></a>

## Proposition 5.5 (The Farey certificate at $`K=240`$), page 18

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
> This bound is *sharp*: $`q = Q_0+1 = 79\,639\,646\,646\,701\,375\,323\,355\,774\,875\,831\,054`$ is the exact first failing denominator, obtained as the denominator of the mediant of two explicit unimodular Farey neighbours.*

The Lean declarations below together state this result.

1. [`Erdos249257.totient_carry_residue_window_1_240_eq`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/CertificateKernel.lean#L18310)

```lean
theorem totient_carry_residue_window_1_240_eq :
    (∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r)) % 2 ^ 240
      = 1299094806818720335611738031537456208600423915562142231419225521361164904
```

2. [`GapFareyBound.gap_check_window_1_240_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/GapFareyBound.lean#L176)

```lean
theorem gap_check_window_1_240_le_79639646646701375323355774875831053
    (q : ℕ) (hq : 0 < q) (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904) % 2 ^ 240 + q * 243 < 2 ^ 240
```

3. [`GapFareyBound.gap_check_window_1_240_first_failure`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/GapFareyBound.lean#L225)

```lean
theorem gap_check_window_1_240_first_failure :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054
```

where [`IsFirstGapFailure`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/GapFareyBound.lean#L44) is

```lean
def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)
```

<a id="prop-gapwindow-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `totient_carry_residue_window_1_240_eq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L259) (E249_04, line 259), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAI.lean#L37) (PaperStatementsAI.lean, line 37), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `gap_check_window_1_240_le_79639646646701375323355774875831053`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L236) (E249_04, line 236), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L127) (PaperStatementsAK.lean, line 127), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `gap_check_window_1_240_first_failure`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L56) (E249_01, line 56), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAK.lean#L118) (PaperStatementsAK.lean, line 118), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-denom-record"></a>

## Theorem 5.6 (Denominator exclusion), page 19

> *For every $`p\in\mathbb{Q}`$ whose reduced denominator is at most $`Q_0`$,
> ``` math
> S \;\neq\; p.
> ```
> Equivalently: *if $`S`$ is rational, its reduced denominator exceeds* $`Q_0 \approx 7.96 \times 10^{34}`$.*

The Lean declaration below states this result.

[`Erdos249257.tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/CertificateKernel.lean#L18384)

```lean
theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ)
```

<a id="thm-denom-record-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_01/Challenge.lean#L44) (E249_01, line 44), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_01/PaperStatementsAI.lean#L57) (PaperStatementsAI.lean, line 57), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_01.json) (E249_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-coprime"></a>

## Proposition 5.9 (Fair-coin coprimality form), page 19

> *Let $`X,Y`$ be independent random variables with $`\Pr(X=n)=\Pr(Y=n)=2^{-n}`$ for $`n \ge 1`$ (independent fair-coin waiting times). Then
> ``` math
> S \;=\; \tfrac12 \;+\; \Pr\bigl(\gcd(X,Y)=1\bigr)
> \;=\; \tfrac12 \;+\; \sum_{\substack{a,b\ge 1\\ \gcd(a,b)=1}} 2^{-(a+b)}.
> ```
> Equivalently, on the visible lattice: summing $`2^{-(a+b)}`$ over the half-open coprime pairs ($`a\ge1`$, $`b\ge0`$, $`\gcd(a,b)=1`$) recovers $`\sum_n \varphi(n)/2^n`$ exactly, with no boundary correction, because the visible-point count on the half-open antidiagonal at height $`n`$ equals $`\varphi(n)`$ for every $`n`$, including $`n=0,1`$.*

The Lean declarations below together state this result.

1. [`Erdos249257.tsum_visible_coprime_pairs_eq_totient_series`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/CertificateKernel.lean#L18544)

```lean
theorem tsum_visible_coprime_pairs_eq_totient_series :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n
```

2. [`Erdos249257.totient_series_eq_half_add_visible_coprime_pairs`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/CertificateKernel.lean#L18557)

```lean
theorem totient_series_eq_half_add_visible_coprime_pairs :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = 1 / 2 + ∑' p : ℕ × ℕ, (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
```

<a id="prop-coprime-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `tsum_visible_coprime_pairs_eq_totient_series`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L277) (E249_04, line 277), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAI.lean#L61) (PaperStatementsAI.lean, line 61), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `totient_series_eq_half_add_visible_coprime_pairs`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L264) (E249_04, line 264), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAI.lean#L46) (PaperStatementsAI.lean, line 46), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-gcdlayer"></a>

## Proposition 5.10 (The gcd-layer normalisation), page 20

> *For independent fair-coin waiting times as above, $`\sum_{g\ge1}\Pr(\gcd(X,Y)=g)=1`$ exactly; and for every $`d>0`$, $`\Pr(d\mid X \wedge d\mid Y) = 1/(2^d-1)^2`$.*

The Lean declarations below together state this result.

1. [`GeometricCoprimality.tsum_gcd_layer_pos_coprime_half_eq_one`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/GeometricCoprimality.lean#L480)

```lean
theorem tsum_gcd_layer_pos_coprime_half_eq_one :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then (((1 : ℝ) / 2) ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = 1
```

2. [`GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/GcdMomentCalculus.lean#L266)

```lean
theorem tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2
```

<a id="prop-gcdlayer-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `tsum_gcd_layer_pos_coprime_half_eq_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L247) (E249_04, line 247), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L156) (PaperStatementsAK.lean, line 156), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)
- `tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L241) (E249_04, line 241), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L145) (PaperStatementsAK.lean, line 145), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-denomcoprime"></a>

## Theorem 5.11 (Denominator exclusion for the coprimality-probability form), page 20

> *Let
> ``` math
> Q_1 := \left\lfloor \frac{Q_0}{2} \right\rfloor = 39\,819\,823\,323\,350\,687\,661\,677\,887\,437\,915\,526.
> ```
> For every $`a\in\mathbb{Z}`$, $`d\in\mathbb{N}`$ with $`0<d\le Q_1`$: the visible coprime-pair probability $`\Pr(\gcd(X,Y)=1)`$ is not equal to $`a/d`$.*

The Lean declaration below states this result.

[`Erdos249257.tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/CertificateKernel.lean#L18572)

```lean
theorem tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 39819823323350687661677887437915526 →
      (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
        ≠ (a : ℝ) / (d : ℝ)
```

<a id="thm-denomcoprime-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L283) (E249_04, line 283), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAI.lean#L66) (PaperStatementsAI.lean, line 66), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-denommobsq"></a>

## Theorem 5.12 (Denominator exclusion for the Möbius-square form), page 20

> *With $`Q_1`$ as in Theorem 5.11: for every $`a\in\mathbb{Z}`$, $`d\in\mathbb{N}`$ with $`0<d\le Q_1`$, the signed series $`T := \sum_{m\ge1} \mu(m)/(2^m-1)^2 = S - \tfrac12`$ (see §5.5) is not equal to $`a/d`$.*

The Lean declaration below states this result.

[`Erdos249257.tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/CertificateKernel.lean#L18487)

```lean
theorem tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 39819823323350687661677887437915526 →
      (∑' k : ℕ+, ((ArithmeticFunction.moebius (k : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (k : ℕ) - 1) ^ 2)
        ≠ (a : ℝ) / (d : ℝ)
```

<a id="thm-denommobsq-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_04/Challenge.lean#L270) (E249_04, line 270), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_04/PaperStatementsAI.lean#L51) (PaperStatementsAI.lean, line 51), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_04.json) (E249_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-mobsq"></a>

## Proposition 5.14 (Möbius-square reduction), page 20

> *``` math
> S \;=\; \sum_{n\ge1}\frac{\varphi(n)}{2^n} \;=\; \frac12 \;+\; \sum_{d\ge1}\frac{\mu(d)}{(2^d-1)^2},
> ```
> where $`\mu`$ is the Möbius function, so $`\mu(d)\in\{-1,0,1\}`$ for every $`d`$. Consequently *Erdős \#249 $`\iff`$ $`T:=\sum_{d\ge1}\mu(d)/(2^d-1)^2 \notin \mathbb{Q}`$*, since adding a rational number does not change irrationality.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.mobius_square_reduction`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR20/MobiusSquareReduction.lean#L10)

```lean
theorem mobius_square_reduction :
    totientSeries = (1 : ℝ) / 2 +
      ∑' d : ℕ+, (ArithmeticFunction.moebius (d : ℕ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.irrational_totient_iff_mobius_square`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR20/MobiusSquareReduction.lean#L17)

```lean
theorem irrational_totient_iff_mobius_square :
    Irrational totientSeries ↔
      Irrational (∑' d : ℕ+, (ArithmeticFunction.moebius (d : ℕ) : ℝ) /
        ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.moebius_three_values`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR20/MobiusSquareReduction.lean#L25)

```lean
theorem moebius_three_values (d : ℕ) :
    ArithmeticFunction.moebius d = -1 ∨ ArithmeticFunction.moebius d = 0 ∨
      ArithmeticFunction.moebius d = 1
```

<a id="prop-mobsq-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `mobius_square_reduction`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_05/Challenge.lean#L64) (E249_05, line 64), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_05/PaperStatementsAY.lean#L65) (PaperStatementsAY.lean, line 65), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_05.json) (E249_05)
- `irrational_totient_iff_mobius_square`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_05/Challenge.lean#L58) (E249_05, line 58), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_05/PaperStatementsAY.lean#L60) (PaperStatementsAY.lean, line 60), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_05.json) (E249_05)
- `moebius_three_values`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_05/Challenge.lean#L46) (E249_05, line 46), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_05/PaperStatementsAJ.lean#L124) (PaperStatementsAJ.lean, line 124), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_05.json) (E249_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-lambertengine"></a>

## Proposition 5.16 (The squared-Lambert identity), page 21

> *For $`w:\mathbb{N}\to\mathbb{R}`$ with $`|w(d)|\le d`$ for all $`d>0`$, and $`0\le r<1`$:
> ``` math
> \sum_{d\ge1} w(d)\left(\frac{r^d}{1-r^d}\right)^2 \;=\; \sum_{n\ge1}\left(\sum_{e\mid n} w(e)\Bigl(\tfrac{n}{e}-1\Bigr)\right) r^n.
> ```*

The Lean declaration below states this result.

[`GcdMomentCalculus.tsum_lambert_linear_weight_sq_pure`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/GcdMomentCalculus.lean#L105)

```lean
theorem tsum_lambert_linear_weight_sq_pure
    (w : ℕ → ℝ) (hw : ∀ d : ℕ, 0 < d → |w d| ≤ (d : ℝ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, w (d : ℕ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ))) ^ 2
      = ∑' n : ℕ+, (∑ e ∈ (n : ℕ).divisors, w e * ((((n : ℕ) / e : ℕ) : ℝ) - 1))
          * r ^ (n : ℕ)
```

<a id="prop-lambertengine-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `tsum_lambert_linear_weight_sq_pure`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_05/Challenge.lean#L73) (E249_05, line 73), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_05/PaperStatementsAK.lean#L134) (PaperStatementsAK.lean, line 134), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_05.json) (E249_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-zetaq"></a>

## Proposition 5.17 (The divisor-sum identity), page 21

> *``` math
> \sum_{d\ge1} \frac{1}{(2^d-1)^2} \;=\; \sum_{n\ge1} \frac{\sigma(n)-\tau(n)}{2^n} \;=\; \zeta_q(2)-\zeta_q(1) \text{ at } q=\tfrac12,
> ```
> where $`\sigma`$ is the sum-of-divisors function and $`\tau`$ the number-of-divisors function. The *identity* is machine-checked. With $`\zeta_q(s)=\sum_{n\ge1}n^{s-1}q^n/(1-q^n)`$, Postelmans and Van Assche prove that $`1,\zeta_q(1),\zeta_q(2)`$ are linearly independent over $`\mathbb{Q}`$ for $`q=1/p`$ with an integer $`p\ge2`$ \[postelmans-vanassche, Theorem 1.3, p. 3\]; at $`q=\tfrac12`$ this gives the irrationality of the *value* $`\zeta_q(2)-\zeta_q(1)`$. Two irrational numbers can have a rational difference, so the separate irrationality of the two values would not suffice.*

The Lean proof assumes the linear independence theorem of Postelmans and Van Assche. Lean takes this input as a hypothesis (`q_Pade_linear_independence`); it is not proved in Lean.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.divisor_sum_identity`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquaredMersenneDivisorIdentities.lean#L36)

```lean
theorem divisor_sum_identity :
    ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          (((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℝ)
            - ((ArithmeticFunction.sigma 0 (n : ℕ) : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.qZeta`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L17)

```lean
def qZeta (q : ℝ) (s : ℕ) : ℝ :=
  ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ (s - 1) * (q ^ (n : ℕ) / (1 - q ^ (n : ℕ)))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.qZeta_half_two_sub_one`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L81)

```lean
theorem qZeta_half_two_sub_one :
    qZeta ((1 : ℝ) / 2) 2 - qZeta ((1 : ℝ) / 2) 1
      = ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_qZeta_half_difference_of_linearIndependent`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L143)

```lean
theorem irrational_qZeta_half_difference_of_linearIndependent
    (hli : ∀ a b c : ℚ,
      (a : ℝ) * 1 + (b : ℝ) * qZeta ((1 : ℝ) / 2) 1
        + (c : ℝ) * qZeta ((1 : ℝ) / 2) 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    Irrational (qZeta ((1 : ℝ) / 2) 2 - qZeta ((1 : ℝ) / 2) 1)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_irrational_pair_with_rational_difference`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L125)

```lean
theorem exists_irrational_pair_with_rational_difference :
    ∃ x y : ℝ, Irrational x ∧ Irrational y ∧ x ≠ y ∧ ¬ Irrational (x - y)
```

<a id="prop-zetaq-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="prop-pillai"></a>

## Proposition 5.18 (The gcd-moment identity), page 22

> *``` math
> \sum_{d\ge1} \frac{\varphi(d)}{(2^d-1)^2} \;=\; \sum_{n\ge1} \bigl(P(n)-n\bigr)\cdot 2^{-n} \;=\; \mathbb{E}[\gcd(X,Y)],
> ```
> where $`P(n) := \sum_{e\mid n}\varphi(e)\cdot(n/e) = (\varphi * \mathrm{Id})(n)`$ is Pillai’s gcd-sum function $`P(n)=\sum_{k\le n}\gcd(k,n)`$ \[toth-gcd, §1, (1)–(2)\] and $`X,Y`$ are the independent fair-coin waiting times of Proposition 5.9. The identity itself is machine-checked; irrationality of $`\mathbb{E}[\gcd(X,Y)]`$ is not proved here. This is a different series from $`S`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.gcd_moment_identity_three_members`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L334)

```lean
theorem gcd_moment_identity_three_members :
    (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' n : ℕ+, (((pillaiP (n : ℕ) : ℕ) : ℝ) - ((n : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ))
      ∧ (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
            then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L307)

```lean
theorem tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
        then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_gcd_Icc_eq_pillaiP`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L77)

```lean
theorem sum_gcd_Icc_eq_pillaiP (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, Nat.gcd k n = pillaiP n
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.pillaiP_eq_totient_mul_id`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L67)

```lean
theorem pillaiP_eq_totient_mul_id (n : ℕ) :
    (totientArith * ArithmeticFunction.id) n = pillaiP n
```

5. [`GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series`](https://github.com/wcook04/plectis-erdos/blob/7f79e63d0b36b5b4f0b47b6368342b4a50824f4e/lean/Erdos249257/GcdMomentCalculus.lean#L235)

```lean
theorem tsum_totient_div_mersenne_sq_eq_gcd_moment_series :
    ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          ((∑ e ∈ (n : ℕ).divisors, (Nat.totient e : ℝ) * (((n : ℕ) / e : ℕ) : ℝ))
            - ((n : ℕ) : ℝ)) * ((1 : ℝ) / 2) ^ (n : ℕ)
```

<a id="prop-pillai-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `gcd_moment_identity_three_members`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_05/Challenge.lean#L150) (E249_05, line 150), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L218) (PaperStatementsAE.lean, line 218), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_05.json) (E249_05)
- `tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_05/Challenge.lean#L167) (E249_05, line 167), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L335) (PaperStatementsAE.lean, line 335), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_05.json) (E249_05)
- `sum_gcd_Icc_eq_pillaiP`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_05/Challenge.lean#L163) (E249_05, line 163), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L295) (PaperStatementsAE.lean, line 295), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_05.json) (E249_05)
- `pillaiP_eq_totient_mul_id`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_05/Challenge.lean#L159) (E249_05, line 159), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L263) (PaperStatementsAE.lean, line 263), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_05.json) (E249_05)
- `tsum_totient_div_mersenne_sq_eq_gcd_moment_series`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_05/Challenge.lean#L81) (E249_05, line 81), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_05/PaperStatementsAK.lean#L150) (PaperStatementsAK.lean, line 150), [replay report](../../evidence/comparator/replay-35935225572/receipt-E249_05.json) (E249_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
