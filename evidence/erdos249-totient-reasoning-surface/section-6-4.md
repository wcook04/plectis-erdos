# Formal evidence: The Binary Totient Series, Section 6, results 6.104 to 6.159

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="prop-b11-inv"></a>

## Proposition 6.104 (Diagonal certificates through $`82`$), page 52

> *The current aggregate establishes
> ``` math
> \forall t\in\mathbb N,\quad t\le82\ \Longrightarrow\ P\,t,
> ```
> where $`P\,t`$ is the diagonal certificate predicate in Proposition <a href="#prop:B3" data-reference-type="ref" data-reference="prop:B3">121</a>. The earlier aggregate covered 28 explicit cases through $`64`$, including $`1,2,3,4,5,7,8,9,11,13,16,17`$; the later theorem fills the gaps and extends the range through $`82`$. Each instance reduces to exact finite arithmetic with the displayed totient values, using the prime-power factorisations and Lucas primality certificates in the source. This proves neither $`P\,83`$ nor infinitely many instances, and therefore does not establish the quantified conditions in Propositions <a href="#prop:A10" data-reference-type="ref" data-reference="prop:A10">120</a>, <a href="#prop:B3" data-reference-type="ref" data-reference="prop:B3">121</a> and <a href="#prop:B7" data-reference-type="ref" data-reference="prop:B7">122</a>.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.historical_table_size_and_initial_depths`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L57)

```lean
theorem historical_table_size_and_initial_depths :
    diagonalPincerCertificateScalesThroughT64.length = 28 ∧
    diagonalPincerCertificateScalesThroughT64.Nodup ∧
    diagonalPincerCertificateScalesThroughT64.getLast? = some 64 ∧
    ([1,2,3,4,5,7,8,9,11,13,16,17].map diagonalPincerKillDepthThroughT64) =
      [6,5,7,7,9,14,15,14,21,22,23,26]
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.historical_table_and_complete_band`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L64)

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
| `historical_table_size_and_initial_depths` | [E249_06/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L97) | [PaperStatementsG.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsG.lean#L47) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `historical_table_and_complete_band` | [E249_06/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L124) | [PaperStatementsI.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsI.lean#L80) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-c1-inv"></a>

## Proposition 6.105 (A coprime-pair expression for $`S`$), page 52

> *For $`n\ge0`$, the number of integer pairs $`a\ge1`$, $`b\ge0`$ with $`a+b=n`$ and $`\gcd(a,b)=1`$ is $`\varphi(n)`$, with $`\varphi(0)=0`$. Indeed, $`b=n-a`$ and $`\gcd(a,n-a)=\gcd(a,n)`$. The boundary case $`n=1`$ contributes $`(a,b)=(1,0)`$; it disappears when both coordinates are required to be positive. Consequently,
> ``` math
> \sum_{\substack{a,b\ge1\\\gcd(a,b)=1}}2^{-(a+b)}=S-\frac12.
> ```
> For independent random variables $`X,Y`$ with $`\Pr(X=n)=\Pr(Y=n)=2^{-n}`$, $`n\ge1`$, the left side is $`\Pr(\gcd(X,Y)=1)`$. Thus $`S-1/2`$ has a coprimality-probability interpretation. This identity does not supply an estimate for the binary digits or tail residues used elsewhere in the paper.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.card_visible_antidiagonal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L218)

```lean
theorem card_visible_antidiagonal (n : ℕ) :
    ((Finset.antidiagonal n).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2).card
      = Nat.totient n
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_zero_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L225)

```lean
theorem totient_zero_eq_zero : Nat.totient 0 = 0
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.visible_antidiagonal_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L228)

```lean
theorem visible_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2)
      = {((1 : ℕ), (0 : ℕ))}
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.positive_antidiagonal_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L234)

```lean
theorem positive_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2) = ∅
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_eq_series_sub_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L241)

```lean
theorem tsum_pos_coprime_pairs_eq_series_sub_half :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then 1 / (2 : ℝ) ^ (q.1 + q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_product_form`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L266)

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
| `card_visible_antidiagonal` | [E249_16/Challenge.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L83) | [PaperStatementsAJ.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L163) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `totient_zero_eq_zero` | [E249_16/Challenge.lean, line 173](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L173) | [PaperStatementsAK.lean, line 66](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L66) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `visible_antidiagonal_one` | [E249_16/Challenge.lean, line 188](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L188) | [PaperStatementsAK.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L110) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `positive_antidiagonal_one` | [E249_16/Challenge.lean, line 151](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L151) | [PaperStatementsAJ.lean, line 480](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L480) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `tsum_pos_coprime_pairs_eq_series_sub_half` | [E249_16/Challenge.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L176) | [PaperStatementsAK.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L68) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `tsum_pos_coprime_pairs_product_form` | [E249_16/Challenge.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L182) | [PaperStatementsAK.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L73) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-values-exponents-one-two"></a>

## Theorem 6.121 (The values at exponents one and two), page 59

> *The first two values are $`\Theta_1=1/2`$ and $`\Theta_2=S-1/2`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.mobiusMersenneTheta_one_and_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L23)

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
| `mobiusMersenneTheta_one_and_two` | [E249_17/Challenge.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L50) | [PaperStatementsBG.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsBG.lean#L28) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-first-two-summands-give-positive"></a>

## Theorem 6.122 (The first two summands give a positive Hankel gap), page 59

> *$`(1-3^{-(r+1)})^2 - (1-3^{-r})(1-3^{-(r+2)}) = 4/3^{r+2}`$, so the rational sequence $`1-3^{-r}`$ is strictly log-concave for every integer $`r\ge1`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_hankel_gap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L35)

```lean
theorem twoAtom_hankel_gap (r : ℕ) :
    (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2
        - (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      = 4 / (3 : ℝ) ^ (r + 2)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.twoAtom_strict_logConcave`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L43)

```lean
theorem twoAtom_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    (1 - 1 / (3 : ℝ) ^ r) * (1 - 1 / (3 : ℝ) ^ (r + 2))
      < (1 - 1 / (3 : ℝ) ^ (r + 1)) ^ 2
```

<a id="thm-first-two-summands-give-positive-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `twoAtom_hankel_gap` | [E249_17/Challenge.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L75) | [PaperStatementsAK.lean, line 90](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAK.lean#L90) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `twoAtom_strict_logConcave` | [E249_17/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L81) | [PaperStatementsAK.lean, line 95](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAK.lean#L95) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-strict-log-concavity-all-integer"></a>

## Theorem 6.123 (Strict log-concavity for all integer $`r\ge1`$), page 59

> *For every integer $`r\ge1`$,
> ``` math
> \Theta_r\Theta_{r+2}<\Theta_{r+1}^2.
> ```
> Equivalently, the determinant of $`\left(\begin{smallmatrix}\Theta_r&\Theta_{r+1}\\
> \Theta_{r+1}&\Theta_{r+2}\end{smallmatrix}\right)`$ is negative. The two-summand comparison gives an elementary proof, detailed below; the same strict inequality is also proved in Lean.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.theta_strict_logConcave`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L52)

```lean
theorem theta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
      < mobiusMersenneTheta (r + 1) ^ 2
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_det_neg`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L58)

```lean
theorem theta_hankel_det_neg (r : ℕ) (hr : 1 ≤ r) :
    Matrix.det (Matrix.of
        ![![mobiusMersenneTheta r, mobiusMersenneTheta (r + 1)],
          ![mobiusMersenneTheta (r + 1), mobiusMersenneTheta (r + 2)]]) < 0
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.theta_hankel_two_neg`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MobiusMersenneLadderLogConcavity.lean#L66)

```lean
theorem theta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2)
        - mobiusMersenneTheta (r + 1) ^ 2 < 0
```

<a id="thm-strict-log-concavity-all-integer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `theta_strict_logConcave` | [E249_17/Challenge.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L67) | [PaperStatementsBG.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsBG.lean#L42) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `theta_hankel_det_neg` | [E249_17/Challenge.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L56) | [PaperStatementsBG.lean, line 33](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsBG.lean#L33) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `theta_hankel_two_neg` | [E249_17/Challenge.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L62) | [PaperStatementsBG.lean, line 38](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsBG.lean#L38) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-binary-carry-criterion"></a>

## Theorem 6.125 (Integer recurrence criterion for a binary series), page 60

> *Let $`c:\mathbb{N}\to\mathbb{N}`$ satisfy $`c(n)\le n`$. Then $`\sum_{n\ge1}c(n)2^{-n}`$ is rational if and only if there are an integer $`v>0`$ and an integer sequence $`u`$ such that
> ``` math
> u(N+1)=2u(N)-v\,c(N+1),\qquad \frac{u(N)}{2^N}\longrightarrow0.
> ```
> For each fixed $`v`$, such a sequence is unique and equals
> ``` math
> u(N)=vR^c_N,\qquad R^c_N=\sum_{j\ge1}\frac{c(N+j)}{2^j}.
> ```*

The Lean declarations below together state this result.

1. [`Erdos249257.binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L426)

```lean
theorem binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u
```

2. [`Erdos249257.temperedBinaryOrbit_eq_scaledTail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L339)

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
| `binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit` | [E257_21/Challenge.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L58) | [PaperStatementsAE.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAE.lean#L45) | [E257_21](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `temperedBinaryOrbit_eq_scaledTail` | [E257_21/Challenge.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L64) | [PaperStatementsAE.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAE.lean#L65) | [E257_21](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-uniqueness-under-growth-condition"></a>

## Proposition 6.126 (Uniqueness under the growth condition), page 60

> *A real sequence $`d`$ with $`d(N{+}1)=2d(N)`$ and $`d(N)=o(2^N)`$ is identically zero.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.doubling_tempered_sequence_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L28)

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
| `doubling_tempered_sequence_eq_zero` | [E249_17/Challenge.lean, line 135](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L135) | [PaperStatementsAE.lean, line 224](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L224) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-exact-rational-approximation-formula"></a>

## Proposition 6.128 (An exact rational approximation formula), page 61

> *For integers $`H,D\ge0`$, with the integer prefixes $`\Phi_N`$ defined above,
> ``` math
> \begin{aligned}
>  R_{2H}-R_H
>  &-\left[\Phi_H-\Phi_{2H}
>    +2^H(2^H-1)\left(\frac12+\sum_{d=1}^{D}\frac{\mu(d)}{(2^d-1)^2}\right)\right]\\
>  &=2^H(2^H-1)\sum_{d>D}\frac{\mu(d)}{(2^d-1)^2}.
> \end{aligned}
> ```
> This follows by substituting the squared-denominator identity for $`S`$ into $`R_{2H}-R_H=2^H(2^H-1)S+\Phi_H-\Phi_{2H}`$. There is no required ordering between $`D`$ and $`H`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_sub_rationalApproximation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L118)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_eq_coefficient_mul_series`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L88)

```lean
theorem tailDifference_eq_coefficient_mul_series (H : ℕ) :
    totientTail (2 * H) - totientTail H =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) +
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_pnat_form`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L99)

```lean
theorem totientSeries_pnat_form :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_eq_half_add_moebius_sq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L106)

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
| `tailDifference_sub_rationalApproximation` | [E249_17/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L223) | [PaperStatementsAX.lean, line 529](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAX.lean#L529) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `tailDifference_eq_coefficient_mul_series` | [E249_17/Challenge.lean, line 216](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L216) | [PaperStatementsAX.lean, line 523](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAX.lean#L523) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `totientSeries_pnat_form` | [E249_17/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L184) | [PaperStatementsAE.lean, line 330](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L330) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `totientSeries_eq_half_add_moebius_sq` | [E249_17/Challenge.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L176) | [PaperStatementsAE.lean, line 323](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L323) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-geometric-tail-bound"></a>

## Proposition 6.129 (A geometric tail bound), page 61

> *For every integer $`D\ge0`$,
> ``` math
> \left|\sum_{d>D}\frac{\mu(d)}{(2^d-1)^2}\right|
>  \le \frac{4}{3(2^{D+1}-1)^2}.
> ```
> Indeed, $`|\mu(d)|\le1`$ and $`2^{D+1+j}-1\ge2^j(2^{D+1}-1)`$ for $`j\ge0`$. The sum of the resulting geometric majorant is $`\sum_{j\ge0}4^{-j}=4/3`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_mobiusSquareTail_le_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L155)

```lean
theorem abs_mobiusSquareTail_le_paper (D : ℕ) :
    |∑' k : ℕ,
        ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
          (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2)| ≤
      4 / (3 * (((2 : ℝ) ^ (D + 1) - 1) ^ 2))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_moebius_cast_le_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L138)

```lean
theorem abs_moebius_cast_le_one (d : ℕ) :
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenne_geometric_shift`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L144)

```lean
theorem mersenne_geometric_shift (D j : ℕ) :
    (2 : ℝ) ^ j * ((2 : ℝ) ^ (D + 1) - 1) ≤ (2 : ℝ) ^ (D + 1 + j) - 1
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_quarter_geometric`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TemperedOrbitAndSquaredMersenneTail.lean#L149)

```lean
theorem tsum_quarter_geometric : ∑' j : ℕ, ((1 : ℝ) / 4) ^ j = 4 / 3
```

<a id="prop-geometric-tail-bound-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `abs_mobiusSquareTail_le_paper` | [E249_17/Challenge.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L103) | [PaperStatementsAE.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L176) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `abs_moebius_cast_le_one` | [E249_17/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L110) | [PaperStatementsAE.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L182) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `mersenne_geometric_shift` | [E249_17/Challenge.lean, line 142](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L142) | [PaperStatementsAE.lean, line 256](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L256) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `tsum_quarter_geometric` | [E249_17/Challenge.lean, line 202](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L202) | [PaperStatementsAE.lean, line 352](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L352) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sum-over-divisor-indices"></a>

## Proposition 6.131 (The sum over divisor indices), page 62

> *For integers $`H>0`$ and $`s\ge0`$, the part of the Möbius expansion indexed by divisors of $`H`$ is
> ``` math
> \sum_{\substack{d\mid H\\d\mid s}}\mu(d)\frac Hd
>        =H\frac{\varphi(\gcd(H,s))}{\gcd(H,s)}.
> ```
> This is the standard identity $`\sum_{d\mid g}\mu(d)/d=\varphi(g)/g`$ at $`g=\gcd(H,s)>0`$. The formal statement writes the same value after extracting $`H/\operatorname{rad}(H)`$, where $`\operatorname{rad}(H)=\prod_{p\mid H}p`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_divisorIndices_mobius`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L68)

```lean
theorem sum_divisorIndices_mobius (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ) =
      (H : ℚ) * (Nat.totient (Nat.gcd H s) : ℚ) / (Nat.gcd H s : ℚ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_moebius_div_eq_totient_div`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L98)

```lean
theorem sum_divisors_moebius_div_eq_totient_div {g : ℕ} (hg : 0 < g) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℚ) / (d : ℚ) =
      (Nat.totient g : ℚ) / (g : ℚ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_divisorIndices_radical_form`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L121)

```lean
theorem sum_divisorIndices_radical_form (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        ArithmeticFunction.moebius d * ((H / d : ℕ) : ℤ) =
      ((H / RadicalMobiusShadow.squarefreeKernel H : ℕ) : ℤ) *
        (RepunitMobiusNumerator.gcdWordCoeff
          (RadicalMobiusShadow.squarefreeKernel H) s : ℤ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.squarefreeKernel_eq_prod_primeFactors`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L117)

```lean
theorem squarefreeKernel_eq_prod_primeFactors (H : ℕ) :
    RadicalMobiusShadow.squarefreeKernel H = ∏ p ∈ H.primeFactors, p
```

<a id="prop-sum-over-divisor-indices-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `sum_divisorIndices_mobius` | [E249_17/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L150) | [PaperStatementsAE.lean, line 298](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L298) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `sum_divisors_moebius_div_eq_totient_div` | [E249_17/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L156) | [PaperStatementsAE.lean, line 303](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L303) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `sum_divisorIndices_radical_form` | [E249_17/Challenge.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L259) | [PaperStatementsAQ.lean, line 85](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAQ.lean#L85) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `squarefreeKernel_eq_prod_primeFactors` | [E249_17/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L146) | [PaperStatementsAE.lean, line 285](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L285) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

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

## Proposition 6.132 (The divisor sum and its complement), page 62

> *For integers $`H>0`$ and $`s\ge0`$,
> ``` math
> \begin{aligned}
>  \varphi(2H+s)-\varphi(H+s)
>  &=H\frac{\varphi(\gcd(H,s))}{\gcd(H,s)}\\
>  &\quad+\sum_{\substack{1\le d\le2H+s\\d\nmid H}}
>  \mu(d)\left(\frac{2H+s}{d}\,\mathbf1_{d\mid2H+s}
>            -\frac{H+s}{d}\,\mathbf1_{d\mid H+s}\right).
> \end{aligned}
> ```
> Here $`\mathbf1`$ is the indicator of the stated divisibility condition. The identity follows by expanding both totients as $`\varphi(n)=\sum_{d\mid n}\mu(d)n/d`$ and separating the indices $`d\mid H`$. Such an index divides either endpoint precisely when it divides $`s`$, and its difference is then $`\mu(d)H/d`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.totientDifference_eq_divisorPart_add_complement`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L217)

```lean
theorem totientDifference_eq_divisorPart_add_complement (H s : ℕ) (hH : 0 < H) :
    (Nat.totient (2 * H + s) : ℚ) - (Nat.totient (H + s) : ℚ) =
      (H : ℚ) * (Nat.totient (Nat.gcd H s) : ℚ) / (Nat.gcd H s : ℚ) +
        ∑ d ∈ {d ∈ Finset.Icc 1 (2 * H + s) | ¬d ∣ H}, complementSummand d H s
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_eq_mobius_divisor_sum`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L134)

```lean
theorem totient_eq_mobius_divisor_sum (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℤ) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ((n / d : ℕ) : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.divisorIndex_endpoint_behaviour`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L141)

```lean
theorem divisorIndex_endpoint_behaviour {d H s : ℕ} (hdH : d ∣ H) :
    (d ∣ 2 * H + s ↔ d ∣ s) ∧ (d ∣ H + s ↔ d ∣ s) ∧
      (ArithmeticFunction.moebius d : ℚ) * ((2 * H + s : ℕ) : ℚ) / (d : ℚ) -
          (ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ) =
        (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_eq_phaseTerm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L159)

```lean
theorem complementSummand_eq_phaseTerm {d H s : ℕ} (hd : 0 < d) (hdH : ¬d ∣ H) :
    complementSummand d H s = ((foreignChannelPhaseTerm d H s : ℤ) : ℚ)
```

<a id="prop-divisor-sum-complement-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totientDifference_eq_divisorPart_add_complement` | [E249_17/Challenge.lean, line 170](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L170) | [PaperStatementsAE.lean, line 318](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L318) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `totient_eq_mobius_divisor_sum` | [E249_17/Challenge.lean, line 189](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L189) | [PaperStatementsAE.lean, line 334](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L334) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `divisorIndex_endpoint_behaviour` | [E249_17/Challenge.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L128) | [PaperStatementsAE.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L218) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `complementSummand_eq_phaseTerm` | [E249_17/Challenge.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L114) | [PaperStatementsAE.lean, line 202](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L202) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-doubling-full-totient-difference"></a>

## Theorem 6.133 (Doubling the full totient difference), page 62

> *For nonnegative integers $`H,r`$ with $`H`$ even,
> ``` math
> \varphi(4H+2r)-\varphi(2H+2r)=
>  \begin{cases}
>  2\bigl(\varphi(2H+r)-\varphi(H+r)\bigr),&r\text{ even},\\
>  \varphi(2H+r)-\varphi(H+r),&r\text{ odd}.
>  \end{cases}
> ```
> This applies to the full difference, not just its divisor contribution. It follows from $`\varphi(2n)=2\varphi(n)`$ for even $`n`$ and $`\varphi(2n)=\varphi(n)`$ for odd $`n`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.totientDifference_doubling_seam`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L262)

```lean
theorem totientDifference_doubling_seam (H r : ℕ) (hH : Even H) :
    (Even r →
        (Nat.totient (4 * H + 2 * r) : ℤ) - (Nat.totient (2 * H + 2 * r) : ℤ) =
          2 * ((Nat.totient (2 * H + r) : ℤ) - (Nat.totient (H + r) : ℤ))) ∧
      (Odd r →
        (Nat.totient (4 * H + 2 * r) : ℤ) - (Nat.totient (2 * H + 2 * r) : ℤ) =
          (Nat.totient (2 * H + r) : ℤ) - (Nat.totient (H + r) : ℤ))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_two_mul_even`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L250)

```lean
theorem totient_two_mul_even {n : ℕ} (hn : Even n) :
    Nat.totient (2 * n) = 2 * Nat.totient n
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_two_mul_odd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L255)

```lean
theorem totient_two_mul_odd {n : ℕ} (hn : Odd n) :
    Nat.totient (2 * n) = Nat.totient n
```

<a id="thm-doubling-full-totient-difference-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totientDifference_doubling_seam` | [E249_17/Challenge.lean, line 161](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L161) | [PaperStatementsAE.lean, line 310](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L310) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `totient_two_mul_even` | [E249_17/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L194) | [PaperStatementsAE.lean, line 338](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L338) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `totient_two_mul_odd` | [E249_17/Challenge.lean, line 198](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L198) | [PaperStatementsAE.lean, line 341](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L341) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-doubling-identity-two-portions-sum"></a>

## Proposition 6.135 (A doubling identity for two portions of the sum), page 63

> *Let $`H>0`$, $`s\ge0`$ and $`d\ge1`$, with $`d\nmid H`$ and $`d\mid H+s`$. The $`d`$-summands in the complementary sums at offsets $`s`$ and $`2s`$ are, respectively,
> ``` math
> -\mu(d)\frac{H+s}{d}
>  \qquad\text{and}\qquad
>  2\mu(d)\frac{H+s}{d}.
> ```
> For the second expression, $`d\mid2H+2s`$ and $`d\nmid H+2s`$; otherwise $`d`$ would divide their difference $`H`$. Thus the second contribution is $`-2`$ times the first, including the zero case $`\mu(d)=0`$. The two terms have different binary weights in a window sum, so this identity alone is not a cancellation of their weighted contributions.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_low_double_echo`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DivisorChannelSplitAndSeamDoubling.lean#L289)

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
| `complementSummand_low_double_echo` | [E249_17/Challenge.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L118) | [PaperStatementsAE.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAE.lean#L205) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-positive-coefficients-numerator-polynomial"></a>

## Theorem 6.136 (Positive coefficients of the numerator polynomial), page 63

> *For a squarefree integer $`r\ge1`$, the numerator polynomial has the explicit expression
> ``` math
> \sum_{d\mid r}\mu(d)\frac rd\sum_{j=0}^{r/d-1}X^{dj}
>    =\sum_{k=0}^{r-1}
>         \frac r{\gcd(r,k)}\varphi(\gcd(r,k))X^k.
> ```
> Every coefficient for $`0\le k<r`$ is positive, and the higher coefficients are zero. Extracting $`X^k`$ on the left gives $`\sum_{d\mid\gcd(r,k)}\mu(d)r/d`$, which proves the formula. The squarefree assumption identifies this divisor sum with the subset-of-primes definition in the formal source.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eq_gcdWordForm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L67)

```lean
theorem paperNumerator_eq_gcdWordForm {r : ℕ} (hr : Squarefree r) :
    paperNumeratorPolynomial r =
      ∑ k ∈ Finset.range r,
        Polynomial.C (((r / Nat.gcd r k) * Nat.totient (Nat.gcd r k) : ℕ) : ℤ) *
          (Polynomial.X : Polynomial ℤ) ^ k
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L82)

```lean
theorem paperNumerator_coeff_pos {r k : ℕ} (hr : Squarefree r) (hk : k < r) :
    0 < (paperNumeratorPolynomial r).coeff k
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L88)

```lean
theorem paperNumerator_coeff_eq_zero {r k : ℕ} (hr : Squarefree r) (hk : r ≤ k) :
    (paperNumeratorPolynomial r).coeff k = 0
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_coeff_eq_gcd_divisor_sum`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L94)

```lean
theorem paperNumerator_coeff_eq_gcd_divisor_sum {r k : ℕ} (hr : Squarefree r)
    (hk : k < r) :
    (paperNumeratorPolynomial r).coeff k =
      ∑ d ∈ (Nat.gcd r k).divisors,
        ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumeratorPolynomial_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L57)

```lean
theorem paperNumeratorPolynomial_eq (r : ℕ) :
    paperNumeratorPolynomial r = mobiusNumeratorPolynomial r
```

<a id="thm-positive-coefficients-numerator-polynomial-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paperNumerator_eq_gcdWordForm` | [E249_17/Challenge.lean, line 292](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L292) | [PaperStatementsAO.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAO.lean#L52) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `paperNumerator_coeff_pos` | [E249_17/Challenge.lean, line 288](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L288) | [PaperStatementsAO.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAO.lean#L49) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `paperNumerator_coeff_eq_zero` | [E249_17/Challenge.lean, line 284](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L284) | [PaperStatementsAO.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAO.lean#L46) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `paperNumerator_coeff_eq_gcd_divisor_sum` | [E249_17/Challenge.lean, line 277](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L277) | [PaperStatementsAO.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAO.lean#L40) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `paperNumeratorPolynomial_eq` | [E249_17/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L255) | [PaperStatementsAQ.lean, line 82](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAQ.lean#L82) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-numerator-polynomial-explicit-positive-coefficients"></a>

## Corollary 6.137, page 63

> *For the same squarefree $`r`$, evaluation at $`X=2`$ gives the integer
> ``` math
> \sum_{d\mid r}\mu(d)\frac rd\frac{2^r-1}{2^d-1}.
> ```
> Each quotient is an integer because $`d\mid r`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L111)

```lean
theorem paperNumerator_eval_two {r : ℕ} (_hr : Squarefree r) :
    (((paperNumeratorPolynomial r).eval 2 : ℤ) : ℚ) =
      ∑ d ∈ r.divisors,
        (ArithmeticFunction.moebius d : ℚ) * ((r / d : ℕ) : ℚ) *
          (((2 : ℚ) ^ r - 1) / ((2 : ℚ) ^ d - 1))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenne_dvd_of_dvd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L106)

```lean
theorem mersenne_dvd_of_dvd {d r : ℕ} (hd : d ∣ r) :
    (2 ^ d - 1 : ℕ) ∣ (2 ^ r - 1 : ℕ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.paperNumerator_eval_two_primeSubsetForm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L145)

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
| `paperNumerator_eval_two` | [E249_18/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L104) | [PaperStatementsAO.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L57) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `mersenne_dvd_of_dvd` | [E249_17/Challenge.lean, line 273](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_17/Challenge.lean#L273) | [PaperStatementsAO.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_17/PaperStatementsAO.lean#L34) | [E249_17](../../evidence/comparator/replay-35882032091/receipt-E249_17.json) |
| `paperNumerator_eval_two_primeSubsetForm` | [E249_18/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L111) | [PaperStatementsAO.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L63) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-geometric-remainder-bound"></a>

## Proposition 6.139 (The geometric remainder bound), page 64

> *The remainder after the first two geometric terms of $`1/(2^n-1)`$ is
> ``` math
> \frac1{2^n-1}-2^{-n}-4^{-n}
>    =\frac{8^{-n}}{1-2^{-n}}
>    \le \frac43\,8^{-n}\qquad(n\ge2).
> ```
> Indeed, $`1-2^{-n}\ge3/4`$. Summing over $`n>m`$, for an integer $`m\ge1`$, gives
> ``` math
> \sum_{n>m}\left(\frac1{2^n-1}-2^{-n}-4^{-n}\right)
>  \le\frac43\sum_{n>m}8^{-n}=\frac4{21}\,8^{-m}.
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenneRemainder_identity_and_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L166)

```lean
theorem mersenneRemainder_identity_and_bound {n : ℕ} (hn : 2 ≤ n) :
    1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n =
        ((1 : ℝ) / 8) ^ n / (1 - ((1 : ℝ) / 2) ^ n) ∧
      1 / ((2 : ℝ) ^ n - 1) - ((1 : ℝ) / 2) ^ n - ((1 : ℝ) / 4) ^ n ≤
        (4 / 3 : ℝ) * ((1 : ℝ) / 8) ^ n
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.one_sub_half_pow_ge`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L156)

```lean
theorem one_sub_half_pow_ge {n : ℕ} (hn : 2 ≤ n) :
    (3 : ℝ) / 4 ≤ 1 - ((1 : ℝ) / 2) ^ n
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenneRemainderTail_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L208)

```lean
theorem mersenneRemainderTail_le {m : ℕ} (hm : 0 < m) :
    ∑' k : ℕ,
        (1 / ((2 : ℝ) ^ (m + k + 1) - 1) - ((1 : ℝ) / 2) ^ (m + k + 1) -
          ((1 : ℝ) / 4) ^ (m + k + 1)) ≤
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_eighth_pow_tail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L182)

```lean
theorem tsum_eighth_pow_tail (m : ℕ) :
    ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) = (1 / 7 : ℝ) * ((1 : ℝ) / 8) ^ m
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.four_thirds_tsum_eighth_pow_tail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NumeratorPolynomialAndMersenneRemainder.lean#L200)

```lean
theorem four_thirds_tsum_eighth_pow_tail (m : ℕ) :
    (4 / 3 : ℝ) * ∑' k : ℕ, ((1 : ℝ) / 8) ^ (m + k + 1) =
      (4 / 21 : ℝ) * ((1 : ℝ) / 8) ^ m
```

<a id="prop-geometric-remainder-bound-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mersenneRemainder_identity_and_bound` | [E249_18/Challenge.lean, line 93](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L93) | [PaperStatementsAO.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L27) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `one_sub_half_pow_ge` | [E249_18/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L100) | [PaperStatementsAO.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L36) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `mersenneRemainderTail_le` | [E249_18/Challenge.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L86) | [PaperStatementsAO.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L21) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `tsum_eighth_pow_tail` | [E249_18/Challenge.lean, line 118](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L118) | [PaperStatementsAO.lean, line 69](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L69) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `four_thirds_tsum_eighth_pow_tail` | [E249_18/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L81) | [PaperStatementsAO.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAO.lean#L17) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-squared-distance-phase-one"></a>

## Proposition 6.140 (Squared distance from the phase one), page 64

> *``` math
> \begin{aligned}
> \sum_{N\in T}\|{E}(h,N,L)-1\|^2
>   &= 2|T|-2\sum_{N\in T}\operatorname{Re}E(h,N,L).
> \end{aligned}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.sum_sq_dist_from_phase_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L31)

```lean
theorem sum_sq_dist_from_phase_one (h L : ℕ) (T : Finset ℕ) :
    ∑ N ∈ T, ‖windowFirstExp h N L - 1‖ ^ 2 =
      2 * (T.card : ℝ) - 2 * ∑ N ∈ T, (windowFirstExp h N L).re
```

<a id="prop-squared-distance-phase-one-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `sum_sq_dist_from_phase_one` | [E249_18/Challenge.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L139) | [PaperStatementsAX.lean, line 513](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAX.lean#L513) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-squared-distance-bound-separated-pairs"></a>

## Lemma 6.141 (Squared-distance bound for separated pairs), page 64

> *For a finite family $`z:T\to\mathbb{C}`$, a real number $`\delta\ge0`$, and any set of pairs $`P\subseteq
> T\times T`$ each separated by $`\ge\delta`$, $`|P|\cdot\delta^2 \le
> \sum_{i,j\in T}\|z_i-z_j\|^2`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.card_mul_sq_le_pairwise_energy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L40)

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
| `card_mul_sq_le_pairwise_energy` | [E249_18/Challenge.lean, line 161](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L161) | [PaperStatementsAE.lean, line 187](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAE.lean#L187) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-divisor-sum"></a>

## Proposition 6.142 (The finite divisor sum), page 65

> *For an integer $`H>0`$, the contribution of the divisor indices to $`R_{2H}-R_H`$ is
> ``` math
> A_H=H\sum_{d\mid H}\frac{\mu(d)}{d(2^d-1)}.
> ```
> For $`d\mid H`$, both $`a_d(H)`$ and $`a_d(2H)`$ equal $`d`$. Hence $`\kappa_d(2H)-\kappa_d(H)=H\mu(d)/(d(2^d-1))`$. Summing over the divisors gives $`A_H`$, not the whole tail difference: the nondivisor terms must still be included.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.divisorChannels_sum_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L69)

```lean
theorem divisorChannels_sum_eq (H : ℕ) (_hH : 0 < H) :
    ∑ d ∈ H.divisors, residueIncrement d H =
      (H : ℝ) *
        ∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1))
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.residueOffset_of_dvd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L50)

```lean
theorem residueOffset_of_dvd {d H : ℕ} (_hd : 0 < d) (hdvd : d ∣ H) :
    residueOffset d H = d ∧ residueOffset d (2 * H) = d
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.residueKernel_increment_of_dvd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L58)

```lean
theorem residueKernel_increment_of_dvd {d H : ℕ} (hd : 0 < d) (hdvd : d ∣ H) :
    foreignResidueKernel d (2 * H) - foreignResidueKernel d H =
      (H : ℝ) * ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
        ((d : ℝ) * ((2 : ℝ) ^ d - 1))
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.scaleExplicitShadow_eq_divisorChannels`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L84)

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
| `divisorChannels_sum_eq` | [E249_18/Challenge.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L182) | [PaperStatementsBE.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBE.lean#L34) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `residueOffset_of_dvd` | [E249_18/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L209) | [PaperStatementsBE.lean, line 57](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBE.lean#L57) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `residueKernel_increment_of_dvd` | [E249_18/Challenge.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L203) | [PaperStatementsBE.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBE.lean#L52) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `scaleExplicitShadow_eq_divisorChannels` | [E249_18/Challenge.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L168) | [PaperStatementsAE.lean, line 270](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAE.lean#L270) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-separation-larger-than-error-implies"></a>

## Proposition 6.143 (Separation larger than the error implies exclusion), page 65

> *Suppose
> ``` math
> \bigl|(R_{2H}-R_H)-(A_H+P_{H,D})\bigr|\le\varepsilon_{H,D},
>  \qquad
>  |A_H+P_{H,D}-z|>\varepsilon_{H,D}\quad\hbox{for every }z\in\mathbb{Z}.
> ```
> Then $`R_{2H}-R_H\notin\mathbb{Z}`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_not_integral_of_separation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L119)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.projectedForeignDefect_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L103)

```lean
theorem projectedForeignDefect_paper (H D : ℕ) :
    projectedForeignDefect H D =
      ∑ d ∈ Finset.Icc 1 D,
        (if d ∣ H then 0
          else foreignResidueKernel d (2 * H) - foreignResidueKernel d H)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.foreignComplementBound_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L110)

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
| `tailDifference_not_integral_of_separation` | [E249_18/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L223) | [PaperStatementsBK.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBK.lean#L23) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `projectedForeignDefect_paper` | [E249_18/Challenge.lean, line 196](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L196) | [PaperStatementsBE.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBE.lean#L46) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `foreignComplementBound_paper` | [E249_18/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L190) | [PaperStatementsBE.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsBE.lean#L41) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-coprime-pair-counting-totient"></a>

## Theorem 6.144 (Coprime-pair counting and the totient), page 66

> *For every $`n\in\mathbb N`$, $`\#\{(a,b)\in\mathbb N^2:a+b=n,\ a>0,\ \gcd(a,b)=1\}=\varphi(n)`$. Here $`b=0`$ is allowed: the boundary pair $`(1,0)`$ accounts for the value $`\varphi(1)=1`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.card_coprime_antidiagonal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L147)

```lean
theorem card_coprime_antidiagonal (n : ℕ) :
    ((Finset.antidiagonal n).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2)).card = Nat.totient n
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.boundary_pair_at_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PhaseEnergyAndForeignResidueProjection.lean#L154)

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
| `card_coprime_antidiagonal` | [E249_18/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L156) | [PaperStatementsAE.lean, line 183](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAE.lean#L183) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `boundary_pair_at_one` | [E249_18/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L149) | [PaperStatementsAE.lean, line 177](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAE.lean#L177) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-two-lattice-sums"></a>

## Proposition 6.145 (Two lattice sums), page 66

> *For $`0\le r<1`$, the two choices of boundary give
> ``` math
> \begin{aligned}
>  \sum_{\substack{a\ge1,\ b\ge0\\\gcd(a,b)=1}}r^{a+b}
>    &=\sum_{n\ge1}\varphi(n)r^n,\\
>  \sum_{\substack{a,b\ge1\\\gcd(a,b)=1}}r^{a+b}
>    &=\sum_{n\ge1}\varphi(n)r^n-r.
> \end{aligned}
> ```
> The removed pair is $`(1,0)`$. Partitioning all strictly positive pairs by their greatest common divisor gives
> ``` math
> \sum_{g\ge1}\ \sum_{\substack{a,b\ge1\\\gcd(a,b)=1}}
>        r^{g(a+b)}=\left(\frac r{1-r}\right)^2.
> ```
> This total is $`1`$ exactly when $`r=1/2`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_totient_pow_shift`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L27)

```lean
theorem tsum_totient_pow_shift {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, (Nat.totient n : ℝ) * r ^ n)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_halfOpen_sum`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L38)

```lean
theorem coprimeLattice_halfOpen_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_positive_sum`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L46)

```lean
theorem coprimeLattice_positive_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = (∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)) - r
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_removed_pair`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L53)

```lean
theorem coprimeLattice_removed_pair (a b : ℕ) :
    ((0 < a ∧ Nat.Coprime a b) ∧ ¬ (0 < a ∧ 0 < b ∧ Nat.Coprime a b))
      ↔ (a = 1 ∧ b = 0)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_gcd_layer_total`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L77)

```lean
theorem coprimeLattice_gcd_layer_total {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (r ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = (r / (1 - r)) ^ 2
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_gcd_layer_total_eq_one_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L84)

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
| `tsum_totient_pow_shift` | [E249_18/Challenge.lean, line 293](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L293) | [PaperStatementsAK.lean, line 78](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAK.lean#L78) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_halfOpen_sum` | [E249_18/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L255) | [PaperStatementsAJ.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L199) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_positive_sum` | [E249_18/Challenge.lean, line 280](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L280) | [PaperStatementsAJ.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L227) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_removed_pair` | [E249_18/Challenge.lean, line 285](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L285) | [PaperStatementsAJ.lean, line 231](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L231) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_gcd_layer_total` | [E249_18/Challenge.lean, line 237](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L237) | [PaperStatementsAJ.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L184) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_gcd_layer_total_eq_one_iff` | [E249_18/Challenge.lean, line 243](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L243) | [PaperStatementsAJ.lean, line 189](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L189) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-classical-coprime-pair-lambert-identity"></a>

## Theorem 6.146 (The classical coprime-pair Lambert identity), page 67

> *For every $`0\le r<1`$, $`\sum_{(a,b)\ \mathrm{coprime},\, a,b\ge 1}
> \dfrac{r^{a+b}}{1-r^{a+b}} = \Bigl(\dfrac{r}{1-r}\Bigr)^2`$, an elementary rational function of $`r`$, hence rational at every rational $`r`$ including $`r=1/2`$. This is the classical visible-point identity, and its Lean proof is a formalisation of it rather than a new result: writing each pair $`(A,B)`$ of positive integers uniquely as $`g\cdot(a,b)`$ with $`\gcd(a,b)=1`$ converts the quadrant sum $`\sum_{A,B\ge1}r^{A+B}=(r/(1-r))^2`$ into the displayed sum over visible points. With the plain weight $`r^{a+b}`$, the same strictly positive index set instead sums to $`\sum_{n\ge1}\varphi(n)r^n-r`$. Thus at $`r=1/2`$ the Lambert-weighted sum is $`1`$, whereas the plain-weight sum is $`S-1/2`$, not $`S`$. Adding the boundary pair $`(1,0)`$ recovers $`S`$ in the plain-weight sum.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_identity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L106)

```lean
theorem coprimeLattice_lambert_identity {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          r ^ (p.1 + p.2) / (1 - r ^ (p.1 + p.2)) else 0)
      = (r / (1 - r)) ^ 2
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_rational`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L114)

```lean
theorem coprimeLattice_lambert_rational (s : ℚ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ v : ℚ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          (s : ℝ) ^ (p.1 + p.2) / (1 - (s : ℝ) ^ (p.1 + p.2)) else 0)
      = (v : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_half_eq_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L127)

```lean
theorem coprimeLattice_lambert_half_eq_one :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          (1 / 2 : ℝ) ^ (p.1 + p.2) / (1 - (1 / 2 : ℝ) ^ (p.1 + p.2)) else 0) = 1
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_positive_sum`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L46)

```lean
theorem coprimeLattice_positive_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = (∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)) - r
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_plain_half_eq_series_sub_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L136)

```lean
theorem coprimeLattice_plain_half_eq_series_sub_half :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (1 / 2 : ℝ) ^ (p.1 + p.2) else 0)
        = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 ∧
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2
        ≠ ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_halfOpen_half_eq_series`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CoprimeLatticeSumsAndLambert.lean#L155)

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
| `coprimeLattice_lambert_identity` | [E249_18/Challenge.lean, line 266](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L266) | [PaperStatementsAJ.lean, line 208](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L208) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_lambert_rational` | [E249_18/Challenge.lean, line 273](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L273) | [PaperStatementsAJ.lean, line 214](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L214) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_lambert_half_eq_one` | [E249_18/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L260) | [PaperStatementsAJ.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L203) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_positive_sum` | [E249_18/Challenge.lean, line 280](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L280) | [PaperStatementsAJ.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L227) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |
| `coprimeLattice_plain_half_eq_series_sub_half` | [E249_19/Challenge.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L92) | [PaperStatementsAJ.lean, line 192](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L192) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `coprimeLattice_halfOpen_half_eq_series` | [E249_18/Challenge.lean, line 249](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_18/Challenge.lean#L249) | [PaperStatementsAJ.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_18/PaperStatementsAJ.lean#L194) | [E249_18](../../evidence/comparator/replay-35882032091/receipt-E249_18.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-nondivisors-short-lcm-window"></a>

## Theorem 6.149 (Nondivisors in a short LCM window), page 67

> *Let $`t\ge1`$. If $`1\le j<2t`$ and $`j\nmid H_t`$, then $`j=p^a>t`$ for a prime $`p`$ and an integer $`a\ge1`$. Every integer $`1\le j\le t`$ divides $`H_t`$. To see the first claim, some prime-power divisor $`p^a`$ of $`j`$ exceeds $`t`$; otherwise every prime-power divisor would divide $`H_t`$. Since $`j<2t<2p^a`$, its remaining cofactor is $`1`$.*
> 
> *If $`j\mid H_t`$ and every prime divisor of $`j`$ also divides $`H_t/j`$, then, for every integer $`q\ge0`$,
> ``` math
> \varphi(qH_t+j)=\varphi(j)\varphi\bigl(q(H_t/j)+1\bigr).
> ```
> Indeed, the second factor’s argument is coprime to $`j`$, so totient multiplicativity applies. The hypothesis is essential to this factorisation: at $`t=2`$, $`j=2`$, $`q=1`$ the left side is $`\varphi(4)=2`$ but the displayed product would be $`1`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.short_lcm_window_nondivisor`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L57)

```lean
theorem short_lcm_window_nondivisor (t j : ℕ) (ht : 1 ≤ t) (hj : 1 ≤ j)
    (hlt : j < 2 * t) (hnd : ¬ j ∣ periodLcm t) :
    ∃ p a : ℕ, Nat.Prime p ∧ 1 ≤ a ∧ j = p ^ a ∧ t < j
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.clean_lcm_ray_factorisation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L67)

```lean
theorem clean_lcm_ray_factorisation (t j q : ℕ) (hdvd : j ∣ periodLcm t)
    (hclean : ∀ p : ℕ, Nat.Prime p → p ∣ j → p ∣ (periodLcm t / j)) :
    q * periodLcm t + j = j * (q * (periodLcm t / j) + 1) ∧
    Nat.Coprime j (q * (periodLcm t / j) + 1) ∧
    Nat.totient (q * periodLcm t + j) = Nat.totient j * Nat.totient (q * (periodLcm t / j) + 1)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.unclean_lcm_ray_counterexample`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L76)

```lean
theorem unclean_lcm_ray_counterexample :
    2 ∣ periodLcm 2 ∧ Nat.totient (periodLcm 2 + 2) = 2 ∧
    Nat.totient 2 * Nat.totient (periodLcm 2 / 2 + 1) = 1 ∧
    ¬ (∀ p : ℕ, Nat.Prime p → p ∣ 2 → p ∣ (periodLcm 2 / 2))
```

4. [`Erdos249257.TotientTailPeriodKiller.dvd_periodLcm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CarrySurvivorExtinction.lean#L525)

```lean
lemma dvd_periodLcm {h t : ℕ} (h1 : 1 ≤ h) (ht : h ≤ t) : h ∣ periodLcm t
```

<a id="thm-nondivisors-short-lcm-window-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `short_lcm_window_nondivisor` | [E249_19/Challenge.lean, line 175](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L175) | [PaperStatementsAT.lean, line 248](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAT.lean#L248) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `clean_lcm_ray_factorisation` | [E249_09/Challenge.lean, line 196](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L196) | [PaperStatementsAT.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L174) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `unclean_lcm_ray_counterexample` | [E249_09/Challenge.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L233) | [PaperStatementsAT.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L241) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `dvd_periodLcm` | [E249_19/Challenge.lean, line 167](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L167) | [PaperStatementsA.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsA.lean#L73) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-unbounded-prime-support-mersenne-factors"></a>

## Theorem 6.151 (Unbounded prime support in Mersenne factors), page 68

> *Every prime divisor $`p`$ of $`2^q-1`$, for prime $`q`$, satisfies $`q\mid p-1`$ (the order of $`2`$ mod $`p`$ is exactly $`q`$, by Fermat/Lagrange in $`(\mathbb{Z}/p)^\times`$); consequently the prime divisors appearing in the layers $`\{2^n-1\}`$ are unbounded, unconditionally, with no cyclotomic resultant hypothesis left open.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_prime_divisor_order`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L33)

```lean
theorem mersenneLayer_prime_divisor_order {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hdvd : p ∣ 2 ^ q - 1) :
    orderOf ((2 : ℕ) : ZMod p) = q ∧ q ∣ p - 1
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_unbounded_prime_support`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L63)

```lean
theorem mersenneLayer_unbounded_prime_support (B N₀ : ℕ) :
    ∃ q p : ℕ, q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ 2 ^ q - 1 ∧ B < p
```

<a id="thm-unbounded-prime-support-mersenne-factors-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mersenneLayer_prime_divisor_order` | [E249_19/Challenge.lean, line 132](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L132) | [PaperStatementsAJ.lean, line 411](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L411) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `mersenneLayer_unbounded_prime_support` | [E249_19/Challenge.lean, line 137](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L137) | [PaperStatementsAJ.lean, line 415](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L415) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-prime-satisfying-stated-cyclotomic-conditions"></a>

## Theorem 6.152 (A prime satisfying the stated cyclotomic conditions), page 68

> *For every period $`h>0`$ and threshold $`N_0`$, there exist a prime $`q`$ and a prime factor $`p`$ of $`|\Phi_{hq}(2)|`$ (the binary cyclotomic layer) with $`p`$ coprime to $`hq`$, $`hq\mid p-1`$, and $`p-1\ge N_0`$. The characteristic-prime exceptional case in the cyclotomic order decomposition is eliminated directly, by choosing $`q>2^h`$ (rules out $`p=q`$) and $`q>h`$ (rules out $`p\mid h`$).*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_clean_cyclotomic_anchor_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L73)

```lean
theorem exists_clean_cyclotomic_anchor_paper (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ, q.Prime ∧ p.Prime ∧
      p ∣ ((Polynomial.cyclotomic (h * q) ℤ).eval 2).natAbs ∧
      Nat.Coprime p (h * q) ∧ h * q ∣ p - 1 ∧ N₀ ≤ p - 1
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_layer_prime_order_decomposition_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L84)

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
| `exists_clean_cyclotomic_anchor_paper` | [E249_19/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L120) | [PaperStatementsAJ.lean, line 270](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L270) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `cyclotomic_layer_prime_order_decomposition_paper` | [E249_19/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L104) | [PaperStatementsAJ.lean, line 217](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L217) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-sufficient-order-hypothesis-unbounded-prime"></a>

## Theorem 6.155 (A sufficient order hypothesis for unbounded prime support), page 68

> *Let $`C:\mathbb{N}\to\mathbb{N}`$, and fix integers $`m\ge1`$ and $`d\ge0`$. Suppose that for every pair of primes $`q,p`$ with $`p\mid C(mq)`$ there is an integer $`k`$ such that
> ``` math
> 1\le k\le d,\qquad mq\mid p^k-1.
> ```
> The divisibility forces $`\gcd(p,mq)=1`$. For such $`p`$, existence of $`k`$ in the displayed range is equivalent to $`\operatorname{ord}_{mq}(p)\le d`$. It also gives $`mq<p^d`$. Hence every fixed finite set of primes is disjoint from the prime divisors of $`C(mq)`$ for all sufficiently large prime $`q`$. If, in addition, for all sufficiently large prime $`q`$ one has $`C(mq)>1`$ and $`\gcd(C(mq),mq)=1`$, then for every $`B,N_0`$ there are primes $`q\ge N_0`$ and $`p>B`$ with $`p\mid C(mq)`$.*
> 
> *Indeed, the divisibility gives $`mq\le p^k-1<p^k\le p^d`$. For a finite set of primes, take $`q`$ larger than all their $`d`$-th powers; for the last assertion, take a prime divisor of the nontrivial value $`C(mq)`$ after this threshold. The stated coprimality is included in the formal source’s layer hypothesis, although this last extraction argument uses only $`C(mq)>1`$. For $`C(n)=2^n-1`$, the first theorem above supplies the hypothesis with $`m=d=1`$: here $`\operatorname{ord}_q(p)=1`$, whereas $`\operatorname{ord}_p(2)=q`$. For $`C(n)=|\Phi_n(2)|`$ and a general fixed $`m>0`$, the source uses the *eventual* version: the divisibility is required only for prime $`q`$ above a fixed threshold. The same proof then applies after that threshold. It is not valid to replace this by an all-prime assertion: $`\Phi_6(2)=3`$, but $`6\nmid3-1`$. For the binary cyclotomic family, choosing $`q>\max(m,2^m)`$ removes these exceptional indices. Other families require their own proof of the divisibility and nontriviality assumptions.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.boundedDegreeOrderConsumer_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L94)

```lean
theorem boundedDegreeOrderConsumer_unfolded (C : ℕ → ℕ) (m d : ℕ) :
    BoundedDegreeOrderConsumer C m d ↔
      ∀ q p : ℕ, q.Prime → p.Prime → p ∣ C (m * q) →
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.coprime_of_dvd_pow_sub_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L101)

```lean
theorem coprime_of_dvd_pow_sub_one {n p k : ℕ} (hp : 0 < p) (hk : 1 ≤ k)
    (hdvd : n ∣ p ^ k - 1) : Nat.Coprime p n
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.dvd_pow_sub_one_iff_orderOf_dvd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L113)

```lean
theorem dvd_pow_sub_one_iff_orderOf_dvd {n p k : ℕ} (hn : 0 < n) (hp : 0 < p) :
    n ∣ p ^ k - 1 ↔ orderOf ((p : ℕ) : ZMod n) ∣ k
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.boundedOrder_witness_iff_orderOf_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L136)

```lean
theorem boundedOrder_witness_iff_orderOf_le {n p d : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hcop : Nat.Coprime p n) :
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ n ∣ p ^ k - 1) ↔ orderOf ((p : ℕ) : ZMod n) ≤ d
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_index_lt_pow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L160)

```lean
theorem orderConsumer_index_lt_pow {C : ℕ → ℕ} {m d q p : ℕ}
    (horder : BoundedDegreeOrderConsumer C m d)
    (hq : q.Prime) (hp : p.Prime) (hpC : p ∣ C (m * q)) :
    m * q < p ^ d
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_finite_prime_escape`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L168)

```lean
theorem orderConsumer_finite_prime_escape {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m) (horder : BoundedDegreeOrderConsumer C m d) :
    ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_unbounded_prime_divisors`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L178)

```lean
theorem orderConsumer_unbounded_prime_divisors {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m)
    (hlayer : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q))
    (horder : BoundedDegreeOrderConsumer C m d) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.unbounded_prime_divisors_of_escape_of_nontrivial`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L190)

```lean
theorem unbounded_prime_divisors_of_escape_of_nontrivial {C : ℕ → ℕ} {m : ℕ}
    (hnontrivial : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q → 1 < C (m * q))
    (hescape : FinitePrimeSupportEscape C m) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_orderConsumer_instance`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L212)

```lean
theorem mersenneLayer_orderConsumer_instance :
    BoundedDegreeOrderConsumer (fun n => 2 ^ n - 1) 1 1 ∧
      ∀ q p : ℕ, q.Prime → p.Prime → p ∣ 2 ^ q - 1 →
        orderOf ((p : ℕ) : ZMod q) = 1 ∧ orderOf ((2 : ℕ) : ZMod p) = q
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.eventual_orderConsumer_conclusions`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L232)

```lean
theorem eventual_orderConsumer_conclusions {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m) (horder : EventualBoundedDegreeOrderConsumer C m d) :
    FinitePrimeSupportEscape C m ∧
      (∀ hsupply : PrimeRayLayerSupply C m, UnboundedPrimeDivisorSupply C m)
```

11. [`ErdosProblems.Erdos249.PaperCompleteR21.binaryCyclotomicLayer_eventual_instance`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L241)

```lean
theorem binaryCyclotomicLayer_eventual_instance (m : ℕ) (hm : 0 < m) :
    EventualBoundedDegreeOrderConsumer binaryCyclotomicLayer m 1
```

where [`EventualBoundedDegreeOrderConsumer`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PrimeRayCyclotomicCurvature.lean#L111) is

```lean
def EventualBoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q p : ℕ,
    q.Prime → Q₀ ≤ q → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1
```

12. [`ErdosProblems.Erdos249.PaperCompleteR21.binaryCyclotomic_allPrime_form_fails`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/MersennePrimeSupportAnchors.lean#L247)

```lean
theorem binaryCyclotomic_allPrime_form_fails :
    ((Polynomial.cyclotomic 6 ℤ).eval 2).natAbs = 3 ∧ ¬ (6 ∣ 3 - 1) ∧
      ¬ BoundedDegreeOrderConsumer binaryCyclotomicLayer 2 1
```

<a id="thm-sufficient-order-hypothesis-unbounded-prime-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `boundedDegreeOrderConsumer_unfolded` | [E249_19/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L81) | [PaperStatementsAJ.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L120) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `coprime_of_dvd_pow_sub_one` | [E249_19/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L100) | [PaperStatementsAJ.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L207) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `dvd_pow_sub_one_iff_orderOf_dvd` | [E249_19/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L110) | [PaperStatementsAJ.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L247) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `boundedOrder_witness_iff_orderOf_le` | [E249_19/Challenge.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L87) | [PaperStatementsAJ.lean, line 125](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L125) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `orderConsumer_index_lt_pow` | [E249_19/Challenge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L147) | [PaperStatementsAJ.lean, line 433](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L433) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `orderConsumer_finite_prime_escape` | [E249_19/Challenge.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L141) | [PaperStatementsAJ.lean, line 428](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L428) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `orderConsumer_unbounded_prime_divisors` | [E249_19/Challenge.lean, line 153](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L153) | [PaperStatementsAJ.lean, line 438](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L438) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `unbounded_prime_divisors_of_escape_of_nontrivial` | [E249_19/Challenge.lean, line 184](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L184) | [PaperStatementsAK.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAK.lean#L100) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `mersenneLayer_orderConsumer_instance` | [E249_19/Challenge.lean, line 126](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L126) | [PaperStatementsAJ.lean, line 406](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L406) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `eventual_orderConsumer_conclusions` | [E249_19/Challenge.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L114) | [PaperStatementsAJ.lean, line 265](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L265) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `binaryCyclotomicLayer_eventual_instance` | [E249_19/Challenge.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L72) | [PaperStatementsAJ.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L113) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `binaryCyclotomic_allPrime_form_fails` | [E249_19/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L76) | [PaperStatementsAJ.lean, line 116](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAJ.lean#L116) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-uniform-positive-gap-rank-one"></a>

## Theorem 6.156 (A uniform positive gap for rank-one quotients), page 69

> *For integers $`r\ge2`$ and $`Y\ge1`$, write
> ``` math
> \Theta_r=\sum_{d\ge1}\frac{\mu(d)}{(2^d-1)^r},
>  \qquad t(Y,r)=\sum_{d=1}^{Y}\frac{\mu(d)}{(2^d-1)^r}.
> ```
> For every $`e\ge1`$ and $`Y\ge4`$,
> ``` math
> \frac{t(Y,e+2)^2}{t(Y,2e+2)}-\Theta_2>\frac1{480}.
> ```
> Here $`\Theta_2=S-1/2`$. For $`r\ge3`$, the proof uses $`1429/1512\le\Theta_r<1`$ and $`|t(Y,r)-\Theta_r|\le1/3584`$ when $`Y\ge4`$. In particular, these inequalities make the denominator positive.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L238)

```lean
theorem rankOneSubrankQuotient_sub_theta_two_gt
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 480 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2
```

2. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersenneTheta_ge_alpha`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L163)

```lean
theorem mobiusMersenneTheta_ge_alpha
    {r : ℕ} (hr : 3 ≤ r) :
    (1429 : ℝ) / 1512 ≤ mobiusMersenneTheta r
```

3. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersenneTheta_lt_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L196)

```lean
theorem mobiusMersenneTheta_lt_one
    {r : ℕ} (hr : 3 ≤ r) :
    mobiusMersenneTheta r < 1
```

4. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.abs_mobiusMersenneTheta_sub_prefix_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L73)

```lean
theorem abs_mobiusMersenneTheta_sub_prefix_le
    {Y r : ℕ} (hY : 4 ≤ Y) (hr : 3 ≤ r) :
    |mobiusMersenneTheta r - mobiusMersennePrefix Y r| ≤
      (1 : ℝ) / 3584
```

5. [`Erdos249257.SignedQMomentObstruction.mobiusMersenneTheta_two_eq_totient_offset`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/SignedQMomentObstruction.lean#L214)

```lean
theorem mobiusMersenneTheta_two_eq_totient_offset :
    mobiusMersenneTheta 2 =
      (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) *
        ((1 : ℝ) / 2) ^ (n : ℕ)) - 1 / 2
```

6. [`ErdosProblems.Erdos249.PaperCompleteR7.rankOne_denominator_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR7/ShortNoteAssemblies.lean#L58)

```lean
theorem rankOne_denominator_pos {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    0 < mobiusMersennePrefix Y (2 * e + 2)
```

<a id="thm-uniform-positive-gap-rank-one-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rankOneSubrankQuotient_sub_theta_two_gt` | [E249_19/Challenge.lean, line 234](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L234) | [PaperStatementsBG.lean, line 78](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsBG.lean#L78) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `mobiusMersenneTheta_ge_alpha` | [E249_19/Challenge.lean, line 224](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L224) | [PaperStatementsBG.lean, line 45](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsBG.lean#L45) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `mobiusMersenneTheta_lt_one` | [E249_19/Challenge.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L229) | [PaperStatementsBG.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsBG.lean#L49) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `abs_mobiusMersenneTheta_sub_prefix_le` | [E249_19/Challenge.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L218) | [PaperStatementsBG.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsBG.lean#L40) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `mobiusMersenneTheta_two_eq_totient_offset` | [E249_19/Challenge.lean, line 198](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_19/Challenge.lean#L198) | [PaperStatementsAF.lean, line 19](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_19/PaperStatementsAF.lean#L19) | [E249_19](../../evidence/comparator/replay-35882032091/receipt-E249_19.json) |
| `rankOne_denominator_pos` | [E249_20/Challenge.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_20/Challenge.lean#L37) | [PaperStatementsO.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_20/PaperStatementsO.lean#L39) | [E249_20](../../evidence/comparator/replay-35882032091/receipt-E249_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-bound-preserved-positive-normalised-averaging"></a>

## Proposition 6.157 (The bound is preserved by positive normalised averaging), page 69

> *For a nonempty finite family of admissible quotients with positive weights summing to $`1`$, the weighted average still exceeds $`\Theta_2`$ by more than $`1/480`$. If an admissible quotient is $`p/q`$ in lowest terms, with $`q>0`$, then $`|q\Theta_2-p|>q/480`$.*

The Lean declarations below together state a result at least as strong as this one. The Lean average bound holds for any positive weights, dividing the weighted sum by the total weight, so the printed case of weights summing to $1$ follows; the Lean bound $|q\Theta_2-p|>q/480$ holds for every representation of an admissible quotient as $p/q$ with $q\ge1$, of which lowest terms is a case.

1. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.positive_direct_sum_sub_theta_two_gt`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L300)

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

2. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.primitive_form_abs_gt`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSubrankObstruction.lean#L341)

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
| `positive_direct_sum_sub_theta_two_gt` | [E249_21/Challenge.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L64) | [PaperStatementsBG.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsBG.lean#L52) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `primitive_form_abs_gt` | [E249_21/Challenge.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L77) | [PaperStatementsBG.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsBG.lean#L65) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-concatenation-specified-period-multiples"></a>

## Theorem 6.159 (Concatenation and specified period multiples), page 70

> *For nonnegative integers $`a,b,N`$, define the integer block sum
> ``` math
> Q_{a,N}=\sum_{j=1}^{a}\varphi(N+j)2^{a-j}.
> ```
> Splitting a block after its first $`a`$ terms gives
> ``` math
> Q_{a+b,N}=2^bQ_{a,N}+Q_{b,N+a}.
> ```
> In particular, $`Q_{2h,N}=2^hQ_{h,N}+Q_{h,N+h}`$. The corresponding cyclotomic identity is $`\Phi_4(2^h)=2^{2h}+1=\Phi_2(2^{2h})`$: the order-four factor at height $`h`$ is the order-two factor at height $`2h`$.*
> 
> *The order-three factor is different: $`\Phi_3(2^h)=2^{2h}+2^h+1`$ comes from tripling the period. It is not generally part of the doubling sequence. For example, $`\Phi_3(2)=7`$ divides none of $`2^{2^j}-1`$, because the order of $`2`$ modulo $`7`$ is $`3`$, which does not divide $`2^j`$. Thus the block identities relate specified period multiples; they do not put all the order-two, order-three and order-four factors into one doubling chain.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_eq_paper_indexed_sum`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L23)

```lean
theorem totientBlock_eq_paper_indexed_sum (a N : ℕ) :
    totientBlock a N
      = ∑ j ∈ Finset.Icc 1 a, (Nat.totient (N + j) : ℤ) * 2 ^ (a - j)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_concatenation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L41)

```lean
theorem totientBlock_concatenation (a b N : ℕ) :
    totientBlock (a + b) N = 2 ^ b * totientBlock a N + totientBlock b (N + a)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_doubling`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L46)

```lean
theorem totientBlock_doubling (h N : ℕ) :
    totientBlock (2 * h) N = 2 ^ h * totientBlock h N + totientBlock h (N + h)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_four_eval`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L53)

```lean
theorem cyclotomic_four_eval (x : ℤ) :
    (Polynomial.cyclotomic 4 ℤ).eval x = x ^ 2 + 1
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_four_two_pow_eq_cyclotomic_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L64)

```lean
theorem cyclotomic_four_two_pow_eq_cyclotomic_two (h : ℕ) :
    (Polynomial.cyclotomic 4 ℤ).eval ((2 : ℤ) ^ h) = 2 ^ (2 * h) + 1 ∧
      (Polynomial.cyclotomic 2 ℤ).eval ((2 : ℤ) ^ (2 * h)) = 2 ^ (2 * h) + 1
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_three_two_pow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L73)

```lean
theorem cyclotomic_three_two_pow (h : ℕ) :
    (Polynomial.cyclotomic 3 ℤ).eval ((2 : ℤ) ^ h) = 2 ^ (2 * h) + 2 ^ h + 1
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.orderOf_two_mod_seven`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L83)

```lean
theorem orderOf_two_mod_seven : orderOf ((2 : ℕ) : ZMod 7) = 3
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.three_not_dvd_two_pow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L92)

```lean
theorem three_not_dvd_two_pow (j : ℕ) : ¬ (3 ∣ 2 ^ j)
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_three_eval_two_not_dvd_doubling_chain`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TotientBlockConcatenation.lean#L100)

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
| `totientBlock_eq_paper_indexed_sum` | [E249_21/Challenge.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L128) | [PaperStatementsG.lean, line 126](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsG.lean#L126) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `totientBlock_concatenation` | [E249_21/Challenge.lean, line 116](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L116) | [PaperStatementsAJ.lean, line 508](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L508) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `totientBlock_doubling` | [E249_21/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L120) | [PaperStatementsAJ.lean, line 511](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L511) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `cyclotomic_four_eval` | [E249_21/Challenge.lean, line 90](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L90) | [PaperStatementsAJ.lean, line 235](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L235) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `cyclotomic_four_two_pow_eq_cyclotomic_two` | [E249_21/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L94) | [PaperStatementsAJ.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L238) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `cyclotomic_three_two_pow` | [E249_21/Challenge.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L106) | [PaperStatementsAJ.lean, line 253](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L253) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `orderOf_two_mod_seven` | [E249_21/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L110) | [PaperStatementsAJ.lean, line 471](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L471) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `three_not_dvd_two_pow` | [E249_21/Challenge.lean, line 113](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L113) | [PaperStatementsAJ.lean, line 506](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L506) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |
| `cyclotomic_three_eval_two_not_dvd_doubling_chain` | [E249_21/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_21/Challenge.lean#L99) | [PaperStatementsAJ.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_21/PaperStatementsAJ.lean#L247) | [E249_21](../../evidence/comparator/replay-35882032091/receipt-E249_21.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
