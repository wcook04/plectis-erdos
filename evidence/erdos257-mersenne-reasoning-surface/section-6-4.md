# Formal evidence: Reciprocal Mersenne Subseries, Section 6, results 6.106 to 6.146

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="record-257bm-i-mob"></a>

## Theorem 6.106 (Möbius inversion of the divisor counts), page 71

> *For a set $`A\subseteq\mathbb{N}`$ and each positive integer $`n`$,
> ``` math
> \sum_{d\mid n}\mu(d)c_A(n/d)=\mathbf1_A(n),
> ```
> where $`\mu`$ is the Möbius function and $`c_A(n)`$ counts the positive elements of $`A`$ dividing $`n`$. Thus the divisor counts determine the positive support exactly. In particular their Möbius transform takes only the values $`0`$ and $`1`$. The identity does not depend on a base.*
> 
> *<span class="sans-serif">(uniform)</span> *mobius-inversion* [`moebius_mul_supportCoeffAF`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L95) [`mobius_supportCoeff_boolean`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L118) [`card_divisors_le_two_mul_sqrt`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L209)*

The Lean declarations below together state a result at least as strong as this one. The Lean statements have the same hypotheses and conclusions as the printed ones, with the identity written as the Dirichlet convolution $\mu*c_A=\mathbf 1_A$ on the positive integers. Separate statements give that the transform equals $1$ exactly on $A$ and takes only the values $0$ and $1$.

1. [`Erdos249257.moebius_mul_supportCoeffAF`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCarry.lean#L95)

```lean
theorem moebius_mul_supportCoeffAF (A : Set ℕ) :
    ArithmeticFunction.moebius * supportCoeffAF A = positiveSupportBitAF A
```

2. [`Erdos249257.mobius_supportCoeff_eq_one_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCarry.lean#L112)

```lean
theorem mobius_supportCoeff_eq_one_iff (A : Set ℕ) {n : ℕ} (hn : 0 < n) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 ↔ n ∈ A
```

3. [`Erdos249257.mobius_supportCoeff_boolean`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCarry.lean#L118)

```lean
theorem mobius_supportCoeff_boolean (A : Set ℕ) (n : ℕ) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 0 ∨
      (ArithmeticFunction.moebius * supportCoeffAF A) n = 1
```

<a id="record-257bm-i-mob-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `moebius_mul_supportCoeffAF` | [E257_29/Challenge.lean, line 231](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L231) | [PaperStatementsAU.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAU.lean#L46) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `mobius_supportCoeff_eq_one_iff` | [E257_29/Challenge.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L227) | [PaperStatementsAU.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAU.lean#L43) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `mobius_supportCoeff_boolean` | [E257_29/Challenge.lean, line 222](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L222) | [PaperStatementsAU.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAU.lean#L39) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i-bridge"></a>

## Theorem 6.107 (The support series as a coefficient series), page 71

> *For $`A\subseteq\mathbb{N}_{>0}`$,
> ``` math
> X_A(2)=\sum_{a\in A}\frac1{2^a-1}
>        =\sum_{n\ge1}\frac{c_A(n)}{2^n}.
> ```
> Expanding each denominator as a geometric series and interchanging nonnegative sums gives the identity. Since $`c_A(n)\le\tau(n)\le n`$, Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a> applies. Together with Theorem <a href="#record:257bm-i-mob" data-reference-type="ref" data-reference="record:257bm-i-mob">149</a>, it expresses rationality through an integer recurrence whose coefficients all come from the same support.*
> 
> *<span class="sans-serif">(uniform)</span> *divisor counts and finite sums* [`erdosSupportSeries_two_eq_binaryCoeffSeries`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L377) [`erdosSupportSeries_rational_iff_exists_temperedCarry`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L384)*

The Lean declarations below together state a result at least as strong as this one. The Lean statements have the same hypotheses and conclusions as the printed ones, for every set $A\subseteq\mathbb N$; an element $0$ contributes to neither side. They also give $c_A(n)\le\tau(n)$, $c_A(n)\le n$, and the resulting criterion that $X_A(2)$ is rational exactly when, for some positive integer $v$, the recurrence $u(N+1)=2u(N)-v\,c_A(N+1)$ has an integer solution with $u(N)/2^N\to0$.

1. [`Erdos249257.erdosSupportSeries_two_eq_binaryCoeffSeries`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCarry.lean#L377)

```lean
theorem erdosSupportSeries_two_eq_binaryCoeffSeries (A : Set ℕ) :
    erdosSupportSeries 2 A = binaryCoeffSeries (supportCoeff A)
```

2. [`Erdos249257.supportCoeff_le_card_divisors`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L8860)

```lean
theorem supportCoeff_le_card_divisors (A : Set ℕ) (n : ℕ) :
    supportCoeff A n ≤ n.divisors.card
```

3. [`Erdos249257.supportCoeff_le_self`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L8868)

```lean
theorem supportCoeff_le_self (A : Set ℕ) (n : ℕ) : supportCoeff A n ≤ n
```

4. [`Erdos249257.erdosSupportSeries_rational_iff_exists_temperedCarry`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCarry.lean#L384)

```lean
theorem erdosSupportSeries_rational_iff_exists_temperedCarry (A : Set ℕ) :
    HasRationalValue (erdosSupportSeries 2 A) ↔
      ∃ q : ℕ, 0 < q ∧ ∃ U : ℕ → ℤ,
        IsTemperedBinaryOrbit (supportCoeff A) q U
```

<a id="record-257bm-i-bridge-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `erdosSupportSeries_two_eq_binaryCoeffSeries` | [E257_29/Challenge.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L218) | [PaperStatementsAU.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAU.lean#L36) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `supportCoeff_le_card_divisors` | [E257_29/Challenge.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L241) | [PaperStatementsAG.lean, line 125](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAG.lean#L125) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `supportCoeff_le_self` | [E257_29/Challenge.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L245) | [PaperStatementsAG.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAG.lean#L128) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `erdosSupportSeries_rational_iff_exists_temperedCarry` | [E257_29/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L212) | [PaperStatementsAU.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAU.lean#L31) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-i2"></a>

## Theorem 6.108 (A restriction on dyadic rational values), page 72

> *If an infinite support $`A\subseteq\mathbb{N}_{>0}`$ has $`X_A(2)=p/2^c`$ for integers $`p`$ and $`c\ge0`$, then $`\sum_{a\in A}1/a`$ either diverges or converges to a value greater than $`1`$. The cited proof averages the shifted integer recurrence and uses a common multiple of two distinct support elements. Thus a convergent reciprocal sum of at most $`1`$ is excluded. This is a separate necessary condition: the reciprocal-summable criterion proved earlier already excludes every support with a convergent reciprocal sum, not just those whose sum is at most $`1`$.*
> 
> *<span class="sans-serif">(uniform)</span> *cesaro-tail* [`dyadic_support_fraction_reciprocalMass_diverges_or_gt_one`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2210) [`one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2124)*

The Lean declarations below together state a result at least as strong as this one. The first Lean statement replaces infinitude by the presence of two distinct positive elements of $A$: if $X_A(2)=p/2^c$ and $\sum_{a\in A}1/a$ converges, then $\sum_{a\in A}1/a>1$; the printed statement for infinite $A$ is the second Lean statement.

1. [`Erdos249257.one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RationalSupportCarrySkeleton.lean#L2124)

```lean
theorem one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    1 < reciprocalMass A
```

2. [`Erdos249257.dyadic_support_fraction_reciprocalMass_diverges_or_gt_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RationalSupportCarrySkeleton.lean#L2210)

```lean
theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A
```

<a id="record-257rig-i2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem` | [E257_29/Challenge.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L283) | [PaperStatementsAV.lean, line 55](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAV.lean#L55) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |
| `dyadic_support_fraction_reciprocalMass_diverges_or_gt_one` | [E257_29/Challenge.lean, line 262](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L262) | [PaperStatementsAV.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAV.lean#L23) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-i3"></a>

## Theorem 6.109 (Unboundedness of a positive shifted recurrence), page 72

> *Let $`A\subseteq\mathbb{N}_{>0}`$ be infinite, fix a shift $`c\ge0`$ and a positive integer $`v`$, and let $`u`$ be a positive integer sequence satisfying
> ``` math
> u(n+1)+v c_A(c+n+1)=2u(n)\qquad(n\ge0).
> ```
> Then $`u`$ is unbounded. Indeed, under a proposed bound $`u(n)\le B`$, choose $`2B+1`$ distinct support elements and a common multiple larger than $`c`$. At the corresponding index the divisor count is at least $`2B+1`$, contradicting the recurrence. This does not conflict with Theorem <a href="#record:257bm-i-t7" data-reference-type="ref" data-reference="record:257bm-i-t7">148</a>, whose condition is $`u(n)/2^n\to0`$, not boundedness. An unbounded sequence can still satisfy that limit.*
> 
> *<span class="sans-serif">(uniform)</span> *common-multiple-forcing* [`shifted_state_unbounded_of_infinite_support`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2327) [`exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2383) [`one_add_mul_card_le_two_mul_shifted_state`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalSupportCarrySkeleton.lean#L2237)*

The Lean declarations below together state a result at least as strong as this one. The unboundedness of $u$ is the second Lean statement as printed; the Lean statements add the quantitative bound $1+v\,|F|\le2u(L-c-1)$ for every finite $F\subseteq A$ whose elements divide some $L>c$, which drives the proof, and, whenever $X_A(2)=p/(2^cv)$, the existence of such a positive unbounded sequence, $u(n)=v\sum_{r\ge1}c_A(c+n+r)2^{-r}$.

1. [`Erdos249257.one_add_mul_card_le_two_mul_shifted_state`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RationalSupportCarrySkeleton.lean#L2237)

```lean
theorem one_add_mul_card_le_two_mul_shifted_state
    (A : Set ℕ) (F : Finset ℕ) (c v L : ℕ) (u : ℕ → ℕ)
    (hcL : c < L) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n)
    (hFA : ∀ a ∈ F, a ∈ A) (hFdvd : ∀ a ∈ F, a ∣ L) :
    1 + v * F.card ≤ 2 * u (L - c - 1)
```

2. [`Erdos249257.shifted_state_unbounded_of_infinite_support`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RationalSupportCarrySkeleton.lean#L2327)

```lean
theorem shifted_state_unbounded_of_infinite_support
    (A : Set ℕ) (hAinf : A.Infinite) (c v : ℕ) (hv : 0 < v)
    (u : ℕ → ℕ) (hpos : ∀ n : ℕ, 0 < u n)
    (hrec : ∀ n : ℕ,
      u (n + 1) + v * supportCoeff A (c + n + 1) = 2 * u n) :
    ∀ B : ℕ, ∃ n : ℕ, B < u n
```

3. [`Erdos249257.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RationalSupportCarrySkeleton.lean#L2383)

```lean
theorem exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      (∀ B : ℕ, ∃ n : ℕ, B < u n)
```

<a id="record-257rig-i3-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `one_add_mul_card_le_two_mul_shifted_state` | [E257_30/Challenge.lean, line 53](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L53) | [PaperStatementsAV.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAV.lean#L59) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `shifted_state_unbounded_of_infinite_support` | [E257_30/Challenge.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L62) | [PaperStatementsAV.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAV.lean#L76) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction` | [E257_29/Challenge.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_29/Challenge.lean#L269) | [PaperStatementsAV.lean, line 29](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_29/PaperStatementsAV.lean#L29) | [E257_29](../../evidence/comparator/replay-35882032091/receipt-E257_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-i4a"></a>

## Theorem 6.110 (Bounds for intervals with zero divisor counts), page 72

> *Suppose that $`X_A(2)=p/(2^cv)`$ for an infinite positive support $`A`$ and an odd positive integer $`v`$. For every $`\varepsilon>0`$ there is $`B`$ such that, for $`N\ge1`$, a run of $`h`$ zero divisor counts starting after $`c+N`$ satisfies $`h\le\varepsilon\log_2N+B`$. In fact this conclusion holds without rationality: fix any $`a\in A`$. Every $`a`$ consecutive positive integers include a multiple of $`a`$, where $`c_A`$ is positive. Hence $`h\le a-1`$, so one can take $`B=a-1`$. The zero-run conclusion therefore imposes no additional restriction on a fixed nonempty support, regardless of the tail estimates used in the linked proof.*
> 
> *<span class="sans-serif">(uniform)</span> *divisor-envelope* [`supportCoeffZeroWindow_length_le_eps_logb`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SublogDivisorCoverage.lean#L435)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_eps_logb`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L219)

```lean
theorem paper_zero_run_le_eps_logb
    (A : Set ℕ) (hinf : A.Infinite) (hzero : 0 ∉ A)
    (p : ℤ) (c v : ℕ) (hv : 0 < v) (_hvodd : Odd v)
    (hvalue : erdosSupportSeries 2 A = (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ N h : ℕ, 1 ≤ N →
        SupportCoeffZeroWindow A (c + N) h →
        (h : ℝ) ≤ ε * Real.logb 2 (N : ℝ) + B
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_zero_run_le_of_mem`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L237)

```lean
theorem paper_zero_run_le_of_mem
    (A : Set ℕ) {a : ℕ} (hapos : 0 < a) (haA : a ∈ A) {N h : ℕ}
    (hwindow : SupportCoeffZeroWindow A N h) :
    h ≤ a - 1
```

<a id="record-257rig-i4a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_zero_run_le_eps_logb` | [E257_30/Challenge.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L86) | [PaperStatementsAL.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAL.lean#L62) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_zero_run_le_of_mem` | [E257_30/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L97) | [PaperStatementsAL.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAL.lean#L73) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-i4b"></a>

## Proposition 6.111 (A subpower bound for divisor counts), page 72

> *For positive integers $`n,k`$, $`\tau(n)^k \le (k^{2^k})^k\cdot n`$, or equivalently $`\tau(n)\le k^{2^k}n^{1/k}`$. The constant absorbs the finitely many primes below $`2^k`$; for larger primes, $`(\nu+1)^k\le p^\nu`$ controls each factor of the divisor product. This estimate is independent of the support problem. The elementary zero-run bound above already follows from a single positive support element, without this estimate or a recurrence.*
> 
> *<span class="sans-serif">(uniform)</span> *divisor-envelope* [`card_divisors_pow_le_divisorSubpowerConst_pow_mul`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SublogDivisorCoverage.lean#L107)*

The Lean declarations below together state a result at least as strong as this one. The Lean statements have the same hypotheses and conclusions as the printed ones, with the constant $k^{2^k}$; the second form also holds at $n=0$.

1. [`Erdos249257.card_divisors_pow_le_divisorSubpowerConst_pow_mul`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/SublogDivisorCoverage.lean#L107)

```lean
theorem card_divisors_pow_le_divisorSubpowerConst_pow_mul
    (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k) :
    n.divisors.card ^ k ≤ divisorSubpowerConst k ^ k * n
```

2. [`Erdos249257.card_divisors_le_divisorSubpowerConst_mul_rpow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/SublogDivisorCoverage.lean#L142)

```lean
theorem card_divisors_le_divisorSubpowerConst_mul_rpow
    (n k : ℕ) (hk : 1 ≤ k) :
    (n.divisors.card : ℝ) ≤
      (divisorSubpowerConst k : ℝ) *
        (n : ℝ) ^ ((k : ℝ)⁻¹)
```

<a id="record-257rig-i4b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `card_divisors_pow_le_divisorSubpowerConst_pow_mul` | [E257_30/Challenge.lean, line 116](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L116) | [PaperStatementsAF.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAF.lean#L32) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `card_divisors_le_divisorSubpowerConst_mul_rpow` | [E257_30/Challenge.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L109) | [PaperStatementsAF.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAF.lean#L26) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-i5"></a>

## Proposition 6.112 (Two distinct prime-power differences commute), page 72

> *Lemma <a href="#lem:mixed-prime-power-layer" data-reference-type="ref" data-reference="lem:mixed-prime-power-layer">100</a> gives the four-term expansion and its divisor-count interpretation. Commutation is elementary for arbitrary positive multipliers. The extraction formula uses distinct primes, *positive* exponents $`e,f`$ and $`\gcd(n,pq)=1`$. The example $`A=\{12\}`$ shows the extracted coefficient explicitly. No rationality statement about multiplicative subsequences follows from commutation alone.*
> 
> *<span class="sans-serif">(uniform)</span> *mobius-inversion* [`mixedPrimePowerLayerTwo_supportCoeffInt`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MaximalOmegaLayer.lean#L39) [`primePowerLayer_comm`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MaximalOmegaLayer.lean#L29)*

The Lean declarations below together state this result.

1. [`Erdos249257.MaximalOmegaLayer.primePowerLayer_comm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MaximalOmegaLayer.lean#L29)

```lean
theorem primePowerLayer_comm
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) :
    primePowerLayer q f (primePowerLayer p e g) n =
      primePowerLayer p e (primePowerLayer q f g) n
```

2. [`Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_supportCoeffInt`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MaximalOmegaLayer.lean#L39)

```lean
theorem mixedPrimePowerLayerTwo_supportCoeffInt
    (A : Set ℕ) {p e q f n : ℕ}
    (hp : p.Prime) (he : 0 < e) (hq : q.Prime) (hf : 0 < f)
    (hpq : p ≠ q) (hn : n.Coprime (p * q)) :
    mixedPrimePowerLayerTwo p e q f (supportCoeffInt A) n =
      supportCoeffInt
        (exactPrimePowerPullback q f (exactPrimePowerPullback p e A)) n
```

3. [`Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo_twelve_fixture`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MaximalOmegaLayer.lean#L65)

```lean
theorem mixedPrimePowerLayerTwo_twelve_fixture :
    mixedPrimePowerLayerTwo 2 2 3 1
      (supportCoeffInt ({12} : Set ℕ)) 1 = 1
```

<a id="record-257rig-i5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `primePowerLayer_comm` | [E257_21/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L180) | [PaperStatementsAA.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAA.lean#L75) | [E257_21](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `mixedPrimePowerLayerTwo_supportCoeffInt` | [E257_21/Challenge.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_21/Challenge.lean#L220) | [PaperStatementsAO.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_21/PaperStatementsAO.lean#L22) | [E257_21](../../evidence/comparator/replay-35882032091/receipt-E257_21.json) |
| `mixedPrimePowerLayerTwo_twelve_fixture` | [E257_30/Challenge.lean, line 138](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L138) | [PaperStatementsAO.lean, line 33](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAO.lean#L33) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i-cross2"></a>

## Theorem 6.114 (Existence of a first crossing), page 73

> *Let $`E\subseteq\{2,3,\ldots\}`$ be finite and suppose $`X_E(2)>1/2`$. There is a least $`c\in E`$ such that
> ``` math
> X_{E\cap[2,c)}(2)<\frac12
>        <X_{E\cap[2,c]}(2),\qquad c\ge4.
> ```
> Positivity of the summands makes the partial sums increasing. Their odd reduced denominators exclude equality with $`1/2`$, so the first crossing is strict on both sides. Finally $`w_2+w_3=10/21<1/2`$, which excludes a crossing before rank $`4`$. This is the finite crossing data used in the later exact-row constructions; the lower bound on $`c`$ and strictness are specific to these weights.*
> 
> *<span class="sans-serif">(uniform)</span> *binary digits* [`exists_first_localMersenne_crossing`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowCrossing.lean#L31)*

The Lean declaration below states this result.

[`Erdos249257.exists_first_localMersenne_crossing`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusExactRowCrossing.lean#L31)

```lean
theorem exists_first_localMersenne_crossing
    {E : Finset ℕ}
    (hE : ∀ d ∈ E, 2 ≤ d)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ,
      c ∈ E ∧
      4 ≤ c ∧
      localMersennePrefixValue (E.filter fun d ↦ d < c) < (1 / 2 : ℚ) ∧
      (1 / 2 : ℚ) <
        localMersennePrefixValue (insert c (E.filter fun d ↦ d < c))
```

<a id="record-257bm-i-cross2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_first_localMersenne_crossing` | [E257_30/Challenge.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L158) | [PaperStatementsAR.lean, line 151](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAR.lean#L151) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-i6"></a>

## Theorem 6.115 (Nonnegative centred carries below the half-value), page 73

> *If $`1\notin A`$ and $`X_A(2)<1/2`$, then
> ``` math
> C_A(N)=\operatorname{ihc}(A,N)-1\ge0\qquad(N\ge0).
> ```
> Indeed, Lemma <a href="#lem:collapse-mech" data-reference-type="ref" data-reference="lem:collapse-mech">15</a> gives
> ``` math
> \operatorname{ihc}(A,N)
>  =2^{N+1}\bigl(1/2-X_A(2)\bigr)
>      +\sum_{r\ge1}c_A(N+1+r)2^{-r}>0.
> ```
> The first term is strictly positive and the tail is nonnegative. Since the half-carry is an integer, it is at least $`1`$; subtracting $`1`$ proves the centred bound. Nonnegativity alone, without this strictness and integrality step, would only give $`C_A(N)\ge-1`$. The argument supplies the lower bound used with the conditional upper bound in Theorem <a href="#record:257rig-c16" data-reference-type="ref" data-reference="record:257rig-c16">127</a>.*
> 
> *<span class="sans-serif">(uniform)</span> *mobius-centred-carry* [`integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L871) [`mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L94)*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfCarryReachability.integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCarryReachability.lean#L871)

```lean
theorem integerHalfCarry_eq_scaled_residual_add_tail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (integerHalfCarry A N : ℝ) =
      (2 : ℝ) ^ (N + 1) * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) +
        binaryCoeffTail (supportCoeff A) (N + 1)
```

2. [`Erdos249257.mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L94)

```lean
theorem mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half
    (A : Set ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry A N
```

<a id="record-257hg-i6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `integerHalfCarry_eq_scaled_residual_add_tail` | [E257_03/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L99) | [PaperStatementsE.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsE.lean#L35) | [E257_03](../../evidence/comparator/replay-35882032091/receipt-E257_03.json) |
| `mobiusCenteredHalfCarry_nonneg_of_supportSeries_lt_half` | [E257_13/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_13/Challenge.lean#L111) | [PaperStatementsI.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_13/PaperStatementsI.lean#L34) | [E257_13](../../evidence/comparator/replay-35882032091/receipt-E257_13.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-i7"></a>

## Theorem 6.116 (Three possibilities at a skipped endpoint), page 73

> *For a rank $`s\ge5`$ omitted by the real greedy support, let $`H_s`$ and $`f_s`$ be as in Lemma <a href="#lem:skipped-endpoint-trichotomy" data-reference-type="ref" data-reference="lem:skipped-endpoint-trichotomy">88</a>. That lemma identifies the actual prefix as $`D_s`$ when $`f_s\le0`$ and as $`B_s`$ when $`f_s>0`$, with the exact remainder or overshoot in each case. To obtain the nonnegative-margin condition in Definition <a href="#record:257bm-c13" data-reference-type="ref" data-reference="record:257bm-c13">124</a>, the negative case would still have to be excluded at every required skipped rank. The trichotomy itself does not exclude it. In particular, the value $`-3`$ excluded for $`C_D`$ under the all-right-tail hypothesis of Theorem <a href="#thm:final-middle-cell" data-reference-type="ref" data-reference="thm:final-middle-cell">87</a> is not an exclusion for $`f_s`$: the coordinates and the hypotheses are different.*
> 
> *<span class="sans-serif">(uniform)</span> *frozen-margin* [`halfGreedy_skipped_endpoint_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L246)*

The Lean declaration below states this result.

[`Erdos249257.halfGreedy_skipped_endpoint_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderSkippedEndpointClassifier.lean#L246)

```lean
theorem halfGreedy_skipped_endpoint_trichotomy
    (s : ℕ) (hs : 5 ≤ s)
    (hskip : ¬ mersenneWeight s ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (s - 1)) :
    (greedyHalfFrozenMargin (s - 1) s < 0 ∧
        halfActualSeamWord s = seamGreedyWord s ∧
        1 ≤ seamIntegerGreedyRemainder s ∧
        greedyHalfFrozenMargin (s - 1) s =
          -(seamIntegerGreedyRemainder s : ℤ)) ∨
      (greedyHalfFrozenMargin (s - 1) s = 0 ∧
        halfActualSeamWord s = seamGreedyWord s ∧
        seamIntegerGreedyRemainder s = 0) ∨
      (0 < greedyHalfFrozenMargin (s - 1) s ∧
        halfActualSeamWord s = seamAboveWord s hs ∧
        greedyHalfFrozenMargin (s - 1) s =
          ((seamAdjacentCut s hs).overshoot : ℤ))
```

<a id="record-257hg-i7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `halfGreedy_skipped_endpoint_trichotomy` | [E257_16/Challenge.lean, line 316](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_16/Challenge.lean#L316) | [PaperStructuresBI.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_16/PaperStructuresBI.lean#L264) | [E257_16](../../evidence/comparator/replay-35882032091/receipt-E257_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-i2"></a>

## Theorem 6.118 (The unweighted sum of remaining gap lengths), page 74

> *For every $`N\ge0`$, the unweighted sum of gap lengths satisfies
> ``` math
> \sum_{n>N}g_n\le\frac29\,4^{-N}+\frac37\,8^{-N},
> ```
> which tends to zero. The estimate follows by summing the per-level bound; it counts one length per level. It does not, by itself, bound the measure of the union of all gaps, because there are $`2^{n-1}`$ disjoint translated gaps at level $`n`$.*
> 
> *<span class="sans-serif">(uniform)</span> *summed-gap-mass* [`summable_mersenneGap_shift`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGapMass.lean#L69) [`mersenneGap_tail_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGapMass.lean#L83) [`tendsto_mersenneGap_tail_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGapMass.lean#L104) [`mersenneGap_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGapMass.lean#L40)*

The Lean declarations below together state this result.

1. [`Erdos249257.mersenneGap_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGapMass.lean#L40)

```lean
theorem mersenneGap_le {n : ℕ} (hn : 0 < n) :
    mersenneGap n ≤ (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n + 3 * ((1 : ℝ) / 8) ^ n
```

2. [`Erdos249257.summable_mersenneGap_shift`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGapMass.lean#L69)

```lean
theorem summable_mersenneGap_shift (N : ℕ) :
    Summable (fun k : ℕ => mersenneGap (N + k + 1))
```

3. [`Erdos249257.mersenneGap_tail_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGapMass.lean#L83)

```lean
theorem mersenneGap_tail_le (N : ℕ) :
    ∑' k : ℕ, mersenneGap (N + k + 1)
      ≤ (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N
```

4. [`Erdos249257.tendsto_mersenneGap_tail_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGapMass.lean#L104)

```lean
theorem tendsto_mersenneGap_tail_zero :
    Tendsto (fun N : ℕ => ∑' k : ℕ, mersenneGap (N + k + 1)) atTop (nhds 0)
```

<a id="record-257hg-i2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mersenneGap_le` | [E257_30/Challenge.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L182) | [PaperStatementsAM.lean, line 103](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAM.lean#L103) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `summable_mersenneGap_shift` | [E257_30/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L186) | [PaperStatementsAM.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAM.lean#L114) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `mersenneGap_tail_le` | [E257_20/Challenge.lean, line 202](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L202) | [PaperStatementsAM.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L106) | [E257_20](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) |
| `tendsto_mersenneGap_tail_zero` | [E257_20/Challenge.lean, line 210](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L210) | [PaperStatementsAM.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAM.lean#L119) | [E257_20](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-i4"></a>

## Theorem 6.120 (A sufficient inequality for a safe skip), page 74

> *Let $`k,u,L\ge1`$ be integers, set $`a=2L-(2^k-1)u`$, and suppose $`a>0`$. For the skipped rational remainder $`\rho=u/(2L)`$, $`\rho\le2^{-k}`$ is equivalent to $`u\le a`$, whereas
> ``` math
> 2u\le3a\quad\Longrightarrow\quad\rho<R_k.
> ```
> The latter implication uses the three-term lower bound above. More explicitly, with $`t=2^k\ge2`$,
> ``` math
> \left(\frac1t+\frac1{3t^2}+\frac1{7t^3}\right)
>        -\frac3{3t-1}
>  =\frac{2t-3}{21t^3(3t-1)}>0.
> ```
> The inequality $`2u\le3a`$ gives $`\rho\le3/(3t-1)`$, proving the claim. The first two terms alone would not prove this comparison. This is a sufficient exclusion of the current tail-mass deficit, not an exact test for membership in the remaining achievement set.*
> 
> *The sufficient condition is weaker than $`u\le a`$. A realizable example is $`(k,u,L,a)=(2,7,13,5)`$; it passes $`2u\le3a`$ but not $`u\le a`$. The linked scalar example $`(u,a)=(3,2)`$ proves strict containment of the inequalities, but is not integral rational data for this substitution. For comparison, the exact mass threshold is $`a/u\ge R_k^{-1}-(2^k-1)`$; its right-hand side lies strictly between $`0`$ and $`2/3`$. None of these comparisons asserts that the half-greedy orbit satisfies the sufficient inequality at every skipped rank.*
> 
> *<span class="sans-serif">(uniform)</span> *lambert-bound* [`skipSafe_of_two_mul_le_three_mul`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L107) [`sharp_of_dyadic`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L197) [`sharp_strictly_stronger`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L200) [`skipSafe_actualTail_of_two_mul_le_three_mul`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L235)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_dyadic_skip_test_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L30)

```lean
theorem paper_dyadic_skip_test_iff {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k) ↔ u ≤ a
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_skip_safe_lb3`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L54)

```lean
theorem paper_sharp_skip_safe_lb3 {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTailLB3 k
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_skip_safe_actual_tail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L62)

```lean
theorem paper_sharp_skip_safe_actual_tail {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTail k
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_three_channel_margin_identity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L71)

```lean
theorem paper_three_channel_margin_identity {t : ℝ} (ht : 2 ≤ t) :
    (1 / t + 1 / (3 * t ^ 2) + 1 / (7 * t ^ 3)) - 3 / (3 * t - 1) =
        (2 * t - 3) / (21 * t ^ 3 * (3 * t - 1)) ∧
      0 < (2 * t - 3) / (21 * t ^ 3 * (3 * t - 1))
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_weaker_than_dyadic`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L92)

```lean
theorem paper_sharp_weaker_than_dyadic {u a : ℕ} (h : u ≤ a) : 2 * u ≤ 3 * a
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_strictly_weaker_realizable`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L97)

```lean
theorem paper_sharp_strictly_weaker_realizable :
    ∃ k u L a : ℕ, 1 ≤ k ∧ 0 < u ∧ 0 < a ∧
      2 ^ k * u + a = 2 * L + u ∧ 2 * u ≤ 3 * a ∧ ¬ u ≤ a
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_gives_three_over_three_t_sub_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L104)

```lean
theorem paper_sharp_gives_three_over_three_t_sub_one {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) ≤ 3 / (3 * (2 : ℝ) ^ k - 1)
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_two_channels_insufficient`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L131)

```lean
theorem paper_two_channels_insufficient :
    1 / (2 : ℝ) + 1 / (3 * (2 : ℝ) ^ 2) < 3 / (3 * (2 : ℝ) - 1)
```

9. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_mass_threshold`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SkipSafetyAndDivisorZeroRuns.lean#L138)

```lean
theorem paper_exact_mass_threshold {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ mersenneTail k ↔
        (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ≤ (a : ℝ) / u) ∧
      0 < (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ∧
      (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) < 2 / 3
```

<a id="record-257hg-i4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_dyadic_skip_test_iff` | [E257_30/Challenge.lean, line 210](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L210) | [PaperStatementsAA.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L190) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_sharp_skip_safe_lb3` | [E257_30/Challenge.lean, line 222](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L222) | [PaperStatementsAA.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L283) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_sharp_skip_safe_actual_tail` | [E257_30/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L199) | [PaperStatementsAM.lean, line 241](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAM.lean#L241) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_three_channel_margin_identity` | [E257_30/Challenge.lean, line 237](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L237) | [PaperStatementsAA.lean, line 298](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L298) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_sharp_weaker_than_dyadic` | [E257_30/Challenge.lean, line 234](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L234) | [PaperStatementsAA.lean, line 293](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L293) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_sharp_strictly_weaker_realizable` | [E257_30/Challenge.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L229) | [PaperStatementsAA.lean, line 289](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L289) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_sharp_gives_three_over_three_t_sub_one` | [E257_30/Challenge.lean, line 216](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L216) | [PaperStatementsAA.lean, line 278](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L278) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_two_channels_insufficient` | [E257_30/Challenge.lean, line 243](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L243) | [PaperStatementsAA.lean, line 303](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAA.lean#L303) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `paper_exact_mass_threshold` | [E257_30/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L190) | [PaperStatementsAM.lean, line 213](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStatementsAM.lean#L213) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-i5"></a>

## Proposition 6.121 (Two unconditional safety cases), page 75

> *Under the positive-integer and skipped-step hypotheses of Theorem <a href="#record:257hg-i4" data-reference-type="ref" data-reference="record:257hg-i4">163</a>, $`u=1`$ implies $`a\ge1`$, so the current remainder is less than $`R_k`$. Conversely, a fatal tail-mass deficit forces $`3a<2u`$, hence $`u\ge2`$, or $`u\ge3`$ when $`u`$ is odd. These are statements about the current step, not infinite survival. The exact declaration names are linked below.*
> 
> *<span class="sans-serif">(uniform)</span> *lambert-bound* [`unitNumerator_skipSafe`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L135) [`two_le_of_fatal`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L161) [`three_le_of_fatal_of_odd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L173) [`unitNumerator_skipSafe_actualTail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfGreedyFatalGap.lean#L246)*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGreedyFatalGap.lean#L135)

```lean
theorem unitNumerator_skipSafe
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTailLB3 k
```

2. [`Erdos249257.HalfGreedyFatalGap.two_le_of_fatal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGreedyFatalGap.lean#L161)

```lean
theorem two_le_of_fatal
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    2 ≤ u
```

3. [`Erdos249257.HalfGreedyFatalGap.three_le_of_fatal_of_odd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGreedyFatalGap.lean#L173)

```lean
theorem three_le_of_fatal_of_odd
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a) (hodd : Odd u)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    3 ≤ u
```

4. [`Erdos249257.HalfGreedyFatalGap.unitNumerator_skipSafe_actualTail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfGreedyFatalGap.lean#L246)

```lean
theorem unitNumerator_skipSafe_actualTail
    {k L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTail k
```

<a id="record-257hg-i5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `unitNumerator_skipSafe` | [E257_30/Challenge.lean, line 267](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L267) | [PaperStructuresH.lean, line 29](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStructuresH.lean#L29) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `two_le_of_fatal` | [E257_30/Challenge.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L259) | [PaperStructuresH.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStructuresH.lean#L22) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `three_le_of_fatal_of_odd` | [E257_30/Challenge.lean, line 251](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L251) | [PaperStructuresH.lean, line 15](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStructuresH.lean#L15) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |
| `unitNumerator_skipSafe_actualTail` | [E257_30/Challenge.lean, line 282](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_30/Challenge.lean#L282) | [PaperStructuresV.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_30/PaperStructuresV.lean#L22) | [E257_30](../../evidence/comparator/replay-35882032091/receipt-E257_30.json) |

Challenge for `unitNumerator_skipSafe`:

```lean
theorem unitNumerator_skipSafe {k u L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTailLB3 k := by sorry
```

Challenge for `two_le_of_fatal`:

```lean
theorem two_le_of_fatal {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    2 ≤ u := by sorry
```

Challenge for `three_le_of_fatal_of_odd`:

```lean
theorem three_le_of_fatal_of_odd {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a) (hodd : Odd u)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (T : ℝ) (hT : mersenneTailLB3 k ≤ T)
    (hfatal : T < (u : ℝ) / (2 * L)) :
    3 ≤ u := by sorry
```

Challenge for `unitNumerator_skipSafe_actualTail`:

```lean
theorem unitNumerator_skipSafe_actualTail {k u L a : ℕ}
    {k L a : ℕ}
    (hk : 1 ≤ k) (ha : 0 < a)
    (hdecomp : 2 ^ k * 1 + a = 2 * L + 1) :
    (1 : ℝ) / (2 * L) < mersenneTail k := by sorry
```

<a id="record-257bm-i13"></a>

## Theorem 6.122 (Two-sided dyadic bounds), page 75

> *Under the local hypothesis excluding the specified three middle cells and imposing the right-pulse bound, induction (base case at row 5 verified by `decide`) propagates it to the universal two-sided bound
> ``` math
> \forall s\ge5,\quad \min(\mathrm{rem}(s),\ \mathrm{overshoot}(s)) \;\le\; 2^s.
> ```
> This conditional bound says that at least one of the remainder and the adjacent overshoot is at most $`2^s`$. It does not assert that both are at most $`2^s`$; that stronger assertion would replace the minimum by a maximum. It is not needed for the charge bound at an actual upper reset: Proposition <a href="#record:257bm-c12" data-reference-type="ref" data-reference="record:257bm-c12">123</a> obtains that bound directly from the upper-reset identity. Applying the inductive argument to another recurrence would require its own transition and separation estimates.*
> 
> *<span class="sans-serif">(uniform)</span> *dyadic-scale* [`SeamTwoSidedDyadicCellEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4374) [`SeamTwoSidedDyadicCellEscape.step`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4398) [`SeamTwoSidedDyadicCellEscape.twoSided`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4448)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_two_sided_dyadic_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/DyadicBandAndTwoSidedBounds.lean#L105)

```lean
theorem paper_two_sided_dyadic_bound
    (hescape : SeamTwoSidedDyadicCellEscape) (s : ℕ) (hs : 5 ≤ s) :
    min (seamIntegerGreedyRemainder s) ((seamAdjacentCut s hs).overshoot) ≤
      2 ^ s
```

<a id="record-257bm-i13-comparator"></a>

**Comparator:** not yet compared.

<a id="record-257bm-i14"></a>

## Proposition 6.123 (A finite band check for $`13\le d\le30`$), page 75

> *For every actual upper-reset index $`13\le d\le30`$ and every $`0\le j\le d`$, the linked certificate verifies
> ``` math
> 2^{d-j+1}<\mathrm{resetCharge}
> \quad\text{or}\quad
> \mathrm{resetCharge}+2(d+j)\le2^{d-j+1}.
> ```
> It computes the successor remainder at each row $`d+1`$, from $`\mathrm{rem}(14)=392`$ through $`\mathrm{rem}(31)=4187487147`$. This proves the required condition on a finite range, not the universal condition for all $`d\ge13`$. A proof for unbounded reset indices must supply a further argument; repeatedly extending the table alone does not establish that statement.*
> 
> *<span class="sans-serif">(fixed)</span> *dyadic-boundary* [`SeamUpperResetDyadicBandEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4566) [`seamUpperResetDyadicBandEscape_through_thirty`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderUpperResetBandCertificates.lean#L78) [`half_mem_mersenneAchievementSet_of_upperResetDyadicBandEscape`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L4790)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_band_check_thirteen_to_thirty`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L29)

```lean
theorem paper_finite_band_check_thirteen_to_thirty
    (d : ℕ) (hd13 : 13 ≤ d) (hd30 : d ≤ 30) (hd5 : 5 ≤ d)
    (hcarry : (seamAdjacentCut d hd5).successorCarries) :
    ∀ j : ℕ, j ≤ d →
      2 ^ (d - j + 1) <
          4 * (seamAdjacentCut d hd5).overshoot +
            (seamAdjacentCut d hd5).abovePulse ∨
        4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
          2 ^ (d - j + 1)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_successor_remainders_fourteen_through_thirtyone`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L44)

```lean
theorem paper_successor_remainders_fourteen_through_thirtyone :
    seamIntegerGreedyRemainder 14 = 392 ∧
      seamIntegerGreedyRemainder 15 = 34333 ∧
      seamIntegerGreedyRemainder 16 = 71791 ∧
      seamIntegerGreedyRemainder 17 = 156085 ∧
      seamIntegerGreedyRemainder 18 = 362187 ∧
      seamIntegerGreedyRemainder 19 = 924455 ∧
      seamIntegerGreedyRemainder 20 = 549353 ∧
      seamIntegerGreedyRemainder 21 = 100251 ∧
      seamIntegerGreedyRemainder 22 = 4595307 ∧
      seamIntegerGreedyRemainder 23 = 9992613 ∧
      seamIntegerGreedyRemainder 24 = 23193229 ∧
      seamIntegerGreedyRemainder 25 = 59218477 ∧
      seamIntegerGreedyRemainder 26 = 35546625 ∧
      seamIntegerGreedyRemainder 27 = 7968765 ∧
      seamIntegerGreedyRemainder 28 = 300310513 ∧
      seamIntegerGreedyRemainder 29 = 664371133 ∧
      seamIntegerGreedyRemainder 30 = 1583742700 ∧
      seamIntegerGreedyRemainder 31 = 4187487147
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_universal_band_condition_unfolded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L77)

```lean
theorem paper_universal_band_condition_unfolded :
    SeamUpperResetDyadicBandEscape ↔
      ∀ (d : ℕ) (hd5 : 5 ≤ d), 13 ≤ d →
        (seamAdjacentCut d hd5).successorCarries →
          ∀ j : ℕ, j ≤ d →
            2 ^ (d - j + 1) <
                4 * (seamAdjacentCut d hd5).overshoot +
                  (seamAdjacentCut d hd5).abovePulse ∨
              4 * (seamAdjacentCut d hd5).overshoot +
                    (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
                2 ^ (d - j + 1)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_universal_band_condition_would_close_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L70)

```lean
theorem paper_universal_band_condition_would_close_half
    (hband : SeamUpperResetDyadicBandEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet
```

<a id="record-257bm-i14-comparator"></a>

**Comparator:** not yet compared.

<a id="record-257bm-i15"></a>

## Theorem 6.124 (A general perturbed greedy recurrence), page 75

> *Let the old integer values be separated by at least $`g\ge1`$, and let the update be $`t(x)=4s(x)+p(x)`$ with $`0\le p(x)\le B<g`$. Suppose $`x_-`$ and $`x_+`$ are the adjacent old values on either side of capacity $`C`$. Theorem <a href="#thm:perturbed-family-maximality" data-reference-type="ref" data-reference="thm:perturbed-family-maximality">105</a> gives the largest admissible updated value at capacity $`4C+g`$ and the exact three-branch remainder after testing the extra weight $`2g+4`$.*
> 
> *The underlying structure in Definition <a href="#defn:perturbed-family" data-reference-type="ref" data-reference="defn:perturbed-family">104</a> assumes only $`B<3g`$; that suffices for order preservation, but the cited maximality application has the additional hypothesis $`B<g`$. The counterexample after Theorem <a href="#thm:perturbed-family-maximality" data-reference-type="ref" data-reference="thm:perturbed-family-maximality">105</a> shows what can fail without it. For a maximum over both choices of the extra weight, rather than the stated two-stage rule, one also needs a separation argument; $`4g-B\ge2g+4`$ suffices, as shown after that theorem.*
> 
> *<span class="sans-serif">(uniform)</span> *abstract-perturbed-greedy* [`PerturbedFamily`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderIntegerGreedy.lean#L1286) [`prefixChoice_maximal`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderIntegerGreedy.lean#L1390) [`nextRemainder_trichotomy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderIntegerGreedy.lean#L1463)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_order_preservation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L97)

```lean
theorem paper_perturbed_order_preservation (F : PerturbedFamily α)
    {x y : α} (hxy : F.oldSum x < F.oldSum y) :
    F.newSum x < F.newSum y
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_prefixChoice_maximal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L106)

```lean
theorem paper_perturbed_prefixChoice_maximal (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap) :
    K.newCapacity = 4 * C + F.gap ∧
      K.successorCarries = (4 * K.overshoot + K.abovePulse ≤ F.gap) ∧
      K.prefixChoice = (if K.successorCarries then K.above else K.below) ∧
      F.newSum K.prefixChoice ≤ K.newCapacity ∧
      ∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤ F.newSum K.prefixChoice
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_nextRemainder_three_branches`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L124)

```lean
theorem paper_perturbed_nextRemainder_three_branches (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] :
    K.terminalWeight = 2 * F.gap + 4 ∧
      K.nextRemainder =
        if K.successorCarries then
          F.gap - (4 * K.overshoot + K.abovePulse)
        else if 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight then
          4 * K.remainder + F.gap - K.belowPulse
        else
          4 * K.remainder - F.gap - K.belowPulse - 4
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_separation_global_maximality`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L140)

```lean
theorem paper_perturbed_separation_global_maximality (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap)
    {x : α} (hx : F.oldSum x < F.oldSum K.prefixChoice) :
    F.newSum x + K.terminalWeight ≤ F.newSum K.prefixChoice
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_two_stage_is_global_maximum`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L158)

```lean
theorem paper_perturbed_two_stage_is_global_maximum (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap)
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap) :
    F.newSum K.prefixChoice +
          (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
            else 0) ≤ K.newCapacity ∧
      (∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0)) ∧
      (∀ x : α, F.newSum x + K.terminalWeight ≤ K.newCapacity →
        F.newSum x + K.terminalWeight ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0))
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_perturbed_weak_cap_counterexample`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L245)

```lean
theorem paper_perturbed_weak_cap_counterexample :
    ¬ weakCapFamily.pulseCap < weakCapFamily.gap ∧
      weakCapFamily.pulseCap < 3 * weakCapFamily.gap ∧
      ¬ weakCapCut.successorCarries ∧
      weakCapCut.newCapacity = 10 ∧
      weakCapFamily.newSum weakCapCut.below = 11 ∧
      ¬ weakCapFamily.newSum weakCapCut.below ≤ weakCapCut.newCapacity ∧
      weakCapFamily.newSum (0 : Fin 3) ≤ weakCapCut.newCapacity
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.prefixChoice_eq_below`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/UpperResetBandCertificate.lean#L259)

```lean
theorem prefixChoice_eq_below (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (h : ¬ K.successorCarries) :
    K.prefixChoice = K.below
```

<a id="record-257bm-i15-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_perturbed_order_preservation` | [E257_12/Challenge.lean, line 316](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_12/Challenge.lean#L316) | [PaperStructuresBN.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_12/PaperStructuresBN.lean#L99) | [E257_12](../../evidence/comparator/replay-35882032091/receipt-E257_12.json) |
| `paper_perturbed_prefixChoice_maximal` | [E257_12/Challenge.lean, line 321](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_12/Challenge.lean#L321) | [PaperStructuresBN.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_12/PaperStructuresBN.lean#L104) | [E257_12](../../evidence/comparator/replay-35882032091/receipt-E257_12.json) |
| `paper_perturbed_nextRemainder_three_branches` | [E257_12/Challenge.lean, line 304](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_12/Challenge.lean#L304) | [PaperStructuresBN.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_12/PaperStructuresBN.lean#L87) | [E257_12](../../evidence/comparator/replay-35882032091/receipt-E257_12.json) |
| `paper_perturbed_separation_global_maximality` | [E257_31/Challenge.lean, line 316](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_31/Challenge.lean#L316) | [PaperStructuresBP.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_31/PaperStructuresBP.lean#L74) | [E257_31](../../evidence/comparator/replay-35882032091/receipt-E257_31.json) |
| `paper_perturbed_two_stage_is_global_maximum` | [E257_31/Challenge.lean, line 323](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_31/Challenge.lean#L323) | [PaperStructuresBP.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_31/PaperStructuresBP.lean#L81) | [E257_31](../../evidence/comparator/replay-35882032091/receipt-E257_31.json) |
| `paper_perturbed_weak_cap_counterexample` | [E257_31/Challenge.lean, line 342](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_31/Challenge.lean#L342) | [PaperStructuresBP.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_31/PaperStructuresBP.lean#L100) | [E257_31](../../evidence/comparator/replay-35882032091/receipt-E257_31.json) |
| `prefixChoice_eq_below` | [E257_32/Challenge.lean, line 60](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L60) | [PaperStructuresBU.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStructuresBU.lean#L71) | [E257_32](../../evidence/comparator/replay-35882032091/receipt-E257_32.json) |

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `paper_perturbed_order_preservation`:

```lean
theorem paper_perturbed_order_preservation {α : Type*} (F : PerturbedFamily α)
    {x y : α} (hxy : F.oldSum x < F.oldSum y) :
    F.newSum x < F.newSum y := by sorry
```

Challenge for `paper_perturbed_prefixChoice_maximal`:

```lean
theorem paper_perturbed_prefixChoice_maximal {α : Type*} (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap) :
    K.newCapacity = 4 * C + F.gap ∧
      K.successorCarries = (4 * K.overshoot + K.abovePulse ≤ F.gap) ∧
      K.prefixChoice = (if K.successorCarries then K.above else K.below) ∧
      F.newSum K.prefixChoice ≤ K.newCapacity ∧
      ∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤ F.newSum K.prefixChoice := by sorry
```

Challenge for `paper_perturbed_nextRemainder_three_branches`:

```lean
theorem paper_perturbed_nextRemainder_three_branches {α : Type*} (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] :
    K.terminalWeight = 2 * F.gap + 4 ∧
      K.nextRemainder =
        if K.successorCarries then
          F.gap - (4 * K.overshoot + K.abovePulse)
        else if 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight then
          4 * K.remainder + F.gap - K.belowPulse
        else
          4 * K.remainder - F.gap - K.belowPulse - 4 := by sorry
```

Challenge for `paper_perturbed_separation_global_maximality`:

```lean
theorem paper_perturbed_separation_global_maximality {α : Type*} (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap)
    {x : α} (hx : F.oldSum x < F.oldSum K.prefixChoice) :
    F.newSum x + K.terminalWeight ≤ F.newSum K.prefixChoice := by sorry
```

Challenge for `paper_perturbed_two_stage_is_global_maximum`:

```lean
theorem paper_perturbed_two_stage_is_global_maximum {α : Type*} (F : PerturbedFamily α)
    {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (hcap : F.pulseCap < F.gap)
    (hsep : K.terminalWeight ≤ 4 * F.gap - F.pulseCap) :
    F.newSum K.prefixChoice +
          (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
            else 0) ≤ K.newCapacity ∧
      (∀ x : α, F.newSum x ≤ K.newCapacity →
        F.newSum x ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0)) ∧
      (∀ x : α, F.newSum x + K.terminalWeight ≤ K.newCapacity →
        F.newSum x + K.terminalWeight ≤
          F.newSum K.prefixChoice +
            (if K.terminalWeight ≤ K.prefixRemainder then K.terminalWeight
              else 0)) := by sorry
```

Challenge for `prefixChoice_eq_below`:

```lean
theorem prefixChoice_eq_below {α : Type*} (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (h : ¬ K.successorCarries) :
    K.prefixChoice = K.below := by sorry
```

<a id="record-257bm-i16"></a>

## Theorem 6.125 (Spacing of compatible reverse-carry words), page 75

> *Consider two integer carry recurrences $`b_i(m)+2u_i(m)=a_i(m)+u_i(m+1)`$, $`i=1,2`$. If $`a_1(k)=a_2(k)`$ and the output bits at $`k`$ are $`1`$ and $`0`$, then the carry difference at $`k+1`$ is odd. If the coefficients and bits agree for the following $`L`$ positions, the difference at $`k+L+1`$ is $`2^L`$ times that odd integer. Consequently absolute terminal bounds $`B_1,B_2`$ give $`2^L\le B_1+B_2`$. Lemma <a href="#lem:reverse-carry-word" data-reference-type="ref" data-reference="lem:reverse-carry-word">89</a> states the exact identity and proves it by subtraction. The linked formal statements encode these agreements; they do not supply terminal bounds for an unrelated digit system.*
> 
> *<span class="sans-serif">(uniform)</span> *reverse-carry-word* [`ReverseCarryWord`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L70) [`overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L124) [`overlappingReverseCarryWords_twoPow_le_realBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L191) [`overlappingMidpointReturns_twoPow_le_realBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L244)*

The Lean declarations below together state this result.

1. [`Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfTrappingReturnCarry.lean#L124)

```lean
theorem overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd
    (left right : ReverseCarryWord) (seam length : ℕ)
    (hcoeffSeam : left.coeff seam = right.coeff seam)
    (hleftSeam : left.bit seam = 1)
    (hrightSeam : right.bit seam = 0)
    (hcoeffOverlap : ∀ j < length,
      left.coeff (seam + 1 + j) = right.coeff (seam + 1 + j))
    (hbitOverlap : ∀ j < length,
      left.bit (seam + 1 + j) = right.bit (seam + 1 + j)) :
    ∃ z : ℤ, Odd z ∧
      carryDifference left right (seam + 1 + length) =
        (2 : ℤ) ^ length * z
```

2. [`Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_twoPow_le_realBound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfTrappingReturnCarry.lean#L191)

```lean
theorem overlappingReverseCarryWords_twoPow_le_realBound
    (left right : ReverseCarryWord) (seam length : ℕ) (bound : ℝ)
    (hcoeffSeam : left.coeff seam = right.coeff seam)
    (hleftSeam : left.bit seam = 1)
    (hrightSeam : right.bit seam = 0)
    (hcoeffOverlap : ∀ j < length,
      left.coeff (seam + 1 + j) = right.coeff (seam + 1 + j))
    (hbitOverlap : ∀ j < length,
      left.bit (seam + 1 + j) = right.bit (seam + 1 + j))
    (hleftNonneg : 0 ≤ left.carry (seam + 1 + length))
    (hrightNonneg : 0 ≤ right.carry (seam + 1 + length))
    (hleftBound : (left.carry (seam + 1 + length) : ℝ) ≤ bound)
    (hrightBound : (right.carry (seam + 1 + length) : ℝ) ≤ bound) :
    (2 : ℝ) ^ length ≤ bound
```

3. [`Erdos249257.HalfTrappingReturnCarry.overlappingMidpointReturns_twoPow_le_realBound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfTrappingReturnCarry.lean#L244)

```lean
theorem overlappingMidpointReturns_twoPow_le_realBound
    (left right : ReverseCarryWord) (N M : ℕ) (bound : ℝ) (hN : 1 ≤ N)
    (hNM : M ≤ 2 * N - 2)
    (hcoeffSeam : left.coeff (M + 1) = right.coeff (M + 1))
    (hleftSeam : left.bit (M + 1) = 1)
    (hrightSeam : right.bit (M + 1) = 0)
    (hcoeffOverlap : ∀ j < 2 * N - M - 1,
      left.coeff (M + 2 + j) = right.coeff (M + 2 + j))
    (hbitOverlap : ∀ j < 2 * N - M - 1,
      left.bit (M + 2 + j) = right.bit (M + 2 + j))
    (hleftNonneg : 0 ≤ left.carry (2 * N + 1))
    (hrightNonneg : 0 ≤ right.carry (2 * N + 1))
    (hleftBound : (left.carry (2 * N + 1) : ℝ) ≤ bound)
    (hrightBound : (right.carry (2 * N + 1) : ℝ) ≤ bound) :
    (2 : ℝ) ^ (2 * N - M - 1) ≤ bound
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_reverse_carry_word`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SeamRowGapAndCarry.lean#L240)

```lean
theorem paper_reverse_carry_word :
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ k L : ℕ, a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        u₁ (k + L + 1) - u₂ (k + L + 1) = 2 ^ L * (2 * (u₁ k - u₂ k) + 1) ∧
          Odd (2 * (u₁ k - u₂ k) + 1)) ∧
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ (k L : ℕ) (B₁ B₂ : ℝ), a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B₁ →
        |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B₂ →
        (2 : ℝ) ^ L ≤ B₁ + B₂) ∧
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ (k L : ℕ) (B : ℝ), a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B →
        |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B →
        (2 : ℝ) ^ L ≤ 2 * B)
```

<a id="record-257bm-i16-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd` | [E257_32/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L97) | [PaperStructuresO.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStructuresO.lean#L67) | [E257_32](../../evidence/comparator/replay-35882032091/receipt-E257_32.json) |
| `overlappingReverseCarryWords_twoPow_le_realBound` | [E257_32/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L111) | [PaperStructuresO.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStructuresO.lean#L80) | [E257_32](../../evidence/comparator/replay-35882032091/receipt-E257_32.json) |
| `overlappingMidpointReturns_twoPow_le_realBound` | [E257_32/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L80) | [PaperStructuresO.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStructuresO.lean#L51) | [E257_32](../../evidence/comparator/replay-35882032091/receipt-E257_32.json) |
| `paper_reverse_carry_word` | [E257_20/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L110) | [PaperStatementsAA.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAA.lean#L238) | [E257_20](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-i17"></a>

## Proposition 6.126 (Changing one support bit at a doubled rank), page 76

> *Let two supports agree except that the second includes $`N+1`$ while the first does not. At the argument $`2(N+1)`$ their divisor counts differ by exactly $`1`$, because $`N+1`$ divides $`2(N+1)`$. More generally the difference at a positive argument $`m`$ is $`\mathbf1_{N+1\mid m}`$. The linked statements apply this identity to the finite supports in their hypotheses. No conclusion about a different coefficient sequence follows without identifying its own support change.*
> 
> *<span class="sans-serif">(uniform)</span> *half-divisor* [`supportCoeff_extend_true_eq_false_add_one_at_double`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfDivisorUnitDrop.lean#L20) [`supportCoeff_boundaryPair_unitDrop_at_double`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfDivisorUnitDrop.lean#L35)*

The Lean declarations below together state a result at least as strong as this one. The Lean identity $c_{A\cup\{d\}}(m)=c_A(m)+\mathbf 1_{d\mid m}$ holds for every positive $m$, every set $A$, finite or infinite, and every $d\notin A$; the printed statement is its case $d=N+1$. `supportCoeff_insert_divisor` is the case $d\mid m$, and the two statements on half words give the difference $1$ at $m=2(N+1)$ for finite binary words.

1. [`Erdos249257.HalfCylinderFiniteShadow.supportCoeff_insert_divisor`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderFiniteShadow.lean#L642)

```lean
theorem supportCoeff_insert_divisor
    (A : Set ℕ) {d n : ℕ} (hd : d ∈ n.divisors) (hdA : d ∉ A) :
    supportCoeff (insert d A) n = supportCoeff A n + 1
```

2. [`Erdos249257.HalfDivisorUnitDrop.supportCoeff_extend_true_eq_false_add_one_at_double`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfDivisorUnitDrop.lean#L20)

```lean
theorem supportCoeff_extend_true_eq_false_add_one_at_double
    {N : ℕ} (a : HalfWord N) :
    supportCoeff (wordSupport (extendHalfWord a true)) (2 * (N + 1)) =
      supportCoeff (wordSupport (extendHalfWord a false)) (2 * (N + 1)) + 1
```

3. [`Erdos249257.HalfDivisorUnitDrop.supportCoeff_boundaryPair_unitDrop_at_double`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfDivisorUnitDrop.lean#L35)

```lean
theorem supportCoeff_boundaryPair_unitDrop_at_double
    {N : ℕ} (a : HalfWord N) (left right : HalfWord (N + 1))
    (hleft : left = extendHalfWord a true)
    (hright : right = extendHalfWord a false) :
    supportCoeff (wordSupport left) (2 * (N + 1)) =
      supportCoeff (wordSupport right) (2 * (N + 1)) + 1
```

4. [`Erdos249257.HalfCylinderIntegerGreedy.supportCoeff_insert_eq_add_indicator`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCylinderIntegerGreedy.lean#L882)

```lean
theorem supportCoeff_insert_eq_add_indicator
    (A : Set ℕ) {d n : ℕ} (hdA : d ∉ A) :
    supportCoeff (insert d A) n =
      supportCoeff A n + if d ∈ n.divisors then 1 else 0
```

<a id="record-257bm-i17-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `supportCoeff_insert_divisor` | [E257_32/Challenge.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L145) | [PaperStatementsAL.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStatementsAL.lean#L43) | [E257_32](../../evidence/comparator/replay-35882032091/receipt-E257_32.json) |
| `supportCoeff_extend_true_eq_false_add_one_at_double` | [E257_20/Challenge.lean, line 263](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L263) | [PaperStatementsAL.lean, line 55](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAL.lean#L55) | [E257_20](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) |
| `supportCoeff_boundaryPair_unitDrop_at_double` | [E257_32/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_32/Challenge.lean#L150) | [PaperStatementsAL.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_32/PaperStatementsAL.lean#L47) | [E257_32](../../evidence/comparator/replay-35882032091/receipt-E257_32.json) |
| `supportCoeff_insert_eq_add_indicator` | [E257_20/Challenge.lean, line 276](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_20/Challenge.lean#L276) | [PaperStatementsAN.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_20/PaperStatementsAN.lean#L32) | [E257_20](../../evidence/comparator/replay-35882032091/receipt-E257_20.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-k1"></a>

## Theorem 6.127 (A bounded model of the doubling-or-return alternative), page 76

> *The dichotomy $`\mathrm{ExactLocalMersenneHalfRow}(2n{-}1) \vee \exists c,\,4\le c\le n\wedge
> \mathrm{ExactLocalMersenneHalfRow}(2c{-}2)`$ (proved for $`n\ge6`$ at Theorem <a href="#record:257bm-k-dich" data-reference-type="ref" data-reference="record:257bm-k-dich">171</a> below) is not by itself enough for cofinality. Countermodel: $`\mathrm{boundedDoubleOrRecycleModel}(n) := (n=6)`$ satisfies exactly the same two-branch transition shape (seed at 6, and `boundedDoubleOrRecycleModel_transition` reproduces the $`\vee`$ shape by always taking the recycle branch with $`c=4`$, conclusion back at $`2\cdot4-2=6`$), yet
> ``` math
> \neg\big(\forall N,\ \exists n\ge N,\ \mathrm{boundedDoubleOrRecycleModel}(n)\big) \qquad \text{(not cofinal ;  only ever true at } n=6\text{)}.
> ```
> Packaged existentially as `exists_seeded_bounded_double_or_recycle_model`. The double-or-recycle transition shape, even together with an endpoint-six seed, is logically insufficient to conclude cofinal exact rows. A genuinely new progress input (strict endpoint growth, or an independent cofinality argument) is required. The countermodel retains only the seed and this transition rule. It therefore tests those premises, not additional arithmetic information that a more structured induction may use.*
> 
> *<span class="sans-serif">(fixed)</span> *meta-logical* [`boundedDoubleOrRecycleModel`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDichotomy.lean#L58) [`boundedDoubleOrRecycleModel_transition`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDichotomy.lean#L64) [`boundedDoubleOrRecycleModel_not_cofinal`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDichotomy.lean#L79) [`exists_seeded_bounded_double_or_recycle_model`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDichotomy.lean#L91)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_bounded_double_or_recycle_countermodel`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L84)

```lean
theorem paper_bounded_double_or_recycle_countermodel :
    (∀ n : ℕ, boundedDoubleOrRecycleModel n ↔ n = 6) ∧
      boundedDoubleOrRecycleModel 6 ∧
      (∀ n : ℕ, 6 ≤ n → boundedDoubleOrRecycleModel n →
        boundedDoubleOrRecycleModel (2 * n - 1) ∨
          ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ boundedDoubleOrRecycleModel (2 * c - 2)) ∧
      (∀ n : ℕ, 6 ≤ n → boundedDoubleOrRecycleModel n →
        4 ≤ 4 ∧ 4 ≤ n ∧ boundedDoubleOrRecycleModel (2 * 4 - 2)) ∧
      ¬ (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ boundedDoubleOrRecycleModel n)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exists_seeded_bounded_double_or_recycle_model`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L102)

```lean
theorem paper_exists_seeded_bounded_double_or_recycle_model :
    ∃ P : ℕ → Prop,
      P 6 ∧
        (∀ n : ℕ, 6 ≤ n → P n →
          P (2 * n - 1) ∨ ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ P (2 * c - 2)) ∧
        ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n
```

<a id="record-257bm-k1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_bounded_double_or_recycle_countermodel` | [E257_33/Challenge.lean, line 52](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L52) | [PaperStatementsAA.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L171) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_exists_seeded_bounded_double_or_recycle_model` | [E257_33/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L63) | [PaperStatementsAA.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L195) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-k-dich"></a>

## Theorem 6.128 (Doubling or returning to an earlier depth), page 76

> *For $`n\ge6`$, $`\mathrm{ExactLocalMersenneHalfRow}(n)`$:
> ``` math
> \mathrm{ExactLocalMersenneHalfRow}(2n-1) \;\vee\; \exists c,\ 4\le c\le n \wedge \mathrm{ExactLocalMersenneHalfRow}(2c-2).
> ```
> Every exact row of depth at least $`6`$ has at least one of the two asserted continuations. The proof separates the below-half case from the above-half case, but the two existential conclusions need not be exclusive. The returned depth $`2c-2`$ is not claimed to exceed $`n`$. The finite Mersenne value cannot equal $`1/2`$, by Observation <a href="#record:257bm-k11" data-reference-type="ref" data-reference="record:257bm-k11">181</a> (`finiteErdosSum_den_odd`); this says nothing about equality of the returned and original depths. For example, at $`n=6`$, the support $`\{2,3,6\}`$ is an exact row, and so is $`\{2,3,6,7,11\}`$ at depth $`11`$. The second conclusion also holds with $`c=4`$, since $`2c-2=6`$. Thus both conclusions hold in this example, and the second allows no depth increase. What is missing, per Theorem <a href="#record:257bm-k1" data-reference-type="ref" data-reference="record:257bm-k1">170</a>, is not another dichotomy but strict endpoint progress in the recycle branch, or a proof the below-half branch recurs ; re-deriving this disjunction without an additional progress argument would not establish cofinality.*
> 
> *<span class="sans-serif">(bounded)</span> *divisor counts and finite sums* [`exactLocalMersenneHalfRow_double_or_recycle`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowDichotomy.lean#L26)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_double_or_recycle`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L33)

```lean
theorem paper_exact_row_double_or_recycle {n : ℕ} (hn : 6 ≤ n)
    (hrow : ExactLocalMersenneHalfRow n) :
    ExactLocalMersenneHalfRow (2 * n - 1) ∨
      ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_row_value_ne_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L41)

```lean
theorem paper_finite_row_value_ne_half {D : Finset ℕ} (h0 : 0 ∉ D) :
    localMersennePrefixValue D ≠ (1 / 2 : ℚ)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_row_example_six_and_eleven`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L55)

```lean
theorem paper_exact_row_example_six_and_eleven :
    localPrefixQuotient ({2, 3, 6} : Finset ℕ) 6 = 2 ^ (6 - 1) - 1 ∧
      ExactLocalMersenneHalfRow 6 ∧
      localPrefixQuotient ({2, 3, 6, 7, 11} : Finset ℕ) 11 = 2 ^ (11 - 1) - 1 ∧
      ExactLocalMersenneHalfRow (2 * 6 - 1) ∧
      (4 ≤ 4 ∧ 4 ≤ 6 ∧ ExactLocalMersenneHalfRow (2 * 4 - 2)) ∧
      2 * 4 - 2 = 6
```

<a id="record-257bm-k-dich-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_exact_row_double_or_recycle` | [E257_33/Challenge.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L140) | [PaperStatementsAX.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAX.lean#L21) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_finite_row_value_ne_half` | [E257_33/Challenge.lean, line 107](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L107) | [PaperStatementsAR.lean, line 243](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAR.lean#L243) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_exact_row_example_six_and_eleven` | [E257_33/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L146) | [PaperStatementsAX.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAX.lean#L26) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-k2"></a>

## Proposition 6.129 (A sufficient fractional-mass bound need not hold), page 76

> *Take $`D=\{2,3\}`$ and $`c=5`$. Direct calculation gives
> ``` math
> X_D(2)=\frac{10}{21}<\frac12
>  <\frac{331}{651}=X_{D\cup\{5\}}(2),\qquad S(D,1,8)=6<8.
> ```
> However, the combined fractional mass is
> ``` math
> \sum_{d\in D\cup\{5\}}\frac{2^8\bmod(2^d-1)}{2^d-1}
>  =\frac{757}{651}>1.
> ```
> The linked `norm_num` proof checks this example. Thus the combined fractional-mass bound by $`1`$, which suffices for the sharp capacity estimate, is not necessary for that estimate. Thus the fractional-mass bound cannot hold at every real crossing core. A proof using it would need to handle the exceptional cores separately; the example does not rule out all uses of fractional-mass estimates. Theorem <a href="#record:257rig-k6" data-reference-type="ref" data-reference="record:257rig-k6">176</a> identifies the support at a critical crossing with a real greedy prefix, but does not prove the missing bound on those prefixes.*
> 
> *<span class="sans-serif">(fixed)</span> *divisor counts and finite sums* [`splitFractionMass_one_bound_not_necessary_fixture`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkippedCoreCriticalCapacity.lean#L183)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_fractional_mass_bound_not_necessary`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L118)

```lean
theorem paper_fractional_mass_bound_not_necessary :
    localMersennePrefixValue ({2, 3} : Finset ℕ) = 10 / 21 ∧
      localMersennePrefixValue ({2, 3} : Finset ℕ) < (1 / 2 : ℚ) ∧
      localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) = 331 / 651 ∧
      (1 / 2 : ℚ) < localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 = 6 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 8 ∧
      localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 2 ^ (5 - 2) ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 = 757 / 651 ∧
      1 < localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 ∧
      localFractionMass (insert 5 ({2, 3} : Finset ℕ)) 8 =
        localFractionMass ({2, 3} : Finset ℕ) 8 + localMersenneFraction 8 5
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_fractional_mass_bound_suffices_for_sharp_capacity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L139)

```lean
theorem paper_fractional_mass_bound_suffices_for_sharp_capacity
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) < localMersennePrefixValue (insert c D))
    (hfrac : localFractionMass (insert c D) (2 * c - 2) ≤ 1) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)
```

<a id="record-257bm-k2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_fractional_mass_bound_not_necessary` | [E257_33/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L111) | [PaperStatementsAR.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAR.lean#L246) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_fractional_mass_bound_suffices_for_sharp_capacity` | [E257_33/Challenge.lean, line 125](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L125) | [PaperStatementsAR.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAR.lean#L259) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-k4"></a>

## Theorem 6.131 (The returning endpoint need not be larger), page 77

> *Theorem <a href="#record:257bm-c10" data-reference-type="ref" data-reference="record:257bm-c10">121</a> (`exists_skippedCoreExactRow_of_value_above`) is unconditional, but its witness is $`\exists c\le n`$, not $`\exists c`$ large: $`2c-2`$ may be $`\le n`$, so the endpoint need not grow. Theorem <a href="#record:257bm-k1" data-reference-type="ref" data-reference="record:257bm-k1">170</a>’s `exists_seeded_bounded_double_or_recycle_model` is the explicit falsifier of the naive hope that growth comes for free: $`\mathrm{boundedDoubleOrRecycleModel}(n):=(n=6)`$ satisfies the same transition schema plus a seed and is not cofinal. Growth is recovered only inside $`\mathrm{ProtectedExactLocalMersenneRow}`$ (Theorem <a href="#record:257bm-c5" data-reference-type="ref" data-reference="record:257bm-c5">114</a>), whose invariants $`\mathrm{endpoint}<2\cdot\mathrm{cutoff}`$ and $`\mathrm{new\_above\_cutoff}`$ force $`c>\mathrm{cutoff}`$ hence $`2c-2>\mathrm{endpoint}`$ ; and maintaining those invariants is precisely what needs the strict-upper (sharp capacity) fill of Theorem <a href="#record:257bm-c7" data-reference-type="ref" data-reference="record:257bm-c7">118</a> rather than this general recycling theorem.*
> 
> *<span class="sans-serif">(bounded)</span> *binary digits* [`exists_skippedCoreExactRow_of_value_above`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusExactRowCrossing.lean#L155)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_skipped_core_recycling_witness_bounded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L163)

```lean
theorem paper_skipped_core_recycling_witness_bounded
    {E : Finset ℕ} {n : ℕ} (hE : ∀ d ∈ E, 2 ≤ d ∧ d ≤ n)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E) :
    ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ ExactLocalMersenneHalfRow (2 * c - 2)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_returning_endpoint_may_fail_to_grow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L172)

```lean
theorem paper_returning_endpoint_may_fail_to_grow :
    ∃ n c : ℕ, 4 ≤ c ∧ c ≤ n ∧ 2 * c - 2 ≤ n ∧
      ExactLocalMersenneHalfRow (2 * c - 2)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_exists_seeded_bounded_double_or_recycle_model`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L102)

```lean
theorem paper_exists_seeded_bounded_double_or_recycle_model :
    ∃ P : ℕ → Prop,
      P 6 ∧
        (∀ n : ℕ, 6 ≤ n → P n →
          P (2 * n - 1) ∨ ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ P (2 * c - 2)) ∧
        ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_protected_row_crossing_beyond_cutoff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L184)

```lean
theorem paper_protected_row_crossing_beyond_cutoff
    (s : ProtectedExactLocalMersenneRow) {e : ℕ} (heSupport : e ∈ s.support)
    (heCross : (1 / 2 : ℚ) <
      localMersennePrefixValue (insert e (s.support.filter fun d => d < e))) :
    s.cutoff < e
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_protected_row_endpoint_growth`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L218)

```lean
theorem paper_protected_row_endpoint_growth
    (s : ProtectedExactLocalMersenneRow) {c : ℕ} (hc : s.cutoff < c) :
    s.endpoint < 2 * c - 2
```

<a id="record-257bm-k4-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_skipped_core_recycling_witness_bounded` | [E257_33/Challenge.lean, line 170](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L170) | [PaperStatementsAS.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAS.lean#L36) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_returning_endpoint_may_fail_to_grow` | [E257_33/Challenge.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L155) | [PaperStatementsAX.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAX.lean#L34) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_exists_seeded_bounded_double_or_recycle_model` | [E257_33/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L63) | [PaperStatementsAA.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L195) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_protected_row_crossing_beyond_cutoff` | [E257_33/Challenge.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L203) | [PaperStructuresBG.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStructuresBG.lean#L68) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_protected_row_endpoint_growth` | [E257_33/Challenge.lean, line 210](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L210) | [PaperStructuresBG.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStructuresBG.lean#L74) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257rig-k6"></a>

## Theorem 6.133 (Uniqueness at a critical crossing), page 78

> *For $`c\ge4`$, $`D`$ bounded $`[2,c)`$, below-half, with genuine crossing deficit $`\tfrac12-\mathrm{value}(D) < \ensuremath{w}(c)`$:
> ``` math
> D \;=\; \mathrm{halfGreedyPrefixSupport}(c-1).
> ```
> Thus $`D=G\cap\{1,\ldots,c-1\}`$: at a critical crossing the support is fixed by $`c`$. The proof uses the strict inequality between each Mersenne weight and the sum of all later weights, as in Theorem <a href="#record:257bm-i11a" data-reference-type="ref" data-reference="record:257bm-i11a">143</a>. Consequently, the support quantifier in Theorem <a href="#record:257bm-c4" data-reference-type="ref" data-reference="record:257bm-c4">113</a> does not allow arbitrary choices of $`D`$. This reduces that hypothesis to a statement about the actual greedy sequence. It does not rule out proving a new bound for that sequence.*
> 
> *<span class="sans-serif">(uniform)</span> *greedy recurrence* [`eq_halfGreedyPrefixSupport_of_critical_crossing`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L50)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_crossing_support_is_greedy_prefix`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ExactRowDichotomyCountermodels.lean#L231)

```lean
theorem paper_critical_crossing_support_is_greedy_prefix
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1) ∧
      (↑D : Set ℕ) = greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Iic (c - 1)
```

<a id="record-257rig-k6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_critical_crossing_support_is_greedy_prefix` | [E257_33/Challenge.lean, line 256](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L256) | [PaperStatementsK.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsK.lean#L122) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257bm-k9"></a>

## Theorem 6.136 (Vanishing of the specified linear-channel determinant), page 78

> *Let $`V`$ be a vector space over $`\mathbb{Q}`$, let $`e:V\to\mathbb{Q}`$ be linear, and let $`(\ell_j)_{j\in\iota}`$ be a finite family of linear functionals vanishing on $`\ker e`$. For any vectors $`(v_i)_{i\in\iota}`$, the matrix $`(\ell_j(v_i))_{i,j\in\iota}`$ has rank at most one, so every square minor of size at least two vanishes. Indeed, the functionals descend to $`V/\ker e`$, which has dimension at most one. This elementary linear-algebra argument applies at every matrix size. It does not cover additional functionals that fail to vanish on $`\ker e`$.*
> 
> *<span class="sans-serif">(uniform)</span> *linear-algebra* [`relationInvariantLinearChannels_det_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfTrappingReturnCarry.lean#L42)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_rank_le_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L37)

```lean
theorem paper_relationInvariant_channels_rank_le_one
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    ∃ u w : ι → ℚ, ∀ i j : ι, channel j (row i) = u i * w j
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_det_eq_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L63)

```lean
theorem paper_relationInvariant_channels_det_eq_zero
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    [Nontrivial ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    Matrix.det (fun i j : ι => channel j (row i)) = 0
```

<a id="record-257bm-k9-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_relationInvariant_channels_rank_le_one` | [E257_33/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L80) | [PaperStatementsAA.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L228) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |
| `paper_relationInvariant_channels_det_eq_zero` | [E257_33/Challenge.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_33/Challenge.lean#L71) | [PaperStatementsAA.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_33/PaperStatementsAA.lean#L219) | [E257_33](../../evidence/comparator/replay-35882032091/receipt-E257_33.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="record-257hg-k12"></a>

## Theorem 6.139 (Excluding the cell with value minus three), page 79

> *At a middle row $`D\ge13`$ followed only by right transitions, $`4\,\mathrm{rem}(D)-p_D^--4\ne-3`$, by Theorem <a href="#thm:final-middle-cell" data-reference-type="ref" data-reference="thm:final-middle-cell">87</a>. Its proof uses the nonnegative centred carry for the completed support, not a finite search. The values $`-2,-1`$ remain among the three exceptional negative cells. Excluding them under this extra tail assumption would still not exclude nonnegative values of the coordinate, or establish the all-middle-row and right-branch hypotheses in Theorem <a href="#thm:two-sided-dyadic" data-reference-type="ref" data-reference="thm:two-sided-dyadic">52</a>. The complete remaining tail inequality is stated in Remark <a href="#rem:tail-dominance-open" data-reference-type="ref" data-reference="rem:tail-dominance-open">260</a>.*
> 
> *<span class="sans-serif">(uniform)</span> *mobius-centred-carry* [`finalMiddleCell_neg_three_not_last`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L587) [`mobiusCenteredHalfCarry_add_two`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L39) [`cofiniteRightTail_ne_zero_centeredEndpoint`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFinalMiddleCellEscape.lean#L547)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_ne_neg_three`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L100)

```lean
theorem paper_final_middle_cell_ne_neg_three
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
        ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≠ -3
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_remaining_negative_values`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L118)

```lean
theorem paper_final_middle_cell_remaining_negative_values
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≤ -4 ∨
      0 ≤ 4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ∨
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_mobiusCenteredHalfCarry_add_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L155)

```lean
theorem paper_mobiusCenteredHalfCarry_add_two (A : Set ℕ) (N : ℕ) :
    mobiusCenteredHalfCarry A (N + 2) =
      4 * mobiusCenteredHalfCarry A N - pairedCenteredForcing A N
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_cofiniteRightTail_ne_zero_centeredEndpoint`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L163)

```lean
theorem paper_cofiniteRightTail_ne_zero_centeredEndpoint
    (A : Set ℕ) (D : ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (hcofinite : Set.Ioi D ⊆ A) :
    mobiusCenteredHalfCarry A (2 * D + 1) ≠ 0
```

<a id="record-257hg-k12-comparator"></a>

**Comparator:** not yet compared.

<a id="prop-unsafe-middle-range-exactly-three"></a>

## Proposition 6.140, page 79

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_unsafe_middle_range_is_three_integers`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LinearChannelAndMiddleCellExclusion.lean#L83)

```lean
theorem paper_unsafe_middle_range_is_three_integers {s : ℕ} (hs : 5 ≤ s) :
    ¬ (4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 ≤ -4 ∨
          0 ≤ 4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4) ↔
      4 * ((seamAdjacentCut s hs).remainder : ℤ) -
            ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -3 ∨
        4 * ((seamAdjacentCut s hs).remainder : ℤ) -
              ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -2 ∨
          4 * ((seamAdjacentCut s hs).remainder : ℤ) -
              ((seamAdjacentCut s hs).belowPulse : ℤ) - 4 = -1
```

<a id="prop-unsafe-middle-range-exactly-three-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_unsafe_middle_range_is_three_integers` | [E257_31/Challenge.lean, line 373](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_31/Challenge.lean#L373) | [PaperStructuresBP.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_31/PaperStructuresBP.lean#L131) | [E257_31](../../evidence/comparator/replay-35882032091/receipt-E257_31.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-approximations-without-compatibility"></a>

## Proposition 6.142, page 81

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_contains_strip_witness`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SharedPrefixFamiliesAndMeasureDichotomy.lean#L37)

```lean
theorem paper_shared_prefix_family_contains_strip_witness
    {K N : ℕ} (S : CylinderStage K N) :
    ∃ a : Erdos249257.HalfCarryReachability.HalfWord N,
      a ⟨0, Nat.zero_lt_succ N⟩ = false ∧
        (∀ h : 1 < N + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N - 1) : ℝ)| ≤
          (halfStripBound N : ℝ)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_strip_witness_after_feedback_all_depths`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L104)

```lean
theorem paper_shared_prefix_family_strip_witness_after_feedback_all_depths
    {K N : ℕ} (S : CylinderStage K N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) :
    ∃ a : Erdos249257.HalfCarryReachability.HalfWord (N + 1),
      a ⟨0, Nat.zero_lt_succ (N + 1)⟩ = false ∧
        (∀ h : 1 < N + 1 + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N + 1 - 1) : ℝ)| ≤
          (halfStripBound (N + 1) : ℝ)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_feedback_row_total_dichotomy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L84)

```lean
theorem paper_feedback_row_total_dichotomy
    {K N : ℕ} (S : CylinderStage K N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) :
    Nonempty (CylinderStage (K + 1) (N + 1)) ∨
      Nonempty (InStripTwoSheetStage K (N + 1))
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.halfTerminalOnlyStripWitness_of_feedbackAdvance`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L74)

```lean
theorem halfTerminalOnlyStripWitness_of_feedbackAdvance
    {K M : ℕ} (S : CylinderStage K M) :
    Erdos249257.HalfCarryReachability.HalfTerminalOnlyStripWitness M
```

where [`HalfTerminalOnlyStripWitness`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TerminalOnlyCofinal.lean#L24) is

```lean
def HalfTerminalOnlyStripWitness (M : ℕ) : Prop :=
  ∃ a : HalfWord M,
    a ⟨0, Nat.zero_lt_succ M⟩ = false ∧
    (∀ h : 1 < M + 1, a ⟨1, h⟩ = false) ∧
    |(integerHalfCarry (wordSupport a) (M - 1) : ℝ)| ≤
      (halfStripBound M : ℝ)
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.halfTerminalOnlyStripWitness_of_inStripTwoSheetStage_via_carries_three_four`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L53)

```lean
theorem halfTerminalOnlyStripWitness_of_inStripTwoSheetStage_via_carries_three_four
    {K M : ℕ} (T : InStripTwoSheetStage K M) :
    Erdos249257.HalfCarryReachability.HalfTerminalOnlyStripWitness M
```

where [`HalfTerminalOnlyStripWitness`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TerminalOnlyCofinal.lean#L24) is

```lean
def HalfTerminalOnlyStripWitness (M : ℕ) : Prop :=
  ∃ a : HalfWord M,
    a ⟨0, Nat.zero_lt_succ M⟩ = false ∧
    (∀ h : 1 < M + 1, a ⟨1, h⟩ = false) ∧
    |(integerHalfCarry (wordSupport a) (M - 1) : ℝ)| ≤
      (halfStripBound M : ℝ)
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.four_le_halfStripBound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L42)

```lean
theorem four_le_halfStripBound (m : ℕ) : 4 ≤ halfStripBound m
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_shared_prefix_family_strip_witness_after_feedback_of_all_depths`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/FeedbackRowStripWitnessAllDepths.lean#L121)

```lean
theorem paper_shared_prefix_family_strip_witness_after_feedback_of_all_depths
    {K N : ℕ} (S : CylinderStage K N) (_hN : 1 ≤ N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) (_h27 : 27 ≤ halfStripBound (N + 1)) :
    ∃ a : Erdos249257.HalfCarryReachability.HalfWord (N + 1),
      a ⟨0, Nat.zero_lt_succ (N + 1)⟩ = false ∧
        (∀ h : 1 < N + 1 + 1, a ⟨1, h⟩ = false) ∧
        |(integerHalfCarry (wordSupport a) (N + 1 - 1) : ℝ)| ≤
          (halfStripBound (N + 1) : ℝ)
```

<a id="prop-finite-approximations-without-compatibility-comparator"></a>

**Comparator:** not yet compared.

<a id="prop-exact-lebesgue-measure-dichotomy"></a>

## Proposition 6.146, page 83

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_volume_supportedMersenneAchievementSet_dichotomy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/SharedPrefixFamiliesAndMeasureDichotomy.lean#L68)

```lean
theorem paper_volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ENNReal) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0)
```

<a id="prop-exact-lebesgue-measure-dichotomy-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_volume_supportedMersenneAchievementSet_dichotomy` | [E257_34/Challenge.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_34/Challenge.lean#L229) | [PaperStatementsAM.lean, line 236](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_34/PaperStatementsAM.lean#L236) | [E257_34](../../evidence/comparator/replay-35882032091/receipt-E257_34.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
