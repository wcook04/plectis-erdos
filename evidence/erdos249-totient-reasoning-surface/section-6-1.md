# Formal evidence: The Binary Totient Series, Section 6, results 6.1 to 6.38

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="catalogue-cert-a9"></a>

## Theorem 6.1 (Rationality gives an eventual tail period), page 24

> *If $`S=a/(2^cv)`$ with $`a\in\mathbb Z`$, $`c\in\mathbb N`$ and $`v`$ a positive odd integer, then
> ``` math
> R_{N+h}-R_N\in\mathbb Z\qquad(N\ge c),\qquad h=\varphi(v)>0.
> ```
> Euler’s theorem gives $`v\mid2^h-1`$, and the prefix-tail identity then makes $`2^N(2^h-1)S`$ integral. Thus rationality supplies a positive shift for which all sufficiently late tail differences are integral.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`eventual_period_of_not_irrational`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L358)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR20.specified_euler_tail_period`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/SpecifiedTailPeriod.lean#L44)

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
| `specified_euler_tail_period` | [E249_05/Challenge.lean, line 166](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L166) | [PaperStatementsAX.lean, line 256](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAX.lean#L256) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d5"></a>

## Theorem 6.2 (Rationality forces unbounded carry rank), page 24

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

[`Erdos249257.not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientCarryKernelRigidity.lean#L300)

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
| `not_irrational_totientSeries_implies_unbounded_carryRank_unconditional` | [E249_32/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_32/Challenge.lean#L94) | [CarryRankFrontier.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_32/CarryRankFrontier.lean#L44) | [E249_32](../../evidence/comparator/replay-35882032091/receipt-E249_32.json) |

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

## Theorem 6.3 (Independence of the retained dyadic sections), page 24

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

[`ErdosProblems.Erdos249.PaperCompleteR8.displayed_canonical_and_full_dyadic`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR8/FullKernelAssemblies.lean#L177)

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
| `displayed_canonical_and_full_dyadic` | [E249_05/Challenge.lean, line 217](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L217) | [CompleteKernelBases.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/CompleteKernelBases.lean#L71) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a8"></a>

## Proposition 6.4 (Denominator divisibility forces tail integrality), page 25

> *If $`S=a/q`$ in lowest terms with $`q>0`$ and $`q\mid2^N(2^h-1)`$, then $`R_{N+h}-R_N\in\mathbb Z`$. Indeed, the prefix identity expresses that difference as $`2^N(2^h-1)S`$ minus an integer. This is the contradiction used by a nonintegrality certificate to exclude the rational value $`a/q`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`tail_diff_int_of_den_dvd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L327)*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.tail_diff_int_of_den_dvd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientTailPeriodKiller.lean#L327)

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
| `tail_diff_int_of_den_dvd` | [E249_05/Challenge.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L233) | [PaperStatementsAD.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAD.lean#L80) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-b5"></a>

## Proposition 6.5 (A cyclotomic factor remains after cancellation), page 25

> *If $`r`$ is squarefree, then
> ``` math
> \gcd\bigl(|P_r(2)|,|\Phi_r(2)|\bigr)=1,
>  \qquad |\Phi_r(2)|\mid\operatorname{den}(b_r).
> ```
> Here $`\Phi_r`$ is the $`r`$-th cyclotomic polynomial. Proposition <a href="#catalogue:mob:b4" data-reference-type="ref" data-reference="catalogue:mob:b4">91</a> gives $`P_r\equiv\mu(r)\pmod{\Phi_r}`$, and $`\mu(r)=\pm1`$ because $`r`$ is squarefree. This proves that the indicated cyclotomic factor cannot cancel from $`b_r`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`mobiusNumerator_gcd_cyclotomicValue`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CyclotomicProjectionOfShadow.lean#L350) [`cyclotomicValue_dvd_baseMobiusShadow_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CyclotomicProjectionOfShadow.lean#L389)*

The Lean declarations below together state this result.

1. [`Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_eval_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RepunitMobiusNumerator.lean#L445)

```lean
theorem mobiusNumeratorPolynomial_eval_two {r : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      RadicalMobiusShadow.mobiusNumerator r
```

2. [`Erdos249257.CyclotomicProjectionOfShadow.mobiusNumerator_gcd_cyclotomicValue`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CyclotomicProjectionOfShadow.lean#L350)

```lean
theorem mobiusNumerator_gcd_cyclotomicValue
    {r : ℕ} (hr : Squarefree r) :
    Nat.gcd
      (RadicalMobiusShadow.mobiusNumerator r).natAbs
      (cyclotomicValue r) = 1
```

3. [`Erdos249257.CyclotomicProjectionOfShadow.cyclotomicValue_dvd_baseMobiusShadow_den`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CyclotomicProjectionOfShadow.lean#L389)

```lean
theorem cyclotomicValue_dvd_baseMobiusShadow_den
    {r : ℕ} (hr : Squarefree r) :
    cyclotomicValue r ∣ (RadicalMobiusShadow.baseMobiusShadow r).den
```

<a id="catalogue-mob-b5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mobiusNumeratorPolynomial_eval_two` | [E249_05/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L272) | [PaperStatementsAQ.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAQ.lean#L58) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `mobiusNumerator_gcd_cyclotomicValue` | [E249_05/Challenge.lean, line 265](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L265) | [PaperStatementsAQ.lean, line 46](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAQ.lean#L46) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `cyclotomicValue_dvd_baseMobiusShadow_den` | [E249_05/Challenge.lean, line 260](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L260) | [PaperStatementsAQ.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAQ.lean#L42) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

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

## Proposition 6.6 (Primes in the upper half remain after cancellation), page 25

> *For $`t\ge5`$ the whole product
> ``` math
> \prod_{p\in\mathcal P_t}(2^p-1)
>        \ \mid\ \operatorname{den}(H_t\beta_{H_t})
> ```
> remains after cancellation. More generally, the source gives the same product-divisibility conclusion for a multiplier coprime to that product; it also supplies a sufficient condition on the multiplier’s prime factors. For the multiplier $`H_t/r_t`$, those prime factors are at most $`t`$, and the LCM result above follows.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`upperHalfPrimes`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L914) [`upperHalfChannel_product_dvd_den_of_scale_primeFactors_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L809) [`lcmHeight_upperHalf_product_dvd_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L983)*

The Lean declarations below together state this result.

1. [`Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmHeight_upperHalf_product_dvd_den`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L983)

```lean
theorem lcmHeight_upperHalf_product_dvd_den
    {t : ℕ} (ht : 5 ≤ t) :
    (∏ p ∈ upperHalfPrimes t, RadicalMobiusShadow.mersenne p) ∣
      ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den
```

2. [`Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfChannel_product_dvd_den_of_coprime_scale`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L795)

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

3. [`Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfChannel_product_dvd_den_of_scale_primeFactors_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MersenneShadowCyclotomicNoncollapse.lean#L809)

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
| `lcmHeight_upperHalf_product_dvd_den` | [E249_05/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L81) | [PaperStatementsAE.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L83) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `upperHalfChannel_product_dvd_den_of_coprime_scale` | [E249_05/Challenge.lean, line 88](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L88) | [PaperStatementsAE.lean, line 89](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L89) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `upperHalfChannel_product_dvd_den_of_scale_primeFactors_le` | [E249_05/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L100) | [PaperStatementsAE.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L100) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

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

## Proposition 6.7 (A lower bound for the reduced denominator), page 26

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

[`ErdosProblems.Erdos249.PaperCompleteR20.upper_half_product_denominator_bounds`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/DenominatorBounds.lean#L10)

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
| `upper_half_product_denominator_bounds` | [E249_05/Challenge.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L131) | [PaperStatementsAE.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L159) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Challenge for `upper_half_product_denominator_bounds`:

```lean
theorem upper_half_product_denominator_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ (∏ p ∈ upperHalfPrimes t, mersenne p) ∧
    (∏ p ∈ upperHalfPrimes t, mersenne p) ≤
      ((lcmHeight t : ℚ) * numericMobiusShadow (lcmHeight t)).den := by sorry
```

<a id="catalogue-mob-b7b"></a>

## Proposition 6.8 (The exact reduced denominator), page 26

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

1. [`Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_exact`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MersenneShadowDenominatorGrowth.lean#L147)

```lean
theorem lcmHeight_scaledMobiusShadow_den_exact (t : ℕ) :
    ((lcmHeight t : ℚ) *
        RadicalMobiusShadow.numericMobiusShadow (lcmHeight t)).den =
      RadicalMobiusShadow.mersenne (lcmRadical t) /
        Nat.gcd (RadicalMobiusShadow.mersenne (lcmRadical t))
          (lcmScale t *
            (CyclicTensorMobiusShadow.oddJordanScalar (lcmRadical t)).natAbs)
```

2. [`Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_five_scaledMobiusShadow_den_exact`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MersenneShadowDenominatorGrowth.lean#L187)

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
| `lcmHeight_scaledMobiusShadow_den_exact` | [E249_05/Challenge.lean, line 292](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L292) | [PaperStatementsAR.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAR.lean#L21) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `lcmHeight_five_scaledMobiusShadow_den_exact` | [E249_05/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L111) | [PaperStatementsAE.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L110) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

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

## Proposition 6.9 (Nonvanishing of a signed dyadic sum), page 26

> *Let $`I`$ be finite, let $`u_i\in\mathbb Z`$ and $`e_i\in\mathbb N`$, and suppose that $`m\in I`$ is the unique index with maximal exponent $`e_m`$. If $`u_m`$ is odd, then
> ``` math
> 2^{e_m}\sum_{i\in I}\frac{u_i}{2^{e_i}}
>        =\sum_{i\in I}u_i2^{e_m-e_i}\equiv1\pmod2.
> ```
> Indeed, every summand other than $`u_m`$ is even. The sum is therefore nonzero. In the determinant application, the rectangular Cauchy–Binet formula produces such finite signed sums from truncated moments. The result tests a specified configuration; it does not show that a suitable maximal-exponent term exists at arbitrarily large scales.*
> 
> *<span class="sans-serif">\[bounded\]</span> [`scaled_dyadic_sum_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SignedQMomentObstruction.lean#L96) [`det_mul_rectangular`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/SignedQMomentObstruction.lean#L29)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_clearing`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/SignedDyadicClearing.lean#L8)

```lean
theorem signed_dyadic_clearing {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α)
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (2 : ℚ) ^ e m * (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) =
      ((∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i) : ℤ) : ℚ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_sum_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/SignedDyadicClearing.lean#L28)

```lean
theorem signed_dyadic_sum_ne_zero {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) ≠ 0
```

3. [`Erdos249257.SignedQMomentObstruction.scaled_dyadic_sum_odd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/SignedQMomentObstruction.lean#L78)

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
| `signed_dyadic_clearing` | [E249_05/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L117) | [PaperStatementsAE.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L145) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `signed_dyadic_sum_ne_zero` | [E249_05/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L124) | [PaperStatementsAE.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L152) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `scaled_dyadic_sum_odd` | [E249_06/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L81) | [PaperStatementsAF.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAF.lean#L30) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a11"></a>

## Proposition 6.10 (Small certificates), page 26

> *For each integer $`1\le h\le8`$, the finite test $`\mathcal C(h,12,16)`$ holds. Each discrepancy uses two 16-term windows. Across all eight shifts, only the 24 distinct totient values at $`13\le n\le36`$ are needed, since the windows overlap. The source verifies the eight integer residue inequalities by exact computation.*
> 
> *Consequently, if $`a/b`$ is a reduced fraction with $`b>0`$ and $`b\mid2^{12}(2^h-1)`$ for at least one $`1\le h\le8`$, then $`S\ne a/b`$. This follows from Propositions <a href="#catalogue:cert:a6" data-reference-type="ref" data-reference="catalogue:cert:a6">69</a> and <a href="#catalogue:cert:a8" data-reference-type="ref" data-reference="catalogue:cert:a8">55</a>.*
> 
> *<span class="sans-serif">\[fixed\]</span> [`certifiedKill_all_small`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L404) [`totient_series_ne_rat_of_den_dvd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L416)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.small_certificate_windows`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L33)

```lean
theorem small_certificate_windows :
    certificateWindowIndices 8 12 16 = Finset.Icc 13 36 ∧
      (certificateWindowIndices 8 12 16).card = 24
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.small_certificates_and_exclusions`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L45)

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
| `small_certificate_windows` | [E249_06/Challenge.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L110) | [PaperStatementsG.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsG.lean#L58) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `small_certificates_and_exclusions` | [E249_06/Challenge.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L136) | [PaperStatementsI.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsI.lean#L92) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a12"></a>

## Proposition 6.11 (A common certificate for sixteen shifts), page 26

> *For each integer $`1\le h\le16`$, one has $`\mathcal C(h,14,9)`$. The common basepoint is $`14`$ and the depth is $`9`$; these parameters have different roles. The two windows for each shift use only the 25 distinct totient values at $`15\le n\le39`$ across the whole family. Thus $`S\ne a/b`$ for every reduced fraction with $`b>0`$ such that $`b\mid2^{14}(2^h-1)`$ for at least one $`1\le h\le16`$.*
> 
> *<span class="sans-serif">\[fixed\]</span> [`totient_series_ne_rat_of_den_dvd_pow_two_mul_mersenne_upto_sixteen`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18890)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificate_windows`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L39)

```lean
theorem sixteen_certificate_windows :
    certificateWindowIndices 16 14 9 = Finset.Icc 15 39 ∧
      (certificateWindowIndices 16 14 9).card = 25
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.sixteen_certificates_and_exclusions`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCertificateBatch.lean#L51)

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
| `sixteen_certificate_windows` | [E249_06/Challenge.lean, line 105](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L105) | [PaperStatementsG.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsG.lean#L54) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `sixteen_certificates_and_exclusions` | [E249_06/Challenge.lean, line 130](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L130) | [PaperStatementsI.lean, line 87](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsI.lean#L87) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-b11"></a>

## Proposition 6.12 (Historical diagonal examples and the complete band through 82), page 27

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

<a id="catalogue-cert-b11-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `historical_table_size_and_initial_depths` | [E249_06/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L97) | [PaperStatementsG.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsG.lean#L47) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `historical_table_and_complete_band` | [E249_06/Challenge.lean, line 124](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L124) | [PaperStatementsI.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsI.lean#L80) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a2"></a>

## Proposition 6.16 (The prefix-tail identity), page 28

> *For every $`N\in\mathbb N`$,
> ``` math
> 2^NS=\Phi_N+R_N,
>  \qquad \Phi_N=\sum_{n\le N}\varphi(n)2^{N-n}\in\mathbb Z.
> ```
> Thus $`R_N`$ and $`2^NS`$ have the same fractional part. Subtracting the identities at $`N+h`$ and $`N`$ gives the tail-difference congruence used in the irrationality criterion.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`two_pow_mul_totient_series_eq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L150)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.prefix_fractional_part`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/TailDepthCorrespondence.lean#L8)

```lean
theorem prefix_fractional_part (N : ℕ) :
    Int.fract ((2 : ℝ)^N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2^n)) =
      Int.fract (totientTail N)
```

2. [`Erdos249257.TotientTailPeriodKiller.two_pow_mul_totient_series_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientTailPeriodKiller.lean#L150)

```lean
theorem two_pow_mul_totient_series_eq (N : ℕ) :
    (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (totientPrefix N : ℝ) + totientTail N
```

3. [`Erdos249257.TotientTailPeriodKiller.tail_diff_mem_int_iff_scaled_series_mem_int`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/LcmConeFlatness.lean#L327)

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
| `prefix_fractional_part` | [E249_06/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L180) | [PaperStatementsAT.lean, line 237](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L237) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `two_pow_mul_totient_series_eq` | [E249_04/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L159) | [PaperStatementsAD.lean, line 90](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAD.lean#L90) | [E249_04](../../evidence/comparator/replay-35882032091/receipt-E249_04.json) |
| `tail_diff_mem_int_iff_scaled_series_mem_int` | [E249_06/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L156) | [PaperStatementsAD.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAD.lean#L77) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a5"></a>

## Lemma 6.17 (The necessary depth inequality), page 28

> *For $`h,N,L\in\mathbb{N}`$, the condition $`\mathcal C(h,N,L)`$ implies
> ``` math
> 2(N+h+L+2)<2^L.
> ```
> Indeed, its lower residue bound must be smaller than its upper bound. Thus $`L>1+\log_2(N+h+L+2)`$ whenever a certificate holds. In particular, a fixed depth cannot accommodate unbounded $`N+h`$. This is a necessary depth bound, not an upper bound for finding a certificate.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`certifiedKill_depth_floor`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L79)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.certificate_logarithmic_depth`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/TailDepthCorrespondence.lean#L20)

```lean
theorem certificate_logarithmic_depth {h N L : ℕ} (hc : certifiedKill h N L) :
    1 + Real.logb 2 ((N : ℝ)+h+L+2) < L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.fixed_depth_bounds_indices`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/TailDepthCorrespondence.lean#L30)

```lean
theorem fixed_depth_bounds_indices {h N L : ℕ} (hc : certifiedKill h N L) :
    N + h < 2^L
```

3. [`Erdos249257.TotientTailPeriodKiller.certifiedKill_depth_floor`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientTailPeriodKiller.lean#L79)

```lean
theorem certifiedKill_depth_floor {h N L : ℕ} (hcert : certifiedKill h N L) :
    (2 * (N + h + L + 2) : ℤ) < 2 ^ L
```

<a id="catalogue-cert-a5-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `certificate_logarithmic_depth` | [E249_06/Challenge.lean, line 172](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L172) | [PaperStatementsAT.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L181) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `fixed_depth_bounds_indices` | [E249_06/Challenge.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L176) | [PaperStatementsAT.lean, line 206](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L206) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `certifiedKill_depth_floor` | [E249_06/Challenge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L147) | [PaperStatementsAD.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAD.lean#L51) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a6"></a>

## Proposition 6.18 (A certificate implies nonintegrality), page 28

> *For all $`h,N,L\in\mathbb N`$,
> ``` math
> \mathcal C(h,N,L)\ \Longrightarrow\ R_{N+h}-R_N\notin\mathbb Z.
> ```
> The scaled truncation error satisfies $`|2^L(R_{N+h}-R_N)-D(h,N,L)|\le N+h+L+2`$. If the tail difference were integral, $`D(h,N,L)`$ would therefore lie within that distance of a multiple of $`2^L`$, contrary to the two strict residue inequalities.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`tail_diff_notMem_int_of_certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L262)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.totient_scaled_truncation_error`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/TailDepthCorrespondence.lean#L13)

```lean
theorem totient_scaled_truncation_error (h N L : ℕ) :
    |(2 : ℝ)^L * (totientTail (N+h) - totientTail N) -
      (windowDiscrepancy h N L : ℝ)| ≤ (N : ℝ)+h+L+2
```

2. [`Erdos249257.TotientTailPeriodKiller.tail_diff_notMem_int_of_certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientTailPeriodKiller.lean#L262)

```lean
theorem tail_diff_notMem_int_of_certifiedKill {h N L : ℕ} (hcert : certifiedKill h N L) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="catalogue-cert-a6-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totient_scaled_truncation_error` | [E249_06/Challenge.lean, line 185](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L185) | [PaperStatementsAT.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L247) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `tail_diff_notMem_int_of_certifiedKill` | [E249_06/Challenge.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L163) | [PaperStatementsAD.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAD.lean#L83) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-a7"></a>

## Theorem 6.19 (Nonintegrality gives a certificate at some depth), page 28

> *For every $`h,N\in\mathbb N`$,
> ``` math
> (\exists L\in\mathbb N,\ \mathcal C(h,N,L))
>  \quad\Longleftrightarrow\quad R_{N+h}-R_N\notin\mathbb Z.
> ```
> For the converse to Proposition <a href="#catalogue:cert:a6" data-reference-type="ref" data-reference="catalogue:cert:a6">69</a>, fix a positive distance from the nonintegral tail difference to the nearest integer. The normalised error $`(N+h+L+2)/2^L`$ tends to zero, so a sufficiently large truncation preserves that distance. This is a pointwise equivalence; irrationality requires the stated quantifiers over the shift and basepoint.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`exists_certifiedKill_iff_tail_diff_notMem_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/LcmConeFlatness.lean#L316)*

The Lean declaration below states this result.

[`Erdos249257.TotientTailPeriodKiller.exists_certifiedKill_iff_tail_diff_notMem_int`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/LcmConeFlatness.lean#L316)

```lean
theorem exists_certifiedKill_iff_tail_diff_notMem_int (h N : ℕ) :
    (∃ L, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="catalogue-cert-a7-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_certifiedKill_iff_tail_diff_notMem_int` | [E249_06/Challenge.lean, line 151](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L151) | [PaperStatementsAD.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAD.lean#L58) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-c1"></a>

## Proposition 6.21 (The Farey gap lemma), page 29

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

[`GapFareyBound.farey_gap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GapFareyBound.lean#L51)

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
| `farey_gap` | [E249_04/Challenge.lean, line 167](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L167) | [PaperStatementsAK.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L115) | [E249_04](../../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d1"></a>

## Proposition 6.22 (An irrationality criterion from rational approximations), page 29

> *Let $`x\in\mathbb R`$ and let $`u_k=p_k/q_k\in\mathbb Q`$ be in lowest terms, with $`q_k>0`$. If $`u_k\ne x`$ for every sufficiently large $`k`$ and $`q_k|x-u_k|\to0`$, then $`x`$ is irrational. Indeed, if $`x=a/b`$ with $`a\in\mathbb Z`$ and $`b\ge1`$, a nonzero integer numerator gives $`q_k|x-u_k|=|a q_k-b p_k|/b\ge1/b`$, a contradiction. This elementary criterion requires both nonvanishing and the scaled error estimate. Convergence $`u_k\to x`$ alone is insufficient, and the approximants need not be continued-fraction convergents.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`irrational_of_den_mul_abs_sub_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L5371)*

The Lean declaration below states this result.

[`Erdos249257.irrational_of_den_mul_abs_sub_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L5371)

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
| `irrational_of_den_mul_abs_sub_tendsto_zero` | [E249_06/Challenge.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L195) | [PaperStatementsAI.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L17) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d2"></a>

## Proposition 6.23 (An irrationality criterion from near integers), page 29

> *Let $`\xi\in\mathbb R`$. Suppose that for every integer $`q\ge1`$ there are integers $`m,z`$ with
> ``` math
> 0<|m\xi-z|<1/q.
> ```
> Then $`\xi`$ is irrational: if $`\xi=a/b`$ with $`b\ge1`$, every nonzero such difference is at least $`1/b`$. Restricting the multiplier to powers $`m=b_0^n`$ of a fixed integer base $`b_0\ge2`$ gives a sufficient special case, not a hypothesis satisfied by every irrational number. The strict lower bound excludes exact integer hits; the upper bound must be available for arbitrarily large $`q`$.*
> 
> *For a binary example, form a number by concatenating the blocks $`10`$ at square indices $`k\ge1`$ and $`01`$ at the other indices. Its binary expansion is not eventually periodic, since the block sequence has increasingly long gaps between the square indices, so the number is irrational. There are no three consecutive equal digits. Every fractional part after a binary shift therefore lies in $`[1/8,7/8]`$, and the multiples $`2^n\xi`$ do not approach the integers. This verifies that the restriction to base powers is genuinely stronger. This example is an ordinary mathematical argument, not an additional claim about the linked formalisation.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`irrational_of_int_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6120) [`irrational_of_pow_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L6149)*

The Lean declarations below together state a result at least as strong as this one. The Lean lower bound $|m\xi-z|\ge1/\operatorname{den}(\xi)$ uses the reduced denominator of $\xi$, which divides $b$ whenever $\xi=a/b$, so the printed bound $1/b$ follows. The near-integer criterion, its base-power case and the square-block example (irrationality, no three consecutive equal digits, fractional parts of $2^n\xi$ in $[1/8,7/8]$) are the remaining Lean statements as printed.

1. [`Erdos249257.irrational_of_int_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L6120)

```lean
theorem irrational_of_int_mul_near_int {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

2. [`Erdos249257.irrational_of_pow_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L6149)

```lean
theorem irrational_of_pow_mul_near_int (b : ℕ) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_near_integer_multiples`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NearIntegerIrrationalityCriterion.lean#L16)

```lean
theorem irrational_of_near_integer_multiples {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_near_integer_base_powers`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/NearIntegerIrrationalityCriterion.lean#L25)

```lean
theorem irrational_of_near_integer_base_powers (b₀ : ℕ) (hb : 2 ≤ b₀) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b₀ : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b₀ : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_le_abs_int_combination`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L33)

```lean
theorem one_div_den_le_abs_int_combination (p : ℚ) (m z : ℤ)
    (hne : (m : ℝ) * (p : ℝ) - (z : ℝ) ≠ 0) :
    (1 : ℝ) / (p.den : ℝ) ≤ |(m : ℝ) * (p : ℝ) - (z : ℝ)|
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.digit_block`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L393)

```lean
theorem digit_block (j : ℕ) :
    (IsSquare (j + 1) → digit (2 * j) = 1 ∧ digit (2 * j + 1) = 0) ∧
      (¬ IsSquare (j + 1) → digit (2 * j) = 0 ∧ digit (2 * j + 1) = 1)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_eventually_periodic`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L424)

```lean
theorem not_eventually_periodic (N P : ℕ) (hP : 0 < P) :
    ¬ ∀ k, N ≤ k → digit k = digit (k + P)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_xi`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L476)

```lean
theorem irrational_xi : Irrational xi
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.no_three_consecutive_equal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L408)

```lean
theorem no_three_consecutive_equal (n : ℕ) :
    ¬ (digit n = digit (n + 1) ∧ digit (n + 1) = digit (n + 2))
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.fract_two_pow_mul_xi_mem_Icc`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L480)

```lean
theorem fract_two_pow_mul_xi_mem_Icc (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * xi) ∈ Set.Icc (1 / 8 : ℝ) (7 / 8)
```

11. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.fract_mem_Icc_of_no_three_equal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L235)

```lean
theorem fract_mem_Icc_of_no_three_equal {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    Int.fract ((2 : ℝ) ^ n * tail d 0) ∈ Set.Icc (1 / 8 : ℝ) (7 / 8)
```

12. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_dist_xi`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L486)

```lean
theorem one_div_eight_le_dist_xi (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * xi - (z : ℝ)|
```

13. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_approaches_int`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L492)

```lean
theorem not_approaches_int {ε : ℝ} (hε : ε ≤ 1 / 8) :
    ¬ ∃ (n : ℕ) (z : ℤ), |(2 : ℝ) ^ n * xi - (z : ℝ)| < ε
```

14. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.not_near_integer_along_powers_of_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L502)

```lean
theorem not_near_integer_along_powers_of_two :
    ¬ ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
        0 < |(2 : ℝ) ^ n * xi - (z : ℝ)| ∧
          |(2 : ℝ) ^ n * xi - (z : ℝ)| < 1 / (q : ℝ)
```

15. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.exists_irrational_basePower_bounded_away`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L515)

```lean
theorem exists_irrational_basePower_bounded_away :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ∀ (n : ℕ) (z : ℤ), (1 : ℝ) / 8 ≤ |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)|
```

16. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.strict_lower_bound_needed`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L550)

```lean
theorem strict_lower_bound_needed :
    ¬ ∀ ξ : ℝ, (∀ q : ℕ, 0 < q → ∃ m z : ℤ,
        |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) → Irrational ξ
```

17. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.upper_bound_needed_for_every_q`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L566)

```lean
theorem upper_bound_needed_for_every_q (q : ℕ) (hq : 0 < q) :
    ∃ ξ : ℝ, ¬ Irrational ξ ∧ ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)
```

18. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail_mem_Icc`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L123)

```lean
theorem tail_mem_Icc {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) :
    1 / 8 ≤ tail d n ∧ tail d n ≤ 7 / 8
```

19. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_tail_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L269)

```lean
theorem irrational_tail_zero {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2)))
    (hper : ∀ N P : ℕ, 0 < P → ¬ ∀ k, N ≤ k → d k = d (k + P)) :
    Irrational (tail d 0)
```

20. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_abs_sub_int`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L243)

```lean
theorem one_div_eight_le_abs_sub_int {d : ℕ → ℕ} (hd : ∀ n, d n ≤ 1)
    (hrun : ∀ n, ¬ (d n = d (n + 1) ∧ d (n + 1) = d (n + 2))) (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * tail d 0 - (z : ℝ)|
```

<a id="catalogue-cert-d2-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_int_mul_near_int` | [E249_06/Challenge.lean, line 201](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L201) | [PaperStatementsAI.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L22) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_pow_mul_near_int` | [E249_06/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L207) | [PaperStatementsAI.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L28) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_near_integer_multiples` | [E249_06/Challenge.lean, line 222](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L222) | [PaperStatementsAJ.lean, line 399](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAJ.lean#L399) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_near_integer_base_powers` | [E249_06/Challenge.lean, line 216](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L216) | [PaperStatementsAJ.lean, line 393](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAJ.lean#L393) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `one_div_den_le_abs_int_combination` | [E249_06/Challenge.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L228) | [PaperStatementsAJ.lean, line 449](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAJ.lean#L449) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `digit_block` | [E249_06/Challenge.lean, line 244](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L244) | [PaperStatementsAL.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L22) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `not_eventually_periodic` | [E249_06/Challenge.lean, line 280](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L280) | [PaperStatementsAL.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L51) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_xi` | [E249_06/Challenge.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L269) | [PaperStatementsAL.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L42) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `no_three_consecutive_equal` | [E249_06/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L272) | [PaperStatementsAL.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L44) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `fract_two_pow_mul_xi_mem_Icc` | [E249_06/Challenge.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L259) | [PaperStatementsAL.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L34) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `fract_mem_Icc_of_no_three_equal` | [E249_06/Challenge.lean, line 254](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L254) | [PaperStatementsAL.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L30) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `one_div_eight_le_dist_xi` | [E249_06/Challenge.lean, line 295](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L295) | [PaperStatementsAL.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L63) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `not_approaches_int` | [E249_06/Challenge.lean, line 276](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L276) | [PaperStatementsAL.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L47) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `not_near_integer_along_powers_of_two` | [E249_06/Challenge.lean, line 284](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L284) | [PaperStatementsAL.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L54) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `exists_irrational_basePower_bounded_away` | [E249_06/Challenge.lean, line 249](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L249) | [PaperStatementsAL.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L26) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `strict_lower_bound_needed` | [E249_07/Challenge.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L50) | [PaperStatementsAL.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAL.lean#L71) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `upper_bound_needed_for_every_q` | [E249_07/Challenge.lean, line 60](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L60) | [PaperStatementsAL.lean, line 79](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAL.lean#L79) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `tail_mem_Icc` | [E249_07/Challenge.lean, line 55](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L55) | [PaperStatementsAL.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAL.lean#L75) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `irrational_tail_zero` | [E249_06/Challenge.lean, line 263](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L263) | [PaperStatementsAL.lean, line 37](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L37) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `one_div_eight_le_abs_sub_int` | [E249_06/Challenge.lean, line 290](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L290) | [PaperStatementsAL.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L59) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d3"></a>

## Proposition 6.24 (A nonzero evaluation minor gives independence), page 29

> *Let $`I`$ be a finite index set and let $`f_j:\mathbb N\to\mathbb Q`$ for $`j\in I`$. If there are evaluation points $`n_i\in\mathbb N`$ such that
> ``` math
> \det\bigl(f_j(n_i)\bigr)_{i,j\in I}\ne0,
> ```
> then the family $`(f_j)_{j\in I}`$ is linearly independent over $`\mathbb Q`$. A relation among the functions, evaluated at the $`n_i`$, gives a vector in the kernel of this nonsingular matrix, so all coefficients vanish. Finiteness is required to form the displayed determinant. In the totient application the arithmetic work is to construct these evaluation points; the implication itself is ordinary linear algebra.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`SeparatedMinorCertificate`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L83) [`linearIndependent_of_separatedMinorCertificate`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L91)*

The Lean declaration below states this result.

[`Erdos249257.linearIndependent_of_separatedMinorCertificate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/TotientMahlerDefect.lean#L91)

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
| `linearIndependent_of_separatedMinorCertificate` | [E249_07/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L76) | [PaperStructuresP.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStructuresP.lean#L36) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-cert-d9"></a>

## Proposition 6.25 (The gap between distinct rational numbers), page 29

> *If $`a/b<c/d`$ are reduced rational numbers with $`b,d>0`$, then
> ``` math
> \frac cd-\frac ab=\frac{bc-ad}{bd}\ge\frac1{bd}.
> ```
> The numerator $`bc-ad`$ is a positive integer. Thus an upper bound on a positive rational error gives a lower bound on the product of the reduced denominators. A large denominator in an unreduced displayed expression need not be the reduced denominator appearing in this conclusion.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`positive_rational_difference_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/PrimitiveRationalGapSupply.lean#L31)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.rational_difference_exact`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/RationalSpacingCorrespondence.lean#L6)

```lean
theorem rational_difference_exact (u v : ℚ) :
    (v : ℝ) - u =
      ((v.num * (u.den : ℤ) - u.num * (v.den : ℤ) : ℤ) : ℝ) /
        ((v.den : ℝ) * u.den)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.rational_cross_numerator_positive`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/RationalSpacingCorrespondence.lean#L17)

```lean
theorem rational_cross_numerator_positive {u v : ℚ} (h : u < v) :
    1 ≤ v.num * (u.den : ℤ) - u.num * (v.den : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.rational_error_denominator_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/RationalSpacingCorrespondence.lean#L27)

```lean
theorem rational_error_denominator_bound {u v : ℚ} {ε : ℝ}
    (h : u < v) (he : (v : ℝ) - u ≤ ε) :
    1 / ((u.den : ℝ) * ε) ≤ v.den
```

4. [`Erdos249257.positive_rational_difference_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/PrimitiveRationalGapSupply.lean#L31)

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
| `rational_difference_exact` | [E249_07/Challenge.lean, line 96](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L96) | [PaperStatementsAJ.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAJ.lean#L131) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `rational_cross_numerator_positive` | [E249_07/Challenge.lean, line 92](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L92) | [PaperStatementsAJ.lean, line 128](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAJ.lean#L128) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `rational_error_denominator_bound` | [E249_07/Challenge.lean, line 102](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L102) | [PaperStatementsAJ.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAJ.lean#L136) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `positive_rational_difference_lower_bound` | [E249_07/Challenge.lean, line 85](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L85) | [PaperStatementsAJ.lean, line 115](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAJ.lean#L115) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a1a"></a>

## Proposition 6.26 (The Möbius identity for $`S`$), page 30

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

1. [`MersenneLambertLadder.tsum_moebius_lambert_sq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/MersenneLambertLadder.lean#L491)

```lean
theorem tsum_moebius_lambert_sq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) * (r ^ (d : ℕ) / (1 - r ^ (d : ℕ)) ^ 2)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * r ^ (n : ℕ)
```

2. [`Erdos249257.totient_series_eq_half_add_moebius_mersenne_square`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L18454)

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
| `tsum_moebius_lambert_sq` | [E249_07/Challenge.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L122) | [PaperStatementsAP.lean, line 16](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAP.lean#L16) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `totient_series_eq_half_add_moebius_mersenne_square` | [E249_07/Challenge.lean, line 112](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L112) | [PaperStatementsAI.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAI.lean#L41) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a1b"></a>

## Corollary 6.27 (An equivalent irrationality question), page 30

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

[`ErdosProblems.Erdos249.PaperCompleteR7.irrational_totient_iff_moebius_square`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR7/ArithmeticAssemblies.lean#L40)

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
| `irrational_totient_iff_moebius_square` | [E249_07/Challenge.lean, line 131](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L131) | [PaperStatementsH.lean, line 16](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsH.lean#L16) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a2"></a>

## Proposition 6.28 (The squared-Lambert identity), page 30

> *Let $`w:\mathbb N\to\mathbb R`$ satisfy $`|w(d)|\le d`$ for $`d\ge1`$, and let $`0\le r<1`$. Then
> ``` math
> \sum_{d\ge1}w(d)\left(\frac{r^d}{1-r^d}\right)^2
>  =\sum_{n\ge1}\left(\sum_{d\mid n}w(d)\left(\frac nd-1\right)\right)r^n.
> ```
> Expand $`(x/(1-x))^2=\sum_{j\ge1}(j-1)x^j`$ and group terms by $`n=dj`$. Absolute convergence follows from the bound on $`w`$ and geometric decay. The cases $`w=\mu`$, $`w=1`$ and $`w=\varphi`$ give the next three series; the same algebra applies to each, but their arithmetic values differ.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`tsum_lambert_linear_weight_sq_pure`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L105)*

The Lean declaration below states this result.

[`GcdMomentCalculus.tsum_lambert_linear_weight_sq_pure`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GcdMomentCalculus.lean#L105)

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
| `tsum_lambert_linear_weight_sq_pure` | [E249_05/Challenge.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L54) | [PaperStatementsAK.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAK.lean#L134) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a4"></a>

## Proposition 6.30 (Weight one and divisor sums), page 30

> *$`\sum_{d:\mathbb{N}^+}' 1/(2^d-1)^2 = \sum_{n:\mathbb{N}^+}' \big(\sigma(n)-\tau(n)\big)\cdot(1/2)^n = \zeta_q(2) - \zeta_q(1)`$ at $`q=1/2`$. The displayed identity is formalised. Irrationality of its value follows from the cited linear independence result of Postelmans and Van Assche, as explained in Proposition <a href="#prop:zetaq" data-reference-type="ref" data-reference="prop:zetaq">48</a>; that literature result is not formalised here. Replacing the weight $`1`$ by $`\mu`$ changes the value to that of Definition <a href="#catalogue:mob:a3" data-reference-type="ref" data-reference="catalogue:mob:a3">80</a>. Observation <a href="#catalogue:mob:a6" data-reference-type="ref" data-reference="catalogue:mob:a6">83</a> compares the two choices of weight.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`tsum_one_div_mersenne_sq_eq_sigma_sub_tau_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L216)*

The Lean proof assumes the linear independence theorem of Postelmans and Van Assche. Lean takes this input as a hypothesis (`q_Pade_linear_independence`); it is not proved in Lean.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.divisor_sum_identity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquaredMersenneDivisorIdentities.lean#L36)

```lean
theorem divisor_sum_identity :
    ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = ∑' n : ℕ+,
          (((ArithmeticFunction.sigma 1 (n : ℕ) : ℕ) : ℝ)
            - ((ArithmeticFunction.sigma 0 (n : ℕ) : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.qZeta`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L17)

```lean
def qZeta (q : ℝ) (s : ℕ) : ℝ :=
  ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ (s - 1) * (q ^ (n : ℕ) / (1 - q ^ (n : ℕ)))
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.qZeta_half_two_sub_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L81)

```lean
theorem qZeta_half_two_sub_one :
    qZeta ((1 : ℝ) / 2) 2 - qZeta ((1 : ℝ) / 2) 1
      = ∑' d : ℕ+, 1 / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_qZeta_half_difference_of_linearIndependent`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/QZetaAnchor.lean#L143)

```lean
theorem irrational_qZeta_half_difference_of_linearIndependent
    (hli : ∀ a b c : ℚ,
      (a : ℝ) * 1 + (b : ℝ) * qZeta ((1 : ℝ) / 2) 1
        + (c : ℝ) * qZeta ((1 : ℝ) / 2) 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    Irrational (qZeta ((1 : ℝ) / 2) 2 - qZeta ((1 : ℝ) / 2) 1)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.moebius_weight_value`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquaredMersenneDivisorIdentities.lean#L98)

```lean
theorem moebius_weight_value :
    ∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
        / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
      = (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)) - 1 / 2
```

<a id="catalogue-mob-a4-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="catalogue-mob-a5"></a>

## Proposition 6.31 (Totient weight and gcd moments), page 31

> *$`\sum_{d:\mathbb{N}^+}' \varphi(d)/(2^d-1)^2 = \sum_{n:\mathbb{N}^+}' (P(n)-n)\cdot(1/2)^n`$, where $`P = \varphi * \mathrm{Id}`$ (Pillai’s gcd-sum function). It also equals $`\mathbb E[\gcd(X,Y)]`$ when $`X,Y`$ are independent and $`\mathbb P(X=n)=\mathbb P(Y=n)=2^{-n}`$ for $`n\ge1`$; see Proposition <a href="#prop:pillai" data-reference-type="ref" data-reference="prop:pillai">49</a>. This is a different weighted series. Its rationality is not settled by the identities proved here.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`tsum_totient_div_mersenne_sq_eq_gcd_moment_series`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L235)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.gcd_moment_identity_three_members`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L334)

```lean
theorem gcd_moment_identity_three_members :
    (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' n : ℕ+, (((pillaiP (n : ℕ) : ℕ) : ℝ) - ((n : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ))
      ∧ (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
            then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L307)

```lean
theorem tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
        then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.pillaiP_eq_totient_mul_id`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L67)

```lean
theorem pillaiP_eq_totient_mul_id (n : ℕ) :
    (totientArith * ArithmeticFunction.id) n = pillaiP n
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.sum_gcd_Icc_eq_pillaiP`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PillaiGcdExpectation.lean#L77)

```lean
theorem sum_gcd_Icc_eq_pillaiP (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, Nat.gcd k n = pillaiP n
```

5. [`GcdMomentCalculus.tsum_totient_div_mersenne_sq_eq_gcd_moment_series`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GcdMomentCalculus.lean#L235)

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
| `gcd_moment_identity_three_members` | [E249_05/Challenge.lean, line 137](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L137) | [PaperStatementsAE.lean, line 218](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L218) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq` | [E249_05/Challenge.lean, line 154](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L154) | [PaperStatementsAE.lean, line 335](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L335) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `pillaiP_eq_totient_mul_id` | [E249_05/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L146) | [PaperStatementsAE.lean, line 263](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L263) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `sum_gcd_Icc_eq_pillaiP` | [E249_05/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L150) | [PaperStatementsAE.lean, line 295](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAE.lean#L295) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `tsum_totient_div_mersenne_sq_eq_gcd_moment_series` | [E249_05/Challenge.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L62) | [PaperStatementsAK.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAK.lean#L150) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a7"></a>

## Proposition 6.33 (The weight of pairs divisible by a fixed integer), page 31

> *Let $`X,Y`$ be independent random variables with $`\mathbb P(X=n)=\mathbb P(Y=n)=2^{-n}`$ for $`n\ge1`$. For every $`d\ge1`$,
> ``` math
> \mathbb P(d\mid X,\ d\mid Y)=\frac1{(2^d-1)^2}.
> ```
> This follows by multiplying the two geometric sums $`\sum_{k\ge1}2^{-dk}=1/(2^d-1)`$. It explains the squared denominator in the preceding Möbius identity.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L266)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.pair_divisibility_mass`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquaredMersenneDivisorIdentities.lean#L62)

```lean
theorem pair_divisibility_mass (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.tsum_geometric_multiples`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquaredMersenneDivisorIdentities.lean#L79)

```lean
theorem tsum_geometric_multiples (d : ℕ) (hd : 0 < d) :
    ∑' k : ℕ, ((1 : ℝ) / 2) ^ (d * (k + 1)) = 1 / ((2 : ℝ) ^ d - 1)
```

3. [`GcdMomentCalculus.tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GcdMomentCalculus.lean#L266)

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
| `pair_divisibility_mass` | [E249_07/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L146) | [PaperStatementsAE.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAE.lean#L283) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `tsum_geometric_multiples` | [E249_07/Challenge.lean, line 164](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L164) | [PaperStatementsAE.lean, line 357](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAE.lean#L357) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `tsum_pos_pair_both_dvd_half_eq_inv_mersenne_sq` | [E249_04/Challenge.lean, line 180](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_04/Challenge.lean#L180) | [PaperStatementsAK.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_04/PaperStatementsAK.lean#L145) | [E249_04](../../evidence/comparator/replay-35882032091/receipt-E249_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a8"></a>

## Proposition 6.34 (The sum over coprime directions), page 31

> *The sum over positive coprime pairs satisfies
> ``` math
> \sum_{\substack{a,b\ge1\\\gcd(a,b)=1}}
>                   \frac1{2^{a+b}-1}=1.
> ```
> To see the normalisation, write every pair of positive integers uniquely as $`(ka,kb)`$ with $`\gcd(a,b)=1`$, and sum $`2^{-k(a+b)}`$ over $`k\ge1`$. The total is $`(\sum_{n\ge1}2^{-n})^2=1`$. This base-two normalisation is used in Proposition <a href="#catalogue:mob:a9a" data-reference-type="ref" data-reference="catalogue:mob:a9a">86</a>.*
> 
> *<span class="sans-serif">\[n/a\]</span> [`tsum_pos_coprime_inv_mersenne_eq_one`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L349)*

The Lean declaration below states this result.

[`GcdMomentCalculus.tsum_pos_coprime_inv_mersenne_eq_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GcdMomentCalculus.lean#L349)

```lean
theorem tsum_pos_coprime_inv_mersenne_eq_one :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
        then 1 / ((2 : ℝ) ^ (p.1 + p.2) - 1) else 0) = 1
```

<a id="catalogue-mob-a8-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `tsum_pos_coprime_inv_mersenne_eq_one` | [E249_07/Challenge.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L176) | [PaperStatementsAK.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAK.lean#L139) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a9a"></a>

## Proposition 6.35 (A Stern–Brocot recursion with stopping), page 32

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

1. [`ErdosProblems.Erdos249.PaperCompleteR21.divisibility_mass`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L42)

```lean
theorem divisibility_mass (a : ℕ) (ha : 0 < a) :
    (∑' k : ℕ, if 0 < k ∧ a ∣ k then ((1 : ℝ) / 2) ^ k else 0)
      = 1 / ((2 : ℝ) ^ a - 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.cylinderMass_eq_divisibility_mass_mul`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L86)

```lean
theorem cylinderMass_eq_divisibility_mass_mul (a b : ℕ+) :
    cylinderMass a b
      = (∑' k : ℕ, if 0 < k ∧ (a : ℕ) ∣ k then ((1 : ℝ) / 2) ^ k else 0)
        * (∑' k : ℕ, if 0 < k ∧ (b : ℕ) ∣ k then ((1 : ℝ) / 2) ^ k else 0)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.cylinder_mediant_split`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L95)

```lean
theorem cylinder_mediant_split (a b : ℕ+) :
    cylinderMass a b
      = 1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + cylinderMass (a + b) b + cylinderMass a (a + b)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.cylinder_root_values`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L103)

```lean
theorem cylinder_root_values :
    cylinderMass 1 1 = 1 ∧
      1 / ((2 : ℝ) ^ (((1 : ℕ+) : ℕ) + ((1 : ℕ+) : ℕ)) - 1) = 1 / 3 ∧
      cylinderMass (1 + 1) 1 = 1 / 3 ∧ cylinderMass 1 (1 + 1) = 1 / 3
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.normalised_split_probabilities`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L117)

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

6. [`ErdosProblems.Erdos249.PaperCompleteR21.stopping_transition_probabilities_sum_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L147)

```lean
theorem stopping_transition_probabilities_sum_one (a b : ℕ+) :
    ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
        / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      + ((2 : ℝ) ^ (a : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      + ((2 : ℝ) ^ (b : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) = 1
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.stopping_probability_ge_third`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SternBrocotStoppingRecursion.lean#L162)

```lean
theorem stopping_probability_ge_third (a b : ℕ+) :
    (1 : ℝ) / 3 ≤ ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
      / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
```

<a id="catalogue-mob-a9a-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `divisibility_mass` | [E249_07/Challenge.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L141) | [PaperStatementsAE.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAE.lean#L227) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `cylinderMass_eq_divisibility_mass_mul` | [E249_07/Challenge.lean, line 186](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L186) | [PaperStatementsAY.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAY.lean#L74) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `cylinder_mediant_split` | [E249_07/Challenge.lean, line 192](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L192) | [PaperStatementsAY.lean, line 79](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAY.lean#L79) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `cylinder_root_values` | [E249_07/Challenge.lean, line 198](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L198) | [PaperStatementsAY.lean, line 84](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAY.lean#L84) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `normalised_split_probabilities` | [E249_07/Challenge.lean, line 204](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L204) | [PaperStatementsAY.lean, line 110](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAY.lean#L110) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `stopping_transition_probabilities_sum_one` | [E249_07/Challenge.lean, line 157](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L157) | [PaperStatementsAE.lean, line 305](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAE.lean#L305) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `stopping_probability_ge_third` | [E249_07/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L152) | [PaperStatementsAE.lean, line 301](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAE.lean#L301) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-a9b"></a>

## Proposition 6.36 (Convergence with an explicit error), page 32

> *In the splitting identity of Proposition <a href="#catalogue:mob:a9a" data-reference-type="ref" data-reference="catalogue:mob:a9a">86</a>, the sum of the two child terms is at most $`2/3`$ of the parent term. If $`M_d(a,b)`$ is the sum of the contributions removed during the first $`d`$ levels, then
> ``` math
> |M(a,b)-M_d(a,b)|\le(2/3)^d M(a,b).
> ```
> In particular, $`M_d(a,b)\to M(a,b)`$. This convergence statement is separate from identifying the limit with a sum over any independently defined infinite set of descendants; no additional identification is asserted here.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`sternBrocotDepthMass_error`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L525) [`tendsto_sternBrocotDepthMass`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GcdMomentCalculus.lean#L560)*

The Lean declarations below together state this result.

1. [`GcdMomentCalculus.cylinderMass_children_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GcdMomentCalculus.lean#L514)

```lean
theorem cylinderMass_children_le (a b : ℕ+) :
    cylinderMass (a + b) b + cylinderMass a (a + b) ≤ (2 / 3) * cylinderMass a b
```

2. [`GcdMomentCalculus.sternBrocotDepthMass_error`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GcdMomentCalculus.lean#L525)

```lean
theorem sternBrocotDepthMass_error (dp : ℕ) :
    ∀ a b : ℕ+,
      0 ≤ cylinderMass a b - sternBrocotDepthMass dp a b
        ∧ cylinderMass a b - sternBrocotDepthMass dp a b
            ≤ (2 / 3 : ℝ) ^ dp * cylinderMass a b
```

3. [`GcdMomentCalculus.tendsto_sternBrocotDepthMass`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GcdMomentCalculus.lean#L560)

```lean
theorem tendsto_sternBrocotDepthMass (a b : ℕ+) :
    Filter.Tendsto (fun dp : ℕ => sternBrocotDepthMass dp a b)
      Filter.atTop (nhds (cylinderMass a b))
```

<a id="catalogue-mob-a9b-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cylinderMass_children_le` | [E249_07/Challenge.lean, line 172](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L172) | [PaperStatementsAK.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAK.lean#L129) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `sternBrocotDepthMass_error` | [E249_07/Challenge.lean, line 224](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L224) | [PaperStatementsB.lean, line 15](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsB.lean#L15) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `tendsto_sternBrocotDepthMass` | [E249_07/Challenge.lean, line 231](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L231) | [PaperStatementsB.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsB.lean#L23) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-b1"></a>

## Proposition 6.37 (A numerator polynomial and its coefficients), page 32

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

1. [`Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_coeff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RepunitMobiusNumerator.lean#L217)

```lean
theorem mobiusNumeratorPolynomial_coeff {r k : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).coeff k =
      if k < r then (gcdWordCoeff r k : ℤ) else 0
```

2. [`Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_coeff_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RepunitMobiusNumerator.lean#L234)

```lean
theorem mobiusNumeratorPolynomial_coeff_pos {r k : ℕ}
    (hr : Squarefree r) (hk : k < r) :
    0 < (mobiusNumeratorPolynomial r).coeff k
```

<a id="catalogue-mob-b1-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `mobiusNumeratorPolynomial_coeff` | [E249_07/Challenge.lean, line 246](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L246) | [PaperStatementsAC.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAC.lean#L36) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |
| `mobiusNumeratorPolynomial_coeff_pos` | [E249_07/Challenge.lean, line 251](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L251) | [PaperStatementsAC.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAC.lean#L40) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="catalogue-mob-b2"></a>

## Proposition 6.38 (Evaluation at two), page 32

> *For squarefree $`r\ge1`$, evaluation of $`P_r`$ at two gives the integer
> ``` math
> P_r(2)=\sum_{d\mid r}\mu(d)\frac rd
>                          \frac{2^r-1}{2^d-1}.
> ```
> Each quotient is an integer because $`d\mid r`$. The formal definition sums over subsets of the prime divisors of $`r`$; for squarefree $`r`$ these are exactly its divisors. This identifies the polynomial calculation with the numerator used in $`b_r`$.*
> 
> *<span class="sans-serif">\[uniform\]</span> [`mobiusNumeratorPolynomial_eval_two`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RepunitMobiusNumerator.lean#L445) [`mobiusNumerator`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RadicalMobiusShadow.lean#L101)*

The Lean declarations below together state this result.

1. [`Erdos249257.RepunitMobiusNumerator.mobiusNumeratorPolynomial_eval_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/RepunitMobiusNumerator.lean#L445)

```lean
theorem mobiusNumeratorPolynomial_eval_two {r : ℕ} (hr : Squarefree r) :
    (mobiusNumeratorPolynomial r).eval 2 =
      RadicalMobiusShadow.mobiusNumerator r
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.numerator_eval_two_divisors`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/NumeratorEvaluation.lean#L32)

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
| `mobiusNumeratorPolynomial_eval_two` | [E249_05/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_05/Challenge.lean#L272) | [PaperStatementsAQ.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_05/PaperStatementsAQ.lean#L58) | [E249_05](../../evidence/comparator/replay-35882032091/receipt-E249_05.json) |
| `numerator_eval_two_divisors` | [E249_07/Challenge.lean, line 279](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_07/Challenge.lean#L279) | [PaperStatementsAQ.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_07/PaperStatementsAQ.lean#L63) | [E249_07](../../evidence/comparator/replay-35882032091/receipt-E249_07.json) |

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
