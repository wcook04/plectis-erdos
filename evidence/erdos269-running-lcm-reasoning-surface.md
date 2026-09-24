# Formal evidence: The Three-Prime Running LCM: Kernel Rank and Tail Arithmetic

This record belongs to the paper [erdos269-running-lcm-reasoning-surface.pdf](../paper/269/erdos269-running-lcm-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`c91562bd574a`](https://github.com/wcook04/plectis-erdos/tree/c91562bd574a387cde904481e609c7b4cacebb14) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35882032091](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35882032091) at corpus commit [`a2faa350b45a`](https://github.com/wcook04/plectis-erdos-lean/tree/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3) (tag `paper-evidence-2026-09-23`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 33 results: 32 with a Lean proof of the whole statement, 1 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 32 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="long269-res-lead-two-prime"></a>

## Theorem 1.1 (two-prime transcendence), page 1

> *Let $`p`$ and $`q`$ be distinct primes. Then $`\mathcal R_{\{p,q\}}`$ and $`\mathcal D_{\{p,q\}}`$ are transcendental.*

The Lean proof assumes the transcendence theorem of Bugeaud and Laurent. Lean takes this input as a hypothesis (`BugeaudLaurentTranscendence`); it is not proved in Lean.

1. [`ErdosProblems.Erdos269.PaperCompleteR21.two_prime_transcendence`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L924)

```lean
theorem two_prime_transcendence (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Transcendental ℚ (repeatedSum p q) ∧ Transcendental ℚ (distinctSum p q)
```

2. [`ErdosProblems.Erdos269.PaperCompleteR21.two_prime_sums_transcendental`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L872)

```lean
theorem two_prime_sums_transcendental (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (distinctSum p q) ∧ Transcendental ℚ (repeatedSum p q)
```

3. [`ErdosProblems.Erdos269.PaperCompleteR21.repeatedSum_comm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L893)

```lean
theorem repeatedSum_comm {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    repeatedSum p q = repeatedSum q p
```

4. [`ErdosProblems.Erdos269.PaperCompleteR21.distinctSum_comm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L906)

```lean
theorem distinctSum_comm {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    distinctSum p q = distinctSum q p
```

5. [`ErdosProblems.Erdos269.PaperCompleteR21.transcendental_heckeValue`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L775)

```lean
theorem transcendental_heckeValue (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (PaperR7.twoPrimeHeckeValue p q)
```

The assumed input [`BugeaudLaurentTranscendence`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR21/TwoPrimeSums.lean#L630) is

```lean
def BugeaudLaurentTranscendence : Prop :=
  ∀ θ β α : ℝ, Irrational θ → 0 < θ → θ < 1 →
    IsAlgebraic ℚ β → IsAlgebraic ℚ α → β ≠ 0 → α ≠ 0 →
    |β| < 1 → |β| * |α| ^ θ < 1 →
    Transcendental ℚ (heckeMahlerSeries θ β α)
```

<a id="long269-res-lead-two-prime-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="long269-res-lcm"></a>

## Theorem 2.1 (the running least common multiple), page 4

> *Let $`p,q,r`$ be pairwise distinct primes and $`x\ge1`$. Then $`\operatorname{L}(x)=\operatorname{H}(x)`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperCompleteR20.running_lcm_real_cutoff_exact`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L49)

```lean
theorem running_lcm_real_cutoff_exact {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x : ℝ} (hx : 1 ≤ x) :
    realPrefixLcm p q r x = realThreePrimeHeight p q r x
```

<a id="long269-res-lcm-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `running_lcm_real_cutoff_exact`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_01/Challenge.lean#L176) (E269_01, line 176), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L67) (PaperStatementsD.lean, line 67), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_01.json) (E269_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-cell"></a>

## Proposition 2.2 (constancy and jump ratios), page 4

> *If $`x,y\ge1`$ lie in the same logarithmic cell then $`\operatorname{L}(x)=\operatorname{L}(y)`$, and the same holds for the kernel at two smooth points of one cell. If $`\lfloor\log_p y\rfloor=\lfloor\log_p x\rfloor+1`$ while the other two logarithms agree, then $`\operatorname{L}(y)=p\,\operatorname{L}(x)`$, and similarly with $`q`$ or $`r`$ in place of $`p`$.*

The Lean declarations below together state this result or one that implies it. The Lean kernel clause holds for all integers $p,q,r>1$, without primality or distinctness; the constancy and jump clauses are the other Lean statements, for real $x,y\ge1$ and pairwise distinct primes.

1. [`ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_eq_of_sameLogCell`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L65)

```lean
theorem realPrefixLcm_eq_of_sameLogCell
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hcell : SameThreePrimeRealLogCell p q r x y) :
    realPrefixLcm p q r x = realPrefixLcm p q r y
```

2. [`ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_first`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L87)

```lean
theorem realPrefixLcm_jump_first
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊ + 1)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realPrefixLcm p q r y = p * realPrefixLcm p q r x
```

3. [`ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_second`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L117)

```lean
theorem realPrefixLcm_jump_second
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊ + 1)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊) :
    realPrefixLcm p q r y = q * realPrefixLcm p q r x
```

4. [`ErdosProblems.Erdos269.PaperCompleteR20.realPrefixLcm_jump_third`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L129)

```lean
theorem realPrefixLcm_jump_third
    {p q r : ℕ} (pPrime : p.Prime) (qPrime : q.Prime) (rPrime : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hp : ⌊Real.logb p y⌋₊ = ⌊Real.logb p x⌋₊)
    (hq : ⌊Real.logb q y⌋₊ = ⌊Real.logb q x⌋₊)
    (hr : ⌊Real.logb r y⌋₊ = ⌊Real.logb r x⌋₊ + 1) :
    realPrefixLcm p q r y = r * realPrefixLcm p q r x
```

5. [`ErdosProblems.Erdos269.PaperCompleteR20.threePrimeKernelQ_eq_of_sameRealLogCell`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L142)

```lean
theorem threePrimeKernelQ_eq_of_sameRealLogCell
    {p q r i j k i' j' k' : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hcell : SameThreePrimeRealLogCell p q r
      (smooth3Val p q r i j k : ℝ) (smooth3Val p q r i' j' k' : ℝ)) :
    threePrimeKernelQ p q r i j k =
      threePrimeKernelQ p q r i' j' k'
```

<a id="long269-res-cell-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `realPrefixLcm_eq_of_sameLogCell`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_01/Challenge.lean#L124) (E269_01, line 124), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L20) (PaperStatementsD.lean, line 20), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_01.json) (E269_01)
- `realPrefixLcm_jump_first`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_01/Challenge.lean#L132) (E269_01, line 132), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L27) (PaperStatementsD.lean, line 27), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_01.json) (E269_01)
- `realPrefixLcm_jump_second`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_01/Challenge.lean#L142) (E269_01, line 142), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L36) (PaperStatementsD.lean, line 36), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_01.json) (E269_01)
- `realPrefixLcm_jump_third`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_01/Challenge.lean#L152) (E269_01, line 152), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L45) (PaperStatementsD.lean, line 45), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_01.json) (E269_01)
- `threePrimeKernelQ_eq_of_sameRealLogCell`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_01/Challenge.lean#L183) (E269_01, line 183), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L73) (PaperStatementsD.lean, line 73), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_01.json) (E269_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-count"></a>

## Proposition 2.3 (jump count), page 4

> *Let $`n\ge0`$. The set of the first $`n`$ positive powers of $`p`$, of $`q`$ and of $`r`$ has exactly $`3n`$ elements, and adjoining the common origin $`1`$ gives exactly $`3n+1`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos269.PaperR7.paper_jump_count`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L69)

```lean
theorem paper_jump_count {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) :
    (threePrimePositiveJumpSet p q r n).card = 3 * n ∧
    (threePrimeJumpSetWithOrigin p q r n).card = 3 * n + 1
```

<a id="long269-res-count-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_jump_count`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_01/Challenge.lean#L206) (E269_01, line 206), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_01/PaperStatementsA.lean#L247) (PaperStatementsA.lean, line 247), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_01.json) (E269_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-fibre"></a>

## Proposition 2.4 (grouping equal heights), page 5

> *For every box $`\mathcal B`$,
> ``` math
> \sum_{(i,j,k)\in\mathcal B}\operatorname{K}(i,j,k)=\sum_{H}\#F(H)/H,
> ```
> the outer sum ranging over the heights attained on $`\mathcal B`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos269.finiteSmoothKernelSum_groupedByHeight`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L407)

```lean
theorem finiteSmoothKernelSum_groupedByHeight
    (p q r hp hq hr : ℕ) :
    (∑ e ∈ smoothExponentBox hp hq hr,
      threePrimeKernelQ p q r e.1 e.2.1 e.2.2) =
      ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r),
        (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹)
```

<a id="long269-res-fibre-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `finiteSmoothKernelSum_groupedByHeight`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_01/Challenge.lean#L228) (E269_01, line 228), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_01/ThreePrimeStructure.lean#L84) (ThreePrimeStructure.lean, line 84), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_01.json) (E269_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-short"></a>

## Lemma 2.5 (uniqueness in a short interval), page 5

> *Let $`b\ge1`$ and $`\eta\le b\,\lambda`$. If $`b^{a}w`$ and $`b^{a'}w`$ both lie in $`[\lambda,\eta)`$ then $`a=a'`$.*

The Lean declaration below states this result or one that implies it. The Lean statement drops the standing assumption $0\le\lambda<\eta$ on the interval: for every real $b\ge1$, $w\ge0$ and real $\lambda,\eta$ with $\eta\le b\lambda$, two points $b^aw,b^{a'}w$ of $[\lambda,\eta)$ have $a=a'$, which is the printed statement.

[`ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_real_base_short_interval`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealBaseShortInterval.lean#L10)

```lean
theorem exponent_unique_real_base_short_interval
    {base lo hi weight : ℝ} {a b : ℕ}
    (hbase : 1 ≤ base) (hweight : 0 ≤ weight)
    (hwidth : hi ≤ base * lo)
    (haLo : lo ≤ base ^ a * weight) (haHi : base ^ a * weight < hi)
    (hbLo : lo ≤ base ^ b * weight) (hbHi : base ^ b * weight < hi) :
    a = b
```

<a id="long269-res-short-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exponent_unique_real_base_short_interval`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_01/Challenge.lean#L239) (E269_01, line 239), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_01/PaperStatementsB.lean#L25) (PaperStatementsB.lean, line 25), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_01.json) (E269_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-drop"></a>

## Proposition 2.6 (counting a shell by two coordinates), page 5

> *<span id="long269:res:shell" label="long269:res:shell"></span> If $`\eta\le r\,\lambda`$ then $`\#\mathcal S\le(h_p+1)(h_q+1)`$, and if $`\eta\le p\,\lambda`$ then $`\#\mathcal S\le(h_q+1)(h_r+1)`$. If moreover $`\eta\le r\,\lambda`$ and $`h_p\le h_q\le h_r`$ with $`h_p+h_q+h_r=j`$, then $`9\,\#\mathcal S\le(j+3)^{2}`$.*

The Lean declaration below states this result or one that implies it. The Lean statement needs only $p,r\ge1$ and any natural number $q$, in place of three distinct primes, and allows any real interval $[\lambda,\eta)$; its three clauses are the three printed bounds on $\#\mathcal S$.

[`ErdosProblems.Erdos269.PaperCompleteR20.realSmoothExponentShell_bounds`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealCutoffs.lean#L285)

```lean
theorem realSmoothExponentShell_bounds
    {p q r hp hq hr j : ℕ} {lo hi : ℝ}
    (hpPos : 0 < p) (hrPos : 0 < r) :
    (hi ≤ (r : ℝ) * lo →
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (hp + 1) * (hq + 1)) ∧
    (hi ≤ (p : ℝ) * lo →
      (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (hq + 1) * (hr + 1)) ∧
    (hi ≤ (r : ℝ) * lo → hp ≤ hq → hq ≤ hr → hp + hq + hr = j →
      9 * (realSmoothExponentShell p q r lo hi hp hq hr).card ≤
        (j + 3) ^ 2)
```

<a id="long269-res-drop-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `realSmoothExponentShell_bounds`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_01/Challenge.lean#L162) (E269_01, line 162), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_01/PaperStatementsD.lean#L54) (PaperStatementsD.lean, line 54), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_01.json) (E269_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-two-prime-rank"></a>

## Proposition 4.1 (two generators separate), page 7

> *For real $`p,q>1`$, with $`L_{p,q}(t)=p^{\lfloor\log_p t\rfloor}q^{\lfloor\log_q t\rfloor}`$ as above, and all integers $`i,j\ge0`$, the two-prime kernel $`\operatorname{K}_2(i,j)=1/L_{p,q}(p^iq^j)`$ is the outer product
> ``` math
> \operatorname{K}_2(i,j)
>  =\bigl(p^{i}q^{\lfloor\log_q p^{i}\rfloor}\bigr)^{-1}
>   \bigl(p^{\lfloor\log_p q^{j}\rfloor}q^{j}\bigr)^{-1},
> ```
> so every two-by-two minor of $`\operatorname{K}_2`$ vanishes.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperCompleteR20.real_two_prime_separation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealTwoPrimeKernel.lean#L63)

```lean
theorem real_two_prime_separation {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    (∀ i j : ℕ, realTwoPrimeKernel p q i j =
      (p ^ i * q ^ ⌊Real.logb q (p ^ i)⌋)⁻¹ *
        (p ^ ⌊Real.logb p (q ^ j)⌋ * q ^ j)⁻¹) ∧
    (∀ i i' j j' : ℕ,
      realTwoPrimeKernel p q i j * realTwoPrimeKernel p q i' j' -
        realTwoPrimeKernel p q i j' * realTwoPrimeKernel p q i' j = 0)
```

<a id="long269-res-two-prime-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `real_two_prime_separation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L59) (E269_02, line 59), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsB.lean#L27) (PaperStatementsB.lean, line 27), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-rank"></a>

## Proposition 4.2 (non-separability at $`\{2,3,5\}`$), page 8

> *With $`(p,q,r)=(2,3,5)`$,
> ``` math
> \det\begin{pmatrix}
>  \operatorname{K}(0,0,0)&\operatorname{K}(0,1,0)\\
>  \operatorname{K}(1,0,0)&\operatorname{K}(1,1,0)
>  \end{pmatrix}
>  =\det\begin{pmatrix}1&1/6\\1/2&1/60\end{pmatrix}
>  =-\frac1{15}\ne0 .
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos269.PaperR7.paper_two_by_two_fixture`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L102)

```lean
theorem paper_two_by_two_fixture :
    threePrimeKernelQ 2 3 5 0 0 0 = 1 ∧
    threePrimeKernelQ 2 3 5 0 1 0 = 1 / 6 ∧
    threePrimeKernelQ 2 3 5 1 0 0 = 1 / 2 ∧
    threePrimeKernelQ 2 3 5 1 1 0 = 1 / 60 ∧
    (Matrix.det (fun i j : Fin 2 => threePrimeKernelQ 2 3 5 i j 0)) = -(1 / 15 : ℚ) ∧
    (Matrix.det (fun i j : Fin 2 => threePrimeKernelQ 2 3 5 i j 0)) ≠ 0
```

<a id="long269-res-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_two_by_two_fixture`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L76) (E269_02, line 76), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsA.lean#L244) (PaperStatementsA.lean, line 244), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-infinite-rank"></a>

## Theorem 4.3 (no finite separation of the kernel), page 8

> *<span id="long269:res:lead-infinite-rank" label="long269:res:lead-infinite-rank"></span> Let $`p,q,r`$ be primes with $`p\ne q`$, $`p\ne r`$ and $`q\ne r`$. For every $`n\ge1`$ there are injective maps $`I,J:\{0,\ldots,n-1\}\to\mathbb{N}`$ such that, for every $`k\ge0`$,
> ``` math
> \det\bigl(\operatorname{K}(I(a),J(b),k)\bigr)_{0\le a,b<n}\ne0 .
> ```
> Consequently, for no finite $`d`$ do there exist rational-valued functions $`f_\ell:\mathbb{N}\to\mathbb{Q}`$ and $`G_\ell:\mathbb{N}^{2}\to\mathbb{Q}`$, $`0\le\ell<d`$, satisfying $`\operatorname{K}(i,j,k)=\sum_{\ell<d}f_\ell(i)G_\ell(j,k)`$ for all $`i,j,k`$.*

The Lean declaration below states this result or one that implies it. The Lean statement also covers $n=0$, where the determinant is empty and equals $1$; for $n\ge1$ it is the printed minor statement, and its second clause is the printed nonseparation for every finite $d$.

[`ErdosProblems.Erdos269.PaperR7.paper_uniform_rank_and_nonseparation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR7BasicAssembly.lean#L22)

```lean
theorem paper_uniform_rank_and_nonseparation {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (_hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ, ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
      ∀ k : ℕ, (Matrix.det fun a b : Fin n =>
        threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
    (∀ d : ℕ, ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
      ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k)
```

<a id="long269-res-infinite-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_uniform_rank_and_nonseparation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L85) (E269_02, line 85), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsA.lean#L252) (PaperStatementsA.lean, line 252), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-finite-cut-rank"></a>

## Proposition 4.4 (rank of threshold columns), page 9

> *Let $`m\ge1`$ and let $`c`$ lie in a field with $`c\ne0,1`$. For $`0\le h\le m`$, let $`v_h`$ be the length-$`m`$ column whose first $`h`$ entries are $`1`$ and whose remaining entries are $`c`$. If the distinct columns of a matrix are the $`v_h`$ with $`h`$ in a nonempty set $`E\subseteq\{0,\ldots,m\}`$, then its rank is
> ``` math
> |E|-\mathbf 1_{\{0,m\}\subseteq E}.
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement drops the hypothesis that $E$ is nonempty; for nonempty $E\subseteq\{0,\ldots,m\}$ and any finite matrix whose set of columns is $\{v_h:h\in E\}$ it gives the printed rank $|E|-\mathbf 1_{\{0,m\}\subseteq E}$.

[`ErdosProblems.Erdos269.PaperR7.rank_cutMatrix`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR7FiniteCutRank.lean#L182)

```lean
theorem rank_cutMatrix {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutVector c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0
```

<a id="long269-res-finite-cut-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `rank_cutMatrix`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L146) (E269_02, line 146), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStructuresH.lean#L18) (PaperStructuresH.lean, line 18), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)

Challenge for `rank_cutMatrix`:

```lean
theorem rank_cutMatrix {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (c : F) (hc0 : c ≠ 0) (hc1 : c ≠ 1) {m : ℕ} (hm : 0 < m)
    (E : Finset ℕ) (hbound : ∀ k ∈ E, k ≤ m)
    (A : Matrix (Fin m) ι F)
    (hcols : Set.range A.col = Set.range (fun k : E => cutVector c m k)) :
    A.rank = E.card - if 0 ∈ E ∧ m ∈ E then 1 else 0 := by sorry
```

<a id="long269-res-uniform-rank"></a>

## Theorem 4.5 (distance from matrices of finite separated rank), page 11

> *Let $`p,q,r`$ be pairwise distinct primes and let $`C`$ be as in (5). Then
> ``` math
> \inf_{A}\ \sup_{i,j\ge0}\ |C(i,j)-A(i,j)|=\frac{1-t}{2}=\frac{r-1}{2r},
> ```
> the infimum being over all matrices $`A`$ of finite separated rank, and it is attained by the constant matrix of value $`(1+t)/2`$.*

The Lean declaration below states this result or one that implies it. The Lean statement drops the hypothesis $p\ne q$, requiring only primes $p,q$ different from $r$; it gives both printed values $(1-t)/2=(r-1)/(2r)$ of the infimum and the constant matrix $(1+t)/2$, $t=r^{-1}$, attaining it.

[`ErdosProblems.Erdos269.PaperR8.uniform_rank_complete`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR8UniformRank.lean#L321)

```lean
theorem uniform_rank_complete {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal ((1 - (r : ℝ)⁻¹) / 2) ∧
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal (((r : ℝ) - 1) / (2 * (r : ℝ))) ∧
    ∃ A : FiniteRankMatrix,
      (∀ i j, A.val i j = (1 + (r : ℝ)⁻¹) / 2) ∧
      uniformError (realCarryMatrix p q r) A.val =
        (⨅ F : FiniteRankMatrix, uniformError (realCarryMatrix p q r) F.val)
```

<a id="long269-res-uniform-rank-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `uniform_rank_complete`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L179) (E269_02, line 179), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsE.lean#L24) (PaperStatementsE.lean, line 24), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-dyadic-alphabet"></a>

## Proposition 5.1 (four possible bases), page 12

> *For every $`a`$,
> ``` math
> \begin{equation}
> \label{long269:eq:dyadic-alphabet}
>  b_a=\frac{P_{a+1}}{P_a}=2\prod_{(p,e)\in I_a}p\in\{2,6,10,30\},
>  \qquad\text{so}\qquad 2\le b_a\le30 .
> \end{equation}
> ```*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos269.dyadicInternalPower_exponent_unique`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L669)

```lean
theorem dyadicInternalPower_exponent_unique
    {p a e f : ℕ} (hp : 2 ≤ p)
    (he : DyadicInternalPower p a e)
    (hf : DyadicInternalPower p a f) :
    e = f
```

2. [`ErdosProblems.Erdos269.exists_dyadicInternalPower_iff_log_succ`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L701)

```lean
theorem exists_dyadicInternalPower_iff_log_succ
    {p a : ℕ} (hp : 2 < p) (hpOdd : Odd p) :
    (∃ e, DyadicInternalPower p a e) ↔
      Nat.log p (2 ^ (a + 1)) = Nat.log p (2 ^ a) + 1
```

3. [`ErdosProblems.Erdos269.log_dyadic_succ_eq_of_no_internalPower`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L734)

```lean
theorem log_dyadic_succ_eq_of_no_internalPower
    {p a : ℕ} (hp : 2 < p) (hpOdd : Odd p)
    (hNo : ¬ ∃ e, DyadicInternalPower p a e) :
    Nat.log p (2 ^ (a + 1)) = Nat.log p (2 ^ a)
```

4. [`ErdosProblems.Erdos269.threePrimeHeight_dyadicBlock_succ`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L781)

```lean
theorem threePrimeHeight_dyadicBlock_succ (a : ℕ) :
    threePrimeHeight 2 3 5 (2 ^ (a + 1)) =
      dyadicBlockBase235 a * threePrimeHeight 2 3 5 (2 ^ a)
```

5. [`ErdosProblems.Erdos269.PaperR7.radix_eq_height_ratio`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR7ActualOrbit.lean#L56)

```lean
theorem radix_eq_height_ratio (a : ℕ) :
    (dyadicBlockBase235 a : ℚ) =
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) /
        (threePrimeHeight 2 3 5 (2 ^ a) : ℚ)
```

6. [`ErdosProblems.Erdos269.dyadicBlockBase235_cases`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L762)

```lean
theorem dyadicBlockBase235_cases (a : ℕ) :
    dyadicBlockBase235 a = 2 ∨
      dyadicBlockBase235 a = 6 ∨
      dyadicBlockBase235 a = 10 ∨
      dyadicBlockBase235 a = 30
```

7. [`ErdosProblems.Erdos269.dyadicBlockBase235_mem_interval`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean#L774)

```lean
theorem dyadicBlockBase235_mem_interval (a : ℕ) :
    2 ≤ dyadicBlockBase235 a ∧ dyadicBlockBase235 a ≤ 30
```

<a id="long269-res-dyadic-alphabet-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `dyadicInternalPower_exponent_unique`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L113) (E269_02, line 113), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsA.lean#L276) (PaperStatementsA.lean, line 276), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)
- `exists_dyadicInternalPower_iff_log_succ`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L120) (E269_02, line 120), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsA.lean#L282) (PaperStatementsA.lean, line 282), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)
- `log_dyadic_succ_eq_of_no_internalPower`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L126) (E269_02, line 126), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsA.lean#L287) (PaperStatementsA.lean, line 287), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)
- `threePrimeHeight_dyadicBlock_succ`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L132) (E269_02, line 132), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsA.lean#L292) (PaperStatementsA.lean, line 292), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)
- `radix_eq_height_ratio`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L96) (E269_02, line 96), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsA.lean#L262) (PaperStatementsA.lean, line 262), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)
- `dyadicBlockBase235_cases`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L102) (E269_02, line 102), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsA.lean#L267) (PaperStatementsA.lean, line 267), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)
- `dyadicBlockBase235_mem_interval`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L109) (E269_02, line 109), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsA.lean#L273) (PaperStatementsA.lean, line 273), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-actual-orbit"></a>

## Theorem 5.2 (the tail recurrence), page 13

> *The shell masses are summable and $`S=\sum_{a\ge0}s_a`$. For every $`a\ge0`$,
> ``` math
> \begin{equation}
> \label{long269:eq:shell-digit-identity}
>  m_a=h_{a+1}s_a\in\mathbb{N}_{>0},
>  \qquad
>  X_{a+1}=b_aX_a-m_a,
>  \qquad
>  X_a=\sum_{j\ge a}\frac{m_j}{b_ab_{a+1}\cdots b_j} .
> \end{equation}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos269.PaperR7.long_actual_orbit`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR7SeriesIdentification.lean#L189)

```lean
theorem long_actual_orbit :
    Summable dyadicShellMassR235 ∧
    paperSeries235 = (∑' a : ℕ, dyadicShellMassR235 a) ∧
    (∀ a : ℕ,
      0 < dyadicOrderedBlockDigit235 a ∧
      (dyadicOrderedBlockDigit235 a : ℝ) =
        (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ) / 2 * dyadicShellMassR235 a ∧
      trueNormalizedState (a + 1) =
        (dyadicBlockBase235 a : ℝ) * trueNormalizedState a -
          (dyadicOrderedBlockDigit235 a : ℝ) ∧
      trueNormalizedState a =
        ∑' n : ℕ, (dyadicOrderedBlockDigit235 (a + n) : ℝ) /
          ∏ j ∈ Finset.range (n + 1), (dyadicBlockBase235 (a + j) : ℝ))
```

<a id="long269-res-actual-orbit-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `long_actual_orbit`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_02/Challenge.lean#L261) (E269_02, line 261), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_02/PaperStatementsC.lean#L127) (PaperStatementsC.lean, line 127), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_02.json) (E269_02)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-literal-triangle"></a>

## Lemma 5.3 (the shell numerator as a weighted lattice count), page 14

> *Put $`\lambda_3=\log_2 3`$, $`\lambda_5=\log_2 5`$ and $`\theta_p=1/\lambda_p`$ for $`p=3,5`$. For $`j,k\ge0`$ write $`w_{j,k}=j\lambda_3+k\lambda_5`$ and $`t_{j,k}=\{w_{j,k}\}`$. The shell numerator is
> ``` math
> m_a=\sum_{\substack{j,k\ge0\\w_{j,k}<a+1}}
>  3^{\lfloor(a+1)\theta_3\rfloor-\lfloor(a+t_{j,k})\theta_3\rfloor}
>  5^{\lfloor(a+1)\theta_5\rfloor-\lfloor(a+t_{j,k})\theta_5\rfloor}.
> ```
> Every summand is in $`\{1,3,5,15\}`$. In particular, for $`a\ge0`$,
> ``` math
> \bigl(\lfloor a/(2\lambda_3)\rfloor+1\bigr)
>  \bigl(\lfloor a/(2\lambda_5)\rfloor+1\bigr)
>  \le m_a\le15(a+1)^2.
> ```
> Thus $`m_a=\Theta((a+1)^2)`$ and the numerator sequence is unbounded. These are integer numerators, not positional digits restricted to $`\{0,\ldots,b_a-1\}`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperCompleteR20.literal_triangle_whole`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/LiteralTriangleReal.lean#L193)

```lean
theorem literal_triangle_whole :
    (∀ a, dyadicOrderedBlockDigit235 a = ∑ v ∈ literalTriangle a, literalLogWeight a v) ∧
    (∀ a v, v ∈ literalTriangle a →
      literalLogWeight a v = 1 ∨ literalLogWeight a v = 3 ∨
      literalLogWeight a v = 5 ∨ literalLogWeight a v = 15) ∧
    (∀ a, triangleRectangleSide a 3 * triangleRectangleSide a 5 ≤ dyadicOrderedBlockDigit235 a) ∧
    (∀ a : ℕ, (a + 1 : ℝ) ^ 2 / triangleQuadraticDenominator ≤ dyadicOrderedBlockDigit235 a ∧
      (dyadicOrderedBlockDigit235 a : ℝ) ≤ 15 * (a + 1 : ℝ) ^ 2) ∧
    (∀ M : ℝ, ∃ a : ℕ, M < dyadicOrderedBlockDigit235 a)
```

<a id="long269-res-literal-triangle-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `literal_triangle_whole`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_03/Challenge.lean#L81) (E269_03, line 81), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_03/PaperStatementsA.lean#L170) (PaperStatementsA.lean, line 170), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_03.json) (E269_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-actual-dichotomy"></a>

## Proposition 5.4 (integer tails or repeated separation from the integers), page 14

> *For every integer $`B\ge1`$, either $`BX_a\in\mathbb{Z}`$ for some $`a\ge0`$ and every later $`a`$, or for every $`a_0`$ there is $`a\ge a_0`$ with $`|BX_a-z|\ge1/31`$ for every $`z\in\mathbb{Z}`$.*

The Lean declaration below states this result or one that implies it. The Lean dichotomy holds for every integer $B$, of which the printed statement takes $B\ge1$.

[`ErdosProblems.Erdos269.PaperR7.scaled_integer_or_cofinal_separation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR7ActualOrbit.lean#L132)

```lean
theorem scaled_integer_or_cofinal_separation (B : ℤ) :
    (∃ a : ℕ, ∀ n, a ≤ n →
      ∃ z : ℤ, (B : ℝ) * trueNormalizedState n = (z : ℝ)) ∨
    (∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
      FarFromIntegers ((B : ℝ) * trueNormalizedState a) ((1 : ℝ) / 31))
```

<a id="long269-res-actual-dichotomy-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `scaled_integer_or_cofinal_separation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_03/Challenge.lean#L191) (E269_03, line 191), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_03/PaperStatementsC.lean#L132) (PaperStatementsC.lean, line 132), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_03.json) (E269_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-actual-tail-bound"></a>

## Theorem 6.1 (a quadratic upper bound), page 15

> *For every $`a\ge0`$, $`0<X_a\le Q(n_a)`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperR8.actual_tail_rank_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR8RankMajorant.lean#L357)

```lean
theorem actual_tail_rank_bound (a : ℕ) :
    0 < trueNormalizedState a ∧
      trueNormalizedState a ≤ (carryMajorantQ (paperJumpIndex a) : ℝ)
```

<a id="long269-res-actual-tail-bound-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `actual_tail_rank_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_03/Challenge.lean#L198) (E269_03, line 198), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_03/PaperStatementsC.lean#L166) (PaperStatementsC.lean, line 166), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_03.json) (E269_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-all-scale-lattice"></a>

## Lemma 6.2 (finite denominator clearing), page 16

> *For all integers $`0\le u\le b`$ the window mass $`h_b\sum_{a=u}^{b-1}s_a`$ is a natural number. If $`S=N/D`$ with $`N\in\mathbb{Z}`$ and $`D\in\mathbb{N}_{>0}`$, then $`DX_a\in\mathbb{Z}`$ for every $`a\ge1`$, and there are indices $`1\le i<j\le D+1`$ for which $`X_i-X_j\in\mathbb{Z}`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperCompleteR20.long_all_scale_lattice_exact`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/BoundedLatticeCollision.lean#L56)

```lean
theorem long_all_scale_lattice_exact :
    (∀ u b : ℕ, u ≤ b → ∃ z : ℕ,
      (threePrimeHeight 2 3 5 (2 ^ b) : ℝ) / 2 *
        (∑ i ∈ Finset.range (b - u), dyadicShellMassR235 (u + i)) = (z : ℝ)) ∧
    (∀ (N : ℤ) (D : ℕ), 0 < D → paperSeries235 = (N : ℝ) / (D : ℝ) →
      (∀ a : ℕ, 1 ≤ a → ∃ z : ℤ,
        (D : ℝ) * trueNormalizedState a = (z : ℝ)) ∧
      ∃ i j : ℕ, 1 ≤ i ∧ i < j ∧ j ≤ D + 1 ∧ ∃ z : ℤ,
        trueNormalizedState i - trueNormalizedState j = (z : ℝ))
```

<a id="long269-res-all-scale-lattice-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `long_all_scale_lattice_exact`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_03/Challenge.lean#L164) (E269_03, line 164), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_03/PaperStatementsC.lean#L60) (PaperStatementsC.lean, line 60), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_03.json) (E269_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-actual-cancellation"></a>

## Theorem 6.3 (rationality gives positive integer tails), page 17

> *<span id="long269:res:lead-carry-bridge" label="long269:res:lead-carry-bridge"></span> <span id="long269:res:actual-carry-bound" label="long269:res:actual-carry-bound"></span><span id="long269:res:denominator-reduction" label="long269:res:denominator-reduction"></span> Suppose $`S=N/D`$ with $`N\in\mathbb{Z}`$, $`D\in\mathbb{N}_{>0}`$, and write
> ``` math
> D=2^{u}3^{v}5^{w}B,\qquad u,v,w\in\mathbb{N},\quad B\in\mathbb{N}_{>0},\quad\gcd(B,30)=1,
>  \qquad a_D=u+1+2v+3w .
> ```
> Then for every $`a\ge a_D`$ the number $`d_a=BX_a`$ is a positive integer and
> ``` math
> d_{a+1}=b_ad_a-Bm_a,\qquad 1\le d_a\le K(B,a)\le90B(a+1)^{2} .
> ```*

The Lean declarations below together state this result or one that implies it. The Lean statement drops $\gcd(B,30)=1$, so it applies to every factorisation $D=2^u3^v5^wB$ with $B\ge1$, and it proves $K(B,a)\le3B(a+1)^2$; the printed bound $K(B,a)\le90B(a+1)^2$ follows.

1. [`ErdosProblems.Erdos269.PaperR11.long_fixed_split_bridgeR11`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/LongWindowCapR11.lean#L37)

```lean
theorem long_fixed_split_bridgeR11 {N : ℤ} {D u v w B : ℕ}
    (hB : 0 < B) (hD : D = 2 ^ u * 3 ^ v * 5 ^ w * B)
    (hval : paperSeries235 = (N : ℝ) / (D : ℝ)) :
    ∀ a, u + 1 + 2 * v + 3 * w ≤ a →
      (paperReducedCarry B a : ℝ) = (B : ℝ) * trueNormalizedState a ∧
      1 ≤ paperReducedCarry B a ∧
      paperReducedCarry B (a + 1) =
        (dyadicBlockBase235 a : ℤ) * paperReducedCarry B a -
          (B : ℤ) * (dyadicOrderedBlockDigit235 a : ℤ) ∧
      paperReducedCarry B a ≤ (longPaperCap B a : ℤ)
```

2. [`ErdosProblems.Erdos269.PaperR11.longPaperCap_le_three_squareR11`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/LongWindowCapR11.lean#L26)

```lean
theorem longPaperCap_le_three_squareR11 (B a : ℕ) :
    longPaperCap B a ≤ 3 * B * (a + 1) ^ 2
```

<a id="long269-res-actual-cancellation-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `long_fixed_split_bridgeR11`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_03/Challenge.lean#L179) (E269_03, line 179), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_03/PaperStatementsC.lean#L99) (PaperStatementsC.lean, line 99), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_03.json) (E269_03)
- `longPaperCap_le_three_squareR11`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_03/Challenge.lean#L175) (E269_03, line 175), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_03/PaperStatementsC.lean#L96) (PaperStatementsC.lean, line 96), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_03.json) (E269_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-exact-denominator"></a>

## Proposition 6.4 (exact denominators and minimal clearing), page 17

> *Suppose $`S=N/(MB)`$ is in lowest terms, with $`M=2^u3^v5^w`$ and $`\gcd(B,30)=1`$. For every $`a\ge1`$,
> ``` math
> \operatorname{den}(X_a)=\frac{MB}{\gcd(M,h_a)},\qquad
>  \operatorname{den}(BX_a)=\frac{M}{\gcd(M,h_a)}.
> ```
> Hence the first integral reduced tail occurs at
> ``` math
> a_* =\min\{a\ge1:2^a\ge\max(2^{u+1},3^v,5^w)\}\le a_D,
> ```
> and $`BX_a`$ is integral exactly for $`a\ge a_*`$. This onset is computable by integer powers; it is not an estimate obtained by rounding logarithms.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos269.PaperR13.exact_denominators_and_minimal_clearing`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperExactDenominatorR13.lean#L334)

```lean
theorem exact_denominators_and_minimal_clearing
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a)
    (hval : paperSeries235 =
      (N : ℝ) / ((2 ^ u * 3 ^ v * 5 ^ w * B : ℕ) : ℝ)) :
    ((rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a : ℚ) : ℝ) =
        trueNormalizedState a ∧
      (rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w * B) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      ((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      (((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den = 1 ↔
        firstClearingIndex u v w ≤ a)
```

2. [`ErdosProblems.Erdos269.PaperR13.scaled_state_is_integer_iff_firstClearingIndex_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperExactDenominatorR13.lean#L309)

```lean
theorem scaled_state_is_integer_iff_firstClearingIndex_le
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a) :
    (∃ z : ℤ,
      (B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a = (z : ℚ)) ↔
      firstClearingIndex u v w ≤ a
```

3. [`ErdosProblems.Erdos269.PaperR13.clearingCondition_iff_max`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperExactDenominatorR13.lean#L166)

```lean
theorem clearingCondition_iff_max {u v w a : ℕ} :
    ClearingCondition u v w a ↔
      1 ≤ a ∧ max (2 ^ (u + 1)) (max (3 ^ v) (5 ^ w)) ≤ 2 ^ a
```

4. [`ErdosProblems.Erdos269.PaperR13.firstClearingIndex_spec`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperExactDenominatorR13.lean#L203)

```lean
theorem firstClearingIndex_spec (u v w : ℕ) :
    ClearingCondition u v w (firstClearingIndex u v w)
```

5. [`ErdosProblems.Erdos269.PaperR13.firstClearingIndex_minimal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperExactDenominatorR13.lean#L208)

```lean
theorem firstClearingIndex_minimal {u v w a : ℕ} (ha : ClearingCondition u v w a) :
    firstClearingIndex u v w ≤ a
```

6. [`ErdosProblems.Erdos269.PaperR13.firstClearingIndex_le_sufficient`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperExactDenominatorR13.lean#L213)

```lean
theorem firstClearingIndex_le_sufficient (u v w : ℕ) :
    firstClearingIndex u v w ≤ u + 1 + 2 * v + 3 * w
```

<a id="long269-res-exact-denominator-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exact_denominators_and_minimal_clearing`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_05/Challenge.lean#L152) (E269_05, line 152), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_05/PaperStatementsG.lean#L102) (PaperStatementsG.lean, line 102), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_05.json) (E269_05)
- `scaled_state_is_integer_iff_firstClearingIndex_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_04/Challenge.lean#L150) (E269_04, line 150), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_04/PaperStatementsF.lean#L50) (PaperStatementsF.lean, line 50), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_04.json) (E269_04)
- `clearingCondition_iff_max`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_04/Challenge.lean#L105) (E269_04, line 105), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_04/PaperStatementsA.lean#L243) (PaperStatementsA.lean, line 243), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_04.json) (E269_04)
- `firstClearingIndex_spec`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_04/Challenge.lean#L146) (E269_04, line 146), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_04/PaperStatementsF.lean#L47) (PaperStatementsF.lean, line 47), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_04.json) (E269_04)
- `firstClearingIndex_minimal`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_04/Challenge.lean#L142) (E269_04, line 142), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_04/PaperStatementsF.lean#L44) (PaperStatementsF.lean, line 44), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_04.json) (E269_04)
- `firstClearingIndex_le_sufficient`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_04/Challenge.lean#L138) (E269_04, line 138), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_04/PaperStatementsF.lean#L41) (PaperStatementsF.lean, line 41), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_04.json) (E269_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-pinning"></a>

## Proposition 6.5 (propagation of integrality and uniqueness of a small solution), page 18

> *For every $`a`$, $`X_a=(m_a+X_{a+1})/b_a>0`$, and if $`X_a\in\mathbb{Z}`$ then $`X_n\in\mathbb{Z}`$ for every $`n\ge a`$. Moreover, fix $`A`$, a positive width function $`w`$ with $`w(A+k)/8^{k}\to0`$, and a real sequence $`(y_n)_{n\ge A}`$ satisfying $`y_{n+1}=b_ny_n-m_n`$. If $`y_n`$ and $`X_n`$ both lie in $`(m_n/b_n,\;m_n/b_n+w(n)]`$ for every $`n\ge A`$, then $`y_A=X_A`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperCompleteR20.paper_pinning_and_eight_scale_rigidity`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/EightScaleRigidity.lean#L77)

```lean
theorem paper_pinning_and_eight_scale_rigidity :
    (∀ a : ℕ, trueNormalizedState a =
      ((dyadicOrderedBlockDigit235 a : ℝ) + trueNormalizedState (a + 1)) /
        (dyadicBlockBase235 a : ℝ) ∧ 0 < trueNormalizedState a) ∧
    (∀ a : ℕ, ∀ z : ℤ, trueNormalizedState a = (z : ℝ) →
      ∀ n, a ≤ n → ∃ w : ℤ, trueNormalizedState n = (w : ℝ)) ∧
    (∀ (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ),
      (∀ n, 0 < width n) →
      (∀ n, A ≤ n → y (n + 1) =
        (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ)) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧
        y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ n, A ≤ n →
        (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < trueNormalizedState n ∧
        trueNormalizedState n ≤
          (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) →
      (∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → width (A + k) / 8 ^ k < ε) →
      y A = trueNormalizedState A)
```

<a id="long269-res-pinning-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_pinning_and_eight_scale_rigidity`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_05/Challenge.lean#L184) (E269_05, line 184), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_05/PaperStatementsC.lean#L98) (PaperStatementsC.lean, line 98), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_05.json) (E269_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-jump-constrained-bound"></a>

## Proposition 6.6 (a smaller quadratic bound), page 18

> *For every $`a\ge0`$,
> ``` math
> 0<X_a\le\widetilde Q(n_a)<Q(n_a),\qquad
>  \widetilde Q(n)=\frac{1210n^2+9130n+18847}{11979}.
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperR10.actual_sharp_tail_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/ActualSharpTailMajorantR10.lean#L339)

```lean
theorem actual_sharp_tail_bound (a : ℕ) :
    0 < trueNormalizedState a ∧
    trueNormalizedState a ≤ (carryMajorantQtilde (paperJumpIndex a) : ℝ) ∧
    (carryMajorantQtilde (paperJumpIndex a) : ℝ) <
      (carryMajorantQ (paperJumpIndex a) : ℝ)
```

<a id="long269-res-jump-constrained-bound-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `actual_sharp_tail_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_05/Challenge.lean#L205) (E269_05, line 205), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_05/PaperStatementsC.lean#L118) (PaperStatementsC.lean, line 118), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_05.json) (E269_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-consumer"></a>

## Proposition 7.1 (least positive residues), page 21

> *Let $`C>0`$ and let $`c`$ be an integer with $`0<c`$ and $`|c|\le K`$. If $`c\equiv N\pmod C`$ and $`K<\operatorname{lpr}_C(N)`$, then the hypotheses are contradictory.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one, with the bound $K$ a natural number; a real $K$ reduces to $\lfloor K\rfloor$, since $|c|$ is an integer.

[`ErdosProblems.Erdos269.no_bounded_positive_int_state_of_leastPositiveResidue`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/ResidueEscape.lean#L110)

```lean
theorem no_bounded_positive_int_state_of_leastPositiveResidue
    {C bound : ℕ} {x c : ℤ}
    (hC : 0 < C)
    (hcpos : 0 < c)
    (hcbound : Int.natAbs c ≤ bound)
    (hescape : bound < leastPositiveResidue C x)
    (hmod : Int.ModEq C c x) :
    False
```

<a id="long269-res-consumer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `no_bounded_positive_int_state_of_leastPositiveResidue`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_05/Challenge.lean#L216) (E269_05, line 216), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_05/PaperStatementsB.lean#L39) (PaperStatementsB.lean, line 39), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_05.json) (E269_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-actual-escape-endpoint"></a>

## Theorem 7.2 (a residue criterion for every dominating bound of size $`o(8^a)`$), page 22

> *<span id="long269:res:lead-escape-equivalence" label="long269:res:lead-escape-equivalence"></span><span id="long269:res:windowconsumer" label="long269:res:windowconsumer"></span> Let $`G:\mathbb{N}_{>0}\times\mathbb{N}\to\mathbb{N}`$ satisfy $`K(B,a)\le G(B,a)`$ for all $`B`$ and $`a`$, and $`G(B,a)/8^{a}\to0`$ as $`a\to\infty`$ for each fixed $`B`$. Then
> ``` math
> \mathsf E(G)\quad\Longleftrightarrow\quad S\notin\mathbb{Q}.
> ```
> Both $`K`$ of (12) and $`K_0(B,a)=90B(a+1)^{2}`$ satisfy these hypotheses, so $`\mathsf E(K)`$, $`\mathsf E(K_0)`$ and irrationality of $`S`$ are mutually equivalent. By contrast, $`\mathsf E(0)`$ holds automatically, since every least positive residue is at least $`1`$; its truth alone therefore provides no contradiction to an integral tail.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperCompleteR20.octic_escape_whole`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/OcticEscapeWhole.lean#L50)

```lean
theorem octic_escape_whole :
    (∀ G : ℕ → ℕ → ℕ,
      (∀ B a, 0 < B → longPaperCap B a ≤ G B a) →
      (∀ B, 0 < B →
        Tendsto (fun a : ℕ => (G B a : ℝ) / (8 : ℝ) ^ a) atTop (𝓝 0)) →
      (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G ↔
        Irrational paperSeries235)) ∧
    (∀ B : ℕ,
      Tendsto (fun a : ℕ => (longPaperCap B a : ℝ) / (8 : ℝ) ^ a) atTop (𝓝 0)) ∧
    (∀ B a : ℕ, longPaperCap B a ≤ shortPaperCap B a) ∧
    (∀ B : ℕ,
      Tendsto (fun a : ℕ => (shortPaperCap B a : ℝ) / (8 : ℝ) ^ a) atTop (𝓝 0)) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 longPaperCap ↔
      Irrational paperSeries235) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 shortPaperCap ↔
      Irrational paperSeries235) ∧
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun _ _ => 0)
```

<a id="long269-res-actual-escape-endpoint-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `octic_escape_whole`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_11/Challenge.lean#L175) (E269_11, line 175), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_11/WindowEscapeEquivalence.lean#L191) (WindowEscapeEquivalence.lean, line 191), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_11.json) (E269_11)

Challenge for `octic_escape_whole`:

```lean
theorem octic_escape_whole :
    (∀ G : ℕ → ℕ → ℕ,
      (∀ B a, 0 < B → longPaperCap B a ≤ G B a) →
      (∀ B, 0 < B → Filter.Tendsto
        (fun a : ℕ => (G B a : ℝ) / (8 : ℝ) ^ a) Filter.atTop (nhds 0)) →
      (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G ↔
        Irrational (dyadicShellTsumTailR235 0))) ∧
    (∀ B : ℕ, Filter.Tendsto
      (fun a : ℕ => (longPaperCap B a : ℝ) / (8 : ℝ) ^ a) Filter.atTop (nhds 0)) ∧
    (∀ B a : ℕ, longPaperCap B a ≤ shortPaperCap B a) ∧
    (∀ B : ℕ, Filter.Tendsto
      (fun a : ℕ => (shortPaperCap B a : ℝ) / (8 : ℝ) ^ a) Filter.atTop (nhds 0)) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 longPaperCap ↔
      Irrational (dyadicShellTsumTailR235 0)) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 shortPaperCap ↔
      Irrational (dyadicShellTsumTailR235 0)) ∧
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun _ _ => 0) := by sorry
```

<a id="long269-res-residue-limit"></a>

## Proposition 7.3 (the fixed-start residue limit), page 22

> *For fixed integers $`B,\ell\ge1`$, write
> ``` math
> R_h=\operatorname{lpr}_{W_{\ell,h}}(-BF_{\ell,h}).
> ```
> For all sufficiently large $`h`$,
> ``` math
> R_h=(\lceil BX_\ell\rceil-BX_\ell)W_{\ell,h}+BX_{\ell+h},
> ```
> and consequently
> ``` math
> \lim_{h\to\infty}\frac{R_h}{W_{\ell,h}}
>  =\lceil BX_\ell\rceil-BX_\ell.
> ```
> In particular, if $`BX_\ell`$ is integral, then $`R_h=BX_{\ell+h}`$ for all sufficiently large $`h`$.*

The Lean declarations below together state this result or one that implies it. The Lean statements hold for every start $\ell\ge0$, of which the printed statement takes $\ell\ge1$, and give for each $B\ge1$ the eventual formula $R_h=(\lceil BX_\ell\rceil-BX_\ell)W_{\ell,h}+BX_{\ell+h}$, the limit of $R_h/W_{\ell,h}$, and $R_h=BX_{\ell+h}$ eventually when $BX_\ell$ is integral.

1. [`ErdosProblems.Erdos269.PaperR14.eventually_fixedStartResidue_formula`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperFixedStartResidueR14.lean#L172)

```lean
theorem eventually_fixedStartResidue_formula (B lo : ℕ) (hB : 0 < B) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        ((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) *
            (actualWindowProduct lo h : ℝ) -
          (B : ℝ) * trueNormalizedState lo *
            (actualWindowProduct lo h : ℝ) +
          (B : ℝ) * trueNormalizedState (lo + h)
```

2. [`ErdosProblems.Erdos269.PaperR14.fixedStartResidue_ratio_tendsto`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperFixedStartResidueR14.lean#L205)

```lean
theorem fixedStartResidue_ratio_tendsto (B lo : ℕ) (hB : 0 < B) :
    Tendsto
      (fun h : ℕ =>
        (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) /
            (actualWindowProduct lo h : ℝ))
      atTop
      (nhds (((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) -
        (B : ℝ) * trueNormalizedState lo))
```

3. [`ErdosProblems.Erdos269.PaperR14.eventually_fixedStartResidue_eq_tail_of_integral`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperFixedStartResidueR14.lean#L231)

```lean
theorem eventually_fixedStartResidue_eq_tail_of_integral
    (B lo : ℕ) (hB : 0 < B) (hInt : ∃ z : ℤ, (B : ℝ) * trueNormalizedState lo = z) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        (B : ℝ) * trueNormalizedState (lo + h)
```

<a id="long269-res-residue-limit-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `eventually_fixedStartResidue_formula`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_05/Challenge.lean#L243) (E269_05, line 243), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_05/FixedStartResidue.lean#L16) (FixedStartResidue.lean, line 16), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_05.json) (E269_05)
- `fixedStartResidue_ratio_tendsto`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_05/Challenge.lean#L254) (E269_05, line 254), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_05/FixedStartResidue.lean#L69) (FixedStartResidue.lean, line 69), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_05.json) (E269_05)
- `eventually_fixedStartResidue_eq_tail_of_integral`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_05/Challenge.lean#L265) (E269_05, line 265), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_05/FixedStartResidue.lean#L122) (FixedStartResidue.lean, line 122), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_05.json) (E269_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-window-growth"></a>

## Proposition 7.4 (growth of the window product), page 24

> *Put $`\theta_3=\log_32`$ and $`\theta_5=\log_52`$. For all $`\ell\ge0`$ and $`h\ge1`$,
> ``` math
> W_{\ell,h}=2^{h}\,
>  3^{\lfloor(\ell+h)\theta_3\rfloor-\lfloor\ell\theta_3\rfloor}\,
>  5^{\lfloor(\ell+h)\theta_5\rfloor-\lfloor\ell\theta_5\rfloor},
>  \qquad
>  \frac{8^{h}}{15}<W_{\ell,h}<15\cdot8^{h} .
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperR7.long_window_growth`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR7WindowResults.lean#L196)

```lean
theorem long_window_growth (lo len : ℕ) (_hlen : 1 ≤ len) :
    actualWindowBase lo len =
      ((2 ^ len *
        3 ^ (⌊((lo + len : ℕ) : ℝ) * Real.logb 3 2⌋₊ -
          ⌊(lo : ℝ) * Real.logb 3 2⌋₊) *
        5 ^ (⌊((lo + len : ℕ) : ℝ) * Real.logb 5 2⌋₊ -
          ⌊(lo : ℝ) * Real.logb 5 2⌋₊) : ℕ) : ℤ) ∧
    (8 : ℝ) ^ len / 15 < (actualWindowBase lo len : ℝ) ∧
    (actualWindowBase lo len : ℝ) < 15 * (8 : ℝ) ^ len
```

<a id="long269-res-window-growth-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `long_window_growth`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_06/Challenge.lean#L76) (E269_06, line 76), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_06/PaperStatementsF.lean#L98) (PaperStatementsF.lean, line 98), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_06.json) (E269_06)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-no-bounded-length"></a>

## Corollary 7.5 (a fixed maximum length cannot cover arbitrarily late starts), page 25

> *Fix $`B\ge1`$ coprime to $`30`$ and $`H\ge1`$. Only finitely many starts $`\ell`$ admit an escaping window of length at most $`H`$ against the bound $`K`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperR7.long_no_bounded_length`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR7WindowResults.lean#L267)

```lean
theorem long_no_bounded_length {B H : ℕ} (hB : 0 < B)
    (_hcop : Nat.Coprime B 30) (_hH : 1 ≤ H) :
    Set.Finite {lo : ℕ | ∃ len : ℕ, 1 ≤ len ∧ len ≤ H ∧
      longPaperCap B (lo + len) <
        leastPositiveResidue (Int.natAbs (actualWindowBase lo len))
          (-((B : ℤ) * actualWindowForcing lo len))}
```

<a id="long269-res-no-bounded-length-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `long_no_bounded_length`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_06/Challenge.lean#L111) (E269_06, line 111), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_06/PaperStatementsG.lean#L146) (PaperStatementsG.lean, line 146), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_06.json) (E269_06)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-weighted-shift-identity"></a>

## Lemma 9.1 (weighted shifts preserve the actual value), page 28

> *Fix integers $`c_0,\ldots,c_\sigma`$, not all zero, independently of the positive integer shift $`r`$. Put
> ``` math
> \gamma_{a,t}=\frac{P_tP_{a+1}}{P_{a+t+1}},\qquad
>  D_{r,a}=15\sum_{j=0}^{\sigma}c_j\gamma_{a,jr}m_{a+jr}.
> ```
> Then $`\gamma_{a,t}\in\{1,1/3,1/5,1/15\}`$ and $`D_{r,a}\in\mathbb{Z}`$. Furthermore, with
> ``` math
> A_r=15\sum_{j=0}^{\sigma}c_jP_{jr},\qquad
>  Z_r=15\sum_{j=0}^{\sigma}c_jP_{jr}
>        \sum_{k<jr}\frac{m_k}{P_{k+1}}\in\mathbb{Z},
> ```
> we have the absolutely convergent identity
> ``` math
> \begin{equation}
> \label{long269:eq:weighted-shift-identity}
>  A_r\alpha-Z_r=\sum_{a\ge0}\frac{D_{r,a}}{P_{a+1}}.
> \end{equation}
> ```
> One may take $`C=225\sum_{j=0}^{\sigma}|c_j|\max(1,j)^2`$ in $`|D_{r,a}|\le C(a+r+1)^2`$. If $`J`$ is the largest index with $`c_J\ne0`$, then $`A_r\ne0`$ whenever $`\sum_{j<J}|c_j|2^{-(J-j)r}<|c_J|`$; an empty sum is zero.*

The Lean declaration below states this result or one that implies it. The Lean statement holds for every integer sequence $c_0,\ldots,c_\sigma$, the zero sequence included, and every shift $r\ge0$, of which the printed statement takes $c\ne0$ and $r\ge1$; with $\alpha=S/2$ its clauses are the printed ones, including the constant $C=225\sum_j|c_j|\max(1,j)^2$ and the criterion for $A_r\ne0$.

[`ErdosProblems.Erdos269.PaperCompleteR20.weighted_shift_whole`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/WeightedShiftValue.lean#L216)

```lean
theorem weighted_shift_whole (c : ℕ → ℤ) (σ r : ℕ) :
    (∀ a t, shiftGamma a t = 1 ∨ shiftGamma a t = 1 / 3 ∨
      shiftGamma a t = 1 / 5 ∨ shiftGamma a t = 1 / 15) ∧
    (∀ a, ∃ z : ℤ, shiftedNumerator c σ r a = (z : ℝ)) ∧
    (∃ z : ℤ, shiftedCorrection c σ r = (z : ℝ)) ∧
    HasSum (fun a : ℕ => shiftedNumerator c σ r a / (shiftHeight (a + 1) : ℝ))
      ((shiftedLeading c σ r : ℝ) * (paperSeries235 / 2) - shiftedCorrection c σ r) ∧
    Summable (fun a : ℕ => |shiftedNumerator c σ r a / (shiftHeight (a + 1) : ℝ)|) ∧
    (∀ a, |shiftedNumerator c σ r a| ≤
      shiftedQuadraticConstant c σ * ((a + r + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ J : ℕ, J ≤ σ → (∀ j, J < j → j ≤ σ → c j = 0) →
      (∑ j ∈ Finset.range J, |(c j : ℝ)| / (2 : ℝ) ^ ((J - j) * r)) < |(c J : ℝ)| →
      shiftedLeading c σ r ≠ 0)
```

<a id="long269-res-weighted-shift-identity-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `weighted_shift_whole`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_06/Challenge.lean#L171) (E269_06, line 171), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_06/PaperStatementsA.lean#L156) (PaperStatementsA.lean, line 156), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_06.json) (E269_06)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-strip-decomposition"></a>

## Proposition 9.2 (an exact interior-and-strip decomposition), page 29

> *For a fixed operator $`c_0,\ldots,c_\sigma`$ and $`r\ge1`$, let $`E_0=\mathcal T_a`$ and $`E_s=\mathcal T_{a+sr}\smallsetminus \mathcal T_{a+(s-1)r}`$ for $`1\le s\le\sigma`$. Then
> ``` math
> \frac{D_{r,a}}{15}=
>  \sum_{s=0}^{\sigma}\ \sum_{(j,k)\in E_s}
>  \omega_a(t_{j,k})\sum_{\nu=s}^{\sigma}c_\nu\chi_\nu(a,t_{j,k}).
> ```
> For the cubic operator $`(1,-3,3,-1)`$, if all these crossing bits vanish, then
> ``` math
> \frac{D_{r,a}}{15}=-M_0+2M_1-M_2,\qquad
>  M_s=\sum_{(j,k)\in \mathcal T_{a+(s+1)r}\smallsetminus \mathcal T_{a+sr}}\omega_a(t_{j,k}).
> ```
> Thus absence of floor crossings cancels the common interior, but not necessarily the three boundary strips.*

The Lean declarations below together state this result or one that implies it. The Lean statements hold for every shift $r\ge0$, of which the printed statement takes $r\ge1$; the cubic hypothesis is the vanishing of both floor carries at every $(j,k)\in\mathcal T_{a+\nu r}$, $\nu\le3$, which are the crossing bits appearing in the sum.

1. [`ErdosProblems.Erdos269.PaperCompleteR20.actual_weighted_strip_decomposition`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/PhaseStripDecomposition.lean#L132)

```lean
theorem actual_weighted_strip_decomposition (c : ℕ → ℤ) (σ r a : ℕ) :
    shiftedNumerator c σ r a / 15 =
      ∑ s ∈ Finset.range (σ + 1),
        ∑ v ∈ entryStrip (fun n => literalTriangle (a + n * r)) s,
          phaseOmega a (Int.fract (triangleLogPoint v)) *
            ∑ ν ∈ Finset.Icc s σ, (c ν : ℝ) *
              phaseChi a (Int.fract (triangleLogPoint v)) (ν * r)
```

2. [`ErdosProblems.Erdos269.PaperCompleteR20.actual_cubic_no_crossing_strips`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/PhaseStripDecomposition.lean#L172)

```lean
theorem actual_cubic_no_crossing_strips (a r : ℕ)
    (hcross : ∀ ν : ℕ, ν ≤ 3 → ∀ v ∈ literalTriangle (a + ν * r),
      phaseCarry 3 a (Int.fract (triangleLogPoint v)) (ν * r) = 0 ∧
      phaseCarry 5 a (Int.fract (triangleLogPoint v)) (ν * r) = 0) :
    shiftedNumerator cubicShiftCoefficient 3 r a / 15 =
      -(∑ v ∈ literalTriangle (a + r) \ literalTriangle a,
          phaseOmega a (Int.fract (triangleLogPoint v))) +
        2 * (∑ v ∈ literalTriangle (a + 2 * r) \ literalTriangle (a + r),
          phaseOmega a (Int.fract (triangleLogPoint v))) -
        (∑ v ∈ literalTriangle (a + 3 * r) \ literalTriangle (a + 2 * r),
          phaseOmega a (Int.fract (triangleLogPoint v)))
```

<a id="long269-res-strip-decomposition-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `actual_weighted_strip_decomposition`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_07/Challenge.lean#L151) (E269_07, line 151), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_07/PaperStatementsA.lean#L99) (PaperStatementsA.lean, line 99), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_07.json) (E269_07)
- `actual_cubic_no_crossing_strips`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_07/Challenge.lean#L138) (E269_07, line 138), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_07/PaperStatementsA.lean#L87) (PaperStatementsA.lean, line 87), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_07.json) (E269_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-fixed-base-recoding"></a>

## Proposition 9.4 (what direct fixed-base recoding preserves), page 31

> *The following identities converge absolutely:
> ``` math
> \alpha=\sum_{a\ge0}\frac{e_a}{30^{a+1}}
>         =\sum_{a\ge0}\frac{v_a}{8^{a+1}},\qquad
>  e_a=\frac{m_a30^{a+1}}{P_{a+1}},\quad
>  v_a=\frac{m_a8^{a+1}}{P_{a+1}}.
> ```
> Here $`e_a\in\mathbb Z_{>0}`$ and $`e_a\ge(15/4)^{a+1}`$, whereas $`v_a\in\mathbb Z[1/15]`$ and $`0<v_a<225(a+1)^2`$. For an integer $`q\ge2`$, the termwise divisibility $`P_n\mid q^n`$ for every $`n\ge1`$ holds exactly when $`30\mid q`$; that direct recoding then has coefficients at least $`(q/8)^{a+1}`$.*

The Lean declaration below states this result or one that implies it. The Lean statement gives $v_a\in15^{-(a+1)}\mathbb Z$, a sharper form of $v_a\in\mathbb Z[1/15]$, and the lower bound $(q/8)^{a+1}$ for the coefficients $m_aq^{a+1}/P_{a+1}$ at every integer $q\ge2$, of which the printed statement uses $30\mid q$; its other clauses are the printed identities and bounds.

[`ErdosProblems.Erdos269.PaperCompleteR20.fixed_base_recoding_whole`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/FixedBaseRecoding.lean#L154)

```lean
theorem fixed_base_recoding_whole :
    (HasSum (fun a : ℕ => recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)|)) ∧
    (HasSum (fun a : ℕ => recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)|)) ∧
    (∀ a : ℕ, (∃ z : ℕ, 0 < z ∧ recodedCoefficient 30 a = (z : ℝ)) ∧
      (15 / 4 : ℝ) ^ (a + 1) ≤ recodedCoefficient 30 a) ∧
    (∀ a : ℕ, (∃ z : ℕ, recodedCoefficient 8 a = (z : ℝ) / (15 : ℝ) ^ (a + 1)) ∧
      0 < recodedCoefficient 8 a ∧ recodedCoefficient 8 a < 225 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ q : ℕ, 2 ≤ q →
      ((∀ n : ℕ, 1 ≤ n → threePrimeHeight 2 3 5 (2 ^ n) ∣ q ^ n) ↔ 30 ∣ q) ∧
      ∀ a : ℕ, ((q : ℝ) / 8) ^ (a + 1) ≤ recodedCoefficient q a)
```

<a id="long269-res-fixed-base-recoding-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `fixed_base_recoding_whole`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_07/Challenge.lean#L160) (E269_07, line 160), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_07/PaperStatementsA.lean#L108) (PaperStatementsA.lean, line 108), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_07.json) (E269_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-res-tails-equivalence"></a>

## Proposition 9.6 (irrationality is equivalent to nonintegrality of every reduced tail), page 33

> *Statement (16), quantified over every $`B\ge1`$ coprime to $`30`$ and every $`a\ge1`$, is equivalent to irrationality of $`S`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.PaperR7.allReducedTailsNonintegral_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperR7RationalBridge.lean#L214)

```lean
theorem allReducedTailsNonintegral_iff :
    AllReducedTailsNonintegral ↔ Irrational paperSeries235
```

<a id="long269-res-tails-equivalence-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `allReducedTailsNonintegral_iff`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_07/Challenge.lean#L200) (E269_07, line 200), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_07/PaperStatementsC.lean#L146) (PaperStatementsC.lean, line 146), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_07.json) (E269_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-long-denominator-reduction"></a>

## Proposition 10.1 (conditional denominator reduction), page 39

> *If $`c_n=D_{\mathrm{sm}}d_n`$ for every $`n`$, with $`D_{\mathrm{sm}}>0`$, then the recurrence and window identity for $`(d_n)`$ have multiplier $`B`$ in place of $`D`$. Moreover, for every $`n`$ and every real $`t`$,
> ``` math
> 0<c_n\le Dt\quad\Longleftrightarrow\quad0<d_n\le Bt.
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement allows any positive integer factor $s$ in place of $D_{\mathrm{sm}}=2^u3^v5^w$ and any integer $B$, without $B>0$ or $\gcd(B,30)=1$; with $s=D_{\mathrm{sm}}$ and $D=sB$ its three conclusions (the recurrence with multiplier $B$, the window identity, and $0<c_n\le Dt\Leftrightarrow0<d_n\le Bt$) are the printed ones.

[`ErdosProblems.Erdos269.PaperCompleteR20.conditional_denominator_reduction_real_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/PaperCompleteR20/RealBoundDenominatorReduction.lean#L25)

```lean
theorem conditional_denominator_reduction_real_bound
    (c d b m : ℕ → ℤ) (s B : ℤ) (hs : 0 < s)
    (hfactor : ∀ n, c n = s * d n)
    (hrec : ∀ n, c (n + 1) = b n * c n - (s * B) * m n) :
    (∀ n, d (n + 1) = b n * d n - B * m n) ∧
    (∀ lo len, d (lo + len) = windowBase b lo len * d lo -
      B * windowForcing b m lo len) ∧
    (∀ n (t : ℝ),
      (0 < c n ∧ (c n : ℝ) ≤ ((s * B : ℤ) : ℝ) * t) ↔
        (0 < d n ∧ (d n : ℝ) ≤ (B : ℝ) * t))
```

<a id="long269-long-denominator-reduction-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `conditional_denominator_reduction_real_bound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_07/Challenge.lean#L209) (E269_07, line 209), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_07/PaperStatementsG.lean#L172) (PaperStatementsG.lean, line 172), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_07.json) (E269_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="long269-long-windowconsumer"></a>

## Proposition 10.2 (escaping windows exclude a positive bounded integer solution), page 40

> *Let $`(b_n)`$ and $`(m_n)`$ be sequences of nonnegative integers, let $`G:\mathbb{N}_{>0}\times\mathbb{N}\to\mathbb{N}`$, and assume the residue condition (14) for these sequences and $`G`$, using $`|W_{\ell,h}|>0`$ as the modulus. Fix $`B>0`$ coprime to $`30`$. There is no integral sequence $`(d_n)`$ satisfying simultaneously $`d_{n+1}=b_nd_n-Bm_n`$, $`d_n>0`$ and $`|d_n|\le G(B,n)`$ for every $`n\ge0`$.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos269.no_positive_reducedCarry_of_cofinalLocalWindowEscape`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos269/RestrictedFloorSum.lean#L645)

```lean
theorem no_positive_reducedCarry_of_cofinalLocalWindowEscape
    (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ)
    (hescape : CofinalLocalWindowEscape b m shortBound)
    (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30)
    (d : ℕ → ℤ)
    (hrec : ∀ n,
      d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ))
    (hpos : ∀ n, 0 < d n)
    (hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n) :
    False
```

<a id="long269-long-windowconsumer-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `no_positive_reducedCarry_of_cofinalLocalWindowEscape`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E269_07/Challenge.lean#L241) (E269_07, line 241), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E269_07/CarryMechanism.lean#L249) (CarryMechanism.lean, line 249), [replay report](../evidence/comparator/replay-35882032091/receipt-E269_07.json) (E269_07)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
