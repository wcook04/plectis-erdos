# Formal evidence: Reciprocal Mersenne Subseries, Section 2

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="prop-canon"></a>

## Proposition 2.2 (Uniqueness under the stated finite conditions), page 24

> *Put $`G=\mathrm{greedyMersenneSupport}(1/2)`$, $`w_n=(2^n-1)^{-1}`$ and $`R_d=\sum_{n>d}w_n`$. The following are three separate uniqueness statements.*
> 
> 1.  *If $`D\subseteq\{1,\ldots,d\}`$ and $`X_D(2)\le1/2\le X_D(2)+R_d`$, then $`D=G\cap\{1,\ldots,d\}`$.*
> 
> 2.  *If $`c\ge4`$, $`D\subseteq\{2,\ldots,c-1\}`$ and $`0<1/2-X_D(2)<w_c`$, then $`D=G\cap\{1,\ldots,c-1\}`$.*
> 
> 3.  *Let positive integer weights $`v_1,\ldots,v_k`$ satisfy $`v_i\ge g+\sum_{j>i}v_j`$ for a positive integer $`g`$. For a nonnegative integer target $`T`$, let $`y^*`$ be the word obtained by visiting these weights in order and taking each when it fits. An admissible Boolean word $`y`$ has $`0\le T-\sum_i y_iv_i<g`$ if and only if $`y=y^*`$ and $`0\le T-\sum_i y_i^*v_i<g`$.*
> 
> *Part (iii) gives uniqueness under the small-remainder condition, not existence. Theorem <a href="#record:257bm-i11a" data-reference-type="ref" data-reference="record:257bm-i11a">143</a> gives a one-weight counterexample to dropping that condition. *straddle-prefix ; integer-greedy* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>\
> *Sources:* [`IsStraddlePrefix.half_agrees_greedy`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L442); [`eq_halfGreedyPrefixSupport_of_critical_crossing`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L50); [`remainder_lt_gap_iff_eq_integerGreedyBits`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusGreedyReduction.lean#L918).*

The Lean declarations below together state a result at least as strong as this one. Items (i), (ii) and (iii) are, in order, `IsStraddlePrefix.half_agrees_greedy`, `eq_halfGreedyPrefixSupport_of_critical_crossing` and `remainder_lt_gap_iff_eq_integerGreedyBits`, with the printed hypotheses. In (ii) the Lean conclusion is equality with the greedy prefix for $1/2$ computed in exact rational arithmetic through $c-1$; `paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc` identifies that prefix with $G\cap\{2,\ldots,c-1\}$, which equals $G\cap\{1,\ldots,c-1\}$ because $w_1=1>1/2$ keeps $1$ out of $G$.

1. [`Erdos249257.IsStraddlePrefix.half_agrees_greedy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L442)

```lean
theorem IsStraddlePrefix.half_agrees_greedy
    {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    ∀ n : ℕ, 0 < n → n ≤ d →
      (n ∈ u ↔ n ∈ greedyMersenneSupport (1 / 2 : ℝ))
```

2. [`Erdos249257.eq_halfGreedyPrefixSupport_of_critical_crossing`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCriticalCapacityCofinal.lean#L50)

```lean
theorem eq_halfGreedyPrefixSupport_of_critical_crossing
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D <
      mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1)
```

3. [`Erdos249257.BooleanMobiusGreedyReduction.remainder_lt_gap_iff_eq_integerGreedyBits`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusGreedyReduction.lean#L918)

```lean
theorem remainder_lt_gap_iff_eq_integerGreedyBits
    {gap C : ℕ} {weights : List ℕ} {bits : List Bool} (hgap : 0 < gap)
    (hdom : GapDominates gap weights)
    (hlen : bits.length = weights.length)
    (hadm : weightedBoolSum weights bits ≤ C) :
    C - weightedBoolSum weights bits < gap ↔
      bits = integerGreedyBits weights C ∧
        integerGreedyRemainder weights C < gap
```

<a id="prop-canon-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-collapse-mech"></a>

## Lemma 2.4 (Carry and residual value), page 25

> *Let $`A \subseteq \mathbb{N}`$ with $`1 \notin A`$, put $`\delta := 1/2 - x_A`$, and let $`\operatorname{ihc}(A,N)`$ denote the integer half-carry at level $`N`$. Then
> ``` math
> \operatorname{ihc}(A,N) \;=\; 2^{N+1}\,\delta \;+\; \mathrm{T}(N+1),
>   \qquad 0 \;\le\; \mathrm{T}(N+1) \;\le\; 2\sqrt{N+1} + 4 ,
> ```
> where $`\mathrm T(m)=\sum_{r\ge1}c_A(m+r)2^{-r}`$. *half-carry recurrence* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>\
> *Sources:* [`integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L871); [`binaryCoeffTail_nonneg`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L78); [`binaryCoeffTail_supportCoeff_le_two_sqrt_add_four`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCarry.lean#L290).*

The Lean declarations below together state a result at least as strong as this one. The Lean identity $\operatorname{ihc}(A,N)=2^{N+1}\delta+\mathrm T(N+1)$ is as printed for $1\notin A$; the Lean bounds $0\le\mathrm T(m)\le2\sqrt m+4$ hold for every $A\subseteq\N$ and every $m$, without the hypothesis $1\notin A$, and the printed bounds are their case $m=N+1$.

1. [`Erdos249257.HalfCarryReachability.integerHalfCarry_eq_scaled_residual_add_tail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCarryReachability.lean#L871)

```lean
theorem integerHalfCarry_eq_scaled_residual_add_tail
    (A : Set ℕ) (hone : 1 ∉ A) (N : ℕ) :
    (integerHalfCarry A N : ℝ) =
      (2 : ℝ) ^ (N + 1) * ((1 : ℝ) / 2 - erdosSupportSeries 2 A) +
        binaryCoeffTail (supportCoeff A) (N + 1)
```

2. [`Erdos249257.binaryCoeffTail_nonneg`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L78)

```lean
theorem binaryCoeffTail_nonneg (c : ℕ → ℕ) (N : ℕ) :
    0 ≤ binaryCoeffTail c N
```

3. [`Erdos249257.binaryCoeffTail_supportCoeff_le_two_sqrt_add_four`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/BooleanMobiusCarry.lean#L290)

```lean
theorem binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    (A : Set ℕ) (N : ℕ) :
    binaryCoeffTail (supportCoeff A) N ≤
      2 * Real.sqrt (N : ℝ) + 4
```

<a id="lem-collapse-mech-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `integerHalfCarry_eq_scaled_residual_add_tail` | [E257_03/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L99) | [PaperStatementsE.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsE.lean#L35) | [E257_03](../../evidence/comparator/replay-35882032091/receipt-E257_03.json) |
| `binaryCoeffTail_nonneg` | [E257_03/Challenge.lean, line 73](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L73) | [PaperStatementsAE.lean, line 69](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsAE.lean#L69) | [E257_03](../../evidence/comparator/replay-35882032091/receipt-E257_03.json) |
| `binaryCoeffTail_supportCoeff_le_two_sqrt_add_four` | [E257_03/Challenge.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L86) | [PaperStatementsAU.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsAU.lean#L47) | [E257_03](../../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-sqrt-witness"></a>

## Lemma 2.6 (The terminal bound at square depths), page 25

> *Suppose $`x_A = 1/2`$ and $`1 \notin A`$. Then for every $`k \ge 1`$,
> ``` math
> \operatorname{ihc}(A, k^2 - 1) \;=\; \mathrm{T}(k^2) \;\le\; 2k + 4 \;=\; \ensuremath{B}(k^2).
> ```
> *half-carry recurrence* <span class="sans-serif">(cofinal)</span> <span class="sans-serif">\[Math\]</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.square_depth_witness`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR20/CarryCollapseCorrespondence.lean#L8)

```lean
theorem square_depth_witness (A : Set ℕ) (hone : 1 ∉ A)
    (hhalf : erdosSupportSeries 2 A = (1 : ℝ) / 2)
    (k : ℕ) (hk : 1 ≤ k) :
    (integerHalfCarry A (k^2-1) : ℝ) = binaryCoeffTail (supportCoeff A) (k^2) ∧
    binaryCoeffTail (supportCoeff A) (k^2) ≤ 2*(k : ℝ)+4 ∧
    (halfStripBound (k^2) : ℝ) = 2*(k : ℝ)+4
```

<a id="lem-sqrt-witness-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `square_depth_witness` | [E257_03/Challenge.lean, line 136](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L136) | [PaperStatementsL.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsL.lean#L28) | [E257_03](../../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-collapsed-list"></a>

## Proposition 2.7 (Six equivalent membership conditions), page 26

> *Each of the following is logically *equivalent* to $`1/2 \in \mathcal{A}`$, not strictly weaker:*
> 
> 1.  *$`C_G(N)\le2\sqrt N+4`$ for every $`N\ge0`$ ([`greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L834); [`greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L953));*
> 
> 2.  *there are arbitrarily large positive exponents outside $`G`$ ([`CofinalPositiveHalfGreedySkips`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusSkipRowCofinal.lean#L22));*
> 
> 3.  *at arbitrarily large depths $`n`$, some $`D\subseteq\{2,\ldots,n\}`$ satisfies $`Q(D,n)=2^{n-1}-1`$ ([`CofinalExactLocalMersenneHalfRows`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCofinalExactRows.lean#L38)); no agreement between the sets $`D`$ at different depths is required;*
> 
> 4.  *at arbitrarily large $`M`$, $`\operatorname{ihc}(G,M)\le B(M+1)`$ ([`GreedyHalfCarryCofinalStripReturn`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CofinalStripReturn.lean#L76));*
> 
> 5.  *at arbitrarily large positive depths $`M`$, some $`D\subseteq\{2,\ldots,M\}`$ satisfies $`|\operatorname{ihc}(D,M-1)|\le B(M)`$ ([`HalfCarryCofinalTerminalOnlyStrip`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TerminalOnlyCofinal.lean#L34));*
> 
> 6.  *the half-target greedy remainder never exceeds the full remaining tail, so no finite fatal gap exists ([`ExistsFatalHalfGap`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L526)); the seven equivalent forms in the later classification express this same condition.*
> 
> *Forward directions are supplied formal (e.g. [`half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L2583), [`half_mem_mersenneAchievementSet_of_cofinalExactLocalRows`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/BooleanMobiusCofinalExactRows.lean#L71), [`existsFatalHalfGap_iff_half_not_mem_mersenneAchievementSet`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCutLocator.lean#L643)). For (d) and (e), the reverse directions use the square depths in Lemma <a href="#lem:sqrt-witness" data-reference-type="ref" data-reference="lem:sqrt-witness">17</a>. All six equivalences, including these reverse directions, are now Lean-checked in [`six_membership_conditions`](https://github.com/wcook04/plectis-erdos/blob/168bf6727758f918a430ef056a1c93d3160b53a6/lean/ErdosProblems/Erdos257/PaperCompleteR20/SixMembershipConditions.lean#L123). For (a), membership gives $`C_G(N)\le2\sqrt{N+1}+3\le2\sqrt N+4`$ when $`N\ge1`$, and $`C_G(0)=0`$. The forward implication still needs the greedy inequality $`x_G\le1/2`$. *half-carry recurrence ; exact-row* <span class="sans-serif">(cofinal)</span> <span class="sans-serif">\[Lean\]</span><span class="sans-serif">\[Math\]</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR20.six_membership_conditions`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR20/SixMembershipConditions.lean#L123)

```lean
theorem six_membership_conditions :
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ N : ℕ, (mobiusCenteredHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        2*Real.sqrt (N : ℝ)+4) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ 0 < n ∧ n ∉ greedyMersenneSupport (1/2 : ℝ)) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ GreedyHalfCarryCofinalStripReturn) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      (∀ n : ℕ, greedyMersenneRemainder (1/2 : ℝ) n ≤ mersenneTail n) ∧
        ¬ ExistsFatalHalfGap)
```

<a id="prop-collapsed-list-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `six_membership_conditions` | [E257_03/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L207) | [PaperStatementsK.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsK.lean#L56) | [E257_03](../../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-local-void"></a>

## Proposition 2.8 (Limits of the specified local summaries), page 27

> *(i) After $`L`$ common steps the endpoint residue mod $`2^L`$ of an affine binary orbit is *independent* of the initial carry: $`u(L) - v(L) = 2^L(u_0 - v_0)`$ ([`affineBinaryOrbit_mod_twoPow_eq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L307)). (ii) Fix $`m\ge2`$ and put $`h=\lfloor(m+1)/2\rfloor`$. Consider the coefficient sequences
> ``` math
> c_r(m)=h-r,\qquad c_r(m+1)=2r,\qquad
>  c_r(j)=0\ (j\ne m,m+1),\qquad 0\le r\le h.
> ```
> Their binary sums are all $`h2^{-m}`$, and their scaled tails before position $`m`$ agree, but their scaled tails immediately after $`m`$ are $`r`$. Thus any exact label-and-decoder system recovering those latter tails must have at least $`h+1=\lfloor(m+1)/2\rfloor+1`$ labels. A state determined only by the common preceding history, with no new input, cannot distinguish them ([`balancedPulse_no_autonomous_decoder`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L247)). (iii) For any starting carry and any finite list of prescribed valuations and odd unit residues modulo $`2^u`$, with $`u\ge1`$, there are integer input coefficients with those data whose successor carries lie in their prescribed centred intervals. The unrestricted higher bits of the input coefficients may be chosen separately at each step, as in Proposition <a href="#prop:2adic-nogo" data-reference-type="ref" data-reference="prop:2adic-nogo">256</a> ([`fixedPrecisionTropicalNoGo`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TropicalCurvatureCarry.lean#L137)), so these fixed-precision symbols alone do not exclude a completion in that specified family. This says nothing about extra constraints imposed by divisor counts from one common support. *carry* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span>*

The Lean declarations below together state a result at least as strong as this one. For (i) the identity $u(L)-v(L)=2^L(u_0-v_0)$ holds for every $L$ and every integer input sequence, and its residue form modulo $2^L$ is stated separately. For (ii), with $m\ge2$ and $0\le r\le h$, the Lean statements give the coefficients $c_r$, their common binary sum $h2^{-m}$, the common scaled tail $h2^{-(m-N)}$ at every $N<m$, the tail $r$ at $m$, the lower bound of $h+1$ labels for any exact label-and-decoder system, and the absence of a decoder from a state that is the same for every $r$. Item (iii) is the cited centred-completion statement, with $|e_{i+1}|\le2^{v_i+u-1}$ for every successor carry.

1. [`Erdos249257.affineBinaryOrbit_mod_twoPow_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L307)

```lean
theorem affineBinaryOrbit_mod_twoPow_eq (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L]
```

2. [`Erdos249257.balancedPulse_weighted_pair`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L200)

```lean
theorem balancedPulse_weighted_pair
    {m r : ℕ} (hr : r ≤ balancedPulseRadius m) :
    2 * balancedPulseCoeff m r m + balancedPulseCoeff m r (m + 1) =
      2 * balancedPulseRadius m
```

3. [`Erdos249257.balancedPulse_endpoint_fanout`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L209)

```lean
theorem balancedPulse_endpoint_fanout (m r : ℕ) :
    balancedPulseCoeff m r (m + 1) / 2 = r
```

4. [`Erdos249257.balancedPulse_label_card_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L228)

```lean
theorem balancedPulse_label_card_lower_bound
    {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ)
    (decode : Λ → ℕ) (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ
```

5. [`Erdos249257.balancedPulse_no_autonomous_decoder`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L247)

```lean
theorem balancedPulse_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_centred_completion_of_fixed_precision`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/CentredCompletionAndDecisionBoundary.lean#L34)

```lean
theorem paper_centred_completion_of_fixed_precision
    (u : ℕ) (hu : 1 ≤ u) (m : ℕ) (v : ℕ → ℕ) (a : ℕ → ℤ)
    (hodd : ∀ i, i < m → Odd (a i)) (e₀ : ℤ) :
    ∃ e z : ℕ → ℤ, e 0 = e₀ ∧
      ∀ i, i < m →
        e (i + 1) = 2 * e i + 2 ^ (v i) * (a i + 2 ^ u * z i) ∧
          |e (i + 1)| ≤ 2 ^ (v i + u - 1)
```

7. [`Erdos249257.affineBinaryOrbit_sub`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L289)

```lean
theorem affineBinaryOrbit_sub (a : ℕ → ℤ) (u0 v0 : ℤ) :
    ∀ L : ℕ,
      affineBinaryOrbit a u0 L - affineBinaryOrbit a v0 L =
        (2 : ℤ) ^ L * (u0 - v0)
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.balancedPulse_common_history`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CarryDescriptionInformationLoss.lean#L93)

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

<a id="prop-local-void-comparator"></a>

**Comparator:** not yet compared.

<a id="prop-exponent-gap"></a>

## Proposition 2.9 (Weighted denominator budget), page 27

> *Let $`n\ge2`$, let $`\mathrm{Skip}_n\subseteq\{2,\ldots,n-1\}`$, and let $`D_n`$ be the reduced denominator of the associated finite sum. Since $`D_n`$ divides the product of its Mersenne denominators,
> ``` math
> \log_2D_n\le\sum_{d\in\mathrm{Skip}_n}\log_2(2^d-1)
>  \le\sum_{d\in\mathrm{Skip}_n}d\le\frac{n(n-1)}2-1.
> ```
> The middle inequality is strict when the skip set is nonempty; for an empty skip set both sums are zero. This is an upper bound, not a quadratic asymptotic for $`D_n`$. Combined with the cited fixed irrationality-measure exponent, it does not supply the required $`2^{-3n/2}`$-scale estimate. Even an asymptotic for the exponent sum would need additional information about the skip distribution. *diophantine* <span class="sans-serif">(cofinal)</span> <span class="sans-serif">\[Math\]</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.skipSum_den_dvd_prod`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/DenominatorBudget.lean#L43)

```lean
theorem skipSum_den_dvd_prod (S : Finset ℕ) (hS : ∀ d ∈ S, 1 ≤ d) :
    ((skipSum S).den : ℤ) ∣ ∏ d ∈ S, ((2 : ℤ) ^ d - 1)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.weighted_denominator_budget`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/DenominatorBudget.lean#L78)

```lean
theorem weighted_denominator_budget (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico 2 n) :
    Real.logb 2 (((skipSum S).den : ℕ) : ℝ)
        ≤ ∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1) ∧
      (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) ≤ ∑ d ∈ S, (d : ℝ) ∧
      (∑ d ∈ S, (d : ℝ)) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 - 1 ∧
      (S.Nonempty →
        (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) < ∑ d ∈ S, (d : ℝ)) ∧
      (S = ∅ → (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) = 0 ∧
        (∑ d ∈ S, (d : ℝ)) = 0)
```

<a id="prop-exponent-gap-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `skipSum_den_dvd_prod` | [E257_04/Challenge.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L65) | [PaperStatementsAA.lean, line 352](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAA.lean#L352) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `weighted_denominator_budget` | [E257_04/Challenge.lean, line 69](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L69) | [PaperStatementsAA.lean, line 355](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAA.lean#L355) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-one-sided"></a>

## Theorem 2.11 (One-sidedness), page 28

> *Non-membership of $`1/2`$ in $`\mathcal A`$ has an effectively checkable finite-certificate formulation, hence a $`\Sigma^0_1`$ formulation. Membership has the complementary $`\Pi^0_1`$ formulation. Survival through a tested finite depth alone does not establish membership; a uniform theorem or inductive invariant could. The arithmetical-hierarchy form by itself proves neither undecidability nor the absence of finite proofs. *meta* <span class="sans-serif">(uniform)</span> <span class="sans-serif">\[Lean\]</span><span class="sans-serif">\[Math\]</span> The linked declarations establish the fatal-gap equivalences. The arithmetical-hierarchy classification also uses the effective tail estimate explained below; it is an ordinary computability deduction, not a separately replayed Lean theorem.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sidedness`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L492)

```lean
theorem paper_one_sidedness :
    (∃ P : ℕ → Prop, ComputablePred P ∧
        ((1 / 2 : ℝ) ∉ mersenneAchievementSet ↔ ∃ n : ℕ, P n) ∧
        ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ∀ n : ℕ, ¬ P n)) ∧
      (∀ d : ℕ, ∃ x : ℝ, IsStraddlePrefix x ∅ d ∧ x ∉ mersenneAchievementSet)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_iff_exists_certificate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L291)

```lean
theorem existsFatalHalfGap_iff_exists_certificate :
    ExistsFatalHalfGap ↔ ∃ p : List Bool × ℕ, FatalHalfGapCertificate p
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_of_certificate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L174)

```lean
theorem existsFatalHalfGap_of_certificate {L : List Bool} {N : ℕ}
    (h : FatalHalfGapCertificate (L, N)) : ExistsFatalHalfGap
```

where [`ExistsFatalHalfGap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/HalfCutLocator.lean#L526) is

```lean
def ExistsFatalHalfGap : Prop :=
  ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
      < 1 / 2 ∧
    (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
      + mersenneWeight (d + 1)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.certificate_of_existsFatalHalfGap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L243)

```lean
theorem certificate_of_existsFatalHalfGap (h : ExistsFatalHalfGap) :
    ∃ p : List Bool × ℕ, FatalHalfGapCertificate p
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.scaledMersenneWeight_cast`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L103)

```lean
theorem scaledMersenneWeight_cast {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (scaledMersenneWeight N n : ℝ) = 2 * (mersenneDen N : ℝ) * mersenneWeight n
```

6. [`ErdosProblems.Erdos257.PaperCompleteR21.certifiedWordValue_cast`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L133)

```lean
theorem certifiedWordValue_cast {L : List Bool} {N : ℕ} (hLN : L.length ≤ N) :
    (certifiedWordValue L N : ℝ)
      = 2 * (mersenneDen N : ℝ) * ∑ n ∈ certWord L, mersenneWeight n
```

7. [`ErdosProblems.Erdos257.PaperCompleteR21.certifiedTailBound_cast`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L144)

```lean
theorem certifiedTailBound_cast {d N : ℕ} (hdN : d + 1 ≤ N) :
    (certifiedTailBound d N : ℝ)
      = 2 * (mersenneDen N : ℝ) *
          ((∑ j ∈ Finset.range (N - (d + 1)), mersenneWeight (d + 1 + 1 + j))
            + mersenneWeight N)
```

8. [`ErdosProblems.Erdos257.PaperCompleteR21.mersenneTail_eq_sum_add`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/OneSidedCertificateHierarchy.lean#L160)

```lean
theorem mersenneTail_eq_sum_add (m K : ℕ) :
    mersenneTail m
      = (∑ j ∈ Finset.range K, mersenneWeight (m + 1 + j)) + mersenneTail (m + K)
```

<a id="thm-one-sided-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_one_sidedness` | [E257_04/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L205) | [PaperStructuresS.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStructuresS.lean#L32) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `existsFatalHalfGap_iff_exists_certificate` | [E257_04/Challenge.lean, line 170](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L170) | [PaperStatementsAM.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L141) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `existsFatalHalfGap_of_certificate` | [E257_04/Challenge.lean, line 174](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L174) | [PaperStatementsAM.lean, line 144](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L144) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `certificate_of_existsFatalHalfGap` | [E257_04/Challenge.lean, line 154](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L154) | [PaperStatementsAM.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L120) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `scaledMersenneWeight_cast` | [E257_04/Challenge.lean, line 183](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L183) | [PaperStatementsAM.lean, line 226](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L226) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `certifiedWordValue_cast` | [E257_04/Challenge.lean, line 165](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L165) | [PaperStatementsAM.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L129) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `certifiedTailBound_cast` | [E257_04/Challenge.lean, line 158](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L158) | [PaperStatementsAM.lean, line 123](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L123) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |
| `mersenneTail_eq_sum_add` | [E257_04/Challenge.lean, line 178](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L178) | [PaperStatementsAM.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAM.lean#L171) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-collapse"></a>

## Proposition 2.5 (A cofinal carry bound), page 25

> *If $`|\operatorname{ihc}(A,N)|\le C\sqrt{N+1}+C'`$ for arbitrarily large $`N`$, with fixed constants $`C,C'`$, then $`\delta=0`$. For the particular greedy support $`A=G`$ of $`1/2`$, a one-sided upper bound $`\operatorname{ihc}(G,N)\le C\sqrt{N+1}+C'`$ already suffices.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR20.half_of_cofinal_absolute_carry`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR20/CofinalCarryCollapse.lean#L46)

```lean
theorem half_of_cofinal_absolute_carry (A : Set ℕ) (hone : 1 ∉ A)
    (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      |(integerHalfCarry A N : ℝ)| ≤ C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 A = (1 : ℝ)/2
```

2. [`ErdosProblems.Erdos257.PaperCompleteR20.greedy_half_of_cofinal_upper_carry`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR20/CofinalCarryCollapse.lean#L91)

```lean
theorem greedy_half_of_cofinal_upper_carry (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 (greedyMersenneSupport (1/2 : ℝ)) = (1 : ℝ)/2
```

<a id="prop-collapse-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `half_of_cofinal_absolute_carry` | [E257_03/Challenge.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L106) | [PaperStatementsE.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsE.lean#L43) | [E257_03](../../evidence/comparator/replay-35882032091/receipt-E257_03.json) |
| `greedy_half_of_cofinal_upper_carry` | [E257_03/Challenge.lean, line 122](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_03/Challenge.lean#L122) | [PaperStatementsD.lean, line 178](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_03/PaperStatementsD.lean#L178) | [E257_03](../../evidence/comparator/replay-35882032091/receipt-E257_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
