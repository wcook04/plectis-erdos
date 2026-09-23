# Formal evidence: Reciprocal Mersenne Subseries, Section 10

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="prop-2adic-nogo"></a>

## Proposition 10.4 (Centred completion of fixed-precision 2-adic data), page 110

> *Fix $`u\ge1`$ and a finite list $`(v_i,a_i)_{0\le i<m}`$, where $`v_i\ge0`$ are integers and the integers $`a_i`$ are odd. For every initial integer $`e_0`$, there are integers $`z_i,e_{i+1}`$ such that
> ``` math
> e_{i+1}=2e_i+2^{v_i}(a_i+2^u z_i),\qquad
>  |e_{i+1}|\le2^{v_i+u-1}\qquad(0\le i<m).
> ```
> Thus one may prescribe the valuation and $`u`$ bits of the odd unit of each input coefficient while keeping every *successor* state in its stated centred interval. The initial state is arbitrary. *2-adic-valuation-unit*<span class="sans-serif">\[Lean\]</span><span class="sans-serif">(finite words)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_centred_completion_of_fixed_precision`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/CentredCompletionAndDecisionBoundary.lean#L34)

```lean
theorem paper_centred_completion_of_fixed_precision
    (u : ℕ) (hu : 1 ≤ u) (m : ℕ) (v : ℕ → ℕ) (a : ℕ → ℤ)
    (hodd : ∀ i, i < m → Odd (a i)) (e₀ : ℤ) :
    ∃ e z : ℕ → ℤ, e 0 = e₀ ∧
      ∀ i, i < m →
        e (i + 1) = 2 * e i + 2 ^ (v i) * (a i + 2 ^ u * z i) ∧
          |e (i + 1)| ≤ 2 ^ (v i + u - 1)
```

<a id="prop-2adic-nogo-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_centred_completion_of_fixed_precision` | [E257_04/Challenge.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L56) | [PaperStatementsAA.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAA.lean#L181) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-upper-unconditional"></a>

## Proposition 10.5 (The upper (carries) successor needs no exceptional-cell exclusion), page 111

> *Let $`s\ge5`$ and suppose the upper branch occurs at row $`s`$, that is, $`(\mathrm{seamAdjacentCut}\ s\ hs).\mathrm{successorCarries}`$ holds. Then
> ``` math
> \mathrm{rem}(s+1)\le2^{s+1}.
> ```
> [`Erdos249257.seamUpperBranch_nextRemainder_le_pow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3924) Indeed, the reset identity expresses $`2^{s+1}`$ as $`\mathrm{rem}(s+1)`$ plus a nonnegative reset charge: [`Erdos249257.seamUpperBranch_remainder_add_resetCharge_eq`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L3542). Thus the upper branch needs no exceptional-value exclusion for the next-row two-sided invariant. This conclusion concerns that induction step, not the absence of upper transitions on the orbit. *quotient-branch-classification* <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_upper_branch_needs_no_exceptional_cell`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/BranchCellHorizonExclusions.lean#L31)

```lean
theorem paper_upper_branch_needs_no_exceptional_cell {s : ℕ} (hs : 5 ≤ s)
    (hcarry : (seamAdjacentCut s hs).successorCarries) :
    seamIntegerGreedyRemainder (s + 1) ≤ 2 ^ (s + 1) ∧
      0 ≤ 4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse ∧
      seamIntegerGreedyRemainder (s + 1) +
          (4 * (seamAdjacentCut s hs).overshoot +
            (seamAdjacentCut s hs).abovePulse) =
        2 ^ (s + 1)
```

<a id="prop-upper-unconditional-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_upper_branch_needs_no_exceptional_cell` | [E257_31/Challenge.lean, line 386](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_31/Challenge.lean#L386) | [PaperStructuresBP.lean, line 145](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_31/PaperStructuresBP.lean#L145) | [E257_31](../../evidence/comparator/replay-35882032091/receipt-E257_31.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-cd-neg3-impossible"></a>

## Theorem 10.6 ($`C_D=-3`$ is impossible at the final middle transition, $`D\ge 13`$), page 111

> *Consider a hypothetical *final middle transition*: a middle transition at row $`D\ge 13`$ ($`\lnot\mathrm{carries}`$, and the middle-branch inequality $`4\mathrm{rem}(D)+\mathrm{gap}-\mathrm{belowPulse} < \mathrm{terminalWeight}`$ holds at $`D`$), followed by an all-right tail forever after ($`\forall s\ge D{+}1`$, $`\mathrm{seamGreedyWord}(s+1) =
> \mathrm{seamGreedyWord}(s).\mathrm{extend}\ \mathrm{true}`$). Under these assumptions,
> ``` math
> \mathrm{belowPulse}(D) + 2 \;\le\; 4\cdot\mathrm{rem}(D),
> ```
> i.e. $`C_D \ge -2`$ ; the cell $`C_D=-3`$ (and every more negative value) is excluded. [`Erdos249257.middleThenAllRight_landingExcess_two_le`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L2319)*
> 
> ***Proof of the bound.** The all-right-tail assumption puts the terminal-augmented finite prefix strictly above $`1/2`$ ([`Erdos249257.half_lt_upper_competitor_of_eventually_right`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderFatalGapRightTail.lean#L627)). Consequently the producer carry is below its complete incidence tail ([`Erdos249257.middleProducer_allRight_forces_carry_lt_tail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1814)), or equivalently $`Z_D<1+1/(2^D-1)`$, where $`Z_D=\mathrm{rem}(D)-\mathrm{seamWordFloorError}(D)`$ ([`Erdos249257.middleProducer_allRight_forces_floorZ_lt_takeThreshold`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCylinderMiddleCarryLowerBound.lean#L1869)). The lower bound uses the other endpoint: under the same tail assumption, the finite value at $`D`$ plus the complete Mersenne tail remains below $`1/2`$. The exact scaled remainder identity therefore gives
> ``` math
> Z_D>4^D\sum_{e>D}\frac1{2^e-1}-2^D>\frac13.
> ```
> The last inequality follows by retaining the first two geometric channels of the complete Mersenne tail. Put $`E_D=\mathrm{seamWordFloorError}(D)`$. Pulse absorption gives $`\mathrm{belowPulse}(D)\le4E_D`$, so
> ``` math
> 4\,\mathrm{rem}(D)-\mathrm{belowPulse}(D)
>  \ge4(\mathrm{rem}(D)-E_D)=4Z_D>\frac43.
> ```
> The left side is an integer, hence is at least $`2`$, as required. The upper threshold inequality alone would not give this lower bound.*
> 
> ***Scope.** This excludes $`C_D=-3`$ at a middle row $`D\ge13`$ under the additional all-right-tail assumption. The general induction requires exclusion of all three cells at every middle row, not just under this extra hypothesis, together with its right-branch bound. The two statements share the same coordinate $`C_D`$ but have different hypotheses. Theorem <a href="#thm:cd-neg3-impossible" data-reference-type="ref" data-reference="thm:cd-neg3-impossible">258</a> is universal over rows satisfying the additional all-right-tail assumption; it does not assert that such a row exists. The induction hypothesis concerns every middle row, without that tail assumption. Excluding $`C_D=-3`$ in the former statement therefore does not supply the exclusion required in the latter. *final-required input; conclusion-excess* **Object or representation:** about the *object* under the stated hypothesis ; a genuine arithmetic consequence of the all-right-tail assumption via the fatal-gap orbit, not a coordinate artifact. <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_at_least_neg_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/BranchCellHorizonExclusions.lean#L50)

```lean
theorem paper_final_middle_cell_at_least_neg_two
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (seamAdjacentCut D (by omega)).belowPulse + 2 ≤
        4 * (seamAdjacentCut D (by omega)).remainder ∧
      (-2 : ℤ) ≤ 4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
          ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ∧
      ∀ c : ℤ, c ≤ -3 →
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 ≠ c
```

<a id="thm-cd-neg3-impossible-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_final_middle_cell_at_least_neg_two` | [E257_12/Challenge.lean, line 249](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_12/Challenge.lean#L249) | [Statement.lean, line 242](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_12/Statement.lean#L242) | [E257_12](../../evidence/comparator/replay-35882032091/receipt-E257_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-cd-remaining"></a>

## Corollary 10.7 (Only $`C_D\in\{-2,-1\}`$ remain among the exceptional dyadic cells), page 112

> *At a final middle row $`D\ge13`$, Theorem <a href="#thm:cd-neg3-impossible" data-reference-type="ref" data-reference="thm:cd-neg3-impossible">258</a> removes $`-3`$ from the exceptional set $`\{-3,-2,-1\}`$, leaving $`-2,-1`$ *within that set*. It does not assert $`C_D\in\{-2,-1\}`$: nonnegative values have not been excluded. Proposition <a href="#prop:upper-unconditional" data-reference-type="ref" data-reference="prop:upper-unconditional">257</a> handles upper transitions in the two-sided induction; it supplies no additional restriction on a middle coordinate. For the all-middle-row induction, the exclusion of all three values still needs proof without an all-right-tail assumption, together with the separate right-branch inequality. *final-required input; conclusion-excess* <span class="sans-serif">\[Lean\]</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_final_middle_cell_remaining_cells`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/BranchCellHorizonExclusions.lean#L81)

```lean
theorem paper_final_middle_cell_remaining_cells
    (D : ℕ) (hD13 : 13 ≤ D)
    (hncarry : ¬ (seamAdjacentCut D (by omega)).successorCarries)
    (hmiddle :
      4 * (seamAdjacentCut D (by omega)).remainder +
            (seamPerturbedFamily D (by omega)).gap -
            (seamAdjacentCut D (by omega)).belowPulse <
          (seamAdjacentCut D (by omega)).terminalWeight)
    (hright : ∀ s : ℕ, D + 1 ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true) :
    (4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -3 ∨
          4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
              ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
            4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
                ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1) →
      4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
              ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -2 ∨
        4 * ((seamAdjacentCut D (by omega)).remainder : ℤ) -
            ((seamAdjacentCut D (by omega)).belowPulse : ℤ) - 4 = -1
```

<a id="cor-cd-remaining-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_final_middle_cell_remaining_cells` | [E257_12/Challenge.lean, line 282](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_12/Challenge.lean#L282) | [Statement.lean, line 277](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_12/Statement.lean#L277) | [E257_12](../../evidence/comparator/replay-35882032091/receipt-E257_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-state-nogo"></a>

## Proposition 10.9 (A finite-state restriction for the stated pulse family), page 113

> *For a “balanced pulse” family at location $`m\ge2`$ (radius $`\rho=\lfloor(m{+}1)/2\rfloor`$, parameters $`0\le r\le\rho`$, moving mass between positions $`m`$ and $`m{+}1`$ with the weighted total $`2c(m)+c(m{+}1)=2\rho`$ of the two coefficients fixed), if a predecessor state is constant across the whole family, then no function $`\mathrm{decode}:\mathrm{State}\to\mathbb N`$ can recover the parameter $`r`$ from $`\mathrm{state}(r)`$ for every $`r`$. The family has exactly $`\rho+1=\lfloor(m{+}1)/2\rfloor+1`$ members, so the fan-out is unbounded in $`m`$. More strongly, any finite set of states carrying an exact decoder for the family has at least $`\rho+1`$ elements, unbounded in $`m`$. [`Erdos249257.balancedPulse_no_autonomous_decoder`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GenericTailOrbitRigidity.lean#L247) (exact family size at [`ErdosProblems.Erdos257.PaperCompleteR21.paper_balanced_pulse_fanout_is_radius_succ`](https://github.com/wcook04/plectis-erdos/blob/168bf6727758f918a430ef056a1c93d3160b53a6/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L61)).*
> 
> ***Scope.** Excludes bounded-state encodings of pre-$`m`$ history that must distinguish every member of the displayed balanced-pulse family, whether the coefficients are $`\varphi`$ or a Möbius-support indicator. Applying it to \#249 or \#257 requires showing that the relevant orbit realises that family, and it does not rule out every finite-state proof strategy. *binary digits, generic* **Object or representation:** about a *representation* class, the encodings of history that separate the balanced-pulse family; it says nothing about $`C`$ or $`\mathcal A`$ directly. <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declarations below together state a result at least as strong as this one. The Lean count of exactly $\rho+1$ family members and the bound $|\mathrm{State}|\ge\rho+1$ for a finite state set carrying an exact decoder hold for every $m\ge0$; the printed statement takes $m\ge2$, where the impossibility of decoding from a constant predecessor state is stated as printed.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_no_autonomous_decoder`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L113)

```lean
theorem paper_pulse_family_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_balanced_pulse_fanout_is_radius_succ`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L61)

```lean
theorem paper_balanced_pulse_fanout_is_radius_succ (m : ℕ) :
    (balancedPulseFamily m).ncard = balancedPulseRadius m + 1 ∧
      (balancedPulseFamily m).ncard = (m + 1) / 2 + 1
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_balanced_pulse_fanout_unbounded_corrected`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L95)

```lean
theorem paper_balanced_pulse_fanout_unbounded_corrected :
    (∀ m : ℕ, m / 2 + 1 ≤ (balancedPulseFamily m).ncard) ∧
      ∀ N : ℕ, ∃ m : ℕ, N ≤ (balancedPulseFamily m).ncard
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_pulse_family_finite_state_card`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L123)

```lean
theorem paper_pulse_family_finite_state_card
    {m : ℕ} {State : Type*} [Fintype State]
    (state : Fin (balancedPulseRadius m + 1) → State)
    (decode : State → ℕ) (hdecode : ∀ r, decode (state r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card State ∧
      ∀ N : ℕ, ∃ m' : ℕ, N ≤ balancedPulseRadius m' + 1
```

5. [`ErdosProblems.Erdos257.PaperCompleteR21.balancedPulseCoeff_injective`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/BalancedPulseFanOutCount.lean#L52)

```lean
theorem balancedPulseCoeff_injective (m : ℕ) :
    Function.Injective (balancedPulseCoeff m)
```

6. [`Erdos249257.balancedPulse_weighted_pair`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/GenericTailOrbitRigidity.lean#L200)

```lean
theorem balancedPulse_weighted_pair
    {m r : ℕ} (hr : r ≤ balancedPulseRadius m) :
    2 * balancedPulseCoeff m r m + balancedPulseCoeff m r (m + 1) =
      2 * balancedPulseRadius m
```

<a id="prop-finite-state-nogo-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_pulse_family_no_autonomous_decoder` | [E257_36/Challenge.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L71) | [PaperStatementsBD.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsBD.lean#L43) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_balanced_pulse_fanout_is_radius_succ` | [E257_36/Challenge.lean, line 53](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L53) | [PaperStatementsBD.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsBD.lean#L28) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_balanced_pulse_fanout_unbounded_corrected` | [E257_36/Challenge.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L58) | [PaperStatementsBD.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsBD.lean#L32) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_pulse_family_finite_state_card` | [E257_36/Challenge.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L63) | [PaperStatementsBD.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsBD.lean#L36) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `balancedPulseCoeff_injective` | [E257_36/Challenge.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L49) | [PaperStatementsBD.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsBD.lean#L23) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `balancedPulse_weighted_pair` | [E257_04/Challenge.lean, line 111](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_04/Challenge.lean#L111) | [PaperStatementsAE.lean, line 47](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_04/PaperStatementsAE.lean#L47) | [E257_04](../../evidence/comparator/replay-35882032091/receipt-E257_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-mobius-nogo"></a>

## Proposition 10.10 (Möbius-support countermodel: the natural negative-sign candidate overshoots), page 113

> *The signed Lambert identity $`\sum_{d\ge1}\mu(d)/(2^d-1) = 1/2`$ is exact. Writing $`N:=\{d:\mu(d)=-1\}`$: $`\sum_{d\in N}1/(2^d-1) = 1/2 + \sum_{d\in P}1/(2^d-1)`$ where $`P:=\{d\ge2:
> \mu(d)=1\}`$, and quantitatively $`1/2 + 1/63 \le \sum_{d\in N}1/(2^d-1)`$ (using the first positive tail term $`d=6`$, $`\mu(6)=1`$) ; the negative-Möbius support strictly *overshoots* $`1/2`$ by at least $`1/63`$. [`MobiusSignSupportNoGo.half_lt_tsum_negativeMobius`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MobiusSignSupportNoGo.lean#L164) (exact decomposition at [`MobiusSignSupportNoGo.tsum_negativeMobius_eq_half_add_positiveMobiusTail`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/MobiusSignSupportNoGo.lean#L111)).*
> 
> ***Scope.** Rules out exactly one natural candidate infinite Boolean support (the negative-Möbius set) as a witness for $`1/2\in\mathcal A`$. A route-sufficiency no-go only ; it says nothing about whether *some other* infinite Boolean support sums to $`1/2`$. *divisor counts and finite sums* **Object or representation:** about the *object* ; a genuine value inequality for one specific candidate set, not a coordinate artifact. Margin $`1/63`$ is the concrete number any repair attempt (adding/removing finitely many elements) must close or exceed. <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(fixed)</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_mobius_support_overshoots_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MobiusSignAndFiniteCertificates.lean#L70)

```lean
theorem paper_mobius_support_overshoots_half :
    (∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1)) = 1 / 2 ∧
      (∑' d : ℕ+, negativeMobiusTerm d)
        = 1 / 2 + ∑' d : ℕ+, positiveMobiusTailTerm d ∧
      (1 : ℝ) / 2 + 1 / 63 ≤ ∑' d : ℕ+, negativeMobiusTerm d ∧
      (1 : ℝ) / 2 < ∑' d : ℕ+, negativeMobiusTerm d
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_first_positiveMobius_tail_term`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MobiusSignAndFiniteCertificates.lean#L48)

```lean
theorem paper_first_positiveMobius_tail_term :
    (∀ d : ℕ+, (d : ℕ) < 6 → positiveMobiusTailTerm d = 0) ∧
      moebius 6 = 1 ∧
      positiveMobiusTailTerm (⟨6, by norm_num⟩ : ℕ+) = (1 : ℝ) / 63
```

<a id="prop-mobius-nogo-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_mobius_support_overshoots_half` | [E257_36/Challenge.lean, line 100](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L100) | [PaperStatementsAQ.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAQ.lean#L36) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_first_positiveMobius_tail_term` | [E257_36/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L94) | [PaperStatementsAQ.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAQ.lean#L31) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-finite-boolsupport-and-onesided"></a>

## Proposition 10.11 (Finite computation and half-membership), page 113

> *No finite positive-index Boolean support has value exactly $`1/2`$: the reduced denominator of any finite Mersenne subset-sum is provably **odd** (each $`2^n-1`$ is odd), while $`1/2`$ needs an even denominator. [`finite_boolSupport_ne_half`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfCarryReachability.lean#L589). Separately, $`\mathsf{CertifiedGreedyMersenneDeath}`$ is a finite-depth certificate of $`x\notin\mathcal A`$, obtained by decidable tests on rational input. For example, the supplied source excludes $`3/4`$ at level $`1`$ with lookahead $`0`$: [`three_fourths_certifiedGreedyMersenneDeath`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1778). Failure to find such a certificate at a given depth does not establish membership. It records survival of that finite test, not survival at every depth. [`Erdos249257.CertifiedGreedyMersenneDeath`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GreedyAchievementSet.lean#L1756).*
> 
> ***Scope.** Any support representing $`1/2`$, if it exists, must be infinite. This follows from denominator parity, independently of the certificate search. The search supplies a different fact: a successful exclusion certificate proves nonmembership, whereas its absence in a bounded search does not prove membership or rationality. The same distinction must be checked separately for any other certificate family. *denominator parity; finite search* <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(fixed)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_support_and_onesided_certificate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/MobiusSignAndFiniteCertificates.lean#L101)

```lean
theorem paper_finite_support_and_onesided_certificate :
    (∀ A : Set ℕ, A.Finite → 0 ∉ A → erdosSupportSeries 2 A ≠ (1 : ℝ) / 2) ∧
      (∀ F : Finset ℕ, 0 ∉ F → Odd (finiteErdosSum F 2).den) ∧
      (∀ n : ℕ, 1 ≤ n → Odd (2 ^ n - 1)) ∧
      ((1 : ℚ) / 2).den = 2 ∧ Even ((1 : ℚ) / 2).den ∧
      (∀ (x : ℚ) (level lookahead : ℕ),
        CertifiedGreedyMersenneDeath x level lookahead →
          ((x : ℚ) : ℝ) ∉ mersenneAchievementSet) ∧
      CertifiedGreedyMersenneDeath (3 / 4 : ℚ) 1 0 ∧
      (3 / 4 : ℝ) ∉ mersenneAchievementSet ∧
      (∀ A : Set ℕ, 0 ∉ A → erdosSupportSeries 2 A = (1 : ℝ) / 2 → A.Infinite)
```

<a id="prop-finite-boolsupport-and-onesided-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_finite_support_and_onesided_certificate` | [E257_36/Challenge.lean, line 150](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L150) | [PaperStatementsR.lean, line 24](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsR.lean#L24) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-carry-survivor-extinction"></a>

## Proposition 10.12 (Period exclusion for the totient series), page 114

> *For $`\sum_n\varphi(n)/2^n`$, the cited finite test proves that $`\mathrm{totientTail}(N+h)-\mathrm{totientTail}(N)`$ is not an integer by excluding every possible integer state in a bounded range within finitely many steps. If the series were rational, some positive period $`h_0`$ would make these tail differences integral for every sufficiently large $`N`$. Telescoping would then give integrality also for every positive multiple $`mh_0`$.*
> 
> *Consequently, the required certificate supply is: for every $`h_0\ge1`$ and every lower bound $`N_0`$, there exist $`m\ge1`$, $`N\ge N_0`$ and a finite test length $`K`$ excluding integrality for $`(mh_0,N)`$. The unbounded choice of $`N`$ is essential; a counterexample before the unknown eventual threshold does not exclude an eventual period. [`Erdos257PeriodNoncollapse.irrational_totient_series_of_multiple_survivor_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L491). It is sufficient instead to obtain such certificates for $`h=\mathrm{lcm}(1,\ldots,t)`$ with both $`t`$ and $`N`$ exceeding arbitrary prescribed lower bounds: [`Erdos257PeriodNoncollapse.irrational_totient_series_of_lcm_survivor_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L540). The supplied finite theorem excludes the tail differences for $`1\le h\le16`$ at $`(N,L)=(14,9)`$, and hence excludes rational values whose reduced denominator divides $`2^{14}(2^h-1)`$ for one of those $`h`$. It does not establish the unbounded certificate supply. [`Erdos257PeriodNoncollapse.totient_series_ne_rat_of_den_dvd_upto_sixteen`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L587).*
> 
> ***Scope.** The declarations in <span class="sans-serif">CarrySurvivorExtinction.lean</span>, <span class="sans-serif">AdjacentCarryTube.lean</span>, <span class="sans-serif">AdjacentPhaseSeparation.lean</span> and <span class="sans-serif">TotientCarryKernelRigidity.lean</span> used in this comparison concern the totient series of Problem 249. Their carry recurrences may suggest constructions for Problem 257, but applying them there requires a new argument for the divisor transform of its chosen support. The totient-specific theorems do not supply that argument. *integer carries; totient series* <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(cofinal)</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_carry_survivor_extinction`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/TotientPeriodCertificateSupply.lean#L40)

```lean
theorem paper_carry_survivor_extinction :
    (∀ h N K : ℕ, survivorKill h N K →
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) ∧
      (¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) →
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
          totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ h N₀ : ℕ,
        (∀ N, N₀ ≤ N →
            totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) →
          ∀ m N : ℕ, N₀ ≤ N →
            totientTail (N + m * h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ∧
      ((∀ h₀ : ℕ, 0 < h₀ → ∀ N₀ : ℕ,
          ∃ m, 0 < m ∧ ∃ N, N₀ ≤ N ∧ ∃ K, survivorKill (m * h₀) N K) →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      ((∀ t₀ N₀ : ℕ,
          ∃ t, t₀ ≤ t ∧ ∃ N, N₀ ≤ N ∧ ∃ K, survivorKill (periodLcm t) N K) →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9) ∧
      (∀ h : ℕ, 1 ≤ h → h ≤ 16 →
        totientTail (14 + h) - totientTail 14 ∉ Set.range ((↑) : ℤ → ℝ)) ∧
      (∀ (r : ℚ) (h : ℕ), 1 ≤ h → h ≤ 16 →
        (r.den : ℕ) ∣ 2 ^ 14 * (2 ^ h - 1) →
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ))
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_periodLcm_is_prefix_lcm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/TotientPeriodCertificateSupply.lean#L23)

```lean
theorem paper_periodLcm_is_prefix_lcm (t : ℕ) :
    0 < periodLcm t ∧ ∀ h : ℕ, 1 ≤ h → h ≤ t → h ∣ periodLcm t
```

<a id="prop-carry-survivor-extinction-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_carry_survivor_extinction` | [E257_36/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L194) | [PaperStatementsP.lean, line 18](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsP.lean#L18) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_periodLcm_is_prefix_lcm` | [E257_36/Challenge.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L219) | [PaperStatementsP.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsP.lean#L44) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-scalar-localization"></a>

## Lemma 10.13 (Denominator complement survives scaling), page 114

> *For $`x:\mathbb Q`$, $`c:\mathbb Z`$, $`H:\mathbb N`$: if $`H\mid x.\mathrm{den}`$ and $`(c\cdot x).\mathrm{den}\mid H`$ ; i.e. multiplying by the integer $`c`$ shrinks the displayed denominator down *into* $`H`$ ; then the **complementary** denominator factor $`x.\mathrm{den}/H`$ divides $`c`$:
> ``` math
> H\mid x.\mathrm{den} \ \land\ (c\cdot x).\mathrm{den}\mid H \implies x.\mathrm{den}/H \mid |c|.
> ```
> [`Erdos249257.AdelicHeightObstruction.scalarLocalization_complement_dvd`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/AdelicHeightObstruction.lean#L23). Equivalently, writing $`D=x.\mathrm{den}/H`$, we have $`D\mid c`$, so $`t=c/D`$ is an integer and $`Hcx=t\,x.\mathrm{num}`$. Here $`H>0`$ follows from $`H\mid x.\mathrm{den}`$, since the reduced denominator is positive. [`Erdos249257.AdelicHeightObstruction.scalarLocalization_integer_eq_mul_num`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/AdelicHeightObstruction.lean#L56).*
> 
> ***Scope.** This is elementary rational arithmetic, independent of the problem. If $`c\ne0`$, divisibility gives the size bound $`|c|\ge x.\mathrm{den}/H`$. The nonzero condition is essential: $`c=0`$ clears every denominator and satisfies the divisibility conclusion without any positive lower bound on $`|c|`$. The lemma therefore constrains denominator clearing by a nonzero bounded multiplier, not arbitrary multiplication. *rational-denominator; height* **Object or representation:** about a *representation* ; pure denominator bookkeeping for $`\mathbb Q`$, with zero problem-specific content; the upstream primitive ([`Erdos249257.RationalDenominatorSurvival.divisor_dvd_divInt_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/RationalDenominatorSurvival.lean#L17)) is the domain-neutral extraction this lemma builds on. <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ScalarLocalisationHeightObstruction.lean#L29)

```lean
theorem paper_scalar_localization (x : ℚ) (c : ℤ) {H : ℕ}
    (hH : H ∣ x.den) (hscaled : ((c : ℚ) * x).den ∣ H) :
    0 < H ∧ x.den / H ∣ c.natAbs ∧ ((x.den / H : ℕ) : ℤ) ∣ c ∧
      (H : ℚ) * (c : ℚ) * x
        = ((c / ((x.den / H : ℕ) : ℤ) : ℤ) : ℚ) * (x.num : ℚ)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization_size_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ScalarLocalisationHeightObstruction.lean#L53)

```lean
theorem paper_scalar_localization_size_bound (x : ℚ) {c : ℤ} {H : ℕ}
    (hH : H ∣ x.den) (hscaled : ((c : ℚ) * x).den ∣ H) (hc : c ≠ 0) :
    x.den / H ≤ c.natAbs
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization_zero_degenerate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ScalarLocalisationHeightObstruction.lean#L62)

```lean
theorem paper_scalar_localization_zero_degenerate (x : ℚ) (H : ℕ) :
    (((0 : ℤ) : ℚ) * x).den = 1 ∧ x.den / H ∣ (0 : ℤ).natAbs ∧
      (0 : ℤ).natAbs = 0
```

<a id="lem-scalar-localization-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_scalar_localization` | [E257_36/Challenge.lean, line 233](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L233) | [PaperStatementsAA.lean, line 266](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAA.lean#L266) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_scalar_localization_size_bound` | [E257_36/Challenge.lean, line 240](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L240) | [PaperStatementsAA.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAA.lean#L272) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |
| `paper_scalar_localization_zero_degenerate` | [E257_36/Challenge.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L245) | [PaperStatementsAA.lean, line 276](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAA.lean#L276) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-mersenne-height"></a>

## Corollary 10.14 (Mersenne specialisation), page 114

> *Let $`x`$ be a positive rational number and let $`r\ge0`$, $`n\ge1`$ be integers. If $`2^r\mid x.\mathrm{num}.\mathrm{natAbs}`$ and $`x<2/(2^n-1)`$, then $`2^r\cdot(2^n-1) < 2\cdot x.\mathrm{den}`$ ; a numerator $`2`$-power lower bound plus a Mersenne-scale upper bound on $`x`$ together force a denominator lower bound, *without* introducing a global prefix LCM. [`Erdos249257.AdelicHeightObstruction.positiveRat_mersenne_height`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/AdelicHeightObstruction.lean#L103) (generic form [`Erdos249257.AdelicHeightObstruction.positiveRat_numDivisor_mul_lt_two_mul_den`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/AdelicHeightObstruction.lean#L77)). To see the inequality directly, write $`x=a/b`$ in lowest terms with $`a,b>0`$. The hypotheses give $`a\ge2^r`$ and $`a(2^n-1)<2b`$. The conclusion follows by substitution. An application of Lemma <a href="#lem:scalar-localization" data-reference-type="ref" data-reference="lem:scalar-localization">265</a> must in addition supply its denominator-divisibility assumptions. *rational-denominator; height, Mersenne instance* <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_height`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ScalarLocalisationHeightObstruction.lean#L77)

```lean
theorem paper_mersenne_height (x : ℚ) {r n : ℕ} (hx : 0 < x) (hn : 1 ≤ n)
    (hpow : 2 ^ r ∣ x.num.natAbs) (hlt : x < (2 : ℚ) / ((2 ^ n - 1 : ℕ) : ℚ)) :
    2 ^ r ≤ x.num.natAbs ∧
      x.num.natAbs * (2 ^ n - 1) < 2 * x.den ∧
      2 ^ r * (2 ^ n - 1) < 2 * x.den
```

<a id="cor-mersenne-height-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `paper_mersenne_height` | [E257_36/Challenge.lean, line 226](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_36/Challenge.lean#L226) | [PaperStatementsAA.lean, line 208](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_36/PaperStatementsAA.lean#L208) | [E257_36](../../evidence/comparator/replay-35882032091/receipt-E257_36.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-critical-band-index"></a>

## Proposition 10.16 (Quantifier collapse: one critical index suffices, not $`d{+}1`$), page 115

> *Let $`d,E\in\mathbb N`$ and assume $`E\le2^{d+1}`$. Then the purely combinatorial statement $`\mathsf{DyadicBandEscape}(d,E) \iff \exists j,\ \mathsf{CriticalDyadicBandIndex}(d,E,j)\land
> E+2(d+j)\le 2^{d-j+1}`$ collapses the $`\forall j\in[0,d]`$ band-avoidance condition (formally $`d{+}1`$ separate inequalities) to checking exactly *one* nearest-boundary index $`j`$. The range assumption ensures that a dyadic threshold lies at or above $`E`$. Choose the smallest such threshold: smaller thresholds are already below $`E`$, while larger thresholds have narrower forbidden bands. Without the range assumption all bands escape automatically when $`E>2^{d+1}`$, but no critical index exists; $`(d,E)=(0,3)`$ is the smallest example. Specialised to the concrete seam reset charge, $`\mathsf{SeamUpperResetCriticalBandEscape}`$ is proved logically *equivalent* to Definition <a href="#defn:band-escape" data-reference-type="ref" data-reference="defn:band-escape">267</a>’s hypothesis. [`Erdos249257.dyadicBandEscape_iff_exists_critical`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L108) (seam specialisation [`Erdos249257.seamUpperResetCriticalBandEscape_iff`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/HalfUpperResetCriticalBand.lean#L883)). Zero Mersenne/seam content in the core lemma ; pure $`(d,E,j)`$ arithmetic over powers of 2. *dyadic-boundary, generic* <span class="sans-serif">\[Lean\]</span><span class="sans-serif">(n/a)</span>*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_band_index_collapse`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/CriticalDyadicBandCollapse.lean#L20)

```lean
theorem paper_critical_band_index_collapse :
    (∀ d E : ℕ, DyadicBandEscape d E ↔
        ∀ j : ℕ, j ≤ d →
          2 ^ (d - j + 1) < E ∨ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)) ∧
      (∀ d E : ℕ, E ≤ 2 ^ (d + 1) →
        (DyadicBandEscape d E ↔ ∃ j : ℕ, CriticalDyadicBandIndex d E j ∧
          E + 2 * (d + j) ≤ 2 ^ (d - j + 1))) ∧
      (∀ d E : ℕ, E ≤ 2 ^ (d + 1) → ∃ j : ℕ, CriticalDyadicBandIndex d E j) ∧
      (∀ d E : ℕ, 2 ^ (d + 1) < E → DyadicBandEscape d E) ∧
      (∀ d E : ℕ, 2 ^ (d + 1) < E → ¬ ∃ j : ℕ, CriticalDyadicBandIndex d E j) ∧
      (2 ^ (0 + 1) < 3 ∧ ∀ d E : ℕ, 2 ^ (d + 1) < E → 0 ≤ d ∧ 3 ≤ E) ∧
      (SeamUpperResetCriticalBandEscape ↔ SeamUpperResetDyadicBandEscape)
```

<a id="prop-critical-band-index-comparator"></a>

**Comparator:** not yet compared.
