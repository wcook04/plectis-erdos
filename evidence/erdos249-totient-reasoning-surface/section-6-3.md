# Formal evidence: The Binary Totient Series, Section 6, results 6.73 to 6.103

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="prop-b7-60c3ed"></a>

## Proposition 6.73 (A sufficient condition on the LCM grid), page 45

> *``` math
> \big(\forall t_0,\ \exists t\ge t_0,\ \exists q\,m\,L,\ 0<q \wedge \mathcal{C}(m\cdot{H}\,t)(q\cdot{H}\,t)\ L\big)
> \implies S\notin\mathbb Q.
> ```
> One residue certificate *anywhere* on the two-multiplier LCM cone, at arbitrarily large $`t`$, suffices; the diagonal choice $`q=m=1`$ recovers Proposition <a href="#prop:B3" data-reference-type="ref" data-reference="prop:B3">123</a>. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean (implication; premise unproved)\]</span> \
> [`irrational_totient_series_of_lcm_cone_window_kill_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19014)*

The Lean declaration below states this result.

[`Erdos249257.irrational_totient_series_of_lcm_cone_window_kill_supply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L19014)

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
| `irrational_totient_series_of_lcm_cone_window_kill_supply` | [E249_12/Challenge.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L239) | [PaperStatementsC.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsC.lean#L21) | [E249_12](../../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

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

## Proposition 6.74 (A finite-grid certificate condition), page 45

> *Let $`H,L\in\mathbb N`$ and let $`Q\subseteq\mathbb N_{>0}`$ be finite and nonempty. Define $`A_q=\sum_{j=1}^{L}\varphi(qH+j)2^{L-j}`$ and $`B_q=qH+L+2`$. If $`B_q<2^L`$ for every $`q\in Q`$ and
> ``` math
> \forall q_i\in Q\ \exists q_j\in Q,\qquad
>  B_{q_j}<(A_{q_i}-A_{q_j})\bmod2^L,
> ```
> then $`R_{q_jH}-R_{q_iH}\notin\mathbb Z`$ for some $`q_i,q_j\in Q`$. Such a test at $`H=H_t`$ for arbitrarily large $`t`$ implies $`S\notin\mathbb Q`$. Neither $`|Q|\ge3`$ nor compatibility of every pair is a hypothesis. The proof, by choosing a minimum tail in the finite set, is given in Theorem <a href="#catalogue:cert:b10a" data-reference-type="ref" data-reference="catalogue:cert:b10a">107</a>. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean (implication; premise unproved)\]</span> \
> [`irrational_totient_series_of_lcm_cone_nonflat_supply`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19140)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L12)

```lean
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L36)

```lean
theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_supply_irrational`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteGridCorrespondence.lean#L49)

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
| `paperGridNumerator_eq` | [E249_09/Challenge.lean, line 287](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L287) | [PaperStatementsAX.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L238) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_grid_nonintegral_pair` | [E249_09/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L272) | [PaperStatementsAX.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L223) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_grid_supply_irrational` | [E249_09/Challenge.lean, line 279](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L279) | [PaperStatementsAX.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAX.lean#L229) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-c2sup"></a>

## Proposition 6.75 (Unbounded Farey bounds imply irrationality), page 45

> *The Farey-gap denominator bound at window $`K`$ is currently $`\sim 7.96\times10^{34}`$ at $`K=240`$ (Prop. <a href="#prop:C2-inv" data-reference-type="ref" data-reference="prop:C2-inv">150</a>). If
> ``` math
> \sup_K\, (b+d)(K) = \infty
> ```
> (that is, the proved exclusion bounds are arbitrarily large), then \#249 follows via the denominator-exclusion implication, without assuming the certificate supply in Proposition <a href="#prop:A10" data-reference-type="ref" data-reference="prop:A10">122</a>. No unboundedness claim is proved or attempted in the record. <span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Open\]</span> \
> [`gap_check_window_1_240_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/GapFareyBound.lean#L176)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.gapCertificate_window_1_240`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyGapDenominatorExclusion.lean#L41)

```lean
theorem gapCertificate_window_1_240 (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    GapCertificate 1 240 q
```

where [`GapCertificate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyGapDenominatorExclusion.lean#L15) is

```lean
def GapCertificate (N K q : ℕ) : Prop :=
  (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K))
      % 2 ^ K + q * (N + K + 2) < 2 ^ K
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_fareyGapExclusionUnbounded`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyGapDenominatorExclusion.lean#L29)

```lean
theorem irrational_totientSeries_of_fareyGapExclusionUnbounded
    (hsup : FareyGapExclusionUnbounded) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.gapFareyBound_window_1_240`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyGapDenominatorExclusion.lean#L51)

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
| `gapCertificate_window_1_240` | [E249_12/Challenge.lean, line 216](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L216) | [PaperStatementsAJ.lean, line 330](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L330) | [E249_12](../../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `irrational_totientSeries_of_fareyGapExclusionUnbounded` | [E249_12/Challenge.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L227) | [PaperStatementsAJ.lean, line 408](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L408) | [E249_12](../../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `gapFareyBound_window_1_240` | [E249_12/Challenge.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L221) | [PaperStatementsAJ.lean, line 349](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAJ.lean#L349) | [E249_12](../../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-d5cons"></a>

## Proposition 6.76 (The lower bound and a false proposed upper bound), page 45

> *By Prop. <a href="#prop:D4-inv" data-reference-type="ref" data-reference="prop:D4-inv">149</a>, the canonical dyadic totient-kernel family is unconditionally $`(2^e+1)`$-dimensional at every level $`e\ge1`$. Rationality of $`S`$ forces an associated tempered carry orbit with $`\mathbb Q`$-rank $`\ge 2^e-1`$ at every level (Prop. <a href="#prop:CP-02" data-reference-type="ref" data-reference="prop:CP-02">141</a>). An upper bound independent of $`e`$ for these same carry ranks would contradict the lower bound. More generally, a bound $`g(e)`$ with $`g(e)<2^e-1`$ at some level $`e\ge1`$ would suffice, provided it applies to the actual carry under the hypothetical rationality of $`S`$. A bound that merely grows with $`e`$ need not contradict anything. The generic assertion for arbitrary rational coefficient series is false: the $`5/4`$ comparison sequence in Section <a href="#sec:mahler-defect" data-reference-type="ref" data-reference="sec:mahler-defect">10.8</a> has an integer carry satisfying the growth condition and the same rank lower bound. The incompatible integer identity and the finite-shift counterexample (Observation <a href="#prop:B4b-kill" data-reference-type="ref" data-reference="prop:B4b-kill">166</a>) remain separate counterexample results. None is a generic rationality-driven rank ceiling. The evidence label below applies to the proved rank floor and counterexample results, not to the counterfactual upper bound. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`not_irrational_totientSeries_implies_unbounded_carryRank_unconditional`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientCarryKernelRigidity.lean#L300)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.rank_floor_and_false_proposed_carryRank_ceiling`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GenericCarryRankCeilingCounterexample.lean#L143)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.fiveQuarter_comparison_rational_with_carryRank_floor`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GenericCarryRankCeilingCounterexample.lean#L64)

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

3. [`ErdosProblems.Erdos249.PaperCompleteR21.no_generic_rationality_carryRank_ceiling`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GenericCarryRankCeilingCounterexample.lean#L100)

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
| `rank_floor_and_false_proposed_carryRank_ceiling` | [E249_13/Challenge.lean, line 109](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_13/Challenge.lean#L109) | [PaperStatementsF.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_13/PaperStatementsF.lean#L25) | [E249_13](../../evidence/comparator/replay-35882032091/receipt-E249_13.json) |
| `fiveQuarter_comparison_rational_with_carryRank_floor` | [E249_13/Challenge.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_13/Challenge.lean#L74) | [PaperStatementsE.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_13/PaperStatementsE.lean#L23) | [E249_13](../../evidence/comparator/replay-35882032091/receipt-E249_13.json) |
| `no_generic_rationality_carryRank_ceiling` | [E249_12/Challenge.lean, line 271](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L271) | [PaperStatementsBH.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsBH.lean#L28) | [E249_12](../../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

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

## Proposition 6.77 (Soundness of the finite carry test), page 45

> *For fixed $`h,N,K\in\mathbb N`$, use the integer recurrences $`c_{h,N,z}`$ defined above. Test each of the $`2(N+h+1)+1`$ candidates $`z\in\mathbb Z`$ with $`|z|\le N+h+1`$. If every candidate has some $`i\le K`$ for which
> ``` math
> |c_{h,N,z}(i)|\ge N+i+h+2,
> ```
> then $`R_{N+h}-R_N\notin\mathbb Z`$. An integral tail difference would give one of the initial candidates and would remain in the *open* strip $`|c_{h,N,z}(i)|<N+i+h+2`$ at every step. Equality at a boundary already excludes a candidate. This is the soundness implication for a specified finite test; no bound for a successful search depth is asserted.*
> 
> *<span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`tail_diff_notMem_int_of_survivorKill`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CarrySurvivorExtinction.lean#L428)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_test_sound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L8)

```lean
theorem finite_carry_test_sound (h N K : ℕ)
    (htest : ∀ z : ℤ, |z| ≤ (N + h + 1 : ℤ) →
      ∃ i : ℕ, i ≤ K ∧ (N + i + h + 2 : ℤ) ≤ |carryOrbit h N z i|) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_candidate_count`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L22)

```lean
theorem finite_carry_candidate_count (h N : ℕ) :
    (Finset.Icc (-(N + h + 1 : ℤ)) (N + h + 1)).card = 2 * (N + h + 1) + 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_true_orbit`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/FiniteCarryCorrespondence.lean#L27)

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
| `finite_carry_test_sound` | [E249_09/Challenge.lean, line 203](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L203) | [PaperStatementsAT.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L182) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_carry_candidate_count` | [E249_09/Challenge.lean, line 294](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L294) | [PaperStatementsAJ.lean, line 121](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAJ.lean#L121) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `finite_carry_true_orbit` | [E249_10/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_10/Challenge.lean#L80) | [PaperStatementsAT.lean, line 160](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_10/PaperStatementsAT.lean#L160) | [E249_10](../../evidence/comparator/replay-35882032091/receipt-E249_10.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ar-04-inv"></a>

## Proposition 6.78 (The exact totient difference on an LCM progression), page 46

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

1. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRayArithmeticLetter_eq_totient_difference`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L56)

```lean
theorem lcmRayArithmeticLetter_eq_totient_difference (t j : ℕ) :
    lcmRayArithmeticLetter t j
      = (Nat.totient (2 * periodLcm t + j) : ℤ)
        - (Nat.totient (periodLcm t + j) : ℤ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_mul_eq_totient_mul_gcd_div_totient_gcd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L70)

```lean
theorem totient_mul_eq_totient_mul_gcd_div_totient_gcd {j x : ℕ} (hj : 0 < j)
    (hx : 0 < x) :
    (Nat.totient (j * x) : ℚ)
      = (Nat.totient j : ℚ) * (Nat.totient x : ℚ) * (Nat.gcd j x : ℚ)
          / (Nat.totient (Nat.gcd j x) : ℚ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_denominators_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L86)

```lean
theorem lcmRay_divisor_denominators_pos {t j : ℕ} (hjdvd : j ∣ periodLcm t) :
    0 < j
      ∧ 0 < Nat.totient (Nat.gcd j (periodLcm t / j + 1))
      ∧ 0 < Nat.totient (Nat.gcd j (2 * (periodLcm t / j) + 1))
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_product_formula`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L104)

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

5. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_clean_formula`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L156)

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

6. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_nondivisor_literal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L144)

```lean
theorem lcmRay_nondivisor_literal {t j : ℕ} (hjdvd : ¬ j ∣ periodLcm t) :
    lcmRayArithmeticLetter t j
      = (Nat.totient (2 * periodLcm t + j) : ℤ)
        - (Nat.totient (periodLcm t + j) : ℤ) ∧
      lcmRayArithmeticLetter t j = deltaTotient (periodLcm t) (periodLcm t + j)
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.lcmRay_divisor_gcd_example`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L180)

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
| `lcmRayArithmeticLetter_eq_totient_difference` | [E249_14/Challenge.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L74) | [PaperStatementsAU.lean, line 193](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L193) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `totient_mul_eq_totient_mul_gcd_div_totient_gcd` | [E249_14/Challenge.lean, line 44](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L44) | [PaperStatementsAK.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAK.lean#L50) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `lcmRay_divisor_denominators_pos` | [E249_14/Challenge.lean, line 91](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L91) | [PaperStatementsAU.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L212) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `lcmRay_divisor_product_formula` | [E249_14/Challenge.lean, line 108](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L108) | [PaperStatementsAU.lean, line 229](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L229) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `lcmRay_divisor_clean_formula` | [E249_14/Challenge.lean, line 80](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L80) | [PaperStatementsAU.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L200) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `lcmRay_nondivisor_literal` | [E249_14/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L120) | [PaperStatementsAU.lean, line 242](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L242) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `lcmRay_divisor_gcd_example` | [E249_14/Challenge.lean, line 97](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L97) | [PaperStatementsAU.lean, line 219](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L219) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ar-03-inv"></a>

## Proposition 6.79 (A lower bound for the totient of a rough integer), page 46

> *Let $`a\ge8`$, set $`t=2^a`$, and let $`n>0`$ be an integer all of whose prime factors exceed $`t`$. If $`n<2^{2t}`$, then $`n`$ has fewer than $`t/4`$ distinct prime factors and
> ``` math
> \varphi(n)>\frac34 n.
> ```
> If $`n`$ has $`r`$ distinct prime factors, then $`n\ge t^r=2^{ar}`$, so $`ar<2t`$ and $`r<t/4`$ because $`a\ge8`$. For the second, use $`\varphi(n)/n=\prod_{p\mid n}(1-1/p)\ge1-\sum_{p\mid n}1/p>3/4`$. These are bounds for rough integers in the stated size range; they are not pointwise bounds for arbitrary totient values.*
> 
> *<span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`three_quarters_mul_lt_totient_of_rough_lt_two_pow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitArithmetic.lean#L768)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.rough_integer_prime_count_and_totient_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L215)

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
| `rough_integer_prime_count_and_totient_bound` | [E249_14/Challenge.lean, line 200](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L200) | [PaperStatementsAJ.lean, line 491](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAJ.lean#L491) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ar-05-inv"></a>

## Proposition 6.80 (Positivity of the short-window differences), page 46

> *For $`a\ge8`$ and $`1\le j<2\cdot2^a`$,
> ``` math
> \delta_{2^a}(j)=\varphi(2H_{2^a}+j)-\varphi(H_{2^a}+j)>0.
> ```
> The proof treats divisor offsets and the exceptional prime-power offsets separately, using multiplicativity and the rough-integer estimate of Proposition <a href="#prop:AR-03-inv" data-reference-type="ref" data-reference="prop:AR-03-inv">130</a>. No rationality hypothesis is used. Positivity of these finitely many coefficients contributes to the later sign theorem; a bound for the remaining infinite tail is still needed to obtain that theorem.*
> 
> *<span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`lcmRayArithmeticLetter_pos_of_lt_two_mul`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitArithmetic.lean#L1703)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_totient_difference_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L229)

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
| `shortWindow_totient_difference_pos` | [E249_14/Challenge.lean, line 146](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L146) | [PaperStatementsAU.lean, line 421](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L421) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ar-06-inv"></a>

## Proposition 6.81 (The accumulated sum is the discrepancy), page 46

> *For all $`t,L\in\mathbb N`$, the weighted diagonal sum is exactly
> ``` math
> \sum_{j=1}^{L}\delta_t(j)2^{L-j}=D(H(t),H(t),L).
> ```
> Thus its two-sided residue inequality is precisely $`\mathcal C(H(t),H(t),L)`$. The equality follows term by term from the definition of $`\delta_t`$. A separate restriction on $`L`$, when present, remains part of the hypothesis; this identity does not supply such a restricted-depth witness.*
> 
> *<span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`lcmDiagonalArithmeticKill_iff_certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitArithmetic.lean#L2045)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.weighted_shortWindow_sum_eq_windowDiscrepancy`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L241)

```lean
theorem weighted_shortWindow_sum_eq_windowDiscrepancy (t L : ℕ) :
    (∑ r ∈ Finset.range L,
        ((Nat.totient (2 * periodLcm t + (r + 1)) : ℤ)
            - (Nat.totient (periodLcm t + (r + 1)) : ℤ)) * 2 ^ (L - 1 - r))
      = windowDiscrepancy (periodLcm t) (periodLcm t) L
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.weighted_shortWindow_band_iff_certifiedKill`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmShortWindowArithmetic.lean#L262)

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
| `weighted_shortWindow_sum_eq_windowDiscrepancy` | [E249_14/Challenge.lean, line 173](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L173) | [PaperStatementsAU.lean, line 548](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L548) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `weighted_shortWindow_band_iff_certifiedKill` | [E249_14/Challenge.lean, line 159](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L159) | [PaperStatementsAU.lean, line 533](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L533) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sep-01-inv"></a>

## Proposition 6.82 (A global-to-local identity), page 47

> *``` math
> \Omega_a \;=\; 2^H(2^H-1)\Big(\textstyle\sum_n' \varphi(n)/2^n\Big) - \big(\Phi_{2H}-\Phi_H\big),\quad H={H}(2^a).
> ```
> Thus a separation estimate for $`\Omega_a`$ is an estimate for this integer translate of a multiple of $`S`$. The identity does not require other rational-approximation arguments to use this particular translate. <span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSeparation.lean#L68)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_global_to_local`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L24)

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
| `actualLcmTailOrbit_global_to_local` | [E249_14/Challenge.lean, line 215](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L215) | [PaperStatementsAT.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAT.lean#L264) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sep-02-inv"></a>

## Proposition 6.83 (A rational approximation with an error bound), page 47

> *For all $`a,q\in\mathbb N`$, with $`H=H_{2^a}`$ and the finite $`\rho_{a,q}`$ defined above,
> ``` math
> |\Omega_a-\rho_{a,q}|<\varepsilon_{a,q}
>      =\frac{2H+2q+3}{2^{2q+1}}.
> ```
> The triangle inequality transfers a separation estimate between the real tail and its rational approximation at the cost of this error. The bound tends to zero with $`q`$ for fixed $`a`$; no assertion of optimality is made. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`abs_actualLcmTailOrbit_sub_rawApprox_lt`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSeparation.lean#L141)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L39)

```lean
theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit (a q : ℕ) :
    |(totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)))
        - actualLcmRawApprox a q|
      < ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.tendsto_actualLcmRawErrorRadius_atTop_nhds_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L49)

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
| `abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit` | [E249_14/Challenge.lean, line 285](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L285) | [PaperStatementsAX.lean, line 247](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAX.lean#L247) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `tendsto_actualLcmRawErrorRadius_atTop_nhds_zero` | [E249_14/Challenge.lean, line 152](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L152) | [PaperStatementsAU.lean, line 443](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L443) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sgn-01"></a>

## Proposition 6.84 (Unconditional positivity), page 47

> *For $`a\ge8`$, $`J+(a+6)<2\cdot2^a`$:
> ``` math
> 0 < R_{2H+J} - R_{H+J},\qquad H={H}(2^a),
> ```
> with no irrationality hypothesis; the true, infinite, real translated tail difference is strictly positive throughout almost the entire short window, proved unconditionally from Prop. <a href="#prop:AR-05-inv" data-reference-type="ref" data-reference="prop:AR-05-inv">131</a> plus a directed one-sided tail bound. Any argument about the sign of the actual orbit (not merely its residue mod $`2^L`$) must agree with this; specialised at $`J=0`$ this gives $`0<\Omega_a`$. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`actualLcmTailDiff_shift_pos`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmOrbitSign.lean#L39)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_tailDiff_shift_pos_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L82)

```lean
theorem actualLcm_tailDiff_shift_pos_paper {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 < totientTail (2 * periodLcm (2 ^ a) + J)
          - totientTail (periodLcm (2 ^ a) + J)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L89)

```lean
theorem actualLcmTailOrbit_pos {a : ℕ} (ha : 8 ≤ a) :
    0 < totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
```

<a id="prop-sgn-01-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `actualLcm_tailDiff_shift_pos_paper` | [E249_14/Challenge.lean, line 250](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L250) | [PaperStatementsAT.lean, line 310](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAT.lean#L310) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `actualLcmTailOrbit_pos` | [E249_14/Challenge.lean, line 223](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L223) | [PaperStatementsAT.lean, line 273](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAT.lean#L273) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sgn-03"></a>

## Proposition 6.85 (The residue forced by integrality), page 47

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

[`ErdosProblems.Erdos249.PaperCompleteR21.actualLcm_integral_forces_topEdgeResidue_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ActualLcmSeparationAndSign.lean#L105)

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
| `actualLcm_integral_forces_topEdgeResidue_paper` | [E249_14/Challenge.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L227) | [PaperStatementsAT.lean, line 286](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAT.lean#L286) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-02-inv"></a>

## Proposition 6.86 (The penultimate term of a partial divisibility pattern), page 47

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

1. [`ErdosProblems.Erdos249.PaperCompleteR21.penultimate_shortWindow_difference_eq_half`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L37)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.dyadicScale_unique_in_open_interval`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L80)

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
| `penultimate_shortWindow_difference_eq_half` | [E249_14/Challenge.lean, line 127](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L127) | [PaperStatementsAU.lean, line 278](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAU.lean#L278) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `dyadicScale_unique_in_open_interval` | [E249_14/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L194) | [PaperStatementsAJ.lean, line 278](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAJ.lean#L278) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-06"></a>

## Proposition 6.69 (A directed certificate condition), page 43

> *For fixed $`h,N\in\mathbb{N}`$, a depth $`L\in\mathbb{N}`$ satisfying
> ``` math
> N+L+2\ \le\ D(h,N,L)\bmod2^L
>  \ \le\ 2^L-(N+h+L+2)
> ```
> exists if and only if $`R_{N+h}-R_N\notin\mathbb Z`$. The endpoint inequalities are non-strict.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L59)

```lean
theorem directed_certificate_iff (h N : ℕ) :
    (∃ L : ℕ,
        ((N : ℤ) + L + 2) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
          windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
            (2 : ℤ) ^ L - ((N : ℤ) + h + L + 2)) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.directed_certificate_example`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/ExtremalOrderDirectedAndPulse.lean#L71)

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
| `directed_certificate_iff` | [E249_12/Challenge.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L74) | [PaperStatementsAT.lean, line 373](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAT.lean#L373) | [E249_12](../../evidence/comparator/replay-35882032091/receipt-E249_12.json) |
| `directed_certificate_example` | [E249_12/Challenge.lean, line 65](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_12/Challenge.lean#L65) | [PaperStatementsAT.lean, line 365](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_12/PaperStatementsAT.lean#L365) | [E249_12](../../evidence/comparator/replay-35882032091/receipt-E249_12.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-te-03-inv"></a>

## Proposition 6.87 (An equivalent test using two residue bits), page 48

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

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_iff_twoBitResidueTest`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L129)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.dyadicMixedGuard_iff_twoBitBand`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L104)

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
| `exists_certifiedKill_iff_twoBitResidueTest` | [E249_14/Challenge.lean, line 256](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L256) | [PaperStatementsAT.lean, line 423](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAT.lean#L423) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |
| `dyadicMixedGuard_iff_twoBitBand` | [E249_14/Challenge.lean, line 188](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_14/Challenge.lean#L188) | [PaperStatementsAJ.lean, line 273](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_14/PaperStatementsAJ.lean#L273) | [E249_14](../../evidence/comparator/replay-35882032091/receipt-E249_14.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-fr-02-inv"></a>

## Proposition 6.88 (The factor in a second difference), page 48

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

1. [`ErdosProblems.Erdos249.PaperCompleteR21.two_mul_totient_dvd_totient_second_difference`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L219)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.fixedRank_cleanWindow_structure`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/PenultimateStaircaseAndRankCurvature.lean#L169)

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
| `two_mul_totient_dvd_totient_second_difference` | [E249_15/Challenge.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L168) | [PaperStatementsAU.lean, line 507](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAU.lean#L507) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `fixedRank_cleanWindow_structure` | [E249_15/Challenge.lean, line 105](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L105) | [PaperStatementsAT.lean, line 507](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L507) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-01-inv"></a>

## Proposition 6.89 (Carry displacement and tail integrality), page 48

> *For a positive integer $`v`$ and a tempered integral totient carry $`u`$,
> ``` math
> v\mid u(N+k)-u(N)\quad\Longleftrightarrow\quad R_{N+k}-R_N\in\mathbb{Z}.
> ```
> Indeed, temperedness identifies $`u(N)=vR_N`$, so the displacement is $`v(R_{N+k}-R_N)`$. This is a divisibility test for that displacement, not a dimension bound for the carry sections. The same proof works for another coefficient sequence once its tempered carry has been identified with its scaled tail; those hypotheses must be checked in each application. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`carryShift_dvd_iff_tailDiff_mem_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailCarryPeriod.lean#L77)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.carryShift_dvd_iff_tailDiff_integral`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TailCarryPeriodAndRankFloor.lean#L31)

```lean
theorem carryShift_dvd_iff_tailDiff_integral {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    (v : ℤ) ∣ u (N + k) - u N
      ↔ ∃ z : ℤ, (z : ℝ) = totientTail (N + k) - totientTail N
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.temperedCarry_eq_scaledTail_and_shift`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TailCarryPeriodAndRankFloor.lean#L20)

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
| `carryShift_dvd_iff_tailDiff_integral` | [E249_15/Challenge.lean, line 190](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L190) | [PaperStatementsBC.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBC.lean#L21) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `temperedCarry_eq_scaledTail_and_shift` | [E249_15/Challenge.lean, line 196](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L196) | [PaperStatementsBC.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBC.lean#L26) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-02"></a>

## Proposition 6.90 (A consequence of rationality and its limitation), page 49

> *If $`S\in\mathbb Q`$, there are a positive integer $`v`$ and a tempered integer carry orbit $`u`$ such that its retained sections through every level $`e`$ have rational rank at least $`2^e-1`$. At the same time, those sections are uniformly eventually periodic modulo $`v`$. Periodicity after reduction modulo $`v`$ is a statement in a finite quotient; it is not a rank upper bound over $`\mathbb Q`$. Proposition <a href="#prop:D5cons" data-reference-type="ref" data-reference="prop:D5cons">127</a> gives the lower bound, while the rational comparison sequence explains why a general rank upper bound cannot be deduced from these recurrence assumptions alone. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`not_irrational_totientSeries_implies_mod_period_and_unbounded_rank`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailCarryPeriod.lean#L224)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.rationality_forces_mod_period_and_unbounded_rank`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TailCarryPeriodAndRankFloor.lean#L46)

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
| `rationality_forces_mod_period_and_unbounded_rank` | [E249_15/Challenge.lean, line 225](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L225) | [PaperStatementsBH.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBH.lean#L50) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-cp-05-inv"></a>

## Proposition 6.91 (A totient difference congruent to two modulo four), page 49

> *For every positive integer $`h`$ and every $`B\in\mathbb N`$, there is a prime $`p>B`$ such that
> ``` math
> \varphi(p+4h)-\varphi(p)\equiv2\pmod4.
> ```
> To construct $`p`$, set $`H=4h`$, choose a prime $`r>H`$ with $`r\equiv1\pmod4`$, and use Dirichlet’s theorem in the progression $`p\equiv3r-H\pmod{4r}`$. This progression is reduced: its residue is odd and is $`-H\not\equiv0\pmod r`$. Then $`p\equiv3\pmod4`$, so $`\varphi(p)=p-1\equiv2\pmod4`$, whereas $`r\mid p+H`$ gives $`4\mid\varphi(p+H)`$. Subtracting gives the stated congruence. This supplies the arithmetic congruence at arbitrarily large primes; the additional finite exclusion in Proposition <a href="#prop:CP-07" data-reference-type="ref" data-reference="prop:CP-07">121</a> remains a separate hypothesis.*
> 
> *<span class="sans-serif">\[cofinal\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`exists_prime_deltaTotient_four_mul_mod_four_two`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailCarryPeriod.lean#L384)*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_totient_shift_four_mul_congr_two_mod_four`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L28)

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
| `exists_prime_totient_shift_four_mul_congr_two_mod_four` | [E249_15/Challenge.lean, line 239](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L239) | [PaperStatementsAJ.lean, line 304](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAJ.lean#L304) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-ta-inv"></a>

## Proposition 6.92 (An arbitrarily long zero prefix followed by a two-adic pulse), page 49

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

1. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_twoAdic_pulse_block`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L81)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.pulse_delta_of_divisor_data`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L41)

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

3. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_integral_tailDiff_half_pulse`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L100)

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
| `exists_prime_twoAdic_pulse_block` | [E249_15/Challenge.lean, line 93](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L93) | [PaperStatementsAT.lean, line 483](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L483) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `pulse_delta_of_divisor_data` | [E249_15/Challenge.lean, line 130](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L130) | [PaperStatementsAU.lean, line 348](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAU.lean#L348) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `exists_prime_integral_tailDiff_half_pulse` | [E249_15/Challenge.lean, line 83](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L83) | [PaperStatementsAT.lean, line 466](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L466) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-mp-01-inv"></a>

## Proposition 6.93 (A Möbius-inversion formula for the tail), page 50

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

1. [`ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_spec`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L114)

```lean
theorem forwardMultiple_spec (N : ℕ) {d : ℕ} (hd : 0 < d) :
    forwardMultipleShift N d = d - N % d ∧
      forwardMultipleQuotient N d = N / d + 1 ∧
      1 ≤ forwardMultipleShift N d ∧
      forwardMultipleShift N d ≤ d ∧
      d ∣ N + forwardMultipleShift N d
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.forwardMultipleShift_least`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L125)

```lean
theorem forwardMultipleShift_least (N : ℕ) {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hlt : m < forwardMultipleShift N d) : ¬ d ∣ N + m
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_enumeration`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L139)

```lean
theorem forwardMultiple_enumeration (N : ℕ) {d : ℕ} (hd : 0 < d) (l : ℕ) :
    N + (forwardMultipleShift N d + d * l) =
      d * (forwardMultipleQuotient N d + l)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.totientTail_eq_tsum_mobius_inversion`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/TwoAdicPulseBlockAndMobiusInversion.lean#L151)

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
| `forwardMultiple_spec` | [E249_15/Challenge.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L264) | [PaperStatementsBA.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBA.lean#L39) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `forwardMultipleShift_least` | [E249_15/Challenge.lean, line 255](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L255) | [PaperStatementsBA.lean, line 32](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBA.lean#L32) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `forwardMultiple_enumeration` | [E249_15/Challenge.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L259) | [PaperStatementsBA.lean, line 35](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBA.lean#L35) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `totientTail_eq_tsum_mobius_inversion` | [E249_15/Challenge.lean, line 279](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L279) | [PaperStatementsBM.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsBM.lean#L21) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-sk-01-inv"></a>

## Proposition 6.94 (Explicit finite examples), page 50

> *The finite certificates $`\mathcal C(H_{16},H_{16},23)`$ and $`\mathcal C(H_{64},H_{64},93)`$ imply $`\Omega_4,\Omega_6\notin\mathbb Z`$. Both satisfy the short-window restriction, since $`23<32`$ and $`93<128`$. They use the pre-existing certificates /. These are two explicit instances of the desired condition, not the start of a proved induction or a claim that no other finite instances can be checked.*
> 
> *<span class="sans-serif">\[fixed\]</span> <span class="sans-serif">\[Cert\]</span> \
> [`actualLcmTailOrbit_four_and_six_notMem_int`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientActualLcmShortKill.lean#L35)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_certificates_kill_omega_four_and_six`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L36)

```lean
theorem shortWindow_certificates_kill_omega_four_and_six :
    certifiedKill (periodLcm 16) (periodLcm 16) 23 ∧
      (23 : ℕ) < 32 ∧
      certifiedKill (periodLcm 64) (periodLcm 64) 93 ∧
      (93 : ℕ) < 128 ∧
      actualLcmTailOrbit 4 ∉ Set.range ((↑) : ℤ → ℝ) ∧
      actualLcmTailOrbit 6 ∉ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_inequalities`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L49)

```lean
theorem shortWindow_inequalities :
    (23 : ℕ) < 2 * 2 ^ 4 ∧ (93 : ℕ) < 2 * 2 ^ 6
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.actualLcmTailOrbit_eq_tail_difference`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L27)

```lean
theorem actualLcmTailOrbit_eq_tail_difference (a : ℕ) :
    actualLcmTailOrbit a =
      totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
```

<a id="prop-sk-01-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `shortWindow_certificates_kill_omega_four_and_six` | [E249_15/Challenge.lean, line 153](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L153) | [PaperStatementsAU.lean, line 420](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAU.lean#L420) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `shortWindow_inequalities` | [E249_15/Challenge.lean, line 245](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L245) | [PaperStatementsAJ.lean, line 502](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAJ.lean#L502) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `actualLcmTailOrbit_eq_tail_difference` | [E249_15/Challenge.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L67) | [PaperStatementsAT.lean, line 253](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L253) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-a5-inv"></a>

## Proposition 6.95 (The necessary depth), page 50

> *Every certificate $`\mathcal C(h,N,L)`$ satisfies
> ``` math
> 2(N+h+L+2)<2^L.
> ```
> The two endpoint margins must fit inside an interval of length $`2^L`$. In particular, successful depths grow at least logarithmically with $`N+h`$. This is a necessary lower bound, not an upper bound for the first successful depth. The later two-bit reformulation applies at its stated modulus and does not reverse this implication.*
> 
> *<span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`certifiedKill_depth_floor`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L79)*

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

<a id="prop-a5-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `certificate_logarithmic_depth` | [E249_06/Challenge.lean, line 172](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L172) | [PaperStatementsAT.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L181) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `fixed_depth_bounds_indices` | [E249_06/Challenge.lean, line 176](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L176) | [PaperStatementsAT.lean, line 206](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAT.lean#L206) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `certifiedKill_depth_floor` | [E249_06/Challenge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L147) | [PaperStatementsAD.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAD.lean#L51) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-a9-inv"></a>

## Proposition 6.96 (Rationality gives an eventual tail period), page 50

> *Suppose $`S=a/(2^c v)`$ in lowest terms, where $`a\in\mathbb Z`$, $`c\ge0`$ and $`v\ge1`$ is odd. Take $`h=\varphi(v)`$, including $`h=1`$ when $`v=1`$. Euler’s theorem gives $`v\mid2^h-1`$, so
> ``` math
> 2^N(2^h-1)S\in\mathbb Z\qquad(N\ge c).
> ```
> The identity relating $`S`$ to its scaled tails therefore gives $`R_{N+h}-R_N\in\mathbb Z`$ for every $`N\ge c`$. These are explicit witnesses for the eventual period asserted in Proposition <a href="#prop:A10" data-reference-type="ref" data-reference="prop:A10">122</a>. To use the finite residue test against a hypothetical rational value, one must obtain a nonintegral difference for its period at an index beyond its preperiod. Soundness proves that the quantified certificate condition rules out rationality. Conversely, the prefix-tail identity makes every positive-shift tail difference nonintegral when $`S`$ is irrational, and pointwise completeness (Theorem <a href="#catalogue:cert:a7" data-reference-type="ref" data-reference="catalogue:cert:a7">70</a>) then supplies a depth. Proposition <a href="#prop:AR-06-inv" data-reference-type="ref" data-reference="prop:AR-06-inv">132</a> only identifies the weighted diagonal sum with $`D`$; it is not the completeness argument and supplies no depth bound. <span class="sans-serif">\[uniform\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`eventual_period_of_not_irrational`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientTailPeriodKiller.lean#L358)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.rational_tail_period_explicit_witnesses`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L65)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_one_eq_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L56)

```lean
theorem totient_one_eq_one : Nat.totient 1 = 1
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.eventual_tail_period_of_not_irrational`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L111)

```lean
theorem eventual_tail_period_of_not_irrational
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_certificate_supply`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L119)

```lean
theorem irrational_of_certificate_supply
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.tail_diff_notMem_int_of_irrational`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L126)

```lean
theorem tail_diff_notMem_int_of_irrational
    (hirr : Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
    {h N : ℕ} (hh : 0 < h) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.exists_certifiedKill_iff_tail_diff_nonintegral`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/RationalTailPeriodWitnesses.lean#L163)

```lean
theorem exists_certifiedKill_iff_tail_diff_nonintegral (h N : ℕ) :
    (∃ L : ℕ, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)
```

<a id="prop-a9-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rational_tail_period_explicit_witnesses` | [E249_15/Challenge.lean, line 140](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L140) | [PaperStatementsAU.lean, line 379](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAU.lean#L379) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `totient_one_eq_one` | [E249_15/Challenge.lean, line 292](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L292) | [PaperStatementsAK.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAK.lean#L56) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `eventual_tail_period_of_not_irrational` | [E249_15/Challenge.lean, line 72](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L72) | [PaperStatementsAT.lean, line 399](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L399) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `irrational_of_certificate_supply` | [E249_15/Challenge.lean, line 120](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L120) | [PaperStatementsAT.lean, line 591](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L591) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `tail_diff_notMem_int_of_irrational` | [E249_15/Challenge.lean, line 162](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L162) | [PaperStatementsAU.lean, line 445](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAU.lean#L445) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |
| `exists_certifiedKill_iff_tail_diff_nonintegral` | [E249_15/Challenge.lean, line 78](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_15/Challenge.lean#L78) | [PaperStatementsAT.lean, line 414](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_15/PaperStatementsAT.lean#L414) | [E249_15](../../evidence/comparator/replay-35882032091/receipt-E249_15.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-b6-inv"></a>

## Proposition 6.97 (Tail integrality on an LCM grid), page 50

> *If $`S\in\mathbb Q`$, there is $`t_1\in\mathbb N`$ such that for all $`t\ge t_1`$, $`q\ge1`$ and $`m\ge0`$,
> ``` math
> R_{(q+m)H(t)}-R_{qH(t)}\in\mathbb Z.
> ```
> The threshold may depend on the hypothetical rational value. A certificate at one fixed scale therefore gives a finite denominator exclusion, not irrationality. Proposition <a href="#prop:B7" data-reference-type="ref" data-reference="prop:B7">124</a> requires certificates at arbitrarily large scales, so that one lies beyond the threshold supplied by any such rational value.*
> 
> *<span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`rational_totient_series_forces_lcm_cone_flatness`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L19002)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_flatness`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L8)

```lean
theorem lcm_grid_flatness
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ t₁ : ℕ, ∀ t, t₁ ≤ t → ∀ q m : ℕ, 0 < q →
      totientTail ((q + m) * periodLcm t) - totientTail (q * periodLcm t)
        ∈ Set.range ((↑) : ℤ → ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR20.certificate_denominator_exclusion`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L27)

```lean
theorem certificate_denominator_exclusion (r : ℚ) (h N L : ℕ)
    (hcert : certifiedKill h N L) (hden : r.den ∣ 2 ^ N * (2 ^ h - 1)) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (r : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR20.lcm_grid_supply_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/LcmGridCorrespondence.lean#L40)

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
| `lcm_grid_flatness` | [E249_09/Challenge.lean, line 209](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L209) | [PaperStatementsAT.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L199) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `certificate_denominator_exclusion` | [E249_09/Challenge.lean, line 191](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L191) | [PaperStatementsAT.lean, line 167](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L167) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |
| `lcm_grid_supply_iff` | [E249_09/Challenge.lean, line 227](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_09/Challenge.lean#L227) | [PaperStatementsAT.lean, line 220](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_09/PaperStatementsAT.lean#L220) | [E249_09](../../evidence/comparator/replay-35882032091/receipt-E249_09.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-d4-inv"></a>

## Proposition 6.98 (Independence of the retained dyadic family), page 51

> *For every $`e\ge0`$, the auxiliary canonical dyadic family has $`2^e+1`$ indexed sections, and these sections are linearly independent over $`\mathbb Q`$. The CRT–Dirichlet argument is explained in Section <a href="#sec:mahler-defect" data-reference-type="ref" data-reference="sec:mahler-defect">10.8</a>; the declaration below counts its index set. For $`e\ge1`$ the family is a basis for all sections through level $`e`$. At $`e=0`$ the auxiliary family still contains both $`\varphi(n)`$ and $`\varphi(2n)`$, so it is not the actual level-zero truncation, whose dimension is one. No rationality hypothesis on $`S`$ is used.*
> 
> *<span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`card_totientCanonicalIndex`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/TotientMahlerDefect.lean#L61)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.card_canonical_dyadic_index`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CanonicalDyadicSectionRank.lean#L21)

```lean
theorem card_canonical_dyadic_index (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.linearIndependent_canonical_dyadic_family`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CanonicalDyadicSectionRank.lean#L26)

```lean
theorem linearIndependent_canonical_dyadic_family (e : ℕ) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.canonical_family_basis_through_level`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CanonicalDyadicSectionRank.lean#L33)

```lean
theorem canonical_family_basis_through_level (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) =
        Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)) ∧
      finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.canonical_level_zero_channels`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CanonicalDyadicSectionRank.lean#L46)

```lean
theorem canonical_level_zero_channels :
    canonicalTotientKernelFamily 0 (Sum.inl 0) =
        (fun n : ℕ => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily 0 (Sum.inl 1) =
        (fun n : ℕ => (Nat.totient (2 * n) : ℚ)) ∧
      Fintype.card (TotientCanonicalIndex 0) = 2
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.finrank_throughLevel_zero_eq_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/CanonicalDyadicSectionRank.lean#L59)

```lean
theorem finrank_throughLevel_zero_eq_one :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1
```

<a id="prop-d4-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `card_canonical_dyadic_index` | [E249_16/Challenge.lean, line 67](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L67) | [PaperStatementsBB.lean, line 56](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsBB.lean#L56) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `linearIndependent_canonical_dyadic_family` | [E249_16/Challenge.lean, line 76](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L76) | [PaperStatementsBB.lean, line 68](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsBB.lean#L68) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `canonical_family_basis_through_level` | [E249_16/Challenge.lean, line 50](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L50) | [PaperStatementsBB.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsBB.lean#L41) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `canonical_level_zero_channels` | [E249_16/Challenge.lean, line 59](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L59) | [PaperStatementsBB.lean, line 49](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsBB.lean#L49) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `finrank_throughLevel_zero_eq_one` | [E249_16/Challenge.lean, line 71](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L71) | [PaperStatementsBB.lean, line 64](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsBB.lean#L64) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-c2-inv"></a>

## Proposition 6.99 (The exact range of the stated Farey-gap inequality), page 51

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

1. [`ErdosProblems.Erdos249.PaperCompleteR21.farey_window_1_240_exact_range`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyExactRangeAndDenominatorExclusion.lean#L26)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.farey_window_1_240_range_magnitude`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyExactRangeAndDenominatorExclusion.lean#L39)

```lean
theorem farey_window_1_240_range_magnitude :
    (796 : ℕ) * 10 ^ 32 ≤ 79639646646701375323355774875831053 ∧
      (79639646646701375323355774875831053 : ℕ) < 797 * 10 ^ 32
```

<a id="prop-c2-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `farey_window_1_240_exact_range` | [E249_16/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L104) | [PaperStatementsAJ.lean, line 330](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L330) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `farey_window_1_240_range_magnitude` | [E249_16/Challenge.lean, line 114](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L114) | [PaperStatementsAJ.lean, line 339](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L339) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-c3-inv"></a>

## Proposition 6.100 (The resulting denominator exclusion), page 51

> *For every reduced fraction $`a/q`$, with $`a\in\mathbb Z`$ and $`q\ge1`$,
> ``` math
> q\le79639646646701375323355774875831053
>  \quad\Longrightarrow\quad S\ne a/q.
> ```
> This is an unconditional finite denominator exclusion. It does not assume certificates at arbitrarily large scales, as required by Proposition <a href="#prop:A10" data-reference-type="ref" data-reference="prop:A10">122</a>. Conversely, excluding this finite range does not rule out rational values with larger reduced denominators. <span class="sans-serif">\[fixed\]</span> <span class="sans-serif">\[Lean\]</span> \
> [`tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18384)*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_reduced_fraction_of_small_denominator`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyExactRangeAndDenominatorExclusion.lean#L49)

```lean
theorem totient_series_ne_reduced_fraction_of_small_denominator (p : ℚ)
    (hden : p.den ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (p : ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_int_div_of_small_denominator`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/FareyExactRangeAndDenominatorExclusion.lean#L57)

```lean
theorem totient_series_ne_int_div_of_small_denominator (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hle : q ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (a : ℝ) / (q : ℝ)
```

<a id="prop-c3-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `totient_series_ne_reduced_fraction_of_small_denominator` | [E249_16/Challenge.lean, line 168](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L168) | [PaperStatementsAK.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L62) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `totient_series_ne_int_div_of_small_denominator` | [E249_16/Challenge.lean, line 163](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L163) | [PaperStatementsAK.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAK.lean#L58) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-d1d2-inv"></a>

## Proposition 6.101 (Two general irrationality criteria), page 51

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

The Lean declarations below together state a result at least as strong as this one. The two criteria and the lower bounds $1/(bq_j)$ and $1/b$ for reduced $x=a/b$ are stated as printed, with $q_j$ the reduced denominator of $u_j$. Sufficiency of the base-power condition is proved without the hypothesis $b_0\ge2$, and the binary example gives an irrational number for which that condition fails at a base $b_0\ge2$.

1. [`Erdos249257.irrational_of_den_mul_abs_sub_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L5371)

```lean
theorem irrational_of_den_mul_abs_sub_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in atTop, ((u k : ℝ)) ≠ x)
    (h0 : Tendsto (fun k => ((u k).den : ℝ) * |x - (u k : ℝ)|) atTop (nhds 0)) :
    Irrational x
```

2. [`Erdos249257.one_div_den_mul_den_le_abs_sub`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L5342)

```lean
theorem one_div_den_mul_den_le_abs_sub {q r : ℚ} (h : q ≠ r) :
    (1 : ℝ) / ((q.den : ℝ) * (r.den : ℝ)) ≤ |(q : ℝ) - (r : ℝ)|
```

3. [`Erdos249257.irrational_of_int_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L6120)

```lean
theorem irrational_of_int_mul_near_int {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

4. [`Erdos249257.irrational_of_pow_mul_near_int`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/Erdos249257/CertificateKernel.lean#L6149)

```lean
theorem irrational_of_pow_mul_near_int (b : ℕ) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_den_mul_error_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L66)

```lean
theorem irrational_of_den_mul_error_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in Filter.atTop, ((u k : ℚ) : ℝ) ≠ x)
    (h0 : Filter.Tendsto (fun k => ((u k).den : ℝ) * |x - ((u k : ℚ) : ℝ)|)
      Filter.atTop (nhds 0)) :
    Irrational x
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_dirichlet_gap`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L75)

```lean
theorem irrational_of_dirichlet_gap {x : ℝ}
    (h : ∀ Q : ℤ, 1 ≤ Q → ∃ m z : ℤ,
      0 < |(m : ℝ) * x - (z : ℝ)| ∧ |(m : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)) :
    Irrational x
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_mul_den_le_abs_diff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L27)

```lean
theorem one_div_den_mul_den_le_abs_diff {x u : ℚ} (hne : x ≠ u) :
    (1 : ℝ) / ((x.den : ℝ) * (u.den : ℝ)) ≤ |(x : ℝ) - (u : ℝ)|
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_le_abs_int_combination`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L33)

```lean
theorem one_div_den_le_abs_int_combination (p : ℚ) (m z : ℤ)
    (hne : (m : ℝ) * (p : ℝ) - (z : ℝ) ≠ 0) :
    (1 : ℝ) / (p.den : ℝ) ≤ |(m : ℝ) * (p : ℝ) - (z : ℝ)|
```

9. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_basePower_dilation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L92)

```lean
theorem irrational_of_basePower_dilation {x : ℝ} (b₀ : ℕ)
    (h : ∀ Q : ℤ, 1 ≤ Q → ∃ n : ℕ, ∃ z : ℤ,
      0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧
        |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)) :
    Irrational x
```

10. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.basePower_dilation_not_universal`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L529)

```lean
theorem basePower_dilation_not_universal :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ¬ ∀ Q : ℤ, 1 ≤ Q → ∃ (n : ℕ) (z : ℤ),
          0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧
            |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)
```

11. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.irrational_xi`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L476)

```lean
theorem irrational_xi : Irrational xi
```

12. [`ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.one_div_eight_le_dist_xi`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/SquareBlockBinaryDilationCountermodel.lean#L486)

```lean
theorem one_div_eight_le_dist_xi (n : ℕ) (z : ℤ) :
    (1 : ℝ) / 8 ≤ |(2 : ℝ) ^ n * xi - (z : ℝ)|
```

<a id="prop-d1d2-inv-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `irrational_of_den_mul_abs_sub_tendsto_zero` | [E249_06/Challenge.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L195) | [PaperStatementsAI.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L17) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `one_div_den_mul_den_le_abs_sub` | [E249_16/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L199) | [PaperStatementsAI.lean, line 34](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAI.lean#L34) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `irrational_of_int_mul_near_int` | [E249_06/Challenge.lean, line 201](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L201) | [PaperStatementsAI.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L22) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_pow_mul_near_int` | [E249_06/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L207) | [PaperStatementsAI.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAI.lean#L28) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_den_mul_error_tendsto_zero` | [E249_16/Challenge.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L134) | [PaperStatementsAJ.lean, line 382](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L382) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `irrational_of_dirichlet_gap` | [E249_16/Challenge.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L141) | [PaperStatementsAJ.lean, line 388](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L388) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `one_div_den_mul_den_le_abs_diff` | [E249_16/Challenge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L147) | [PaperStatementsAJ.lean, line 453](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L453) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `one_div_den_le_abs_int_combination` | [E249_06/Challenge.lean, line 228](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L228) | [PaperStatementsAJ.lean, line 449](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAJ.lean#L449) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `irrational_of_basePower_dilation` | [E249_16/Challenge.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L119) | [PaperStatementsAJ.lean, line 367](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L367) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `basePower_dilation_not_universal` | [E249_16/Challenge.lean, line 207](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L207) | [PaperStatementsAL.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAL.lean#L23) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `irrational_xi` | [E249_06/Challenge.lean, line 269](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L269) | [PaperStatementsAL.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L42) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |
| `one_div_eight_le_dist_xi` | [E249_06/Challenge.lean, line 295](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_06/Challenge.lean#L295) | [PaperStatementsAL.lean, line 63](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_06/PaperStatementsAL.lean#L63) | [E249_06](../../evidence/comparator/replay-35882032091/receipt-E249_06.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-d7-inv"></a>

## Proposition 6.102 (Lambert identities involving $`S`$), page 52

> *For $`L(f)=\sum_{n\ge1}f(n)/(2^n-1)`$, the identities are $`L(\mu)=1/2`$, $`L(\varphi)=2`$, $`L(1)=E`$ and $`L(\varphi*\mu)=S`$. The last identity rewrites the same unknown value; it does not deduce its irrationality from that of $`E`$. The value $`L(\mathrm{Id})=\sum_{m\ge1}\sigma(m)/2^m`$ is transcendental by Nesterenko \[nesterenko1996, Cor. 2, p. 1320\] (cited, not formalised). These examples show that Lambert-series form alone does not determine arithmetic status. The accompanying source reference checks the equality between the two indexing conventions for $`S`$, not every status claim in this paragraph; the individual comparisons are in Proposition <a href="#catalogue:cert:d7" data-reference-type="ref" data-reference="catalogue:cert:d7">94</a> and its table. <span class="sans-serif">\[n/a\]</span> <span class="sans-serif">\[Lean, Cited\]</span> \
> [`tsum_totient_div_pow_two_eq_pnat_half_pow`](https://github.com/wcook04/plectis-erdos/blob/99f4bf47422abbd8757cbb22b50ba079d764d3a7/Erdos249257/CertificateKernel.lean#L18415)*

The Lean proof assumes Nesterenko's algebraic independence theorem. Lean takes this input as a hypothesis (`NesterenkoTranscendenceP`); it is not proved in Lean.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.lambert_ladder_four_values`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L38)

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

2. [`ErdosProblems.Erdos249.PaperCompleteR21.primWeight_is_totient_conv_moebius`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L53)

```lean
theorem primWeight_is_totient_conv_moebius (n : ℕ) :
    ∑ e ∈ n.divisors, MersenneLambertLadder.primWeight e = (Nat.totient n : ℤ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.totient_series_index_bridge'`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L58)

```lean
theorem totient_series_index_bridge' :
    (∑' n : ℕ, (Nat.totient n : ℝ) / (2 : ℝ) ^ n)
      = ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.lambert_id_rung_eq_sigma_series`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L80)

```lean
theorem lambert_id_rung_eq_sigma_series :
    (∑' d : ℕ+, ((d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1))
      = ∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ)
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.transcendental_sigma_series`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L118)

```lean
theorem transcendental_sigma_series (hN : NesterenkoTranscendenceP) :
    Transcendental ℚ
      (∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ))
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.lambert_id_rung_transcendental`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L167)

```lean
theorem lambert_id_rung_transcendental (hN : NesterenkoTranscendenceP) :
    (∑' d : ℕ+, ((d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1))
        = ∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ) ∧
      Transcendental ℚ
        (∑' m : ℕ+, ((ArithmeticFunction.sigma 1 (m : ℕ) : ℕ) : ℝ) / (2 : ℝ) ^ (m : ℕ))
```

The assumed input [`NesterenkoTranscendenceP`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/LambertSigmaRungAndNesterenko.lean#L112) is

```lean
def NesterenkoTranscendenceP : Prop :=
  ∀ q : ℝ, IsAlgebraic ℚ q → 0 < |q| → |q| < 1 → Transcendental ℚ (ramanujanP q)
```

<a id="prop-d7-inv-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="prop-d9-inv"></a>

## Proposition 6.103 (A general rational gap bound), page 52

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

1. [`ErdosProblems.Erdos249.PaperCompleteR21.rational_gap_lower_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L138)

```lean
theorem rational_gap_lower_bound {lo hi : ℚ} (hlt : lo < hi) :
    (1 : ℝ) / ((hi.den : ℝ) * (lo.den : ℝ)) ≤ (hi : ℝ) - (lo : ℝ)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.den_lower_bound_of_positive_error`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L146)

```lean
theorem den_lower_bound_of_positive_error {S u : ℚ} (hlt : u < S) {ε : ℝ}
    (herr : (S : ℝ) - (u : ℝ) ≤ ε) :
    (1 : ℝ) / ((u.den : ℝ) * ε) ≤ (S.den : ℝ)
```

3. [`ErdosProblems.Erdos249.PaperCompleteR21.denominator_bound_tendsto_atTop_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L164)

```lean
theorem denominator_bound_tendsto_atTop_iff {f : ℕ → ℝ} (hpos : ∀ N, 0 < f N) :
    Filter.Tendsto (fun N => 1 / f N) Filter.atTop Filter.atTop ↔
      Filter.Tendsto f Filter.atTop (nhds 0)
```

4. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_den_mul_error_product_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L189)

```lean
theorem irrational_of_den_mul_error_product_tendsto_zero
    {x : ℝ} {u : ℕ → ℚ} {ε : ℕ → ℝ}
    (hne : ∀ j, ((u j : ℚ) : ℝ) ≠ x)
    (herr : ∀ j, |x - ((u j : ℚ) : ℝ)| ≤ ε j)
    (h0 : Filter.Tendsto (fun j => ((u j).den : ℝ) * ε j) Filter.atTop (nhds 0)) :
    Irrational x
```

5. [`ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_denominator_bound_vacuous`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/GeneralIrrationalityCriteriaAndGapBounds.lean#L201)

```lean
theorem dyadic_prefix_denominator_bound_vacuous (N : ℕ) :
    (1 : ℝ) / ((2 : ℝ) ^ N * (((N : ℝ) + 2) / (2 : ℝ) ^ N)) = 1 / ((N : ℝ) + 2) ∧
      1 / ((N : ℝ) + 2) ≤ 1
```

6. [`ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_den_dvd`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicPrefixTailBound.lean#L14)

```lean
theorem dyadic_prefix_den_dvd (N : ℕ) :
    (((totientPrefix N : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den ∣ 2 ^ N
```

7. [`ErdosProblems.Erdos249.PaperCompleteR21.totientTail_le_add_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicPrefixTailBound.lean#L22)

```lean
theorem totientTail_le_add_two (N : ℕ) :
    totientTail N ≤ (N : ℝ) + 2
```

8. [`ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_tail_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR21/DyadicPrefixTailBound.lean#L28)

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
| `rational_gap_lower_bound` | [E249_16/Challenge.lean, line 156](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L156) | [PaperStatementsAJ.lean, line 493](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L493) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `den_lower_bound_of_positive_error` | [E249_16/Challenge.lean, line 89](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L89) | [PaperStatementsAJ.lean, line 259](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L259) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `denominator_bound_tendsto_atTop_iff` | [E249_16/Challenge.lean, line 94](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L94) | [PaperStatementsAJ.lean, line 267](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L267) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `irrational_of_den_mul_error_product_tendsto_zero` | [E249_16/Challenge.lean, line 126](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L126) | [PaperStatementsAJ.lean, line 374](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L374) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `dyadic_prefix_denominator_bound_vacuous` | [E249_16/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L99) | [PaperStatementsAJ.lean, line 289](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAJ.lean#L289) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `dyadic_prefix_den_dvd` | [E249_16/Challenge.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L221) | [PaperStatementsAT.lean, line 402](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAT.lean#L402) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `totientTail_le_add_two` | [E249_16/Challenge.lean, line 238](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L238) | [PaperStatementsAU.lean, line 517](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAU.lean#L517) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |
| `dyadic_prefix_tail_le` | [E249_16/Challenge.lean, line 225](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_16/Challenge.lean#L225) | [PaperStatementsAT.lean, line 405](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_16/PaperStatementsAT.lean#L405) | [E249_16](../../evidence/comparator/replay-35882032091/receipt-E249_16.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
