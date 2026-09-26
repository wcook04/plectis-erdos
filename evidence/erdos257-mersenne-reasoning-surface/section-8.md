# Formal evidence: Reciprocal Mersenne Subseries, Section 8

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="prop-one-orbit"></a>

## Proposition 8.1 (Stability of each fixed greedy prefix), page 88

> *Let $`t_j\to1/2`$ and, for each fixed $`n\ge2`$, let $`v_n^{(j)}\to x_n=(2^n-1)^{-1}`$, with $`v_n^{(j)}>0`$. Apply the greedy rule with target $`t_j`$ and weights $`v_n^{(j)}`$ in increasing order of $`n`$, through depths $`m_j\to\infty`$. For every fixed depth $`K`$, the decisions at ranks $`2,\ldots,K`$ eventually agree with those of the real half-greedy rule. This assertion concerns finite prefixes, not survival at all ranks.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_one_orbit_stability`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L272)

```lean
theorem paper_one_orbit_stability
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (dep : ℕ → ℕ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n)))
    (hvpos : ∀ j n : ℕ, 0 < v j n)
    (hdep : Filter.Tendsto dep Filter.atTop Filter.atTop)
    (K : ℕ) :
    ∀ᶠ j in Filter.atTop, K ≤ dep j ∧
      ∀ n : ℕ, 2 ≤ n → n ≤ K →
        ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
          (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)))
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.approx_orbit_induction`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L182)

```lean
theorem approx_orbit_induction
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n))) :
    ∀ r : ℕ,
      Filter.Tendsto (fun j => tailGreedyRemainder (t j) (v j) r) Filter.atTop
          (nhds (greedyMersenneRemainder (1 / 2 : ℝ) (r + 1))) ∧
        ∀ᶠ j in Filter.atTop, ∀ n : ℕ, 2 ≤ n → n ≤ r + 1 →
          ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
            (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)))
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder_mersenne`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L166)

```lean
theorem tailGreedyRemainder_mersenne (m : ℕ) :
    tailGreedyRemainder (1 / 2 : ℝ) mersenneWeight m
      = greedyMersenneRemainder (1 / 2 : ℝ) (m + 1)
```

<a id="prop-one-orbit-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_one_orbit_stability`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L104) (E257_43, line 104), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsN.lean#L246) (PaperStatementsN.lean, line 246), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)
- `approx_orbit_induction`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L78) (E257_43, line 78), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsN.lean#L121) (PaperStatementsN.lean, line 121), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)
- `tailGreedyRemainder_mersenne`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L127) (E257_43, line 127), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsN.lean#L283) (PaperStatementsN.lean, line 283), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-no-ties"></a>

## Lemma 8.2 (No-ties lemma), page 89

> *At every rank $`k`$ of the full greedy orbit for target $`1/2`$, both defining comparisons are strict: $`\rho\ne x_k`$ and $`\rho\ne T_{k+1}`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L126)

```lean
theorem paper_no_ties (k : ℕ) (hk : 2 ≤ k) :
    greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneWeight k ∧
      greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneTail k
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_take`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L71)

```lean
theorem paper_no_ties_take (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneWeight (n + 1)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_skip`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L114)

```lean
theorem paper_no_ties_skip (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneTail (n + 1)
```

4. [`ErdosProblems.Erdos257.PaperCompleteR21.irrational_mersenneTail`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/GreedyOrbitNoTies.lean#L44)

```lean
theorem irrational_mersenneTail : ∀ n : ℕ, Irrational (mersenneTail n)
```

<a id="lem-no-ties-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_no_ties`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L91) (E257_43, line 91), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsN.lean#L230) (PaperStatementsN.lean, line 230), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)
- `paper_no_ties_take`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L100) (E257_43, line 100), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsN.lean#L241) (PaperStatementsN.lean, line 241), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)
- `paper_no_ties_skip`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L96) (E257_43, line 96), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsN.lean#L236) (PaperStatementsN.lean, line 236), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)
- `irrational_mersenneTail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L141) (E257_43, line 141), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsAM.lean#L200) (PaperStatementsAM.lean, line 200), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-tr-forced-greedy"></a>

## Lemma 8.4 (Forced greedy), page 90

> *For every $`J\ge2`$: $`w_n^{(J)}>T_{n+1}^{(J)}`$ for all $`n`$ (the $`q=1`$ terms agree exactly, and every $`q\ge2`$ tail term is strictly smaller than the corresponding weight term). Consequently the greedy support is the unique candidate support, and $`\mathrm{HalfRung}(J)`$ holds iff the greedy orbit for $`1/2`$ under weights $`w_n^{(J)}`$ never lands in a fatal interval $`(T_{n+1}^{(J)},w_n^{(J)})`$. Rank $`1`$ is always a safe skip; ranks $`2`$ and $`3`$ are always takes.*

The Lean declarations below together state this result or one that implies it. The Lean statements have the same hypotheses and conclusions as the printed ones, and the uniqueness is stronger: every set $A\subseteq\mathbb N$ with $\sum_{n\in A}w_n^{(J)}=1/2$ is the greedy support, with no restriction to $A\subseteq\{2,3,\ldots\}$. The inequality $w_n^{(J)}>T_{n+1}^{(J)}$ holds for every $n\ge0$, and a rank $n$ is fatal when the greedy remainder before rank $n$ lies in $(T_{n+1}^{(J)},w_n^{(J)})$.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_unique_support_and_criterion`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungGreedyDecision.lean#L486)

```lean
theorem paper_forced_greedy_unique_support_and_criterion {J : ℕ} (hJ : 2 ≤ J) :
    (∀ A : Set ℕ, ∑' n : ℕ, rungSupportWeight J A n = 1 / 2 → A = rungGreedySupport J) ∧
      (HalfRung J ↔ ∀ n : ℕ, ¬ RungFatal J n)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_low_ranks`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungGreedyDecision.lean#L567)

```lean
theorem paper_forced_greedy_low_ranks {J : ℕ} (hJ : 2 ≤ J) :
    (1 ∉ rungGreedySupport J ∧ rungRem J 1 ≤ rungTail J 1) ∧
      2 ∈ rungGreedySupport J ∧ 3 ∈ rungGreedySupport J
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.paper_forced_greedy_tail_lt_weight'`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungGreedyDecision.lean#L147)

```lean
theorem paper_forced_greedy_tail_lt_weight' {J : ℕ} (hJ : 2 ≤ J) (n : ℕ) :
    rungTail J n < rungWeight J n
```

<a id="lem-tr-forced-greedy-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-tr-parity"></a>

## Lemma 8.5 (Parity forces infinite support), page 90

> *For every $`J\ge2`$, no finite $`A\subseteq\{2,3,\ldots\}`$ attains $`\mathrm{HalfRung}(J)`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_parity_excludes_finite_support`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungWitnessHorizon.lean#L176)

```lean
theorem paper_parity_excludes_finite_support {J : ℕ} (hJ : 2 ≤ J)
    (A : Finset ℕ) (hA : ∀ n ∈ A, 2 ≤ n) :
    ∑ n ∈ A, truncWeight J n ≠ 1 / 2
```

<a id="lem-tr-parity-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_parity_excludes_finite_support`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L221) (E257_43, line 221), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsAA.lean#L203) (PaperStatementsAA.lean, line 203), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-tr-witness-exclusion"></a>

## Theorem 8.6 (Witness exclusion), page 90

> *Define the misalignment mass
> ``` math
> \mu_J(M):=\sum_{q=2}^{J}\frac{2^{M\bmod q}}{2^q-1}.
> ```
> Let $`J\ge3`$, $`n\ge4`$, and suppose some $`M\in[n,2n-2]`$ has $`\mu_J(M)\le\tfrac{11}{15}`$. Then no Boolean prefix $`D\subseteq\{2,\ldots,n-1\}`$ satisfies
> ``` math
> T_{n+1}^{(J)}<\tfrac12-\sum_{d\in D}w_d^{(J)}<w_n^{(J)};
> ```
> This excludes the specified gap for every Boolean prefix, not only the greedy prefix.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_witness_exclusion`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungWitnessHorizon.lean#L250)

```lean
theorem paper_witness_exclusion {J n M : ℕ} (hJ : 3 ≤ J) (hn : 4 ≤ n)
    (hMlow : n ≤ M) (hMhigh : M + 2 ≤ 2 * n)
    (hmu : misalignMass J M ≤ 11 / 15)
    (D : Finset ℕ) (hD : ∀ d ∈ D, 2 ≤ d ∧ d + 1 ≤ n) :
    ¬ (truncTail J n < 1 / 2 - ∑ d ∈ D, truncWeight J d ∧
        1 / 2 - ∑ d ∈ D, truncWeight J d < truncWeight J n)
```

<a id="thm-tr-witness-exclusion-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_witness_exclusion`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L230) (E257_43, line 230), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsAA.lean#L323) (PaperStatementsAA.lean, line 323), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-tr-half-lcm"></a>

## Corollary 8.7 (Half-LCM horizon), page 90

> *Let $`J\ge2`$ and $`L_J:=\mathrm{lcm}(2,3,\ldots,J)`$. For every $`n\ge\max\{4,L_J/2+1\}`$ there is an $`M\in[n,2n-2]`$ with $`\mu_J(M)<11/15`$. Thus witness exclusion leaves only the finite window $`[4,L_J/2]`$ to check.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_half_lcm_horizon`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungWitnessHorizon.lean#L467)

```lean
theorem paper_half_lcm_horizon {J n : ℕ} (hJ : 2 ≤ J) (hn4 : 4 ≤ n)
    (hn : truncLcm J / 2 + 1 ≤ n) :
    ∃ M : ℕ, n ≤ M ∧ M + 2 ≤ 2 * n ∧ misalignMass J M < 11 / 15
```

<a id="cor-tr-half-lcm-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_half_lcm_horizon`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L212) (E257_43, line 212), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsAA.lean#L190) (PaperStatementsAA.lean, line 190), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-tr-mod12"></a>

## Lemma 8.8 (Mod-12 filter, $`J\ge7`$), page 91

> *For $`J\ge7`$, the inequality $`\mu_J(M)\le11/15`$ implies $`12\mid M`$. Thus only multiples of $`12`$ need be tested as witnesses in each interval $`[n,2n-2]`$; no potentially uncovered rank is discarded.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_mod_twelve_filter`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungWitnessHorizon.lean#L544)

```lean
theorem paper_mod_twelve_filter {J M : ℕ} (hJ : 7 ≤ J)
    (hmu : misalignMass J M ≤ 11 / 15) : 12 ∣ M
```

<a id="lem-tr-mod12-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_mod_twelve_filter`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L217) (E257_43, line 217), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsAA.lean#L200) (PaperStatementsAA.lean, line 200), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-tr-finite-decision"></a>

## Theorem 8.9 (Finite decision procedure), page 91

> *Call $`n\in[4,L_J/2]`$ **bad** if no $`M\in[n,2n-2]`$ has $`\mu_J(M)\le\tfrac{11}{15}`$, and set $`B(J):=\max(\mathrm{bad}\cup\{3\})`$. Then $`\mathrm{HalfRung}(J)`$ holds iff the greedy orbit for $`1/2`$ under weights $`w_n^{(J)}`$ survives every rank from $`2`$ through $`B(J)`$. This is a finite exact decision procedure.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos257.PaperCompleteR21.paper_rung_finite_decision`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos257/PaperCompleteR21/TruncatedRungGreedyDecision.lean#L896)

```lean
theorem paper_rung_finite_decision {J : ℕ} (hJ : 2 ≤ J) :
    HalfRung J ↔ ∀ n : ℕ, 2 ≤ n → n ≤ rungDecisionHorizon J → ¬ RungFatal J n
```

<a id="thm-tr-finite-decision-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_rung_finite_decision`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E257_43/Challenge.lean#L191) (E257_43, line 191), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E257_43/PaperStatementsJ.lean#L25) (PaperStatementsJ.lean, line 25), [replay report](../../evidence/comparator/replay-35935225572/receipt-E257_43.json) (E257_43)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
