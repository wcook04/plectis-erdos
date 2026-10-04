# Formal evidence: Paths in Polynomial Lemniscates:\\A Degree-Seven Counterexample\\and Radial Connections

This record belongs to the paper [erdos-1041-lemniscate-newton-flow.pdf](../paper/1041/erdos-1041-lemniscate-newton-flow.pdf). For every result it lists the Lean declarations that state it, and the recorded Comparator check where there is one. The paper's verification concordance uses this result mapping.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`436f55ebdafa`](https://github.com/wcook04/plectis-erdos/tree/436f55ebdafa67e4af0fff79f621c13f2ded12bf) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 4 results: 4 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 2 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below. Comparator checks separately declared statements, the axiom budget and kernel acceptance; it does not establish novelty, significance or peer review.

<a id="res-ani-degree-seven-counterexample"></a>

## Theorem 1.2 (`ani`’s degree-seven example), page 2

> *The monic polynomial $`f`$ in (2) has seven distinct zeros in the open unit disc. Every connected set $`K\subset\Omega_f`$ containing two of its zeros satisfies $`\mathcal H^1(K)>2`$.*

The Lean declarations below together state this result or one that implies it. `erdos1041_counterexample` shows $f$ is monic of degree seven with distinct roots (`roots.Nodup`) in the open unit disc; `erdos1041_counterexample_hausdorff` bounds $\mathcal H^1(K)>2$ for every preconnected $K\subset\{|f|<1\}$ containing two distinct roots, and a connected set is preconnected. `erdos1041_hausdorff_negation` and `erdos1041_hausdorff_answer_false` give the Formal Conjectures forms.

1. [`Erdos1041.Counterexample.erdos1041_counterexample`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/Counterexample/Assembly.lean#L319)

```lean
theorem erdos1041_counterexample :
    f.Monic ∧ f.natDegree = 7 ∧
    (∀ z, f.IsRoot z → ‖z‖ < 1) ∧
    f.roots.Nodup ∧
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) → γ 0 = z₁ → γ 1 = z₂ →
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖f.eval (γ τ)‖ < 1) →
        (2 : ENNReal) < pathLength γ
```

2. [`Erdos1041.Counterexample.erdos1041_counterexample_hausdorff`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L283)

```lean
theorem erdos1041_counterexample_hausdorff :
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K → K ⊆ Omega f →
        (2 : ℝ≥0∞) < μH[1] K
```

3. [`Erdos1041.Counterexample.erdos1041_hausdorff_negation`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L407)

```lean
theorem erdos1041_hausdorff_negation :
    ¬ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2
```

4. [`Erdos1041.Counterexample.erdos1041_hausdorff_answer_false`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L449)

```lean
theorem erdos1041_hausdorff_answer_false :
    False ↔ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2
```

<a id="res-ani-degree-seven-counterexample-comparator"></a>

**Comparator:** not yet compared.

<a id="lem-two-sheet-bottleneck"></a>

## Lemma 2.1, page 3

> *Let $`p`$ be a polynomial and $`U`$ a component of $`\{|p|<1\}`$ on which $`p`$ has degree two, with one simple critical point $`c`$ and $`v=p(c)\ne0`$. Write $`p(c+z)-v=z^2A(z)`$ and put $`M=|A(0)|`$, $`\delta=1-|v|`$. Let $`h>0`$. If $`|A(z)/A(0)-1|\le1/4`$ for $`|z|\le h`$ and $`\delta<Mh^2/4`$, then every connected subset $`K`$ of $`U`$ containing its two roots $`a,b`$ satisfies
> ``` math
> \mathcal H^1(K)\ge |a-c|+|b-c|-\frac83\sqrt{\delta/M}.
> ```*

The Lean declaration below states this result or one that implies it. Take the nonzero normaliser aHat = A(0), with M = |A(0)| and h > 0, as required by hh in s3_bottleneck_hausdorff. The degree-two and unique-simple-critical-point hypotheses supply its two-zero component assumptions. The theorem allows preconnected sets and gives the same Hausdorff lower bound.

[`Erdos1041.Counterexample.s3_bottleneck_hausdorff`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L187)

```lean
theorem s3_bottleneck_hausdorff
    (p : Polynomial ℂ) (cc : ℂ) (hcc : cc ∈ Omega p)
    (hcrit : (Polynomial.derivative p).IsRoot cc)
    (hv : p.eval cc ≠ 0)
    (b₁ b₂ : ℂ) (hne : b₁ ≠ b₂)
    (hb₁ : b₁ ∈ connectedComponentIn (Omega p) cc)
    (hb₂ : b₂ ∈ connectedComponentIn (Omega p) cc)
    (hr₁ : p.IsRoot b₁) (hr₂ : p.IsRoot b₂)
    (hzeros : ∀ w ∈ connectedComponentIn (Omega p) cc, p.IsRoot w → w = b₁ ∨ w = b₂)
    (huniq : ∀ c' ∈ connectedComponentIn (Omega p) cc,
      (Polynomial.derivative p).IsRoot c' → c' = cc)
    (aHat : ℂ) (haHat : aHat ≠ 0) (h : ℝ) (hh : 0 < h)
    (hdisk : ∀ z : ℂ, ‖z‖ ≤ h → ‖(shiftQuad p cc).eval z / aHat - 1‖ ≤ 1 / 4)
    (δ : ℝ) (hδ : δ = 1 - ‖p.eval cc‖) (hδpos : 0 < δ)
    (hδsmall : δ < ‖aHat‖ * h ^ 2 / 4)
    (K : Set ℂ) (hK : IsPreconnected K)
    (hKsub : K ⊆ connectedComponentIn (Omega p) cc)
    (hK₁ : b₁ ∈ K) (hK₂ : b₂ ∈ K) :
    ENNReal.ofReal (‖b₁ - cc‖ + ‖b₂ - cc‖ - 8 / 3 * Real.sqrt (δ / ‖aHat‖))
      ≤ μH[1] K
```

<a id="lem-two-sheet-bottleneck-comparator"></a>

**Comparator:** not yet compared.

s3_bottleneck_hausdorff has no Comparator association; the lemma was isolated as a paper statement in round 12

<a id="res-trinomial-all-degree"></a>

## Theorem 3.1 (all-degree monic trinomials), page 6

> *Let $`1\le m<n`$ and
> ``` math
> f(z)=z^n+az^m+b,
> ```
> with every zero in the open unit disc. For any zero $`\zeta`$, the entire segment $`[0,\zeta]`$ lies in $`\{|f|<1\}`$. Distinct zeros $`\zeta_1,\zeta_2`$ are therefore joined by the broken line $`\zeta_1\to0\to\zeta_2`$ of length $`\|\zeta_1\|+\|\zeta_2\|<2`$ inside the open unit lemniscate.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos1041.PaperTrinomialWholeR21.all_degree_monic_trinomials_whole`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperTrinomialWholeR21.lean#L23)

```lean
theorem all_degree_monic_trinomials_whole
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1) :
    (∀ z : ℂ, polynomialValue n m a b z = 0 →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1) ∧
    ∀ z₁ z₂ : ℂ,
      polynomialValue n m a b z₁ = 0 →
      polynomialValue n m a b z₂ = 0 → z₁ ≠ z₂ →
      Continuous (hub z₁ 0 z₂) ∧
      hub z₁ 0 z₂ 0 = z₁ ∧ hub z₁ 0 z₂ 2 = z₂ ∧
      (∀ t ∈ Icc (0 : ℝ) 2,
        ‖polynomialValue n m a b (hub z₁ 0 z₂ t)‖ < 1) ∧
      BoundedVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2) ∧
      (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal =
        ‖z₁‖ + ‖z₂‖ ∧
      (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal < 2
```

<a id="res-trinomial-all-degree-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `all_degree_monic_trinomials_whole`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_01/Challenge.lean#L121) (E1041_01, line 121), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_01/PaperStatementsAA.lean#L34) (PaperStatementsAA.lean, line 34), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_01.json) (E1041_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-sextic-spoke"></a>

## Proposition 3.2 (failure of a prescribed radial segment), page 7

> *There exist $`r\in(0,1)`$ for which every zero of
> ``` math
> f_r(z)=z^6+\tfrac15 r^2 z^4-\tfrac15 r^4 z^2-r^6
> ```
> lies in the open unit disc, yet the radial segment from the origin to the zero $`r`$ leaves $`\{|f_r|<1\}`$.*

The Lean declaration below states this result or one that implies it. The Lean statement finds a point $tr$ of the spoke, $0<t<1$, with $|f_r(tr)|>1$, so the spoke leaves even the closed set $\{|f_r|\le1\}$; the printed statement needs only a point with $|f_r|\ge1$.

[`ErdosProblems.Erdos1041.PaperCompleteR20.sextic_spoke_counterexample_whole`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/SexticSpokeWhole.lean#L9)

```lean
theorem sextic_spoke_counterexample_whole :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ w : ℂ, sextic (r : ℂ) w = 0 → ‖w‖ < 1) ∧
      sextic (r : ℂ) (r : ℂ) = 0 ∧
      ∃ t : ℝ, 0 < t ∧ t < 1 ∧
        1 < ‖sextic (r : ℂ) ((t : ℂ) * (r : ℂ))‖
```

<a id="res-sextic-spoke-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `sextic_spoke_counterexample_whole`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_05/Challenge.lean#L55) (E1041_05, line 55), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_05/PaperStatementsR.lean#L18) (PaperStatementsR.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_05.json) (E1041_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
