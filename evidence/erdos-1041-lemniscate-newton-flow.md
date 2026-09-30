# Formal evidence: Paths in Polynomial Lemniscates:\\A Degree-Seven Counterexample\\and Radial Connections

This record belongs to the paper [erdos-1041-lemniscate-newton-flow.pdf](../paper/1041/erdos-1041-lemniscate-newton-flow.pdf). For every result it lists the Lean declarations that state it, and the recorded Comparator check where there is one. The inline links and margin marks in the paper use the same result mapping.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`436f55ebdafa`](https://github.com/wcook04/plectis-erdos/tree/436f55ebdafa67e4af0fff79f621c13f2ded12bf) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 8 results: 4 with a Lean proof of the whole statement, 3 whose Lean proof assumes a named input (marked with a dagger), 1 without a Lean proof of the whole statement; 2 compared.

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

## Proposition 3.2 (failure of a prescribed radial segment), page 6

> *There exist $`r\in(0,1)`$ for which every zero of
> ``` math
> f_r(z)=z^6+\tfrac15 r^2 z^4-\tfrac15 r^4 z^2-r^6
> ```
> lies in the open unit disc, yet the radial spoke from the origin to the zero $`r`$ leaves $`\{|f_r|<1\}`$.*

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

<a id="res-low-critical-thirteen-twentyfifths"></a>

## Passage (beginning “res:low-critical-thirteen-twentyfifths…”), page 7

**No Lean proof of the whole statement.** In Lean, the degree-two case and the closing inequality $(13/25)e^X<1$ at the recorded stopping time $X=635762889599/10^{12}$ are checked; the computation that certifies $X$ and the analytic argument in higher degrees are not.

<a id="res-scaled-low-critical"></a>

## Passage (beginning “res:scaled-low-critical…”), page 7

The Lean proof assumes Theorem 4.1 as stated. Lean takes this input as a hypothesis (`LowCriticalThirteenTwentyFifths`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCritical_of_lowCritical`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/LowCriticalScaleTransport.lean#L460)

```lean
theorem scaledLowCritical_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCritical
```

where [`ScaledLowCritical`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L54) is

```lean
def ScaledLowCritical : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      (2 * (((25 / 13 : ℝ) * μ) ^ (1 / (p.natDegree : ℝ))))
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCriticalFiveHalves_of_lowCritical`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/LowCriticalScaleTransport.lean#L491)

```lean
theorem scaledLowCriticalFiveHalves_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCriticalFiveHalves
```

where [`ScaledLowCriticalFiveHalves`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L61) is

```lean
def ScaledLowCriticalFiveHalves : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      ((5 / 2 : ℝ) * (μ ^ (1 / (p.natDegree : ℝ))))
```

The assumed input [`LowCriticalThirteenTwentyFifths`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L49) is

```lean
def LowCriticalThirteenTwentyFifths : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ → μ ≤ 13 / 25 → HasDistinctConnection p 1 2
```

<a id="res-scaled-low-critical-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-critical-value-separation"></a>

## Passage (beginning “res:critical-value-separation…”), page 9

The Lean proof assumes the connector and area construction that this proof produces. Lean takes this input as a hypothesis (`DiscSepBergmanArea`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_separation_short`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L534)

```lean
theorem discSep_separation_short (hext : DiscSepBergmanArea)
    {f : ℂ[X]} {n : ℕ} {c : ℂ} {w₀ S : ℝ}
    (hn : 3 ≤ n) (hdeg : f.natDegree = n) (hmonic : f.Monic)
    (hcrit : f.derivative.eval c = 0)
    (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv : f.eval c ≠ 0)
    (hw₀ : 0 ≤ w₀) (hw₁ : w₀ ≤ 1) (hS : max w₀ (1 - w₀) < S)
    (hsep : ∀ d : ℂ, d ≠ c → f.derivative.eval d = 0 →
      S ≤ ‖f.eval d / f.eval c - (w₀ : ℂ)‖) :
    ∃ (a b : ℂ) (γ : ℝ → ℂ) (Lf : ℝ), a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ContinuousOn γ (Set.Icc (-1 : ℝ) 1) ∧ γ (-1) = a ∧ γ 1 = b ∧
      (∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖f.eval (γ ξ)‖ ≤ ‖f.eval c‖) ∧
      BoundedVariationOn γ (Set.Icc (-1 : ℝ) 1) ∧
      0 ≤ Lf ∧ eVariationOn γ (Set.Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal Lf ∧
      Lf ^ 2 ≤ 2 * ‖f.eval c‖ ^ ((2 : ℝ) / (n : ℝ)) *
        discSepCoefficient n S (w₀ * (1 - w₀))
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSepNormalise_spec`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L410)

```lean
theorem discSepNormalise_spec {f : ℂ[X]} {n : ℕ} {c v : ℂ} {r w₀ S : ℝ}
    (hn : 3 ≤ n) (hdeg : f.natDegree = n) (hmonic : f.Monic)
    (hcrit : f.derivative.eval c = 0)
    (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hvdef : v = f.eval c) (hv : v ≠ 0)
    (hrdef : r = ‖v‖ ^ (1 / (n : ℝ)))
    (hw₀ : 0 ≤ w₀) (hw₁ : w₀ ≤ 1) (hS : max w₀ (1 - w₀) < S)
    (hsep : ∀ d : ℂ, d ≠ c → f.derivative.eval d = 0 → S ≤ ‖f.eval d / v - (w₀ : ℂ)‖) :
    DiscSepNormalised (discSepNormalise f c r v) n w₀ S
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_transport`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L475)

```lean
theorem discSep_transport {f P : ℂ[X]} {c v : ℂ} {r L : ℝ} {Z : ℝ → ℂ}
    (hr : 0 < r) (hv : v ≠ 0)
    (hP : ∀ w : ℂ, P.eval w = f.eval ((r : ℂ) * w + c) * v⁻¹)
    (hZ : DiscSepConnector P Z L) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (-1 : ℝ) 1) ∧
      γ (-1) ≠ γ 1 ∧ f.eval (γ (-1)) = 0 ∧ f.eval (γ 1) = 0 ∧
      (∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖f.eval (γ ξ)‖ ≤ ‖v‖) ∧
      BoundedVariationOn γ (Set.Icc (-1 : ℝ) 1) ∧
      eVariationOn γ (Set.Icc (-1 : ℝ) 1) ≤ ENNReal.ofReal (r * L)
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_squared_length_le`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L305)

```lean
theorem discSep_squared_length_le {n : ℕ} {w₀ S L area : ℝ}
    (hw₀ : 0 ≤ w₀) (hS : max w₀ (1 - w₀) < S)
    (hBergman : L ^ 2 ≤ 2 / Real.pi *
      Real.log ((1 + discSepQsq S (w₀ * (1 - w₀))) /
        (1 - discSepQsq S (w₀ * (1 - w₀)))) * area)
    (hArea : area ≤ Real.pi * (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ))) :
    L ^ 2 ≤ 2 * discSepCoefficient n S (w₀ * (1 - w₀))
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_bergman_factor`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L179)

```lean
theorem discSep_bergman_factor {S p : ℝ} (hS : 0 < S) (hden : 0 < S ^ 2 - S + p) :
    (1 + discSepQsq S p) / (1 - discSepQsq S p)
      = (S ^ 2 + S + p) / (S ^ 2 - S + p)
```

The assumed input [`DiscSepBergmanArea`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L293) is

```lean
def DiscSepBergmanArea : Prop :=
  ∀ (P : ℂ[X]) (n : ℕ) (w₀ S : ℝ), DiscSepNormalised P n w₀ S →
    ∃ (Z : ℝ → ℂ) (L area : ℝ),
      DiscSepConnector P Z L ∧
      L ^ 2 ≤ 2 / Real.pi *
        Real.log ((1 + discSepQsq S (w₀ * (1 - w₀))) /
          (1 - discSepQsq S (w₀ * (1 - w₀)))) * area ∧
      area ≤ Real.pi * (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ))
```

<a id="res-critical-value-separation-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-critical-value-thresholds"></a>

## Passage (beginning “res:critical-value-thresholds…”), page 9

The Lean proof assumes the connector and area construction in the proof of Theorem 5.1; for the absorbed S>=4/3 corollary (SeparationParent), Theorem 5.1 as stated. Lean takes this input as a hypothesis (`DiscSepBergmanArea`, `CriticalValueSeparationTheorem`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_uniform_radius`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L702)

```lean
theorem discSep_uniform_radius (hext : DiscSepBergmanArea)
    {f : ℂ[X]} {n : ℕ} {c : ℂ} {w₀ S : ℝ}
    (hn : 3 ≤ n) (hdeg : f.natDegree = n) (hmonic : f.Monic)
    (hroots : ∀ z : ℂ, f.eval z = 0 → ‖z‖ < 1)
    (hcrit : f.derivative.eval c = 0)
    (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv : f.eval c ≠ 0) (hv1 : ‖f.eval c‖ < 1)
    (hw₀ : 0 ≤ w₀) (hw₁ : w₀ ≤ 1) (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2)
    (hsep : ∀ d : ℂ, d ≠ c → f.derivative.eval d = 0 →
      S ≤ ‖f.eval d / f.eval c - (w₀ : ℂ)‖) :
    ∃ (a b : ℂ) (γ : ℝ → ℂ), a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ContinuousOn γ (Set.Icc (-1 : ℝ) 1) ∧ γ (-1) = a ∧ γ 1 = b ∧
      (∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖f.eval (γ ξ)‖ < 1) ∧
      BoundedVariationOn γ (Set.Icc (-1 : ℝ) 1) ∧
      eVariationOn γ (Set.Icc (-1 : ℝ) 1) < ENNReal.ofReal 2
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_cubic_six_fifths`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L738)

```lean
theorem discSep_cubic_six_fifths (hext : DiscSepBergmanArea)
    {f : ℂ[X]} {c : ℂ}
    (hdeg : f.natDegree = 3) (hmonic : f.Monic)
    (hroots : ∀ z : ℂ, f.eval z = 0 → ‖z‖ < 1)
    (hcrit : f.derivative.eval c = 0)
    (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv : f.eval c ≠ 0) (hv1 : ‖f.eval c‖ < 1)
    (hsep : ∀ d : ℂ, d ≠ c → f.derivative.eval d = 0 →
      6 / 5 ≤ ‖f.eval d / f.eval c - (1 : ℂ)‖) :
    ∃ (a b : ℂ) (γ : ℝ → ℂ), a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ContinuousOn γ (Set.Icc (-1 : ℝ) 1) ∧ γ (-1) = a ∧ γ 1 = b ∧
      (∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖f.eval (γ ξ)‖ < 1) ∧
      BoundedVariationOn γ (Set.Icc (-1 : ℝ) 1) ∧
      eVariationOn γ (Set.Icc (-1 : ℝ) 1) < ENNReal.ofReal 2
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSepCoefficient_lt_two`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L645)

```lean
theorem discSepCoefficient_lt_two {n : ℕ} (hn : 3 ≤ n) {S p : ℝ}
    (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2) (hp0 : 0 ≤ p) :
    discSepCoefficient n S p < 2
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSepCoefficient_three_six_fifths`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L677)

```lean
theorem discSepCoefficient_three_six_fifths : discSepCoefficient 3 (6 / 5) 0 < 2
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separation_parent`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SeparationParent.lean#L162)

```lean
theorem separation_parent (hSep : CriticalValueSeparationTheorem)
    {f : ℂ[X]} {c : ℂ} {w₀ S : ℝ}
    (hmonic : f.Monic) (hdeg : 3 ≤ f.natDegree)
    (hroots : PaperAnalyticTargets.RootsInOpenUnitDisc f)
    (hcrit : f.derivative.eval c = 0) (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv0 : f.eval c ≠ 0) (hv1 : ‖f.eval c‖ < 1)
    (hw0 : 0 ≤ w₀) (hw1 : w₀ ≤ 1) (hS : 4 / 3 ≤ S)
    (hsep : ValueSeparatedAtCentre f c w₀ S) :
    PaperAnalyticTargets.HasDistinctConnection f 1 2
```

where [`HasDistinctConnection`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L45) is

```lean
def HasDistinctConnection (p : ℂ[X]) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ p.eval a = 0 ∧ p.eval b = 0 ∧ ConnectedBelow p.eval R L a b
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separationCoefficient_lt_two`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SeparationParent.lean#L98)

```lean
theorem separationCoefficient_lt_two {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : 0 ≤ p) :
    separationCoefficient n (4 / 3) p < 2
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.squared_bound_lt_four`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SeparationParent.lean#L123)

```lean
theorem squared_bound_lt_four {n : ℕ} (hn : 3 ≤ n) {v p : ℝ} (hv0 : 0 < v) (hv1 : v < 1)
    (hp : 0 ≤ p) :
    2 * v ^ ((2 : ℝ) / (n : ℝ)) * separationCoefficient n (4 / 3) p < 4
```

8. [`ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.connectedBelow_of_connectedAtMost`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SeparationParent.lean#L144)

```lean
theorem connectedBelow_of_connectedAtMost {f : ℂ → ℂ} {R L R' L' : ℝ} {a b : ℂ}
    (h : PaperAnalyticTargets.ConnectedAtMost f R L a b) (hR : R < R') (hL : L < L')
    (hL0 : 0 ≤ L) : PaperCurve.ConnectedBelow f R' L' a b
```

where [`ConnectedBelow`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCurveAssembly.lean#L176) is

```lean
def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
```

The assumed input [`DiscSepBergmanArea`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L293) is

```lean
def DiscSepBergmanArea : Prop :=
  ∀ (P : ℂ[X]) (n : ℕ) (w₀ S : ℝ), DiscSepNormalised P n w₀ S →
    ∃ (Z : ℝ → ℂ) (L area : ℝ),
      DiscSepConnector P Z L ∧
      L ^ 2 ≤ 2 / Real.pi *
        Real.log ((1 + discSepQsq S (w₀ * (1 - w₀))) /
          (1 - discSepQsq S (w₀ * (1 - w₀)))) * area ∧
      area ≤ Real.pi * (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ))
```

The assumed input [`CriticalValueSeparationTheorem`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SeparationParent.lean#L60) is

```lean
def CriticalValueSeparationTheorem : Prop :=
  ∀ (f : ℂ[X]) (c : ℂ) (w₀ S : ℝ), f.Monic → 3 ≤ f.natDegree →
    f.derivative.eval c = 0 → f.derivative.derivative.eval c ≠ 0 →
    f.eval c ≠ 0 → 0 ≤ w₀ → w₀ ≤ 1 → max w₀ (1 - w₀) < S →
    ValueSeparatedAtCentre f c w₀ S →
    ∃ a b : ℂ, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      PaperAnalyticTargets.ConnectedAtMost f.eval ‖f.eval c‖
        (Real.sqrt (2 * ‖f.eval c‖ ^ ((2 : ℝ) / (f.natDegree : ℝ)) *
          separationCoefficient f.natDegree S (w₀ * (1 - w₀)))) a b
```

<a id="res-critical-value-thresholds-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).
