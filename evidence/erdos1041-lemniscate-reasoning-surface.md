# Formal evidence: Paths in Polynomial Lemniscates:\\A Degree-Seven Counterexample and Radial Connections

This record belongs to the paper [erdos1041-lemniscate-reasoning-surface.pdf](../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the recorded Comparator check where there is one. The paper's verification concordance uses this result mapping.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`436f55ebdafa`](https://github.com/wcook04/plectis-erdos/tree/436f55ebdafa67e4af0fff79f621c13f2ded12bf) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 37 results: 25 with a Lean proof of the whole statement, 10 whose Lean proof assumes a named input (marked with a dagger), 2 without a Lean proof of the whole statement; 23 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below. Comparator checks separately declared statements, the axiom budget and kernel acceptance; it does not establish novelty, significance or peer review.

<a id="res-ani-degree-seven-counterexample-long"></a>

## Theorem 1.2 (`ani`’s counterexample), page 2

> *The monic polynomial in (2) has seven distinct roots in the open unit disc. Every connected subset of its strict unit lemniscate containing two roots has one-dimensional Hausdorff measure greater than $`2`$.*

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

<a id="res-ani-degree-seven-counterexample-long-comparator"></a>

**Comparator:** not yet compared.

The pending status applies to this row's complete declaration set. [Receipt E1041_01](comparator/replay-35935225572/receipt-E1041_01.json) from [replay 35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572), at corpus commit `cc7e541cf2081c6fef5a5e377d52e365e33b01eb`, passed for `PalomarCorpus.E1041.PaperStatementsAE.erdos1041_hausdorff_negation`, `PalomarCorpus.E1041.PaperStatementsAE.erdos1041_hausdorff_answer_false` and the degree-seven existence statement `PalomarCorpus.E1041.PaperStatementsA.erdos1041_ani_degree_seven`. The two negation forms are proved from the corresponding declarations listed above. This row also lists the fixed-polynomial statements `erdos1041_counterexample` and `erdos1041_counterexample_hausdorff`; neither is selected in that receipt or bound in the Comparator association map. The counterexample therefore has a passing comparison, including the Hausdorff-negation statement, while the complete four-declaration paper row remains pending.

Next check: Compare the fixed-polynomial path-length and Hausdorff-measure statements, then bind all four declarations to passing receipts before marking the complete row compared.

<a id="lem-two-sheet-bottleneck-long"></a>

## Lemma 2.1 (a bottleneck estimate), page 3

> *Let $`p`$ be a polynomial and $`U`$ a component of $`\{|p|<1\}`$ on which $`p`$ is a proper map of degree two. Suppose its only critical point $`c`$ is simple and $`v=p(c)\ne0`$. Write
> ``` math
> p(c+z)-v=z^2 A(z),\qquad M=|A(0)|,\qquad \delta=1-|v|.
> ```
> Suppose $`h>0`$, $`|A(z)/A(0)-1|\le1/4`$ for $`|z|\le h`$, and $`\delta<Mh^2/4`$. If $`a,b`$ are the two zeros in $`U`$, every connected $`K\subset U`$ containing $`a,b`$ satisfies
> ``` math
> \mathcal H^1(K)\ge |a-c|+|b-c|-\frac83\sqrt{\delta/M}.
> ```*

The Lean declaration below states this result or one that implies it. `s3_bottleneck_hausdorff` is stated for any nonzero normaliser $\hat a$ with $|A(z)/\hat a-1|\le1/4$ on $|z|\le h$ and $\delta<|\hat a|h^2/4$; take $\hat a=A(0)$, nonzero because $c$ is simple. Its hypotheses that $a\ne b$ are the only zeros and $c$ the only critical point in the component are what the degree-two hypothesis supplies; it allows preconnected $K$, and $\mathrm{ofReal}(x)\le\mathcal H^1(K)$ is the printed bound.

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

<a id="lem-two-sheet-bottleneck-long-comparator"></a>

**Comparator:** not yet compared.

s3_bottleneck_hausdorff has no Comparator association; the lemma was isolated as a paper statement in round 12

<a id="res-trinomial-all-degree"></a>

## Theorem 3.1 (trinomial root connections), page 8

> *Let $`n,m`$ be integers with $`1\le m<n`$, and let $`f(z)=z^n+az^m+b`$ have every zero in $`\mathbb{D}`$. For every zero $`\zeta`$, the segment $`[0,\zeta]`$ lies in $`E_f`$. Consequently any two zeros $`\zeta_1,\zeta_2`$ are joined in $`E_f`$ by the broken line $`\zeta_1\to0\to\zeta_2`$, of length $`|\zeta_1|+|\zeta_2|<2`$.*

The Lean declarations below together state this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

1. [`ErdosProblems.Erdos1041.PaperTrinomial.all_spokes`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperTrinomial.lean#L26)

```lean
theorem all_spokes {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z : ℂ} (hz : polynomialValue n m a b z = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1
```

2. [`ErdosProblems.Erdos1041.PaperTrinomial.complete_trinomial`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperTrinomial.lean#L38)

```lean
theorem complete_trinomial {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z₁ z₂ : ℂ} (h₁ : polynomialValue n m a b z₁ = 0)
    (h₂ : polynomialValue n m a b z₂ = 0) :
    Continuous (hub z₁ 0 z₂) ∧
    hub z₁ 0 z₂ 0 = z₁ ∧ hub z₁ 0 z₂ 2 = z₂ ∧
    (∀ t ∈ Icc (0 : ℝ) 2,
      ‖polynomialValue n m a b (hub z₁ 0 z₂ t)‖ < 1) ∧
    BoundedVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2) ∧
    (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal = ‖z₁‖ + ‖z₂‖ ∧
    (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal < 2
```

<a id="res-trinomial-all-degree-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `all_spokes`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_01/Challenge.lean#L145) (E1041_01, line 145), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_01/PaperStatementsH.lean#L17) (PaperStatementsH.lean, line 17), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_01.json) (E1041_01)
- `complete_trinomial`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_01/Challenge.lean#L108) (E1041_01, line 108), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_01/PaperStatementsAA.lean#L21) (PaperStatementsAA.lean, line 21), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_01.json) (E1041_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-low-critical-thirteen-twentyfifths"></a>

## Passage (beginning “res:low-critical-thirteen-twentyfifths…”), page 10

**No Lean proof of the whole statement.** In Lean, the degree-two case and the closing inequality $(13/25)e^X<1$ at the recorded stopping time $X=635762889599/10^{12}$ are checked; the computation that certifies $X$ and the analytic argument in higher degrees are not.

<a id="res-low-critical-scale-free"></a>

## Passage (beginning “res:low-critical-scale-free…”), page 10

The Lean proof assumes Theorem 4.1 as stated. Lean takes this input as a hypothesis (`LowCriticalThirteenTwentyFifths`); it is not proved in Lean.

[`ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCritical_of_lowCritical`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/LowCriticalScaleTransport.lean#L460)

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

The assumed input [`LowCriticalThirteenTwentyFifths`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L49) is

```lean
def LowCriticalThirteenTwentyFifths : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ → μ ≤ 13 / 25 → HasDistinctConnection p 1 2
```

<a id="res-low-critical-scale-free-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-circle-slice-packing"></a>

## Lemma 4.3 (circle-slice packing), page 12

> *Under (7), for every $`r>0`$,
> ``` math
> \sum_{j=1}^{k}w(d_j,r)\le\pi,\qquad
>  w(d,r)=\arccos\Bigl(\operatorname{clamp}
>    \frac{\cosh d\cosh r-\cosh(D/2)}{\sinh d\sinh r}\Bigr),
> ```
> where $`\operatorname{clamp}`$ truncates its argument to $`[-1,1]`$.*

The Lean declarations below together state this result or one that implies it. The Lean statement proves $\sum_jw(d_j,r)\le\pi$ for every separation $D>0$, with the points in geodesic polar coordinates $(d_j,\theta_j)$, $d_j>0$, about $i$ in the upper half-plane, the image of the disc model under an isometry sending $0$ to $i$; a second form holds in any metric space obeying the hyperbolic law of cosines. The printed statement is the case $D=4\operatorname{artanh}\sqrt{\tanh(1/a)}$ with $d_j=d(0,b_j)>0$.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.circle_slice_packing`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L563)

```lean
theorem circle_slice_packing {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (polar (d i) (θ i)) (polar (d j) (θ j)))
    {r : ℝ} (hr : 0 < r) :
    ∑ j, sliceHalfAngle D (d j) r ≤ π
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.cosh_dist_polar`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L141)

```lean
theorem cosh_dist_polar (d₁ θ₁ d₂ θ₂ : ℝ) :
    cosh (dist (polar d₁ θ₁) (polar d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂)
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dist_polar_I`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L166)

```lean
theorem dist_polar_I (d θ : ℝ) : dist (polar d θ) UpperHalfPlane.I = |d|
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.exists_polar`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L177)

```lean
theorem exists_polar (z : ℍ) : ∃ d θ : ℝ, 0 ≤ d ∧ polar d θ = z
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.polar_zero_zero`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L162)

```lean
theorem polar_zero_zero : polar 0 0 = UpperHalfPlane.I
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.circle_slice_packing_abstract`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L315)

```lean
theorem circle_slice_packing_abstract {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (pt (d i) (θ i)) (pt (d j) (θ j)))
    {r : ℝ} (hr : 0 < r) :
    ∑ j, sliceHalfAngle D (d j) r ≤ π
```

<a id="res-circle-slice-packing-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `circle_slice_packing`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_01/Challenge.lean#L210) (E1041_01, line 210), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_01/PaperStatementsAC.lean#L20) (PaperStatementsAC.lean, line 20), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_01.json) (E1041_01)
- `cosh_dist_polar`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_01/Challenge.lean#L250) (E1041_01, line 250), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_01/PaperStatementsC.lean#L20) (PaperStatementsC.lean, line 20), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_01.json) (E1041_01)
- `dist_polar_I`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_01/Challenge.lean#L255) (E1041_01, line 255), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_01/PaperStatementsC.lean#L24) (PaperStatementsC.lean, line 24), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_01.json) (E1041_01)
- `exists_polar`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_01/Challenge.lean#L258) (E1041_01, line 258), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_01/PaperStatementsC.lean#L26) (PaperStatementsC.lean, line 26), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_01.json) (E1041_01)
- `polar_zero_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_01/Challenge.lean#L261) (E1041_01, line 261), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_01/PaperStatementsC.lean#L28) (PaperStatementsC.lean, line 28), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_01.json) (E1041_01)
- `circle_slice_packing_abstract`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_01/Challenge.lean#L217) (E1041_01, line 217), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_01/PaperStatementsAC.lean#L26) (PaperStatementsAC.lean, line 26), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_01.json) (E1041_01)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-dual-arity-floor"></a>

## Passage (beginning “res:dual-arity-floor…”), page 13

The Lean proof assumes the separation bound (7) and the radius and budget bounds (8), which this proof derives from the standing failure hypothesis. Lean takes this input as a hypothesis (`hsep`, `hrad`, `hbudget`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dual_arity_floor_sup`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L594)

```lean
theorem dual_arity_floor_sup {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (polar (d i) (θ i)) (polar (d j) (θ j)))
    {p : ℕ} (r σ : Fin p → ℝ) (hr : ∀ i, 0 < r i) (hσ : ∀ i, 0 ≤ σ i)
    {a x dlow U : ℝ} (hdlow : 0 < dlow) (hdlowval : lam dlow = delta a / 2)
    (hrad : ∀ j, lam (d j) ≤ delta a / 2)
    (hbudget : x ≤ ∑ j, lam (d j))
    (hU : IsLUB {y : ℝ | ∃ s : ℝ, dlow ≤ s ∧
      y = lam s - ∑ i, σ i * sliceHalfAngle D s (r i)} U)
    (hUpos : 0 < U) :
    (x - π * ∑ i, σ i) / U ≤ (k : ℝ)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dual_arity_floor`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L579)

```lean
theorem dual_arity_floor {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (polar (d i) (θ i)) (polar (d j) (θ j)))
    {p : ℕ} (r σ : Fin p → ℝ) (hr : ∀ i, 0 < r i) (hσ : ∀ i, 0 ≤ σ i)
    {a x dlow U : ℝ} (hdlow : 0 < dlow) (hdlowval : lam dlow = delta a / 2)
    (hrad : ∀ j, lam (d j) ≤ delta a / 2)
    (hbudget : x ≤ ∑ j, lam (d j))
    (hU : ∀ s : ℝ, dlow ≤ s → lam s - ∑ i, σ i * sliceHalfAngle D s (r i) ≤ U)
    (hUpos : 0 < U) :
    (x - π * ∑ i, σ i) / U ≤ (k : ℝ)
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.le_of_lam_le`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L506)

```lean
theorem le_of_lam_le {d₁ d₂ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h : lam d₂ ≤ lam d₁) :
    d₁ ≤ d₂
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.cosh_dist_polar`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L141)

```lean
theorem cosh_dist_polar (d₁ θ₁ d₂ θ₂ : ℝ) :
    cosh (dist (polar d₁ θ₁) (polar d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dual_arity_floor_abstract`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L513)

```lean
theorem dual_arity_floor_abstract {P : Type*} [PseudoMetricSpace P] (pt : ℝ → ℝ → P)
    (hlaw : ∀ d₁ θ₁ d₂ θ₂ : ℝ, cosh (dist (pt d₁ θ₁) (pt d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂))
    {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (pt (d i) (θ i)) (pt (d j) (θ j)))
    {p : ℕ} (r σ : Fin p → ℝ) (hr : ∀ i, 0 < r i) (hσ : ∀ i, 0 ≤ σ i)
    {a x dlow U : ℝ} (hdlow : 0 < dlow) (hdlowval : lam dlow = delta a / 2)
    (hrad : ∀ j, lam (d j) ≤ delta a / 2)
    (hbudget : x ≤ ∑ j, lam (d j))
    (hU : ∀ s : ℝ, dlow ≤ s → lam s - ∑ i, σ i * sliceHalfAngle D s (r i) ≤ U)
    (hUpos : 0 < U) :
    (x - π * ∑ i, σ i) / U ≤ (k : ℝ)
```

<a id="res-dual-arity-floor-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-scaled-low-critical-path"></a>

## Passage (beginning “res:scaled-low-critical-path…”), page 17

The Lean proof assumes Theorem 4.1 as stated, and only in degrees above two. Lean takes this input as a hypothesis (`LowCriticalThirteenTwentyFifths`); it is not proved in Lean.

[`ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCriticalFiveHalves_of_lowCritical`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/LowCriticalScaleTransport.lean#L491)

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

<a id="res-scaled-low-critical-path-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-constant-factor-path"></a>

## Passage (beginning “res:constant-factor-path…”), page 18

The Lean proof assumes the level and direction averaging construction that this proof produces. Lean takes this input as a hypothesis (`CFAPathConstruction`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_constant_factor_path`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L677)

```lean
theorem cfa_constant_factor_path (hext : CFAPathConstruction)
    {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hn : 2 ≤ n) (hmonic : f.Monic) (hdeg : f.natDegree = n)
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) :
    cfaJoinedAtMost f z (2 * μ) ((71 / 10) * μ ^ ((1 : ℝ) / (n : ℝ))) ∧
      (μ ≤ 1 / 2 → cfaJoinedBelow f z 1 5.7)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaBracket_two_three_twentieths_lt`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L355)

```lean
theorem cfaBracket_two_three_twentieths_lt {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k) :
    cfaBracket n k 2 (3 / 20) ≤ 71 / 10
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaBracket_five_point_seven`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L393)

```lean
theorem cfaBracket_five_point_seven {k : ℕ} (hk : 2 ≤ k) :
    Real.sqrt (2 / (k : ℝ)) *
        (Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 +
          (Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) + Real.pi / Real.sqrt (Real.log 2)))
      ≤ 5.7
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degenerate`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L313)

```lean
theorem cfa_degenerate {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) (hμ0 : μ = 0) :
    ∃ i j : Fin n, i ≠ j ∧ z i = z j ∧ f.eval (z i) = 0
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degree_two_mu`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L606)

```lean
theorem cfa_degree_two_mu {f : ℂ[X]} {z : Fin 2 → ℂ} {μ : ℝ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) :
    μ = ‖(z 0 - z 1) / 2‖ ^ 2
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degree_two_below`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L627)

```lean
theorem cfa_degree_two_below {f : ℂ[X]} {z : Fin 2 → ℂ} {μ R L : ℝ}
    (hz' : f = ∏ i, (X - C (z i))) (hmu : μ = ‖(z 0 - z 1) / 2‖ ^ 2)
    (hR : μ < R) (hL : ‖z 0 - z 1‖ ≤ L) : cfaJoinedBelow f z R L
```

where [`cfaJoinedBelow`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L240) is

```lean
def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaTwoRpow_le`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L184)

```lean
theorem cfaTwoRpow_le {n : ℕ} (hn : 3 ≤ n) : (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 63 / 50
```

The assumed input [`CFAPathConstruction`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L346) is

```lean
def CFAPathConstruction : Prop :=
  ∀ (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (μ lam r : ℝ),
    3 ≤ n → f.Monic → f.natDegree = n → RootEnumeration f z →
    CriticalMinimum f μ → 0 < μ → 0 < r → r < 1 → 1 < lam →
    ∃ k : ℕ, 2 ≤ k ∧
      cfaJoinedBelow f z (lam * μ) (cfaBracket n k lam r * μ ^ ((1 : ℝ) / (n : ℝ)))
```

<a id="res-constant-factor-path-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-constant-factor-arity"></a>

## Passage (beginning “res:constant-factor-arity…”), page 20

The Lean proof assumes the level and direction averaging construction in the proof of Theorem 5.1. Lean takes this input as a hypothesis (`CFAArityConstruction`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_arity_criterion`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L765)

```lean
theorem cfa_arity_criterion {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ} {k₀ : ℕ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ)
    (hcase : 0 < μ →
      (μ ≤ 1 / 2 ∧ 17 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 2 (13 / 100)) ∨
      (μ ≤ 1 / 4 ∧ 12 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 4 (3 / 25)) ∨
      (μ ≤ 1 / 8 ∧ 10 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 8 (11 / 100))) :
    cfaJoinedBelow f z 1 2
```

where [`cfaJoinedBelow`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L240) is

```lean
def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaArityBracket_case_one`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L440)

```lean
theorem cfaArityBracket_case_one : (cfaArityBracket 2 (13 / 100)) ^ 2 ≤ 34
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaArityBracket_case_two`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L455)

```lean
theorem cfaArityBracket_case_two : (cfaArityBracket 4 (3 / 25)) ^ 2 ≤ 24
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaArityBracket_case_three`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L470)

```lean
theorem cfaArityBracket_case_three : (cfaArityBracket 8 (11 / 100)) ^ 2 ≤ 20
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaArity_length_le`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L485)

```lean
theorem cfaArity_length_le {k₀ : ℕ} {B : ℝ} (hk : 2 ≤ k₀) (hB0 : 0 ≤ B)
    (hB : B ^ 2 ≤ 2 * (k₀ : ℝ)) : Real.sqrt (2 / (k₀ : ℝ)) * B ≤ 2
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degenerate`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L313)

```lean
theorem cfa_degenerate {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) (hμ0 : μ = 0) :
    ∃ i j : Fin n, i ≠ j ∧ z i = z j ∧ f.eval (z i) = 0
```

The assumed input [`CFAArityConstruction`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L428) is

```lean
def CFAArityConstruction (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (k₀ : ℕ) (lam r : ℝ) : Prop :=
  cfaJoinedBelow f z 1 (Real.sqrt (2 / (k₀ : ℝ)) * cfaArityBracket lam r)
```

<a id="res-constant-factor-arity-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-constant-factor-capacity"></a>

## Passage (beginning “res:constant-factor-capacity…”), page 21

The Lean proof assumes the level and direction averaging construction in the proof of Theorem 5.1, together with the area-capacity inequality. Lean takes this input as a hypothesis (`CFACapacityConstruction`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_capacity_criterion`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L538)

```lean
theorem cfa_capacity_criterion {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {κ : ℝ} {k₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hκ0 : 0 ≤ κ) (hκ : κ ≤ cfaTau k₀)
    (hext : CFACapacityConstruction n f z κ k₀) :
    cfaJoinedBelow f z 1 2
```

where [`cfaJoinedBelow`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L240) is

```lean
def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaTau_third`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L583)

```lean
theorem cfaTau_third {k : ℕ} (hk : 2 ≤ k) : (1 : ℝ) / 3 ≤ cfaTau k
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaTau_cutoffs`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L591)

```lean
theorem cfaTau_cutoffs :
    (2 / 5 : ℝ) ≤ cfaTau 3 ∧ (12 / 25 : ℝ) ≤ cfaTau 4 ∧ (1 / 2 : ℝ) ≤ cfaTau 5 ∧
    (7 / 12 : ℝ) ≤ cfaTau 6 ∧ (16 / 25 : ℝ) ≤ cfaTau 7 ∧ (2 / 3 : ℝ) ≤ cfaTau 8 ∧
    (7 / 10 : ℝ) ≤ cfaTau 9 ∧ (39 / 40 : ℝ) ≤ cfaTau 16
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaTau_ge_of_sq`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L572)

```lean
theorem cfaTau_ge_of_sq {k : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (h : (cfaA + cfaB * q) ^ 2 ≤ 2 * (k : ℝ)) : q ≤ cfaTau k
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaA_bound`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L508)

```lean
theorem cfaA_bound : Real.sqrt 2 * (1 / 20) / (1 - 1 / 20) ^ 2 ≤ cfaA
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaB_bound`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L514)

```lean
theorem cfaB_bound :
    Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2) ≤ cfaB
```

The assumed input [`CFACapacityConstruction`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L529) is

```lean
def CFACapacityConstruction (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (κ : ℝ) (k₀ : ℕ) : Prop :=
  cfaJoinedBelow f z 1
    (Real.sqrt (2 / (k₀ : ℝ)) *
      (Real.sqrt 2 * (1 / 20) / (1 - 1 / 20) ^ 2 +
        κ * (Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2))))
```

<a id="res-constant-factor-capacity-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-one-root-gamma-false"></a>

## Proposition 5.5 (a counterexample to the proposed one-root perimeter bound), page 23

> *Let $`p(z)=z^8-(3/2)z`$ and let $`C`$ be the component of $`\{|p|\le1\}`$ containing the origin. Then $`C`$ contains exactly one zero and a neighbourhood of the closed disc of radius $`5/8`$, so $`\mathcal H^1(\partial C)>5\pi/4`$. The constant $`\Gamma(1/4)^2/(2\sqrt{\pi})`$ is at most $`(\pi/2)(1+\sqrt2)<5\pi/4`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.one_root_gamma_false_unconditional`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/LobeUnconditional.lean#L41)

```lean
theorem one_root_gamma_false_unconditional :
    {z : ℂ | z ∈ lobeComponent ∧ lobePolynomial.eval z = 0} = {(0 : ℂ)} ∧
      (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall (0 : ℂ) (5 / 8) ⊆ U ∧
        U ⊆ lobeComponent) ∧
      ENNReal.ofReal (5 * Real.pi / 4)
        < MeasureTheory.Measure.hausdorffMeasure 1 (frontier lobeComponent) ∧
      Real.Gamma (1 / 4) ^ 2 / (2 * Real.sqrt Real.pi)
        ≤ (Real.pi / 2) * (1 + Real.sqrt 2) ∧
      (Real.pi / 2) * (1 + Real.sqrt 2) < 5 * Real.pi / 4
```

<a id="res-one-root-gamma-false-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `one_root_gamma_false_unconditional`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_05/Challenge.lean#L267) (E1041_05, line 267), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_05/PaperStructuresAD.lean#L19) (PaperStructuresAD.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_05.json) (E1041_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-conjecture-p-consumer"></a>

## Passage (beginning “res:conjecture-p-consumer…”), page 24

The Lean proof assumes the two-component split at the first critical level that this proof constructs. Lean takes this input as a hypothesis (`SubcriticalSplitExists`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.subcritical_perimeter_path_paper`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L265)

```lean
theorem subcritical_perimeter_path_paper
    (p : Polynomial ℂ) (n : ℕ) (μ β : ℝ)
    (hmonic : p.Monic) (hsf : Squarefree p) (hdeg : p.natDegree = n) (hn : 2 ≤ n)
    (hμ : CriticalMinimum p μ) (hμpos : 0 < μ) (hβ : 0 < β)
    (hperim : ∀ σ : ℝ, 0 < σ → σ < μ → ∀ z : ℂ, ‖p.eval z‖ ≤ σ →
      μH[(1 : ℝ)] (frontier (connectedComponentIn {w : ℂ | ‖p.eval w‖ ≤ σ} z))
        ≤ ENNReal.ofReal (β * σ ^ (1 / (n : ℝ))))
    (hsplit : SubcriticalSplitExists (fun z => p.eval z) μ (β * μ ^ (1 / (n : ℝ)))) :
    HasDistinctConnectionAtMost (fun z => p.eval z) μ (β * μ ^ (1 / (n : ℝ)))
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.subcritical_perimeter_path`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L245)

```lean
theorem subcritical_perimeter_path {f : ℂ → ℂ} {μ P : ℝ} (hP : 0 ≤ P)
    (hsplit : SubcriticalSplitExists f μ P) :
    HasDistinctConnectionAtMost f μ P
```

where [`HasDistinctConnectionAtMost`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L239) is

```lean
def HasDistinctConnectionAtMost (f : ℂ → ℂ) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ f a = 0 ∧ f b = 0 ∧ ConnectedAtMost f R L a b
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.connectedAtMost_half_perimeter`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L203)

```lean
theorem connectedAtMost_half_perimeter {f : ℂ → ℂ} {R H : ℝ} {a c : ℂ}
    (h : JordanArcDatum f R H a c) : ConnectedAtMost f R (H / 2) a c
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.halfPerimeterJoin_of_jordanArcDatum`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L216)

```lean
theorem halfPerimeterJoin_of_jordanArcDatum {f : ℂ → ℂ} {R : ℝ} {U : Set ℂ}
    (h : ∀ H : ℝ, μH[(1 : ℝ)] (frontier U) ≤ ENNReal.ofReal H →
      ∀ p ∈ U, ∀ q ∈ frontier U, JordanArcDatum f R H p q) :
    HalfPerimeterJoin f R U
```

where [`HalfPerimeterJoin`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L183) is

```lean
def HalfPerimeterJoin (f : ℂ → ℂ) (R : ℝ) (U : Set ℂ) : Prop :=
  ∀ H : ℝ, μH[(1 : ℝ)] (frontier U) ≤ ENNReal.ofReal H →
    ∀ p ∈ U, ∀ q ∈ frontier U, ConnectedAtMost f R (H / 2) p q
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.half_perimeter_selection`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L166)

```lean
theorem half_perimeter_selection {du dv lenA1 lenA2 lenA' uv H : ℝ}
    (hsplit : du + dv = uv) (hchord : uv ≤ lenA')
    (htotal : lenA1 + lenA2 + lenA' ≤ H) :
    min (du + lenA1) (dv + lenA2) ≤ H / 2
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.connectedAtMost_trans`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L86)

```lean
theorem connectedAtMost_trans {f : ℂ → ℂ} {R L₁ L₂ : ℝ} {a c b : ℂ}
    (h₁ : ConnectedAtMost f R L₁ a c) (h₂ : ConnectedAtMost f R L₂ c b)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    ConnectedAtMost f R (L₁ + L₂) a b
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.connectedAtMost_symm`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L62)

```lean
theorem connectedAtMost_symm {f : ℂ → ℂ} {R L : ℝ} {a b : ℂ}
    (h : ConnectedAtMost f R L a b) : ConnectedAtMost f R L b a
```

where [`ConnectedAtMost`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L24) is

```lean
def ConnectedAtMost (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ ≤ R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L
```

8. [`ErdosProblems.Erdos1041.PaperCompleteR21.connectedAtMost_mono`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L56)

```lean
theorem connectedAtMost_mono {f : ℂ → ℂ} {R L L' : ℝ} {a b : ℂ}
    (h : ConnectedAtMost f R L a b) (hLL : L ≤ L') : ConnectedAtMost f R L' a b
```

where [`ConnectedAtMost`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L24) is

```lean
def ConnectedAtMost (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ ≤ R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L
```

The assumed input [`SubcriticalSplitExists`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L230) is

```lean
def SubcriticalSplitExists (f : ℂ → ℂ) (μ P : ℝ) : Prop :=
  ∃ (a b c : ℂ) (Ua Ub : Set ℂ), a ≠ b ∧ f a = 0 ∧ f b = 0 ∧
    a ∈ Ua ∧ b ∈ Ub ∧ c ∈ frontier Ua ∧ c ∈ frontier Ub ∧
    μH[(1 : ℝ)] (frontier Ua) ≤ ENNReal.ofReal P ∧
    μH[(1 : ℝ)] (frontier Ub) ≤ ENNReal.ofReal P ∧
    HalfPerimeterJoin f μ Ua ∧ HalfPerimeterJoin f μ Ub
```

<a id="res-conjecture-p-consumer-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-degree-three"></a>

## Theorem 6.1 (the cubic case), page 25

> *Let $`f(z)=\prod_{j=1}^{3}(z-z_j)`$ with $`|z_j|<1`$, the roots listed with multiplicity. Then two listed root occurrences are joined inside $`\{|f|<1\}`$ by a polygonal path of length strictly below $`2`$. If $`f`$ is squarefree the two are distinct.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos1041.PaperCubicCompletion.cubic_paper_complete`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCubicCompletion.lean#L297)

```lean
theorem cubic_paper_complete (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : RootEnumeration p z) (hz : ∀i, ‖z i‖<1) :
    ∃ i j : Fin 3, ∃ c : ℂ, i ≠ j ∧
      Continuous (hub (z i) c (z j)) ∧
      BoundedVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) ∧
      HubBelow p.eval 1 2 (z i) c (z j) ∧
      ConnectedBelow p.eval 1 2 (z i) (z j) ∧
      (Squarefree p → z i ≠ z j)
```

<a id="res-degree-three-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cubic_paper_complete`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_02/Challenge.lean#L182) (E1041_02, line 182), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_02/CubicPath.lean#L18) (CubicPath.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_02.json) (E1041_02)

Challenge for `cubic_paper_complete`:

```lean
theorem cubic_paper_complete (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : p = ∏ i, (X - C (z i))) (hz : ∀ i, ‖z i‖ < 1) :
    ∃ i j : Fin 3, ∃ c : ℂ, i ≠ j ∧
      Continuous (hub (z i) c (z j)) ∧
      BoundedVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) ∧
      ((∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (hub (z i) c (z j) t)‖ < 1) ∧
        eVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
        γ 0 = z i ∧ γ 2 = z j ∧
        (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
        BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
        eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (Squarefree p → z i ≠ z j) := by sorry
```

<a id="res-critical-value-separation"></a>

## Passage (beginning “res:critical-value-separation…”), page 27

The Lean proof assumes the connector and area construction that this proof produces. Lean takes this input as a hypothesis (`DiscSepBergmanArea`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_separation_long`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L344)

```lean
theorem discSep_separation_long (hext : DiscSepBergmanArea)
    {P : ℂ[X]} {n : ℕ} {w₀ S : ℝ} (hyp : DiscSepNormalised P n w₀ S) :
    ∃ (Z : ℝ → ℂ) (L : ℝ),
      DiscSepConnector P Z L ∧
      P.eval (Z (-1)) = 0 ∧ P.eval (Z 1) = 0 ∧ Z (-1) ≠ Z 1 ∧
      (∀ ξ ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (Z ξ)‖ ≤ 1) ∧
      L ^ 2 ≤ 2 * discSepCoefficient n S (w₀ * (1 - w₀)) ∧
      (discSepCoefficient n S (w₀ * (1 - w₀)) < 2 → L < 2)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_squared_length_le`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L305)

```lean
theorem discSep_squared_length_le {n : ℕ} {w₀ S L area : ℝ}
    (hw₀ : 0 ≤ w₀) (hS : max w₀ (1 - w₀) < S)
    (hBergman : L ^ 2 ≤ 2 / Real.pi *
      Real.log ((1 + discSepQsq S (w₀ * (1 - w₀))) /
        (1 - discSepQsq S (w₀ * (1 - w₀)))) * area)
    (hArea : area ≤ Real.pi * (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ))) :
    L ^ 2 ≤ 2 * discSepCoefficient n S (w₀ * (1 - w₀))
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_length_lt_two`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L334)

```lean
theorem discSep_length_lt_two {M L : ℝ} (hL : 0 ≤ L) (hbound : L ^ 2 ≤ 2 * M)
    (hM : M < 2) : L < 2
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_bergman_factor`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L179)

```lean
theorem discSep_bergman_factor {S p : ℝ} (hS : 0 < S) (hden : 0 < S ^ 2 - S + p) :
    (1 + discSepQsq S p) / (1 - discSepQsq S p)
      = (S ^ 2 + S + p) / (S ^ 2 - S + p)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_target_starShaped`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L209)

```lean
theorem discSep_target_starShaped {a S : ℝ} (ha : 0 ≤ a) (haS : a < S) {ξ : ℂ}
    (hξ : ‖ξ ^ 2 - (a : ℂ)‖ < S) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((t : ℂ) * ξ) ^ 2 - (a : ℂ)‖ < S
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_mobius_norm_lt`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L238)

```lean
theorem discSep_mobius_norm_lt {a S : ℝ} (ha : 0 ≤ a) (haS : a < S) {w : ℂ}
    (hw : ‖w - (a : ℂ)‖ < S) :
    ‖(S : ℂ) * w‖ < ‖(S : ℂ) ^ 2 + (a : ℂ) * w - (a : ℂ) ^ 2‖
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

## Passage (beginning “res:critical-value-thresholds…”), page 30

The Lean proof assumes the connector and area construction in the proof of Theorem 7.1. Lean takes this input as a hypothesis (`DiscSepBergmanArea`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSepCoefficient_lt_two`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L645)

```lean
theorem discSepCoefficient_lt_two {n : ℕ} (hn : 3 ≤ n) {S p : ℝ}
    (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2) (hp0 : 0 ≤ p) :
    discSepCoefficient n S p < 2
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_uniform_radius`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L702)

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

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_ratio_le_branch`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L629)

```lean
theorem discSep_ratio_le_branch {S p : ℝ} (hS : 1 < S) (hp : 0 ≤ p) :
    (S ^ 2 + S + p) / (S ^ 2 - S + p) ≤ (S + 1) / (S - 1)
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_branch_le_seven`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L637)

```lean
theorem discSep_branch_le_seven {S : ℝ} (hS : 4 / 3 ≤ S) : (S + 1) / (S - 1) ≤ 7
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

<a id="res-critical-value-thresholds-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-sep-or-false"></a>

## Proposition 8.1 (failure of two critical-value criteria to cover all polynomials), page 32

> *Let $`f(z)=z^3+(3/100)z-3/4`$. Every root lies in the open unit disc, both critical points are simple, the critical values lie on distinct positive rays, $`\mu>13/25`$, and
> ``` math
> \bigl|1-f(c_-)/f(c_+)\bigr|<2/375<2.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperSeparationCounterexample.complete_sep_or_counterexample`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperSeparationCounterexample.lean#L189)

```lean
theorem complete_sep_or_counterexample :
    P.Monic ∧ P.natDegree = 3 ∧
    (∀ z : ℂ, P.eval z = 0 → ‖z‖ < 1) ∧
    (∀ z : ℂ, P.derivative.eval z = 0 ↔ z = plus ∨ z = minus) ∧
    plus ≠ minus ∧
    (∀ z : ℂ, P.derivative.eval z = 0 → P.derivative.derivative.eval z ≠ 0) ∧
    IsLeast {x : ℝ | ∃ c : ℂ, P.derivative.eval c = 0 ∧ x = ‖P.eval c‖} mu ∧
    (13 / 25 : ℝ) < mu ∧
    ¬ SamePositiveRay (P.eval plus) (P.eval minus) ∧
    ‖1 - P.eval minus / P.eval plus‖ < (2 / 375 : ℝ) ∧
    (2 / 375 : ℝ) < 2
```

<a id="res-sep-or-false-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `complete_sep_or_counterexample`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_05/Challenge.lean#L219) (E1041_05, line 219), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_05/PaperStatementsQ.lean#L44) (PaperStatementsQ.lean, line 44), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_05.json) (E1041_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-arity-not-capacity"></a>

## Proposition 8.2 (root count does not force a capacity gap), page 33

> *Let $`g(z)=z^3-(3/400)z-3/32`$. All roots lie in the open unit disc and $`\mu=187/2000\le1/2`$. The first merger joins two root components, so $`k_0=2`$, but the component at level $`2\mu`$ containing that pair has normalised capacity $`1`$.*

The Lean proof assumes the classical value $t^{1/n}$ of the transfinite diameter of the filled lemniscate $\{|p|\le t\}$ of a monic polynomial $p$ of degree $n$, used only in the capacity clause. Lean takes this input as a hypothesis (`LemniscateTransfiniteDiameter`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.Arity.arity_not_capacity`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ArityNotCapacity.lean#L677)

```lean
theorem arity_not_capacity (hLTD : LemniscateTransfiniteDiameter) :
    G.Monic ∧ G.natDegree = 3 ∧
      PaperAnalyticTargets.RootsInOpenUnitDisc G ∧
      PaperAnalyticTargets.CriticalMinimum G (187 / 2000 : ℝ) ∧
      (187 / 2000 : ℝ) ≤ 1 / 2 ∧
      (∀ c : ℂ, G.derivative.eval c = 0 ∧ ‖G.eval c‖ = 187 / 2000 ↔ c = -(1 / 20)) ∧
      (∃ a b : ℂ, a ≠ b ∧
        G.roots.filter
            (· ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)))
          = {a, b} ∧
        b ∉ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} a ∧
        a ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20)) ∧
        b ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20))) ∧
      Multiset.card (G.roots.filter
          (· ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20))))
        = 2 ∧
      transfiniteDiameter
          (closure (connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20))))
        / (2 * (187 / 2000 : ℝ)) ^ ((1 : ℝ) / 3) = 1
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.Arity.arity_first_merger`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ArityNotCapacity.lean#L568)

```lean
theorem arity_first_merger :
    (∃ a b : ℂ, a ≠ b ∧
      G.roots.filter
          (· ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)))
        = {a, b} ∧
      b ∉ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 187 / 2000} a ∧
      a ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20)) ∧
      b ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20))) ∧
    Multiset.card (G.roots.filter
        (· ∈ connectedComponentIn {z : ℂ | ‖G.eval z‖ ≤ 187 / 2000} (-(1 / 20)))) = 2 ∧
    connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20)) =
      {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)}
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.Arity.closure_doubleLevelComponent`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ArityNotCapacity.lean#L660)

```lean
theorem closure_doubleLevelComponent :
    closure (connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20))) =
      {z : ℂ | ‖G.eval z‖ ≤ 2 * (187 / 2000)}
```

The assumed input [`LemniscateTransfiniteDiameter`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ArityNotCapacity.lean#L95) is

```lean
def LemniscateTransfiniteDiameter : Prop :=
  ∀ (p : ℂ[X]) (t : ℝ), p.Monic → 1 ≤ p.natDegree → 0 < t →
    transfiniteDiameter {z | ‖p.eval z‖ ≤ t} = t ^ ((1 : ℝ) / p.natDegree)
```

<a id="res-arity-not-capacity-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="prop-sharp-collinear-chebyshev-comparator"></a>

## Theorem 9.1 (Chebyshev comparison), page 34

> *Let $`m\ge0`$, let $`p\in\mathbb R[X]`$ be monic of degree $`m+2`$, and let
> ``` math
> -1<c_0<\cdots<c_m<1,\qquad |c_i|\le1.
> ```
> Suppose $`p(-1)=p(1)=0`$ and $`p(c_i)p(c_{i+1})<0`$ for $`0\le i<m`$. Then
> ``` math
> \min_{0\le i\le m}|p(c_i)|\le C_{m+2}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/SharpCollinearChebyshev.lean#L133)

```lean
theorem exists_peak_le_comparisonBound
    {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hp : p.IsMonicOfDegree (m + 2))
    (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1)
    (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0)
    (hpalt : ∀ i : Fin m,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) :
    ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2)
```

<a id="prop-sharp-collinear-chebyshev-comparator-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exists_peak_le_comparisonBound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L42) (E1041_03, line 42), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsI.lean#L18) (PaperStatementsI.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-sharp-collinear-diameter"></a>

## Theorem 9.2 (a sharp bound for collinear roots), page 34

> *Let $`f`$ be a monic polynomial of degree $`n\ge2`$ whose zero occurrences are collinear, and let $`D`$ be their diameter. Some two adjacent zero occurrences are joined by a segment of length at most $`D`$ on which
> ``` math
> |f(z)|\le
>  \frac{(D/2)^n}{2^{n-1}\cos^n(\pi/(2n))}.          \tag{9}
> ```
> The constant in *(9)* is best possible in every degree. Equality is attained by affine images of the zeros of $`T_n`$ whose extreme zeros have distance $`D`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L367)

```lean
theorem sharp_collinear_root_diameter {n : ℕ} (hn : 2 ≤ n)
    (base dir : ℂ) (hdir : ‖dir‖ = 1) (y : Fin n → ℝ) (f : ℂ[X])
    (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ)))) (D : ℝ)
    (hD : IsGreatest {d : ℝ | ∃ j k : Fin n,
        d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D) :
    ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
      (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
      dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
      ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
        ‖f.eval z‖
          ≤ 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) * (D / 2) ^ n
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter_monic`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L967)

```lean
theorem sharp_collinear_root_diameter_monic {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) :
    ∃ y : Fin n → ℝ, f = (∏ k, (X - C (base + dir * (y k : ℂ)))) ∧
      ∀ D : ℝ, IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
            ‖f.eval z‖
              ≤ 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n)
                * (D / 2) ^ n
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.exists_collinear_factorisation`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L928)

```lean
theorem exists_collinear_factorisation (base dir : ℂ) :
    ∀ (n : ℕ) (f : ℂ[X]), f.IsMonicOfDegree n →
      (∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) →
      ∃ y : Fin n → ℝ, f = ∏ k : Fin n, (X - C (base + dir * (y k : ℂ)))
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.exists_gap_le_comparisonBound`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L212)

```lean
theorem exists_gap_le_comparisonBound {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1) (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤ comparisonBound (m + 2)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_equality_attained`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L836)

```lean
theorem sharp_collinear_equality_attained {m : ℕ} (base dir : ℂ) (hdir : ‖dir‖ = 1)
    {D : ℝ} (hD : 0 < D) (f : ℂ[X])
    (hf : f = ∏ k : Fin (m + 2), (X - C (base + dir * ((D / 2 * chebNode m k : ℝ) : ℂ)))) :
    IsGreatest {d : ℝ | ∃ j k : Fin (m + 2),
        d = dist (base + dir * ((D / 2 * chebNode m j : ℝ) : ℂ))
                 (base + dir * ((D / 2 * chebNode m k : ℝ) : ℂ))} D ∧
      ∀ i : Fin (m + 1),
        ∃ z ∈ segment ℝ (base + dir * ((D / 2 * chebNode m i.castSucc : ℝ) : ℂ))
                        (base + dir * ((D / 2 * chebNode m i.succ : ℝ) : ℂ)),
          ‖f.eval z‖
            = 1 / (2 ^ ((m + 2) - 1)
                * Real.cos (Real.pi / (2 * ((m + 2 : ℕ) : ℝ))) ^ (m + 2))
              * (D / 2) ^ (m + 2)
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.chebyshev_configuration_attains`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L769)

```lean
theorem chebyshev_configuration_attains {m : ℕ} (base dir : ℂ) (hdir : ‖dir‖ = 1)
    {R : ℝ} (hR : 0 < R) (f : ℂ[X])
    (hf : f = ∏ k : Fin (m + 2), (X - C (base + dir * ((R * chebNode m k : ℝ) : ℂ)))) :
    IsGreatest {d : ℝ | ∃ j k : Fin (m + 2),
        d = dist (base + dir * ((R * chebNode m j : ℝ) : ℂ))
                 (base + dir * ((R * chebNode m k : ℝ) : ℂ))} (2 * R) ∧
      ∀ i : Fin (m + 1),
        ∃ z ∈ segment ℝ (base + dir * ((R * chebNode m i.castSucc : ℝ) : ℂ))
                        (base + dir * ((R * chebNode m i.succ : ℝ) : ℂ)),
          ‖f.eval z‖ = comparisonBound (m + 2) * R ^ (m + 2)
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.monicScaledChebyshev_eq_prod`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L684)

```lean
theorem monicScaledChebyshev_eq_prod (m : ℕ) :
    monicScaledChebyshev (m + 2) = ∏ i : Fin (m + 2), (X - C (chebNode m i))
```

8. [`ErdosProblems.Erdos1041.PaperCompleteR21.collinearDiameterBound_sharpConstant`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L871)

```lean
theorem collinearDiameterBound_sharpConstant {n : ℕ} (hn : 2 ≤ n) :
    CollinearDiameterBound n
      (1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n))
```

9. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharpConstant_le_of_collinearDiameterBound`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L878)

```lean
theorem sharpConstant_le_of_collinearDiameterBound {n : ℕ} (hn : 2 ≤ n) {K : ℝ}
    (hK : CollinearDiameterBound n K) :
    1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) ≤ K
```

<a id="thm-sharp-collinear-diameter-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `sharp_collinear_root_diameter`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L86) (E1041_03, line 86), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L31) (PaperStatementsE.lean, line 31), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `sharp_collinear_root_diameter_monic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L99) (E1041_03, line 99), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L43) (PaperStatementsE.lean, line 43), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `exists_collinear_factorisation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L75) (E1041_03, line 75), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L22) (PaperStatementsE.lean, line 22), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `exists_gap_le_comparisonBound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L141) (E1041_03, line 141), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsS.lean#L31) (PaperStatementsS.lean, line 31), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `sharp_collinear_equality_attained`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L151) (E1041_03, line 151), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsS.lean#L39) (PaperStatementsS.lean, line 39), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `chebyshev_configuration_attains`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L129) (E1041_03, line 129), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsS.lean#L20) (PaperStatementsS.lean, line 20), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `monicScaledChebyshev_eq_prod`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L147) (E1041_03, line 147), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsS.lean#L36) (PaperStatementsS.lean, line 36), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `collinearDiameterBound_sharpConstant`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L70) (E1041_03, line 70), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L18) (PaperStatementsE.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `sharpConstant_le_of_collinearDiameterBound`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L81) (E1041_03, line 81), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L27) (PaperStatementsE.lean, line 27), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-collinear-erdos-1041"></a>

## Corollary 9.3 (collinear Erdős case), page 35

> *If the zero occurrences of a monic polynomial of degree $`n\ge2`$ lie on one line in the open unit disc, two of them are joined by a curve of length strictly below $`2`$ inside $`\{|f|<1\}`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.collinear_erdos_1041`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L515)

```lean
theorem collinear_erdos_1041 {n : ℕ} (hn : 2 ≤ n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (y : Fin n → ℝ) (f : ℂ[X]) (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ))))
    (hdisc : ∀ k : Fin n, ‖base + dir * (y k : ℂ)‖ < 1) :
    ∃ j k : Fin n, j ≠ k ∧
      ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow f.eval 1 2
        (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.collinear_erdos_1041_monic`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L984)

```lean
theorem collinear_erdos_1041_monic {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ))
    (hdisc : ∀ z ∈ f.roots, ‖z‖ < 1) :
    ∃ a b : ℂ, a ∈ f.roots ∧ b ∈ f.roots ∧
      ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow f.eval 1 2 a b
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.exists_collinear_factorisation`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L928)

```lean
theorem exists_collinear_factorisation (base dir : ℂ) :
    ∀ (n : ℕ) (f : ℂ[X]), f.IsMonicOfDegree n →
      (∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) →
      ∃ y : Fin n → ℝ, f = ∏ k : Fin n, (X - C (base + dir * (y k : ℂ)))
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L367)

```lean
theorem sharp_collinear_root_diameter {n : ℕ} (hn : 2 ≤ n)
    (base dir : ℂ) (hdir : ‖dir‖ = 1) (y : Fin n → ℝ) (f : ℂ[X])
    (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ)))) (D : ℝ)
    (hD : IsGreatest {d : ℝ | ∃ j k : Fin n,
        d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D) :
    ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
      (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
      dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
      ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
        ‖f.eval z‖
          ≤ 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) * (D / 2) ^ n
```

<a id="cor-collinear-erdos-1041-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `collinear_erdos_1041`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L181) (E1041_03, line 181), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsT.lean#L21) (PaperStatementsT.lean, line 21), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `collinear_erdos_1041_monic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L189) (E1041_03, line 189), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsT.lean#L28) (PaperStatementsT.lean, line 28), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `exists_collinear_factorisation`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L75) (E1041_03, line 75), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L22) (PaperStatementsE.lean, line 22), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)
- `sharp_collinear_root_diameter`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_03/Challenge.lean#L86) (E1041_03, line 86), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L31) (PaperStatementsE.lean, line 31), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_03.json) (E1041_03)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `collinear_erdos_1041`:

```lean
theorem collinear_erdos_1041 {n : ℕ} (hn : 2 ≤ n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (y : Fin n → ℝ) (f : ℂ[X]) (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ))))
    (hdisc : ∀ k : Fin n, ‖base + dir * (y k : ℂ)‖ < 1) :
    ∃ j k : Fin n, j ≠ k ∧
      ConnectedBelow f.eval 1 2
        (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) := by sorry
```

Challenge for `collinear_erdos_1041_monic`:

```lean
theorem collinear_erdos_1041_monic {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ))
    (hdisc : ∀ z ∈ f.roots, ‖z‖ < 1) :
    ∃ a b : ℂ, a ∈ f.roots ∧ b ∈ f.roots ∧
      ConnectedBelow f.eval 1 2 a b := by sorry
```

<a id="prop-primitive-quintic-two-tail-energy-selector"></a>

## Theorem 9.4 (a consequence of three moment identities), page 36

> *Suppose
> ``` math
> \sum_{i=0}^4x_i=-r,\qquad
>  \sum_{i=0}^4(2x_i^2-s_i)=r^2,\qquad
>  \sum_{i=0}^4(4x_i^3-3s_ix_i)=-r^3.              \tag{10}
> ```
> Then at least one of the ten pairs $`0\le i<j\le4`$ satisfies $`E_i<1`$ and $`E_j<1`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.primitiveInterior_exists_two_tailEnergy_lt_one`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PrimitiveQuinticInteriorTail.lean#L272)

```lean
theorem primitiveInterior_exists_two_tailEnergy_lt_one
    {r : ℝ}
    {x0 x1 x2 x3 x4 s0 s1 s2 s3 s4 : ℝ}
    (hr : 0 < r) (hr2 : r < 2)
    (hs0 : 0 ≤ s0) (hs0one : s0 ≤ 1) (hx0s : x0 ^ 2 ≤ s0)
    (hs1 : 0 ≤ s1) (hs1one : s1 ≤ 1) (hx1s : x1 ^ 2 ≤ s1)
    (hs2 : 0 ≤ s2) (hs2one : s2 ≤ 1) (hx2s : x2 ^ 2 ≤ s2)
    (hs3 : 0 ≤ s3) (hs3one : s3 ≤ 1) (hx3s : x3 ^ 2 ≤ s3)
    (hs4 : 0 ≤ s4) (hs4one : s4 ≤ 1) (hx4s : x4 ^ 2 ≤ s4)
    (hm1 : x0 + x1 + x2 + x3 + x4 = -r)
    (hm2 : (2 * x0 ^ 2 - s0) + (2 * x1 ^ 2 - s1) +
        (2 * x2 ^ 2 - s2) + (2 * x3 ^ 2 - s3) +
        (2 * x4 ^ 2 - s4) = r ^ 2)
    (hm3 : (4 * x0 ^ 3 - 3 * s0 * x0) +
        (4 * x1 ^ 3 - 3 * s1 * x1) +
        (4 * x2 ^ 3 - 3 * s2 * x2) +
        (4 * x3 ^ 3 - 3 * s3 * x3) +
        (4 * x4 ^ 3 - 3 * s4 * x4) = -r ^ 3) :
    (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1)
```

<a id="prop-primitive-quintic-two-tail-energy-selector-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `primitiveInterior_exists_two_tailEnergy_lt_one`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L54) (E1041_04, line 54), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsM.lean#L14) (PaperStatementsM.lean, line 14), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-primitive-quintic-two-tail"></a>

## Theorem 9.5 (a quintic with two missing coefficients), page 36

> *Let
> ``` math
> p(z)=z^5+az^4+bz+c
> ```
> and suppose its five zero occurrences $`w_0,\ldots,w_4`$ lie in the closed unit disc. At least two distinct indices satisfy
> ``` math
> |bw_i+c|\le1.                                    \tag{11}
> ```
> If $`a\ne0`$, two indices can be chosen with strict inequalities. If $`a=0`$, every index satisfies *(11)*, and equality holds exactly when $`|w_i|=1`$.*
>
> *For open-disc zeros, two zero occurrences are joined inside $`\{|p|<1\}`$ by a curve of length below $`2`$: use the two radial spokes through $`0`$ when their values are distinct, and the constant path when the selected occurrences have the same value.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.primitive_quintic_two_tail`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/PrimitiveQuinticClosedDisc.lean#L260)

```lean
theorem primitive_quintic_two_tail (a b c : ℂ) (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z) :
    ((∀ i, ‖w i‖ ≤ 1) →
        (∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ ≤ 1 ∧ ‖b * w j + c‖ ≤ 1) ∧
        (a ≠ 0 → ∃ i j : Fin 5, i ≠ j ∧
          ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1) ∧
        (a = 0 → ∀ i : Fin 5,
          ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1))) ∧
      ((∀ i, ‖w i‖ < 1) →
        ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 ∧
          ConnectedBelow (value a b c) 1 2 (w i) (w j) ∧
          (w i ≠ w j → HubBelow (value a b c) 1 2 (w i) 0 (w j)) ∧
          (w i = w j →
            (∀ t : ℝ, ‖value a b c ((fun _ : ℝ => w i) t)‖ < 1) ∧
            eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0))
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.primitive_quintic_two_tail_of_polynomial`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/PrimitiveQuinticClosedDisc.lean#L313)

```lean
theorem primitive_quintic_two_tail_of_polynomial (p : ℂ[X]) (hp : p.Monic)
    (hd : p.natDegree = 5) (a b c : ℂ)
    (hvalue : ∀ z, p.eval z = value a b c z) :
    ∃ w : Fin 5 → ℂ, (∀ z, p.eval z = rootProduct w z) ∧
      ((∀ i, ‖w i‖ ≤ 1) →
          (∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ ≤ 1 ∧ ‖b * w j + c‖ ≤ 1) ∧
          (a ≠ 0 → ∃ i j : Fin 5, i ≠ j ∧
            ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1) ∧
          (a = 0 → ∀ i : Fin 5,
            ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1))) ∧
        ((∀ i, ‖w i‖ < 1) →
          ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 ∧
            ConnectedBelow (value a b c) 1 2 (w i) (w j) ∧
            (w i ≠ w j → HubBelow (value a b c) 1 2 (w i) 0 (w j)) ∧
            (w i = w j →
              (∀ t : ℝ, ‖value a b c ((fun _ : ℝ => w i) t)‖ < 1) ∧
              eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0))
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.two_tails_closedDisc_of_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/PrimitiveQuinticClosedDisc.lean#L93)

```lean
theorem two_tails_closedDisc_of_ne_zero {a b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z)
    (hw : ∀ i, ‖w i‖ ≤ 1) (ha : a ≠ 0) :
    ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.tail_le_one_and_eq_iff_of_leading_zero`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/PrimitiveQuinticClosedDisc.lean#L199)

```lean
theorem tail_le_one_and_eq_iff_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (hw : ∀ i, ‖w i‖ ≤ 1)
    (i : Fin 5) :
    ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.tail_norm_of_leading_zero`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/PrimitiveQuinticClosedDisc.lean#L82)

```lean
theorem tail_norm_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (i : Fin 5) :
    ‖b * w i + c‖ = ‖w i‖ ^ 5
```

6. [`ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.complete_primitive_quintic`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperPrimitiveCompletionR10.lean#L237)

```lean
theorem complete_primitive_quintic (p : ℂ[X]) (hp : p.Monic)
    (hd : p.natDegree = 5) (a b c : ℂ)
    (hvalue : ∀ z, p.eval z = value a b c z)
    (hdisk : ∀ z, p.eval z = 0 → ‖z‖ < 1) :
    ∃ w : Fin 5 → ℂ, (∀ z, p.eval z = rootProduct w z) ∧
      ∃ i j : Fin 5, i ≠ j ∧ ‖b*w i+c‖ < 1 ∧ ‖b*w j+c‖ < 1 ∧
        ConnectedBelow p.eval 1 2 (w i) (w j) ∧
        (w i ≠ w j → HubBelow p.eval 1 2 (w i) 0 (w j)) ∧
        (w i = w j →
          (∀ t : ℝ, ‖p.eval ((fun _ : ℝ => w i) t)‖ < 1) ∧
          eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0)
```

<a id="thm-primitive-quintic-two-tail-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `primitive_quintic_two_tail`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L117) (E1041_04, line 117), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsU.lean#L24) (PaperStatementsU.lean, line 24), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)
- `primitive_quintic_two_tail_of_polynomial`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L134) (E1041_04, line 134), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsU.lean#L40) (PaperStatementsU.lean, line 40), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)
- `two_tails_closedDisc_of_ne_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L171) (E1041_04, line 171), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsV.lean#L30) (PaperStatementsV.lean, line 30), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)
- `tail_le_one_and_eq_iff_of_leading_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L160) (E1041_04, line 160), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsV.lean#L21) (PaperStatementsV.lean, line 21), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)
- `tail_norm_of_leading_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L166) (E1041_04, line 166), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsV.lean#L26) (PaperStatementsV.lean, line 26), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)
- `complete_primitive_quintic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_05/Challenge.lean#L138) (E1041_05, line 138), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_05/PaperStatementsU.lean#L58) (PaperStatementsU.lean, line 58), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_05.json) (E1041_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-cubic-safe-root-spoke"></a>

## Theorem 9.6 (a contained radial segment for a cubic), page 38

> *If $`r,s,v\in\mathbb C`$ have modulus below one, at least one $`u\in\{r,s,v\}`$ satisfies
> ``` math
> \left|(tu-r)(tu-s)(tu-v)\right|\le1
>  \qquad(0\le t\le1).
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.cubic_has_safe_root_spoke`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/CubicQuotientFiberCase.lean#L161)

```lean
theorem cubic_has_safe_root_spoke {r s v : ℂ}
    (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) (hv : ‖v‖ < 1) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * r - r) * ((t : ℂ) * r - s) * ((t : ℂ) * r - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * s - s) * ((t : ℂ) * s - r) * ((t : ℂ) * s - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * v - v) * ((t : ℂ) * v - r) * ((t : ℂ) * v - s)‖ ≤ 1)
```

<a id="lem-cubic-safe-root-spoke-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `cubic_has_safe_root_spoke`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L181) (E1041_04, line 181), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsJ.lean#L16) (PaperStatementsJ.lean, line 16), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-translated-cubic-quotient-fibres"></a>

## Theorem 9.7 (a cubic composed with a power map), page 38

> *Let $`q\ge2`$, $`h\in\mathbb C`$, $`P`$ be monic cubic, and
> ``` math
> f(z)=P((z-h)^q).
> ```
> If every zero of $`f`$ lies in the open unit disc and $`f`$ has at least two distinct zero values, then two zeros are joined through $`h`$ by a two-segment path of length below $`2`$ inside $`\{|f|<1\}`$. Equivalently, under the same hypotheses the conclusion holds for polynomials of the form
> ``` math
> (z-h)^{3q}+A(z-h)^{2q}+B(z-h)^q+C
> ```
> in every degree $`3q\ge6`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperCubicFibres.complete_translated_cubic_quotient_fibres`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCubicFibres.lean#L240)

```lean
theorem complete_translated_cubic_quotient_fibres
    {q : ℕ} (hq : 2 ≤ q) (h : ℂ) (P : ℂ[X])
    (hP : P.Monic) (hdeg : P.natDegree = 3)
    (hdisk : ∀ z : ℂ, P.eval ((z - h) ^ q) = 0 → ‖z‖ < 1)
    (htwo : ∃ a b : ℂ, a ≠ b ∧
      P.eval ((a - h) ^ q) = 0 ∧ P.eval ((b - h) ^ q) = 0) :
    ∃ a b : ℂ, a ≠ b ∧ P.eval ((a - h) ^ q) = 0 ∧
      P.eval ((b - h) ^ q) = 0 ∧
      HubBelow (fun z => P.eval ((z - h) ^ q)) 1 2 a h b
```

<a id="thm-translated-cubic-quotient-fibres-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `complete_translated_cubic_quotient_fibres`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_02/Challenge.lean#L212) (E1041_02, line 212), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_02/CubicPath.lean#L54) (CubicPath.lean, line 54), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_02.json) (E1041_02)

Challenge for `complete_translated_cubic_quotient_fibres`:

```lean
theorem complete_translated_cubic_quotient_fibres
    {q : ℕ} (hq : 2 ≤ q) (h : ℂ) (P : ℂ[X])
    (hP : P.Monic) (hdeg : P.natDegree = 3)
    (hdisk : ∀ z : ℂ, P.eval ((z - h) ^ q) = 0 → ‖z‖ < 1)
    (htwo : ∃ a b : ℂ, a ≠ b ∧
      P.eval ((a - h) ^ q) = 0 ∧ P.eval ((b - h) ^ q) = 0) :
    ∃ a b : ℂ, a ≠ b ∧ P.eval ((a - h) ^ q) = 0 ∧
      P.eval ((b - h) ^ q) = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 2, ‖P.eval ((hub a h b t - h) ^ q)‖ < 1) ∧
      eVariationOn (hub a h b) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2 := by sorry
```

<a id="res-complementary-binomial-chords"></a>

## Theorem 10.1 (complementary binomial chords), page 41

> *Two adjacent zeros of $`z^n-a`$ can be joined by an explicit polygonal path inside $`\{|z^n-a|<1\}`$ of length strictly below $`2`$. For $`r<r_*`$ the adjacent-root chord itself works. For $`r\ge r_*`$, two radial legs and an inner adjacent crossing chord work after an arbitrarily small radial contraction. These two constructions meet at $`r=r_*`$, where the outer chord attains $`|f|=1`$ at its midpoint and therefore lies only in the closed lemniscate. Open containment at and above the switch uses the inner chord after a radial contraction.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_path`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1084)

```lean
theorem binomial_chords_path {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((r : ℝ) : ℂ) ≠ ((r : ℝ) : ℂ) * chordOmega n ∧
      (((r : ℝ) : ℂ)) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      (((r : ℝ) : ℂ) * chordOmega n) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
        ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_below_threshold`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1094)

```lean
theorem binomial_chords_below_threshold {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hlt : r < chordThreshold n) :
    PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n)
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_above_threshold`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1104)

```lean
theorem binomial_chords_above_threshold {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hge : chordThreshold n ≤ r) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n)
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_at_threshold`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1118)

```lean
theorem binomial_chords_at_threshold {n : ℕ} (hn : 2 ≤ n) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(chordPoint n (chordThreshold n) u) ^ n
          - ((chordThreshold n : ℝ) : ℂ) ^ n‖ ≤ 1) ∧
      ‖(chordPoint n (chordThreshold n) (1 / 2)) ^ n
        - ((chordThreshold n : ℝ) : ℂ) ^ n‖ = 1
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chord_maximum`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1129)

```lean
theorem binomial_chord_maximum {n : ℕ} (hn : 2 ≤ n) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(chordPoint n s u) ^ n - ((r : ℝ) : ℂ) ^ n‖ ≤ r ^ n + (s * chordCos n) ^ n) ∧
      ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = r ^ n + (s * chordCos n) ^ n
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chord_decisive_step`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1138)

```lean
theorem binomial_chord_decisive_step {n : ℕ} (hn : 2 ≤ n) {θ : ℝ}
    (hθ : (n : ℝ) * |θ| ≤ Real.pi) :
    1 + Real.cos ((n : ℝ) * θ) ≤ 2 * Real.cos θ ^ n
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_inner_chord_maximal`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1145)

```lean
theorem binomial_inner_chord_maximal {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ^ n < 1) (hswitch : 1 ≤ r ^ n * (1 + chordCos n ^ n)) :
    ‖(chordPoint n (innerRadius n r) (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = 1 ∧
      (∀ s : ℝ, innerRadius n r < s → s ≤ r →
        1 < ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖)
```

<a id="res-complementary-binomial-chords-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `binomial_chords_path`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L97) (E1041_06, line 97), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsD.lean#L46) (PaperStatementsD.lean, line 46), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `binomial_chords_below_threshold`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L91) (E1041_06, line 91), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsD.lean#L41) (PaperStatementsD.lean, line 41), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `binomial_chords_above_threshold`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L77) (E1041_06, line 77), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsD.lean#L29) (PaperStatementsD.lean, line 29), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `binomial_chords_at_threshold`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L83) (E1041_06, line 83), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsD.lean#L34) (PaperStatementsD.lean, line 34), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `binomial_chord_maximum`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L71) (E1041_06, line 71), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsD.lean#L24) (PaperStatementsD.lean, line 24), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `binomial_chord_decisive_step`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L66) (E1041_06, line 66), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsD.lean#L19) (PaperStatementsD.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `binomial_inner_chord_maximal`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L105) (E1041_06, line 105), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsD.lean#L53) (PaperStatementsD.lean, line 53), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `binomial_chords_path`:

```lean
theorem binomial_chords_path {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((r : ℝ) : ℂ) ≠ ((r : ℝ) : ℂ) * chordOmega n ∧
      (((r : ℝ) : ℂ)) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      (((r : ℝ) : ℂ) * chordOmega n) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
        ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by sorry
```

Challenge for `binomial_chords_below_threshold`:

```lean
theorem binomial_chords_below_threshold {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hlt : r < chordThreshold n) :
    ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by sorry
```

Challenge for `binomial_chords_above_threshold`:

```lean
theorem binomial_chords_above_threshold {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hge : chordThreshold n ≤ r) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by sorry
```

<a id="res-critical-value-budget"></a>

## Theorem 10.2 (a mean bound for critical values), page 48

> *Let $`f`$ be monic of degree $`n\ge2`$, with roots in a closed disc of radius $`R\ge0`$. If $`c_1,\ldots,c_{n-1}`$ are its critical points counted with multiplicity, then
> ``` math
> \begin{equation}
> \label{eq:critical-value-quadratic-budget}
>  \sum_{j=1}^{n-1}|f(c_j)|^{2/(n-1)}
>  \le(n-1)R^{2n/(n-1)}.
> \end{equation}
> ```
> Consequently the lower exponents used elsewhere in the record satisfy
> ``` math
> \begin{equation}
> \label{eq:critical-value-power-budget}
>  \sum_{j=1}^{n-1}|f(c_j)|^{1/(n-1)}
>  \le(n-1)R^{n/(n-1)}
> \end{equation}
> ```
> and
> ``` math
> \sum_{j=1}^{n-1}|f(c_j)|^{1/n}\le(n-1)R.
> ```
> The constant is attained by $`f(z)=(z-\tau)^n-\lambda`$ with enclosing disk centred at $`\tau`$ and radius $`R=|\lambda|^{1/n}`$.*

The Lean declarations below together state this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one. `paper_critical_value_mean` states the quadratic budget and the $1/n$ consequence, the statement absorbed from the short paper's former res:fp-to-s.

1. [`ErdosProblems.Erdos1041.PaperCompleteR20.critical_value_three_budgets`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/CriticalMeanWhole.lean#L14)

```lean
theorem critical_value_three_budgets {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.Monic) (hdeg : f.natDegree = n) (h : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc f h R) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration f c) :
    (∑ j, ‖f.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
      ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ j, ‖f.eval (c j)‖ ^ (1 / ((n : ℝ) - 1))) ≤
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ j, ‖f.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR20.critical_value_three_budgets_sharp`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/CriticalMeanWhole.lean#L36)

```lean
theorem critical_value_three_budgets_sharp (n : ℕ) (hn : 2 ≤ n) (h lam : ℂ) :
    let R := ‖lam‖ ^ (1 / (n : ℝ))
    let f := radialEqualityPolynomial n h lam
    f.Monic ∧ f.natDegree = n ∧ RootsInClosedDisc f h R ∧
    CriticalEnumeration f (fun _ : Fin (n - 1) => h) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (2 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (1 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (1 / (n : ℝ))) = ((n : ℝ) - 1) * R
```

3. [`ErdosProblems.Erdos1041.paper_critical_value_mean`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCriticalValueMeanR10.lean#L101)

```lean
theorem paper_critical_value_mean : PaperAnalyticTargets.CriticalValueMean
```

where [`CriticalValueMean`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L102) is

```lean
def CriticalValueMean : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ) (h : ℂ) (R : ℝ),
    2 ≤ n → p.Monic → p.natDegree = n → 0 ≤ R →
    RootsInClosedDisc p h R → CriticalEnumeration p c →
      (∑ j, ‖p.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
        ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
      (∑ j, ‖p.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R
```

<a id="res-critical-value-budget-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `critical_value_three_budgets`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L199) (E1041_04, line 199), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsO.lean#L21) (PaperStatementsO.lean, line 21), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)
- `critical_value_three_budgets_sharp`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L221) (E1041_04, line 221), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsP.lean#L23) (PaperStatementsP.lean, line 23), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)
- `paper_critical_value_mean`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L163) (E1041_06, line 163), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/CriticalValueMean.lean#L15) (CriticalValueMean.lean, line 15), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `paper_critical_value_mean`:

```lean
theorem paper_critical_value_mean (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ) (h : ℂ) (R : ℝ)
    (hn : 2 ≤ n) (hp : p.Monic) (hdeg : p.natDegree = n) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc p h R) (hc : CriticalEnumeration p c) :
    (∑ j, ‖p.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
        ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
      (∑ j, ‖p.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R := by sorry
```

<a id="res-reflected-critical-value"></a>

## Lemma 10.3 (reflected-derivative bound), page 49

> *If $`f`$ is monic of degree $`n\ge2`$ with roots in the closed unit disk, and $`c_1,\ldots,c_{n-1}`$ list its critical points with multiplicity, then
> ``` math
> \begin{equation}
> \label{eq:critical-reflected-product}
>  |f(c_j)|\le\prod_{k=1}^{n-1}|1-\overline{c_j}c_k|.
> \end{equation}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperReflectedCompletion.reflected_critical_value`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperReflectedCompletion.lean#L254)

```lean
theorem reflected_critical_value : ReflectedCriticalValue
```

where [`ReflectedCriticalValue`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L95) is

```lean
def ReflectedCriticalValue : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ), 2 ≤ n → p.Monic →
    p.natDegree = n → RootsInClosedDisc p 0 1 → CriticalEnumeration p c →
      ∀ j, ‖p.eval (c j)‖ ≤ ∏ k, ‖1 - conj (c k) * c j‖
```

<a id="res-reflected-critical-value-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `reflected_critical_value`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L250) (E1041_04, line 250), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsW.lean#L25) (PaperStatementsW.lean, line 25), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-fp-weighted-all-degree"></a>

## Theorem 10.4 (a weighted inequality for points in a disc), page 50

> *Let $`c_1,\ldots,c_m\in\overline{\mathbb D}`$ and let $`w_j>0`$ satisfy $`\sum_j w_j=1`$. Set
> ``` math
> G(z)=\prod_k |1-\overline{c_k}z|^{w_k}.
> ```
> Then
> ``` math
> \sum_j w_j G(c_j)^2\le 1,
> ```
> with equality if and only if every $`c_j=0`$. Equal weights therefore give $`\sum_j(\prod_k|1-\overline{c_k}c_j|)^{1/m}\le m`$ for every $`m`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1041.paper_weighted_free_point`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperWeightedRefinementsR10.lean#L17)

```lean
theorem paper_weighted_free_point : PaperAnalyticTargets.WeightedFreePoint
```

where [`WeightedFreePoint`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L87) is

```lean
def WeightedFreePoint : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (w : Fin m → ℝ),
    (∀ j, ‖c j‖ ≤ 1) → (∀ j, 0 < w j) → (∑ j, w j) = 1 →
      (∑ j, w j * weightedProduct c w (c j) ^ 2) ≤ 1 ∧
      ((∑ j, w j * weightedProduct c w (c j) ^ 2) = 1 ↔ ∀ j, c j = 0)
```

2. [`ErdosProblems.Erdos1041.geometric_row_mean_closed_disc_le`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperWeightedRefinementsR10.lean#L155)

```lean
theorem geometric_row_mean_closed_disc_le {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, (∏ k, ‖1 - conj (c j) * c k‖) ^ ((m : ℝ)⁻¹)) ≤ (m : ℝ)
```

<a id="res-fp-weighted-all-degree-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_weighted_free_point`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L130) (E1041_06, line 130), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsAB.lean#L22) (PaperStatementsAB.lean, line 22), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `geometric_row_mean_closed_disc_le`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L140) (E1041_06, line 140), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsL.lean#L19) (PaperStatementsL.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)

Each Challenge states the same proposition as the Lean declaration it targets except where shown below, with every definition it uses restated from Mathlib alone.

Challenge for `paper_weighted_free_point`:

```lean
theorem paper_weighted_free_point : WeightedFreePoint := by sorry
```

<a id="res-critical-proximity"></a>

## Theorem 10.5 (a geometric-mean bound for distances to a critical point), page 55

> *Let $`n\ge2`$, let $`z_1,\ldots,z_n,c\in\mathbb C`$ with $`c\ne z_k`$ for every $`k`$, and suppose
> ``` math
> \sum_{k=1}^n\frac1{c-z_k}=0.
> ```
> If $`r>0`$ is determined by
> ``` math
> r^n=\prod_{k=1}^n|c-z_k|,
> ```
> then there are distinct indices $`i,j`$ such that
> ``` math
> |c-z_i|+|c-z_j|\le2r.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.exists_two_roots_dist_sum_le_two_mul_geomMean`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean#L291)

```lean
theorem exists_two_roots_dist_sum_le_two_mul_geomMean
    {n : ℕ} (hn : 2 ≤ n) (z : Fin n → ℂ) (c : ℂ)
    (hne : ∀ k, c - z k ≠ 0)
    (hcrit : ∑ k, (c - z k)⁻¹ = 0)
    {r : ℝ} (hr : 0 < r) (hrn : r ^ n = ∏ k, ‖c - z k‖) :
    ∃ i j : Fin n, i ≠ j ∧ ‖c - z i‖ + ‖c - z j‖ ≤ 2 * r
```

<a id="res-critical-proximity-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `exists_two_roots_dist_sum_le_two_mul_geomMean`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_05/Challenge.lean#L67) (E1041_05, line 67), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_05/PaperStatementsK.lean#L16) (PaperStatementsK.lean, line 16), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_05.json) (E1041_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-two-nearest-roots"></a>

## Corollary 10.6 (two nearest roots), page 56

> *If the roots lie in the open unit disc and $`c`$ is a non-root critical point, the two nearest roots to $`c`$ have total distance strictly below $`2`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1041.PaperCompleteR20.two_nearest_roots_of_polynomial_critical`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/TwoNearestPolynomial.lean#L9)

```lean
theorem two_nearest_roots_of_polynomial_critical {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (c : ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (hp : (∏ k : Fin n, (X - C (z k))).eval c ≠ 0)
    (hcrit : (∏ k : Fin n, (X - C (z k))).derivative.eval c = 0)
    (i j : Fin n) (hij : i ≠ j)
    (hi : ∀ k, ‖c - z i‖ ≤ ‖c - z k‖)
    (hj : ∀ k, k ≠ i → ‖c - z j‖ ≤ ‖c - z k‖) :
    ‖c - z i‖ + ‖c - z j‖ < 2
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR20.exists_two_nearest_roots_of_polynomial_critical`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/TwoNearestPolynomial.lean#L31)

```lean
theorem exists_two_nearest_roots_of_polynomial_critical {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ) (c : ℂ) (hz : ∀ k, ‖z k‖ < 1)
    (hp : (∏ k : Fin n, (X - C (z k))).eval c ≠ 0)
    (hcrit : (∏ k : Fin n, (X - C (z k))).derivative.eval c = 0) :
    ∃ i j : Fin n, i ≠ j ∧
      (∀ k, ‖c - z i‖ ≤ ‖c - z k‖) ∧
      (∀ k, k ≠ i → ‖c - z j‖ ≤ ‖c - z k‖) ∧
      ‖c - z i‖ + ‖c - z j‖ < 2
```

<a id="res-two-nearest-roots-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `two_nearest_roots_of_polynomial_critical`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_05/Challenge.lean#L91) (E1041_05, line 91), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_05/PaperStatementsB.lean#L27) (PaperStatementsB.lean, line 27), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_05.json) (E1041_05)
- `exists_two_nearest_roots_of_polynomial_critical`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_05/Challenge.lean#L81) (E1041_05, line 81), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_05/PaperStatementsB.lean#L18) (PaperStatementsB.lean, line 18), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_05.json) (E1041_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-straight-no-go"></a>

## Proposition 10.7 (two counterexamples to straight-path assertions), page 57

> *There is a monic quintic with all roots in the open unit disc and a non-root critical point $`c`$ whose unique nearest root has a point on the straight segment to $`c`$ outside $`\{|f|<1\}`$. There is also a monic cubic with all roots in the open unit disc such that the midpoint of every pair of distinct roots lies outside $`\{|f|<1\}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperStraightObstructions.complete_straight_path_obstructions`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperStraightObstructions.lean#L178)

```lean
theorem complete_straight_path_obstructions :
    (∃ f : ℂ[X], f.Monic ∧ f.natDegree = 5 ∧
      (∀ z : ℂ, f.eval z = 0 → ‖z‖ < 1) ∧
      ∃ c w : ℂ, f.derivative.eval c = 0 ∧ f.eval c ≠ 0 ∧ f.eval w = 0 ∧
        (∀ z : ℂ, f.eval z = 0 → z ≠ w → ‖c - w‖ < ‖c - z‖) ∧
        ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 1 < ‖f.eval (c + (t : ℂ) * (w - c))‖) ∧
    (∃ g : ℂ[X], g.Monic ∧ g.natDegree = 3 ∧
      (∀ z : ℂ, g.eval z = 0 → ‖z‖ < 1) ∧
      ∀ z w : ℂ, g.eval z = 0 → g.eval w = 0 → z ≠ w →
        1 < ‖g.eval ((z + w) / 2)‖)
```

<a id="res-straight-no-go-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `complete_straight_path_obstructions`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_05/Challenge.lean#L105) (E1041_05, line 105), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_05/PaperStatementsG.lean#L16) (PaperStatementsG.lean, line 16), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_05.json) (E1041_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-orlicz-currency"></a>

## Theorem 10.8 (the relation between two merger-scale integrals), page 64

> *Define
> ``` math
> \Phi(x)=\int_0^x\frac{dt}{\log(\coth t)}\qquad(x\ge0).
> ```
> At $`t=0`$ the integrand is understood by its continuous limiting value $`0`$ (equivalently, the integral is improper at that endpoint). For every integer $`k\ge1`$ and $`0<r\le1`$, with $`x=k^{-1}\log(1/r)`$,
> ``` math
> I_k(r)=k\Phi(x).                                      \tag{O1}
> ```
> The function $`\Phi`$ is increasing and strictly convex on $`(0,\infty)`$, and
> ``` math
> \frac{\Phi(x)}x\longrightarrow0\qquad(x\downarrow0). \tag{O2}
> ```
> Consequently, for every fixed $`k\ge1`$ and every $`c>0`$, some $`0<r<1`$ satisfies
> ``` math
> I_k(r)<c\,\frac1k\log\frac1r.                        \tag{O3}
> ```
> In particular, no positive universal constant bounds $`I_k(r)`$ below by that constant times $`k^{-1}\log(1/r)`$.*

The Lean declarations below together state this result or one that implies it. The Lean statements prove $\Phi$ strictly increasing on $[0,\infty)$, which contains the printed monotonicity on $(0,\infty)$, and the integrand $1/\log(\coth t)$ continuous on $\mathbb R$ with value $0$ at $t=0$, which is the printed convention. The identity (O1), strict convexity on $(0,\infty)$, (O2), (O3) and the absence of a universal constant are stated as printed.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.orlicz_currency`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L374)

```lean
theorem orlicz_currency :
    (Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0) ∧ orliczKernel 0 = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ r : ℝ, 0 < r → r ≤ 1 →
        mergerIntegral k r = k * Phi (Real.log (1 / r) / k)) ∧
      StrictMonoOn Phi (Ioi (0 : ℝ)) ∧
      MonotoneOn Phi (Ioi (0 : ℝ)) ∧
      StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi ∧
      Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ c : ℝ, 0 < c → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        mergerIntegral k r < c * (Real.log (1 / r) / k)) ∧
      ¬ ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ r : ℝ, 0 < r → r < 1 →
        c * (Real.log (1 / r) / k) ≤ mergerIntegral k r
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_continuous`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L115)

```lean
theorem orliczKernel_continuous : Continuous orliczKernel
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L163)

```lean
theorem orliczKernel_tendsto_zero : Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0)
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.mergerIntegral_eq_mul_phi`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L278)

```lean
theorem mergerIntegral_eq_mul_phi {k : ℕ} (hk : 1 ≤ k) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    mergerIntegral k r = k * Phi (Real.log (1 / r) / k)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictMonoOn`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L196)

```lean
theorem phi_strictMonoOn : StrictMonoOn Phi (Ici (0 : ℝ))
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictConvexOn`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L203)

```lean
theorem phi_strictConvexOn : StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.phi_div_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L209)

```lean
theorem phi_div_tendsto_zero :
    Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0)
```

8. [`ErdosProblems.Erdos1041.PaperCompleteR21.exists_mergerIntegral_lt`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L341)

```lean
theorem exists_mergerIntegral_lt {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ mergerIntegral k r < c * (Real.log (1 / r) / k)
```

<a id="res-orlicz-currency-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `orlicz_currency`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L203) (E1041_06, line 203), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsF.lean#L30) (PaperStatementsF.lean, line 30), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `orliczKernel_continuous`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L197) (E1041_06, line 197), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsF.lean#L26) (PaperStatementsF.lean, line 26), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `orliczKernel_tendsto_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L200) (E1041_06, line 200), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsF.lean#L28) (PaperStatementsF.lean, line 28), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `mergerIntegral_eq_mul_phi`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L192) (E1041_06, line 192), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsF.lean#L22) (PaperStatementsF.lean, line 22), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `phi_strictMonoOn`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L224) (E1041_06, line 224), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsF.lean#L48) (PaperStatementsF.lean, line 48), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `phi_strictConvexOn`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L221) (E1041_06, line 221), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsF.lean#L46) (PaperStatementsF.lean, line 46), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `phi_div_tendsto_zero`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L217) (E1041_06, line 217), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsF.lean#L43) (PaperStatementsF.lean, line 43), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)
- `exists_mergerIntegral_lt`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L188) (E1041_06, line 188), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/PaperStatementsF.lean#L19) (PaperStatementsF.lean, line 19), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-value"></a>

## Theorem 11.1 (value equation), page 65

> *For a polynomial $`f`$ and a differentiable curve $`z:I\to\mathbb C`$ on an interval $`I`$, assume $`f'(z(t))\ne0`$ and $`z'(t)=-f(z(t))/f'(z(t))`$ throughout $`I`$. Then $`w=f\circ z`$ satisfies $`w'=-w`$, and
> ``` math
> f(z(t))=e^{-(t-t_0)}f(z(t_0))\qquad(t,t_0\in I).
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement allows any function $f$ with a complex derivative at each point $z(t)$, $t\in I$, of which a polynomial is a case; its conclusions are $w'=-w$ on $I$ and $f(z(t))=e^{-(t-t_0)}f(z(t_0))$ for $t,t_0\in I$.

[`ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_value_whole`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/NewtonRealTime.lean#L52)

```lean
theorem newton_real_value_whole
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {I : Set ℝ} (hI : OrdConnected I)
    (hf : ∀ t ∈ I, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ I,
      HasDerivWithinAt z (newtonFlowVector (f (z t)) (f' (z t))) I t)
    (hc : ∀ t ∈ I, f' (z t) ≠ 0) :
    (∀ t ∈ I, HasDerivWithinAt (fun s => f (z s)) (-f (z t)) I t) ∧
    (∀ t ∈ I, ∀ t₀ ∈ I,
      f (z t) = (Real.exp (-(t - t₀)) : ℂ) * f (z t₀))
```

<a id="res-value-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `newton_real_value_whole`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L275) (E1041_04, line 275), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsQ.lean#L40) (PaperStatementsQ.lean, line 40), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-ray"></a>

## Corollary 11.2 (ray separation), page 66

> *Let $`a<b`$ and let the value trajectory $`t\mapsto f(z(t))`$ be continuous on $`[a,b]`$. Assume the Newton equation and $`f'(z(t))\ne0`$ on $`(a,b)`$ only. Then
> ``` math
> f(z(b))=e^{a-b}f(z(a)).
> ```
> If these endpoint values are nonzero, they lie on one positive ray. Therefore critical points with values on distinct positive rays cannot be endpoints of such a finite connection. The trajectory in the $`z`$ plane need not be radial.*

The Lean declaration below states this result or one that implies it. The Lean statement allows any function $f$ with a complex derivative at each $z(t)$, $a<t<b$, of which a polynomial is a case. It gives $f(z(b))=e^{a-b}f(z(a))$ and that the two endpoint values lie on one positive ray, which excludes endpoints whose values lie on distinct positive rays.

[`ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_endpoint_whole`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/PaperCompleteR20/NewtonRealTime.lean#L69)

```lean
theorem newton_real_endpoint_whole
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn (fun t => f (z t)) (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ Ioo a b,
      HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hc : ∀ t ∈ Ioo a b, f' (z t) ≠ 0) :
    f (z b) = (Real.exp (a - b) : ℂ) * f (z a) ∧
      SamePositiveRay (f (z a)) (f (z b))
```

<a id="res-ray-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `newton_real_endpoint_whole`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L264) (E1041_04, line 264), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsQ.lean#L30) (PaperStatementsQ.lean, line 30), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-locus"></a>

## Theorem 12.1 (ray-collision locus), page 67

> *Let $`a\ne b`$ be complex. Every common translation $`\beta`$ for which $`a+\beta`$ and $`b+\beta`$ lie on the same positive ray has the form
> ``` math
> \beta=\frac{ra-b}{1-r},
>   \qquad r\in\mathbb{R}_{>0},\ r\ne1 .
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.translated_samePositiveRay_parameterization`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L107)

```lean
theorem translated_samePositiveRay_parameterization
    {a b shift : ℂ} (hab : a ≠ b)
    (hray : SamePositiveRay (a + shift) (b + shift)) :
    ∃ r : ℝ, 0 < r ∧ r ≠ 1 ∧
      shift = ((r : ℂ) * a - b) / ((1 - r : ℝ) : ℂ)
```

<a id="res-locus-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `translated_samePositiveRay_parameterization`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_04/Challenge.lean#L294) (E1041_04, line 294), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_04/PaperStatementsN.lean#L20) (PaperStatementsN.lean, line 20), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_04.json) (E1041_04)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-attachment-aware-reeb"></a>

## Passage (beginning “res:attachment-aware-reeb…”), page 70

**No Lean proof of the whole statement.** In Lean, Component-local surjectivity, finite fibres, covering and unique continuous root-labelled branches on a finite outward-slit domain are checked in OutwardSlitDomain at public commit 8bf96bdcae6b9201c670fff3037c49c70ec6de8d, alongside ray-disjointness, level-separation and saddle-scale prerequisites. The complete theorem still lacks a Lean proof of component sheet count, conformality, Morse, monodromy and embedded-tree assertions; prerequisite checking does not establish the complete theorem..
