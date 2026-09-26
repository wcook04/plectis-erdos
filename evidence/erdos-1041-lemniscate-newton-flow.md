# Formal evidence: Paths in Polynomial Lemniscates:\\A Degree-Seven Counterexample\\and Two Short-Path Criteria

This record belongs to the paper [erdos-1041-lemniscate-newton-flow.pdf](../paper/1041/erdos-1041-lemniscate-newton-flow.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`4d41eaab40de`](https://github.com/wcook04/plectis-erdos/tree/4d41eaab40de87460b9049d84455ef18660b858e) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 25 results: 18 with a Lean proof of the whole statement, 6 whose Lean proof assumes a named input (marked with a dagger), 1 without a Lean proof of the whole statement; 17 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="res-ani-degree-seven-counterexample"></a>

## Passage (beginning “The degree-seven polynomial constructed by…”), page 2

The Lean declarations below together state this result or one that implies it. The polynomial is monic of degree seven with distinct roots in the open unit disc, and every continuous root-to-root path in $\{|f|<1\}$ has length greater than $2$ (`erdos1041_counterexample`). The Hausdorff bound holds for every preconnected subset of $\{|f|<1\}$ containing two distinct roots (`erdos1041_counterexample_hausdorff`), so it covers the image of every continuous root-to-root path, which is connected. The negation and `answer(False)` forms of the Formal Conjectures statement are `erdos1041_hausdorff_negation` and `erdos1041_hausdorff_answer_false`.

1. [`Erdos1041.Counterexample.erdos1041_counterexample`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/Counterexample/Assembly.lean#L319)

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

2. [`Erdos1041.Counterexample.erdos1041_counterexample_hausdorff`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L283)

```lean
theorem erdos1041_counterexample_hausdorff :
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K → K ⊆ Omega f →
        (2 : ℝ≥0∞) < μH[1] K
```

3. [`Erdos1041.Counterexample.erdos1041_hausdorff_negation`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L407)

```lean
theorem erdos1041_hausdorff_negation :
    ¬ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2
```

4. [`Erdos1041.Counterexample.erdos1041_hausdorff_answer_false`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L449)

```lean
theorem erdos1041_hausdorff_answer_false :
    False ↔ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2
```

<a id="res-ani-degree-seven-counterexample-comparator"></a>

**Comparator:** not yet compared.

<a id="res-trinomial-all-degree"></a>

## Theorem 2.1 (all-degree monic trinomials), page 2

> *Let $`1\le m<n`$ and
> ``` math
> f(z)=z^n+az^m+b,
> ```
> with every zero in the open unit disc. For any zero $`\zeta`$, the entire segment $`[0,\zeta]`$ lies in $`\{|f|<1\}`$. Distinct zeros $`\zeta_1,\zeta_2`$ are therefore joined by the broken line $`\zeta_1\to0\to\zeta_2`$ of length $`\|\zeta_1\|+\|\zeta_2\|<2`$ inside the open unit lemniscate.*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos1041.PaperTrinomialWholeR21.all_degree_monic_trinomials_whole`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperTrinomialWholeR21.lean#L23)

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

## Proposition 2.2 (failure of a prescribed radial segment), page 3

> *There exist $`r\in(0,1)`$ for which every zero of
> ``` math
> f_r(z)=z^6+\tfrac15 r^2 z^4-\tfrac15 r^4 z^2-r^6
> ```
> lies in the open unit disc, yet the radial spoke from the origin to the zero $`r`$ leaves $`\{|f_r|<1\}`$.*

The Lean declaration below states this result or one that implies it. The Lean statement finds a point $tr$ of the spoke, $0<t<1$, with $|f_r(tr)|>1$, so the spoke leaves even the closed set $\{|f_r|\le1\}$; the printed statement needs only a point with $|f_r|\ge1$.

[`ErdosProblems.Erdos1041.PaperCompleteR20.sextic_spoke_counterexample_whole`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR20/SexticSpokeWhole.lean#L9)

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

## Theorem 3.1 (a small critical value), page 4

> *Let $`f`$ be squarefree and monic of degree $`n\ge2`$, and let $`\mu`$ be its least critical-value modulus. If $`\mu\le13/25`$, then two distinct roots are joined inside $`\{|f|<1\}`$ by a rectifiable curve of length strictly less than $`2`$.*

**No Lean proof of the whole statement.** In Lean, the degree-two case and the closing inequality $(13/25)e^X<1$ at the recorded stopping time $X=635762889599/10^{12}$ are checked; the computation that certifies $X$ and the analytic argument in higher degrees are not.

<a id="res-scaled-low-critical"></a>

## Corollary 3.2 (scale-free connection), page 4

> *Every squarefree monic polynomial of degree $`n\ge2`$ has two distinct roots joined in $`\{|f|<(25/13)\mu\}`$ by a curve of length less than
> ``` math
> 2\bigl((25/13)\mu\bigr)^{1/n}.
> ```
> In every degree the length can be chosen less than $`(5/2)\mu^{1/n}`$.*

The Lean proof assumes Theorem 3.1 as stated. Lean takes this input as a hypothesis (`LowCriticalThirteenTwentyFifths`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCritical_of_lowCritical`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/LowCriticalScaleTransport.lean#L460)

```lean
theorem scaledLowCritical_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCritical
```

where [`ScaledLowCritical`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L54) is

```lean
def ScaledLowCritical : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      (2 * (((25 / 13 : ℝ) * μ) ^ (1 / (p.natDegree : ℝ))))
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCriticalFiveHalves_of_lowCritical`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/LowCriticalScaleTransport.lean#L491)

```lean
theorem scaledLowCriticalFiveHalves_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCriticalFiveHalves
```

where [`ScaledLowCriticalFiveHalves`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L61) is

```lean
def ScaledLowCriticalFiveHalves : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      ((5 / 2 : ℝ) * (μ ^ (1 / (p.natDegree : ℝ))))
```

The assumed input [`LowCriticalThirteenTwentyFifths`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L49) is

```lean
def LowCriticalThirteenTwentyFifths : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ → μ ≤ 13 / 25 → HasDistinctConnection p 1 2
```

<a id="res-scaled-low-critical-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-constant-factor-path"></a>

## Theorem 3.3 (a uniform path bound at level $`2\mu`$), page 6

> *For every monic polynomial $`f`$ of degree $`n\ge2`$, two zero occurrences are joined by a possibly degenerate path of length at most
> ``` math
> \frac{71}{10}\,\rho
> ```
> inside $`K_{2\mu}`$. If $`f`$ is squarefree, their locations are distinct. If $`\mu\le1/2`$, the construction may be chosen inside $`\{|f|<1\}`$ with length at most $`5.7`$.*

The Lean proof assumes the level and direction averaging construction that this proof produces. Lean takes this input as a hypothesis (`CFAPathConstruction`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_constant_factor_path`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L677)

```lean
theorem cfa_constant_factor_path (hext : CFAPathConstruction)
    {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hn : 2 ≤ n) (hmonic : f.Monic) (hdeg : f.natDegree = n)
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) :
    cfaJoinedAtMost f z (2 * μ) ((71 / 10) * μ ^ ((1 : ℝ) / (n : ℝ))) ∧
      (μ ≤ 1 / 2 → cfaJoinedBelow f z 1 5.7)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaBracket_two_three_twentieths_lt`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L355)

```lean
theorem cfaBracket_two_three_twentieths_lt {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k) :
    cfaBracket n k 2 (3 / 20) ≤ 71 / 10
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaBracket_five_point_seven`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L393)

```lean
theorem cfaBracket_five_point_seven {k : ℕ} (hk : 2 ≤ k) :
    Real.sqrt (2 / (k : ℝ)) *
        (Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 +
          (Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) + Real.pi / Real.sqrt (Real.log 2)))
      ≤ 5.7
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degenerate`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L313)

```lean
theorem cfa_degenerate {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) (hμ0 : μ = 0) :
    ∃ i j : Fin n, i ≠ j ∧ z i = z j ∧ f.eval (z i) = 0
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degree_two_mu`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L606)

```lean
theorem cfa_degree_two_mu {f : ℂ[X]} {z : Fin 2 → ℂ} {μ : ℝ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) :
    μ = ‖(z 0 - z 1) / 2‖ ^ 2
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degree_two_below`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L627)

```lean
theorem cfa_degree_two_below {f : ℂ[X]} {z : Fin 2 → ℂ} {μ R L : ℝ}
    (hz' : f = ∏ i, (X - C (z i))) (hmu : μ = ‖(z 0 - z 1) / 2‖ ^ 2)
    (hR : μ < R) (hL : ‖z 0 - z 1‖ ≤ L) : cfaJoinedBelow f z R L
```

where [`cfaJoinedBelow`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L240) is

```lean
def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaTwoRpow_le`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L184)

```lean
theorem cfaTwoRpow_le {n : ℕ} (hn : 3 ≤ n) : (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 63 / 50
```

The assumed input [`CFAPathConstruction`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L346) is

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

<a id="res-critical-proximity"></a>

## Theorem 4.1 (a geometric-mean bound for distances to a critical point), page 8

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

[`ErdosProblems.Erdos1041.exists_two_roots_dist_sum_le_two_mul_geomMean`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean#L291)

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

## Corollary 4.2 (two nearest roots), page 8

> *If the roots lie in the open unit disc and $`c`$ is a non-root critical point, the two nearest roots to $`c`$ have total distance strictly below $`2`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1041.PaperCompleteR20.two_nearest_roots_of_polynomial_critical`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR20/TwoNearestPolynomial.lean#L9)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR20.exists_two_nearest_roots_of_polynomial_critical`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR20/TwoNearestPolynomial.lean#L31)

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

## Proposition 4.3 (two counterexamples to straight-path assertions), page 9

> *There is a monic quintic with all roots in the open unit disc and a non-root critical point $`c`$ whose unique nearest root has a point on the straight spoke to $`c`$ outside $`\{|f|<1\}`$. There is also a monic cubic with all roots in the open unit disc such that the midpoint of every pair of distinct roots lies outside $`\{|f|<1\}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperStraightObstructions.complete_straight_path_obstructions`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperStraightObstructions.lean#L178)

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

<a id="res-cubic-fibres"></a>

## Theorem 5.1 (a cubic composed with a power map), page 10

> *Let $`q\ge2`$, $`h\in\mathbb C`$, and let $`P`$ be a monic cubic. Put
> ``` math
> f(z)=P((z-h)^q).
> ```
> If all zeros of $`f`$ lie in the open unit disc and $`f`$ has at least two distinct zeros, then two distinct zeros of $`f`$ are joined by a two-segment path of length strictly less than $`2`$ contained in $`\{|f|<1\}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperCubicFibres.complete_translated_cubic_quotient_fibres`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCubicFibres.lean#L240)

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

<a id="res-cubic-fibres-comparator"></a>

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

<a id="res-primitive-quintic"></a>

## Theorem 5.2 (quintics with two missing coefficients), page 10

> *Let
> ``` math
> p(z)=z^5+az^4+bz+c
> ```
> be monic with all five root occurrences in the open unit disc. Then two distinct root occurrences $`w_i,w_j`$ satisfy
> ``` math
> |bw_i+c|<1,
>   \qquad
>   |bw_j+c|<1,
> ```
> and the corresponding two radial spokes join them through the origin inside $`\{|p|<1\}`$ with total length strictly below $`2`$. If the two occurrences coincide, the associated root-to-root path is degenerate.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.complete_primitive_quintic`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperPrimitiveCompletionR10.lean#L237)

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

<a id="res-primitive-quintic-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `complete_primitive_quintic`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_05/Challenge.lean#L138) (E1041_05, line 138), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_05/PaperStatementsU.lean#L58) (PaperStatementsU.lean, line 58), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_05.json) (E1041_05)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-critical-value-separation"></a>

## Theorem 6.1 (separation of one simple critical value), page 11

> *Let $`f`$ be monic of degree $`n\ge3`$, let $`c`$ be a simple critical point, and put $`v=f(c)\ne0`$. Fix $`w_0\in[0,1]`$ and $`S>\max(w_0,1-w_0)`$. Suppose every other critical point $`d`$ satisfies
> ``` math
> \left|\frac{f(d)}v-w_0\right|\ge S .
> ```
> Put $`p=w_0(1-w_0)`$. Then two distinct roots are joined inside $`\{|f|\le|v|\}`$ by a curve $`\Gamma`$ satisfying
> ``` math
> \begin{equation}
> \label{eq:disk-family-length}
>  \operatorname{length}(\Gamma)^2
>  \le 2|v|^{2/n}\Bigl(\frac{S}{n-1}\Bigr)^{2/n}
>  \log\!\frac{S^2+S+p}{S^2-S+p}.
> \end{equation}
> ```*

The Lean proof assumes the connector and area construction that this proof produces. Lean takes this input as a hypothesis (`DiscSepBergmanArea`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_separation_short`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L534)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSepNormalise_spec`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L410)

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

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_transport`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L475)

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

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_squared_length_le`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L305)

```lean
theorem discSep_squared_length_le {n : ℕ} {w₀ S L area : ℝ}
    (hw₀ : 0 ≤ w₀) (hS : max w₀ (1 - w₀) < S)
    (hBergman : L ^ 2 ≤ 2 / Real.pi *
      Real.log ((1 + discSepQsq S (w₀ * (1 - w₀))) /
        (1 - discSepQsq S (w₀ * (1 - w₀)))) * area)
    (hArea : area ≤ Real.pi * (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ))) :
    L ^ 2 ≤ 2 * discSepCoefficient n S (w₀ * (1 - w₀))
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_bergman_factor`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L179)

```lean
theorem discSep_bergman_factor {S p : ℝ} (hS : 0 < S) (hden : 0 < S ^ 2 - S + p) :
    (1 + discSepQsq S p) / (1 - discSepQsq S p)
      = (S ^ 2 + S + p) / (S ^ 2 - S + p)
```

The assumed input [`DiscSepBergmanArea`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L293) is

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

## Corollary 6.2 (uniform radius $`4/3`$), page 12

> *Let $`f`$ be monic of degree $`n\ge3`$ with all roots in the open unit disc. If $`c`$ is a simple critical point with $`0<|f(c)|<1`$ and, for some $`w_0\in[0,1]`$, every other critical point $`d`$ satisfies
> ``` math
> \left|\frac{f(d)}{f(c)}-w_0\right|\ge\frac43,
> ```
> then two roots are joined inside $`\{|f|<1\}`$ by a curve of length strictly below $`2`$. In degree three the branch-centred choice $`w_0=1`$ already works with $`4/3`$ replaced by $`6/5`$.*

The Lean proof assumes the connector and area construction in the proof of Theorem 6.1. Lean takes this input as a hypothesis (`DiscSepBergmanArea`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_uniform_radius`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L702)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_cubic_six_fifths`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L738)

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

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSepCoefficient_lt_two`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L645)

```lean
theorem discSepCoefficient_lt_two {n : ℕ} (hn : 3 ≤ n) {S p : ℝ}
    (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2) (hp0 : 0 ≤ p) :
    discSepCoefficient n S p < 2
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSepCoefficient_three_six_fifths`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L677)

```lean
theorem discSepCoefficient_three_six_fifths : discSepCoefficient 3 (6 / 5) 0 < 2
```

The assumed input [`DiscSepBergmanArea`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L293) is

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

<a id="res-separation-parent"></a>

## Corollary 6.3 (a sufficient condition for a length-$`2`$ path), page 12

> *Let $`f`$ be monic of degree $`n\ge3`$ with all roots in the open unit disc, and let $`c`$ be a simple critical point with $`v=f(c)`$ and $`0<|v|<1`$. If some real centre $`w_0\in[0,1]`$ admits a radius $`S\ge4/3`$ such that $`|f(d)/v-w_0|\ge S`$ for every other critical point $`d`$, then Erdős Problem #1041 holds for $`f`$.*

The Lean proof assumes Theorem 6.1 as stated. Lean takes this input as a hypothesis (`CriticalValueSeparationTheorem`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separation_parent`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SeparationParent.lean#L162)

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

where [`HasDistinctConnection`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L45) is

```lean
def HasDistinctConnection (p : ℂ[X]) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ p.eval a = 0 ∧ p.eval b = 0 ∧ ConnectedBelow p.eval R L a b
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separationCoefficient_lt_two`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SeparationParent.lean#L98)

```lean
theorem separationCoefficient_lt_two {n : ℕ} (hn : 3 ≤ n) {p : ℝ} (hp : 0 ≤ p) :
    separationCoefficient n (4 / 3) p < 2
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.squared_bound_lt_four`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SeparationParent.lean#L123)

```lean
theorem squared_bound_lt_four {n : ℕ} (hn : 3 ≤ n) {v p : ℝ} (hv0 : 0 < v) (hv1 : v < 1)
    (hp : 0 ≤ p) :
    2 * v ^ ((2 : ℝ) / (n : ℝ)) * separationCoefficient n (4 / 3) p < 4
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.connectedBelow_of_connectedAtMost`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SeparationParent.lean#L144)

```lean
theorem connectedBelow_of_connectedAtMost {f : ℂ → ℂ} {R L R' L' : ℝ} {a b : ℂ}
    (h : PaperAnalyticTargets.ConnectedAtMost f R L a b) (hR : R < R') (hL : L < L')
    (hL0 : 0 ≤ L) : PaperCurve.ConnectedBelow f R' L' a b
```

where [`ConnectedBelow`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCurveAssembly.lean#L176) is

```lean
def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
```

The assumed input [`CriticalValueSeparationTheorem`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SeparationParent.lean#L60) is

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

<a id="res-separation-parent-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-sep-or-false"></a>

## Proposition 7.1 (failure of two critical-value criteria to cover all polynomials), page 13

> *Let $`f(z)=z^3+(3/100)z-3/4`$. Every root lies in the open unit disc, both critical points are simple, the critical values lie on distinct positive rays, $`\mu>13/25`$, and
> ``` math
> \bigl|1-f(c_-)/f(c_+)\bigr|<2/375<2.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperSeparationCounterexample.complete_sep_or_counterexample`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperSeparationCounterexample.lean#L189)

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

<a id="res-one-root-gamma-false"></a>

## Proposition 7.2 (a counterexample to the proposed one-root perimeter bound), page 13

> *Let $`p(z)=z^8-(3/2)z`$ and let $`C`$ be the component of $`\{|p|\le1\}`$ containing the origin. Then $`C`$ contains exactly one zero and a neighbourhood of the closed disc of radius $`5/8`$, so $`\mathcal H^1(\partial C)>5\pi/4`$. The constant $`\Gamma(1/4)^2/(2\sqrt{\pi})`$ is at most $`(\pi/2)(1+\sqrt2)<5\pi/4`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperCompleteR21.Lobe.one_root_gamma_false_unconditional`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/LobeUnconditional.lean#L41)

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

<a id="res-arity-not-capacity"></a>

## Proposition 7.3 (root count does not force a capacity gap), page 14

> *Let $`g(z)=z^3-(3/400)z-3/32`$. All roots lie in the open unit disc and $`\mu=187/2000\le1/2`$. The first merger joins two root components, so $`k_0=2`$, but the component at level $`2\mu`$ containing that pair has normalised capacity $`1`$.*

The Lean proof assumes the classical value $t^{1/n}$ of the transfinite diameter of the filled lemniscate $\{|p|\le t\}$ of a monic polynomial $p$ of degree $n$, used only in the capacity clause. Lean takes this input as a hypothesis (`LemniscateTransfiniteDiameter`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.Arity.arity_not_capacity`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ArityNotCapacity.lean#L677)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.Arity.arity_first_merger`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ArityNotCapacity.lean#L568)

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

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.Arity.closure_doubleLevelComponent`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ArityNotCapacity.lean#L660)

```lean
theorem closure_doubleLevelComponent :
    closure (connectedComponentIn {z : ℂ | ‖G.eval z‖ < 2 * (187 / 2000)} (-(1 / 20))) =
      {z : ℂ | ‖G.eval z‖ ≤ 2 * (187 / 2000)}
```

The assumed input [`LemniscateTransfiniteDiameter`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ArityNotCapacity.lean#L95) is

```lean
def LemniscateTransfiniteDiameter : Prop :=
  ∀ (p : ℂ[X]) (t : ℝ), p.Monic → 1 ≤ p.natDegree → 0 < t →
    transfiniteDiameter {z | ‖p.eval z‖ ≤ t} = t ^ ((1 : ℝ) / p.natDegree)
```

<a id="res-arity-not-capacity-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-value"></a>

## Theorem 8.1 (value equation), page 14

> *For a polynomial $`f`$ and a differentiable curve $`z:I\to\mathbb C`$ on an interval $`I`$, assume $`f'(z(t))\ne0`$ and $`z'(t)=-f(z(t))/f'(z(t))`$ throughout $`I`$. Then $`w=f\circ z`$ satisfies $`w'=-w`$, and
> ``` math
> f(z(t))=e^{-(t-t_0)}f(z(t_0))\qquad(t,t_0\in I).
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement allows any function $f$ with a complex derivative at each point $z(t)$, $t\in I$, of which a polynomial is a case; its conclusions are $w'=-w$ on $I$ and $f(z(t))=e^{-(t-t_0)}f(z(t_0))$ for $t,t_0\in I$.

[`ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_value_whole`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR20/NewtonRealTime.lean#L52)

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

## Corollary 8.2 (ray separation), page 15

> *Let $`a<b`$, let $`z:[a,b]\to\mathbb C`$ be continuous, and suppose $`z`$ is differentiable on $`(a,b)`$ with $`f'(z(t))\ne0`$ and $`z'(t)=-f(z(t))/f'(z(t))`$ there. Then
> ``` math
> f(z(b))=e^{a-b}f(z(a)).
> ```
> If the endpoint values are nonzero, they lie on the same positive ray. In particular, critical points whose values lie on distinct positive rays cannot be the endpoints of such a finite connection.*

The Lean declaration below states this result or one that implies it. The Lean statement allows any function $f$ with a complex derivative at each $z(t)$, $a<t<b$, and assumes only that $f\circ z$ is continuous on $[a,b]$, which holds when $f$ is a polynomial and $z$ is continuous. It gives $f(z(b))=e^{a-b}f(z(a))$ and that the two endpoint values lie on one positive ray, which excludes endpoints whose values lie on distinct positive rays.

[`ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_endpoint_whole`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR20/NewtonRealTime.lean#L69)

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

## Theorem 9.1 (ray-collision locus), page 16

> *Let $`a\ne b`$ be complex. Every common translation $`\beta`$ for which $`a+\beta`$ and $`b+\beta`$ lie on the same positive ray has the form
> ``` math
> \beta=\frac{ra-b}{1-r},
>   \qquad r\in\mathbb{R}_{>0},\ r\ne1 .
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.translated_samePositiveRay_parameterization`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L107)

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

<a id="res-complementary-binomial-chords"></a>

## Theorem 13.1 (complementary binomial chords), page 18

> *Two adjacent zeros of $`z^n-a`$ can be joined by an explicit polygonal path inside $`\{|z^n-a|<1\}`$ of length strictly below $`2`$. For $`r<r_*`$ the adjacent-root chord itself works. For $`r\ge r_*`$, two radial legs and an inner adjacent crossing chord work after an arbitrarily small radial contraction. These two constructions meet at $`r=r_*`$, where the outer chord attains $`|f|=1`$ at its midpoint and therefore lies only in the closed lemniscate. Open containment at and above the switch uses the inner chord after a radial contraction.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_path`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1084)

```lean
theorem binomial_chords_path {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((r : ℝ) : ℂ) ≠ ((r : ℝ) : ℂ) * chordOmega n ∧
      (((r : ℝ) : ℂ)) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      (((r : ℝ) : ℂ) * chordOmega n) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
        ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_below_threshold`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1094)

```lean
theorem binomial_chords_below_threshold {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hlt : r < chordThreshold n) :
    PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n)
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_above_threshold`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1104)

```lean
theorem binomial_chords_above_threshold {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hge : chordThreshold n ≤ r) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    PaperCurve.ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n)
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_at_threshold`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1118)

```lean
theorem binomial_chords_at_threshold {n : ℕ} (hn : 2 ≤ n) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(chordPoint n (chordThreshold n) u) ^ n
          - ((chordThreshold n : ℝ) : ℂ) ^ n‖ ≤ 1) ∧
      ‖(chordPoint n (chordThreshold n) (1 / 2)) ^ n
        - ((chordThreshold n : ℝ) : ℂ) ^ n‖ = 1
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chord_maximum`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1129)

```lean
theorem binomial_chord_maximum {n : ℕ} (hn : 2 ≤ n) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(chordPoint n s u) ^ n - ((r : ℝ) : ℂ) ^ n‖ ≤ r ^ n + (s * chordCos n) ^ n) ∧
      ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = r ^ n + (s * chordCos n) ^ n
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chord_decisive_step`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1138)

```lean
theorem binomial_chord_decisive_step {n : ℕ} (hn : 2 ≤ n) {θ : ℝ}
    (hθ : (n : ℝ) * |θ| ≤ Real.pi) :
    1 + Real.cos ((n : ℝ) * θ) ≤ 2 * Real.cos θ ^ n
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.binomial_inner_chord_maximal`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/BinomialChords.lean#L1145)

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

<a id="res-sharp-collinear-root-diameter"></a>

## Theorem 14.1 (sharp collinear root-diameter bound), page 19

> *Let $`f`$ be monic of degree $`n\ge2`$, with collinear zero occurrences of diameter $`D`$. Then some two zero occurrences are joined by their straight segment, of length at most $`D`$, on which
> ``` math
> |f|\le C_n\left(\frac D2\right)^n.
> ```
> The constant is sharp: equality is attained by the affine images of the scaled Chebyshev root configuration with extreme roots at distance $`D`$.*

The Lean declarations below together state this result or one that implies it. The bound is proved for every monic $f$ of degree $n\ge2$ whose zeros lie on one line, and the chosen pair is adjacent on that line, with no zero strictly between them (`sharp_collinear_root_diameter_monic`). The Chebyshev configuration with extreme roots at distance $D$, placed on any line by a translation and a rotation, attains $C_n(D/2)^n$ on every gap between adjacent roots (`sharp_collinear_equality_attained`), and no constant smaller than $C_n$ gives the adjacent-pair bound (`sharpConstant_le_of_collinearDiameterBound`).

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L367)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter_monic`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L967)

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

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.exists_collinear_factorisation`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L928)

```lean
theorem exists_collinear_factorisation (base dir : ℂ) :
    ∀ (n : ℕ) (f : ℂ[X]), f.IsMonicOfDegree n →
      (∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) →
      ∃ y : Fin n → ℝ, f = ∏ k : Fin n, (X - C (base + dir * (y k : ℂ)))
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.exists_gap_le_comparisonBound`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L212)

```lean
theorem exists_gap_le_comparisonBound {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1) (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤ comparisonBound (m + 2)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_equality_attained`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L836)

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

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.chebyshev_configuration_attains`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L769)

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

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.monicScaledChebyshev_eq_prod`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L684)

```lean
theorem monicScaledChebyshev_eq_prod (m : ℕ) :
    monicScaledChebyshev (m + 2) = ∏ i : Fin (m + 2), (X - C (chebNode m i))
```

8. [`ErdosProblems.Erdos1041.PaperCompleteR21.collinearDiameterBound_sharpConstant`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L871)

```lean
theorem collinearDiameterBound_sharpConstant {n : ℕ} (hn : 2 ≤ n) :
    CollinearDiameterBound n
      (1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n))
```

9. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharpConstant_le_of_collinearDiameterBound`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L878)

```lean
theorem sharpConstant_le_of_collinearDiameterBound {n : ℕ} (hn : 2 ≤ n) {K : ℝ}
    (hK : CollinearDiameterBound n K) :
    1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) ≤ K
```

<a id="res-sharp-collinear-root-diameter-comparator"></a>

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

<a id="res-fp-weighted-all-degree"></a>

## Theorem 15.1 (a weighted inequality for points in a disc), page 20

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

1. [`ErdosProblems.Erdos1041.paper_weighted_free_point`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperWeightedRefinementsR10.lean#L17)

```lean
theorem paper_weighted_free_point : PaperAnalyticTargets.WeightedFreePoint
```

where [`WeightedFreePoint`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L87) is

```lean
def WeightedFreePoint : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (w : Fin m → ℝ),
    (∀ j, ‖c j‖ ≤ 1) → (∀ j, 0 < w j) → (∑ j, w j) = 1 →
      (∑ j, w j * weightedProduct c w (c j) ^ 2) ≤ 1 ∧
      ((∑ j, w j * weightedProduct c w (c j) ^ 2) = 1 ↔ ∀ j, c j = 0)
```

2. [`ErdosProblems.Erdos1041.geometric_row_mean_closed_disc_le`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperWeightedRefinementsR10.lean#L155)

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

<a id="res-fp-to-s"></a>

## Theorem 15.2 (critical-value mean in every degree), page 22

> *Let $`f`$ be monic of degree $`n\ge2`$, with roots in a closed disc of radius $`R`$, and let $`c_1,\ldots,c_{n-1}`$ be its critical points with multiplicity. Then
> ``` math
> \sum_{j=1}^{n-1}|f(c_j)|^{2/(n-1)}
>  \le(n-1)R^{2n/(n-1)}.
> ```
> In particular, $`\sum_j|f(c_j)|^{1/n}\le(n-1)R`$ in every degree.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.paper_critical_value_mean`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCriticalValueMeanR10.lean#L101)

```lean
theorem paper_critical_value_mean : PaperAnalyticTargets.CriticalValueMean
```

where [`CriticalValueMean`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L102) is

```lean
def CriticalValueMean : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ) (h : ℂ) (R : ℝ),
    2 ≤ n → p.Monic → p.natDegree = n → 0 ≤ R →
    RootsInClosedDisc p h R → CriticalEnumeration p c →
      (∑ j, ‖p.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
        ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
      (∑ j, ‖p.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R
```

<a id="res-fp-to-s-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `paper_critical_value_mean`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E1041_06/Challenge.lean#L163) (E1041_06, line 163), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E1041_06/CriticalValueMean.lean#L15) (CriticalValueMean.lean, line 15), [replay report](../evidence/comparator/replay-35935225572/receipt-E1041_06.json) (E1041_06)

Challenge for `paper_critical_value_mean`:

```lean
theorem paper_critical_value_mean (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ) (h : ℂ) (R : ℝ)
    (hn : 2 ≤ n) (hp : p.Monic) (hdeg : p.natDegree = n) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc p h R) (hc : CriticalEnumeration p c) :
    (∑ j, ‖p.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
        ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
      (∑ j, ‖p.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R := by sorry
```

<a id="res-orlicz-currency"></a>

## Theorem 16.1 (the relation between two merger-scale integrals), page 23

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

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.orlicz_currency`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L374)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_continuous`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L115)

```lean
theorem orliczKernel_continuous : Continuous orliczKernel
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L163)

```lean
theorem orliczKernel_tendsto_zero : Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0)
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.mergerIntegral_eq_mul_phi`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L278)

```lean
theorem mergerIntegral_eq_mul_phi {k : ℕ} (hk : 1 ≤ k) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    mergerIntegral k r = k * Phi (Real.log (1 / r) / k)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictMonoOn`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L196)

```lean
theorem phi_strictMonoOn : StrictMonoOn Phi (Ici (0 : ℝ))
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictConvexOn`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L203)

```lean
theorem phi_strictConvexOn : StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.phi_div_tendsto_zero`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L209)

```lean
theorem phi_div_tendsto_zero :
    Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0)
```

8. [`ErdosProblems.Erdos1041.PaperCompleteR21.exists_mergerIntegral_lt`](https://github.com/wcook04/plectis-erdos/blob/4d41eaab40de87460b9049d84455ef18660b858e/lean/ErdosProblems/Erdos1041/PaperCompleteR21/MergerScaleOrlicz.lean#L341)

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
