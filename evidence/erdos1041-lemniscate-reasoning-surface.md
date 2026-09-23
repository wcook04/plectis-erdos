# Formal evidence: Paths in Polynomial Lemniscates: Proofs and Examples

This record belongs to the paper [erdos1041-lemniscate-reasoning-surface.pdf](../paper/1041/erdos1041-lemniscate-reasoning-surface.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`c91562bd574a`](https://github.com/wcook04/plectis-erdos/tree/c91562bd574a387cde904481e609c7b4cacebb14) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35882032091](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35882032091) at corpus commit [`a2faa350b45a`](https://github.com/wcook04/plectis-erdos-lean/tree/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3) (tag `paper-evidence-2026-09-23`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 27 results: 16 with a Lean proof of the whole statement, 9 whose Lean proof assumes a named input (marked with a dagger), 2 without a Lean proof of the whole statement; 14 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

<a id="res-ani-degree-seven-counterexample-long"></a>

## Passage (beginning “The degree-seven polynomial constructed by…”), page 2

The Lean declarations below together state a result at least as strong as this one. The first Lean statement gives that the polynomial is monic of degree seven with distinct roots in the open unit disc, and that every continuous path in $\{|f|<1\}$ joining two distinct roots has total variation greater than $2$. The second gives the Hausdorff bound for every preconnected subset of $\{|f|<1\}$ containing two distinct roots, which covers the image of such a path because that image is connected. The last two are the negation and `answer(False)` forms of the Formal Conjectures statement, in which length is one-dimensional Hausdorff measure.

1. [`Erdos1041.Counterexample.erdos1041_counterexample`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/Counterexample/Assembly.lean#L319)

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

2. [`Erdos1041.Counterexample.erdos1041_counterexample_hausdorff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L283)

```lean
theorem erdos1041_counterexample_hausdorff :
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K → K ⊆ Omega f →
        (2 : ℝ≥0∞) < μH[1] K
```

3. [`Erdos1041.Counterexample.erdos1041_hausdorff_negation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L407)

```lean
theorem erdos1041_hausdorff_negation :
    ¬ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2
```

4. [`Erdos1041.Counterexample.erdos1041_hausdorff_answer_false`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/Counterexample/HausdorffLength.lean#L449)

```lean
theorem erdos1041_hausdorff_answer_false :
    False ↔ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2
```

<a id="res-ani-degree-seven-counterexample-long-comparator"></a>

**Comparator:** not yet compared.

<a id="res-trinomial-all-degree"></a>

## Theorem 2.1 (trinomial root connections), page 3

> *Let $`n,m`$ be integers with $`1\le m<n`$, and let $`f(z)=z^n+az^m+b`$ have every zero in $`\mathbb{D}`$. For every zero $`\zeta`$, the segment $`[0,\zeta]`$ lies in $`E_f`$. Consequently any two zeros $`\zeta_1,\zeta_2`$ are joined in $`E_f`$ by the broken line $`\zeta_1\to0\to\zeta_2`$, of length $`|\zeta_1|+|\zeta_2|<2`$.*

The Lean declarations below together state a result at least as strong as this one. The Lean statement has the same hypotheses and conclusion as the printed one.

1. [`ErdosProblems.Erdos1041.PaperTrinomial.all_spokes`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperTrinomial.lean#L26)

```lean
theorem all_spokes {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z : ℂ} (hz : polynomialValue n m a b z = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1
```

2. [`ErdosProblems.Erdos1041.PaperTrinomial.complete_trinomial`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperTrinomial.lean#L38)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `all_spokes` | [E1041_01/Challenge.lean, line 119](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_01/Challenge.lean#L119) | [PaperStatementsH.lean, line 17](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_01/PaperStatementsH.lean#L17) | [E1041_01](../evidence/comparator/replay-35882032091/receipt-E1041_01.json) |
| `complete_trinomial` | [E1041_01/Challenge.lean, line 82](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_01/Challenge.lean#L82) | [PaperStatementsAA.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_01/PaperStatementsAA.lean#L21) | [E1041_01](../evidence/comparator/replay-35882032091/receipt-E1041_01.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-low-critical-thirteen-twentyfifths"></a>

## Theorem 3.1 (a small least critical value forces a short connector), page 5

> *Let $`f`$ be squarefree and monic of degree $`n\ge2`$ with $`\mu\le13/25`$. Then two distinct roots of $`f`$ are joined inside $`\{|f|<1\}`$ by a rectifiable curve of length strictly below $`2`$. No hypothesis is placed on the locations of the roots, on the number of roots in any component, or on the capacity of any component.*

**No Lean proof of the whole statement.** In Lean, the degree-two case and the closing inequality $(13/25)e^X<1$ at the recorded stopping time $X=635762889599/10^{12}$ are checked; the computation that certifies $X$ and the analytic argument in higher degrees are not.

<a id="res-low-critical-scale-free"></a>

## Corollary 3.2 (scale-free form), page 5

> *Every squarefree monic $`f`$ of degree $`n\ge2`$ has two distinct roots joined inside $`\{|f|<(25/13)\mu\}`$ by a curve of length below $`2\bigl((25/13)\mu\bigr)^{1/n}`$.*

The Lean proof assumes Theorem 3.1 as stated. Lean takes this input as a hypothesis (`LowCriticalThirteenTwentyFifths`); it is not proved in Lean.

[`ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCritical_of_lowCritical`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/LowCriticalScaleTransport.lean#L460)

```lean
theorem scaledLowCritical_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCritical
```

where [`ScaledLowCritical`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L54) is

```lean
def ScaledLowCritical : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      (2 * (((25 / 13 : ℝ) * μ) ^ (1 / (p.natDegree : ℝ))))
```

The assumed input [`LowCriticalThirteenTwentyFifths`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L49) is

```lean
def LowCriticalThirteenTwentyFifths : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ → μ ≤ 13 / 25 → HasDistinctConnection p 1 2
```

<a id="res-low-critical-scale-free-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-circle-slice-packing"></a>

## Lemma 3.3 (circle-slice packing), page 7

> *Under <a href="#eq:lc-separation" data-reference-type="eqref" data-reference="eq:lc-separation">[eq:lc-separation]</a>, for every $`r>0`$,
> ``` math
> \sum_{j=1}^{k}w(d_j,r)\le\pi,\qquad
>  w(d,r)=\arccos\Bigl(\operatorname{clamp}
>    \frac{\cosh d\cosh r-\cosh(D/2)}{\sinh d\sinh r}\Bigr),
> ```
> where $`\operatorname{clamp}`$ truncates its argument to $`[-1,1]`$.*

The Lean declarations below together state a result at least as strong as this one. The Lean statement proves $\sum_jw(d_j,r)\le\pi$ for every separation $D>0$, with the points in geodesic polar coordinates $(d_j,\theta_j)$, $d_j>0$, about $i$ in the upper half-plane, the image of the disc model under an isometry sending $0$ to $i$; a second form holds in any metric space obeying the hyperbolic law of cosines. The printed statement is the case $D=4\operatorname{artanh}\sqrt{\tanh(1/a)}$ with $d_j=d(0,b_j)>0$.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.circle_slice_packing`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L563)

```lean
theorem circle_slice_packing {k : ℕ} (d θ : Fin k → ℝ) (hd : ∀ j, 0 < d j)
    {D : ℝ} (hD : 0 < D)
    (hsep : ∀ i j : Fin k, i ≠ j → D ≤ dist (polar (d i) (θ i)) (polar (d j) (θ j)))
    {r : ℝ} (hr : 0 < r) :
    ∑ j, sliceHalfAngle D (d j) r ≤ π
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.cosh_dist_polar`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L141)

```lean
theorem cosh_dist_polar (d₁ θ₁ d₂ θ₂ : ℝ) :
    cosh (dist (polar d₁ θ₁) (polar d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂)
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dist_polar_I`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L166)

```lean
theorem dist_polar_I (d θ : ℝ) : dist (polar d θ) UpperHalfPlane.I = |d|
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.exists_polar`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L177)

```lean
theorem exists_polar (z : ℍ) : ∃ d θ : ℝ, 0 ≤ d ∧ polar d θ = z
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.polar_zero_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L162)

```lean
theorem polar_zero_zero : polar 0 0 = UpperHalfPlane.I
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.circle_slice_packing_abstract`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L315)

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

**Comparator:** not yet compared.

<a id="res-dual-arity-floor"></a>

## Theorem 3.4 (a lower bound for the number of roots), page 7

> *Fix radii $`r_1,\ldots,r_p>0`$ and weights $`\sigma_1,\ldots,\sigma_p\ge0`$, put $`\Sigma=\sum_i\sigma_i`$ and
> ``` math
> U=\sup_{d\ge d_{\mathrm{low}}(a)}
>    \Bigl[\lambda(d)-\sum_i\sigma_i\,w(d,r_i)\Bigr],
>  \qquad
>  \lambda\bigl(d_{\mathrm{low}}(a)\bigr)=\frac{\delta(a)}2 .
> ```
> If $`U>0`$, then failure forces $`k\ge(x-\pi\Sigma)/U`$.*

The Lean proof assumes the separation bound (3) and the radius and budget bounds (4), which this proof derives from the standing failure hypothesis. Lean takes this input as a hypothesis (`hsep`, `hrad`, `hbudget`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dual_arity_floor_sup`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L594)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dual_arity_floor`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L579)

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

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.le_of_lam_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L506)

```lean
theorem le_of_lam_le {d₁ d₂ : ℝ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) (h : lam d₂ ≤ lam d₁) :
    d₁ ≤ d₂
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.cosh_dist_polar`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L141)

```lean
theorem cosh_dist_polar (d₁ θ₁ d₂ θ₂ : ℝ) :
    cosh (dist (polar d₁ θ₁) (polar d₂ θ₂))
      = cosh d₁ * cosh d₂ - sinh d₁ * sinh d₂ * cos (θ₁ - θ₂)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.Hyperbolic.dual_arity_floor_abstract`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/HyperbolicLawOfCosines.lean#L513)

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

## Corollary 3.5 (scaled low-critical connection), page 12

> *Every squarefree monic polynomial $`f`$ of degree $`n\ge2`$ has two distinct zeros joined by a rectifiable curve of length less than $`(5/2)\mu^{1/n}`$ in $`\{|f|<(25/13)\mu\}`$, where $`\mu=\min_{f'(c)=0}|f(c)|`$.*

The Lean proof assumes Theorem 3.1 as stated, and only in degrees above two. Lean takes this input as a hypothesis (`LowCriticalThirteenTwentyFifths`); it is not proved in Lean.

[`ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCriticalFiveHalves_of_lowCritical`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/LowCriticalScaleTransport.lean#L491)

```lean
theorem scaledLowCriticalFiveHalves_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCriticalFiveHalves
```

where [`ScaledLowCriticalFiveHalves`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L61) is

```lean
def ScaledLowCriticalFiveHalves : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      ((5 / 2 : ℝ) * (μ ^ (1 / (p.natDegree : ℝ))))
```

The assumed input [`LowCriticalThirteenTwentyFifths`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L49) is

```lean
def LowCriticalThirteenTwentyFifths : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ → μ ≤ 13 / 25 → HasDistinctConnection p 1 2
```

<a id="res-scaled-low-critical-path-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-constant-factor-path"></a>

## Theorem 4.1 (a uniform path bound at level $`2\mu`$), page 13

> *For every monic polynomial $`f`$ of degree $`n\ge2`$, two zero occurrences are joined by a possibly degenerate path of length at most
> ``` math
> \frac{71}{10}\,\rho
> ```
> inside $`K_{2\mu}`$. If $`f`$ is squarefree, their locations are distinct. If $`\mu\le1/2`$, the construction may be chosen inside $`\{|f|<1\}`$ with length at most $`5.7`$.*

The Lean proof assumes the level and direction averaging construction that this proof produces. Lean takes this input as a hypothesis (`CFAPathConstruction`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_constant_factor_path`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L677)

```lean
theorem cfa_constant_factor_path (hext : CFAPathConstruction)
    {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hn : 2 ≤ n) (hmonic : f.Monic) (hdeg : f.natDegree = n)
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) :
    cfaJoinedAtMost f z (2 * μ) ((71 / 10) * μ ^ ((1 : ℝ) / (n : ℝ))) ∧
      (μ ≤ 1 / 2 → cfaJoinedBelow f z 1 5.7)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaBracket_two_three_twentieths_lt`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L355)

```lean
theorem cfaBracket_two_three_twentieths_lt {n k : ℕ} (hn : 3 ≤ n) (hk : 2 ≤ k) :
    cfaBracket n k 2 (3 / 20) ≤ 71 / 10
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaBracket_five_point_seven`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L393)

```lean
theorem cfaBracket_five_point_seven {k : ℕ} (hk : 2 ≤ k) :
    Real.sqrt (2 / (k : ℝ)) *
        (Real.sqrt 2 * (3 / 20) / (1 - 3 / 20) ^ 2 +
          (Real.sqrt (Real.log ((2 : ℝ) / (3 / 20))) + Real.pi / Real.sqrt (Real.log 2)))
      ≤ 5.7
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degenerate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L313)

```lean
theorem cfa_degenerate {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) (hμ0 : μ = 0) :
    ∃ i j : Fin n, i ≠ j ∧ z i = z j ∧ f.eval (z i) = 0
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degree_two_mu`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L606)

```lean
theorem cfa_degree_two_mu {f : ℂ[X]} {z : Fin 2 → ℂ} {μ : ℝ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) :
    μ = ‖(z 0 - z 1) / 2‖ ^ 2
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degree_two_below`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L627)

```lean
theorem cfa_degree_two_below {f : ℂ[X]} {z : Fin 2 → ℂ} {μ R L : ℝ}
    (hz' : f = ∏ i, (X - C (z i))) (hmu : μ = ‖(z 0 - z 1) / 2‖ ^ 2)
    (hR : μ < R) (hL : ‖z 0 - z 1‖ ≤ L) : cfaJoinedBelow f z R L
```

where [`cfaJoinedBelow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L240) is

```lean
def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaTwoRpow_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L184)

```lean
theorem cfaTwoRpow_le {n : ℕ} (hn : 3 ≤ n) : (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 63 / 50
```

The assumed input [`CFAPathConstruction`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L346) is

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

## Corollary 4.2 (a criterion using the number of roots at the first merger), page 15

> *Let $`f`$ be monic with every root in the open unit disc, let $`c_*`$ be a critical point with $`|f(c_*)|=\mu`$, and let $`k_0`$ be the number of roots, counted with multiplicity, in the component of $`K_\mu`$ containing $`c_*`$. Then Erdős #1041 holds for $`f`$ in each of the three cases
> ``` math
> \mu\le\tfrac12\ \text{and}\ k_0\ge17,\qquad
>  \mu\le\tfrac14\ \text{and}\ k_0\ge12,\qquad
>  \mu\le\tfrac18\ \text{and}\ k_0\ge10 .
> ```*

The Lean proof assumes the level and direction averaging construction in the proof of Theorem 4.1. Lean takes this input as a hypothesis (`CFAArityConstruction`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_arity_criterion`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L765)

```lean
theorem cfa_arity_criterion {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ} {k₀ : ℕ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ)
    (hcase : 0 < μ →
      (μ ≤ 1 / 2 ∧ 17 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 2 (13 / 100)) ∨
      (μ ≤ 1 / 4 ∧ 12 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 4 (3 / 25)) ∨
      (μ ≤ 1 / 8 ∧ 10 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 8 (11 / 100))) :
    cfaJoinedBelow f z 1 2
```

where [`cfaJoinedBelow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L240) is

```lean
def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaArityBracket_case_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L440)

```lean
theorem cfaArityBracket_case_one : (cfaArityBracket 2 (13 / 100)) ^ 2 ≤ 34
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaArityBracket_case_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L455)

```lean
theorem cfaArityBracket_case_two : (cfaArityBracket 4 (3 / 25)) ^ 2 ≤ 24
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaArityBracket_case_three`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L470)

```lean
theorem cfaArityBracket_case_three : (cfaArityBracket 8 (11 / 100)) ^ 2 ≤ 20
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaArity_length_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L485)

```lean
theorem cfaArity_length_le {k₀ : ℕ} {B : ℝ} (hk : 2 ≤ k₀) (hB0 : 0 ≤ B)
    (hB : B ^ 2 ≤ 2 * (k₀ : ℝ)) : Real.sqrt (2 / (k₀ : ℝ)) * B ≤ 2
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_degenerate`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L313)

```lean
theorem cfa_degenerate {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) (hμ0 : μ = 0) :
    ∃ i j : Fin n, i ≠ j ∧ z i = z j ∧ f.eval (z i) = 0
```

The assumed input [`CFAArityConstruction`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L428) is

```lean
def CFAArityConstruction (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (k₀ : ℕ) (lam r : ℝ) : Prop :=
  cfaJoinedBelow f z 1 (Real.sqrt (2 / (k₀ : ℝ)) * cfaArityBracket lam r)
```

<a id="res-constant-factor-arity-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-constant-factor-capacity"></a>

## Corollary 4.3 (a criterion using component capacity), page 15

> *Keep the hypotheses of Corollary <a href="#res:constant-factor-arity" data-reference-type="ref" data-reference="res:constant-factor-arity">10</a> with $`0<\mu\le1/2`$, let $`C`$ be the component of $`\{|f|<2\mu\}`$ containing $`c_*`$, and put $`\kappa=\operatorname{cap}(\overline C)/(2\mu)^{1/n}`$. If $`\kappa\le\tau_{k_0}`$, where
> ``` math
> \tau_k=\frac{\sqrt{2k}-A}{B},\qquad
>  A=\frac{283}{3610},\qquad B=\frac{52029}{9100},
> ```
> then Erdős #1041 holds for $`f`$. In particular $`\kappa\le1/3`$ suffices for every root count $`k_0\ge2`$, and the rational cutoffs $`2/5,\,12/25,\,1/2,\,7/12,\,16/25,\,2/3,\,7/10`$ suffice at $`k_0=3,\ldots,9`$, rising to $`39/40`$ at $`k_0=16`$.*

The Lean proof assumes the level and direction averaging construction in the proof of Theorem 4.1, together with the area-capacity inequality. Lean takes this input as a hypothesis (`CFACapacityConstruction`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfa_capacity_criterion`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L538)

```lean
theorem cfa_capacity_criterion {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {κ : ℝ} {k₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hκ0 : 0 ≤ κ) (hκ : κ ≤ cfaTau k₀)
    (hext : CFACapacityConstruction n f z κ k₀) :
    cfaJoinedBelow f z 1 2
```

where [`cfaJoinedBelow`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L240) is

```lean
def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaTau_third`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L583)

```lean
theorem cfaTau_third {k : ℕ} (hk : 2 ≤ k) : (1 : ℝ) / 3 ≤ cfaTau k
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaTau_cutoffs`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L591)

```lean
theorem cfaTau_cutoffs :
    (2 / 5 : ℝ) ≤ cfaTau 3 ∧ (12 / 25 : ℝ) ≤ cfaTau 4 ∧ (1 / 2 : ℝ) ≤ cfaTau 5 ∧
    (7 / 12 : ℝ) ≤ cfaTau 6 ∧ (16 / 25 : ℝ) ≤ cfaTau 7 ∧ (2 / 3 : ℝ) ≤ cfaTau 8 ∧
    (7 / 10 : ℝ) ≤ cfaTau 9 ∧ (39 / 40 : ℝ) ≤ cfaTau 16
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaTau_ge_of_sq`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L572)

```lean
theorem cfaTau_ge_of_sq {k : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (h : (cfaA + cfaB * q) ^ 2 ≤ 2 * (k : ℝ)) : q ≤ cfaTau k
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaA_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L508)

```lean
theorem cfaA_bound : Real.sqrt 2 * (1 / 20) / (1 - 1 / 20) ^ 2 ≤ cfaA
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.cfaB_bound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L514)

```lean
theorem cfaB_bound :
    Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2) ≤ cfaB
```

The assumed input [`CFACapacityConstruction`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/ConstantFactorAreaCriteria.lean#L529) is

```lean
def CFACapacityConstruction (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (κ : ℝ) (k₀ : ℕ) : Prop :=
  cfaJoinedBelow f z 1
    (Real.sqrt (2 / (k₀ : ℝ)) *
      (Real.sqrt 2 * (1 / 20) / (1 - 1 / 20) ^ 2 +
        κ * (Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2))))
```

<a id="res-constant-factor-capacity-comparator"></a>

**Comparator:** not applicable (no unconditional Lean proof of the whole statement).

<a id="res-conjecture-p-consumer"></a>

## Theorem 4.5 (a path from a subcritical perimeter bound), page 18

> *Let $`f`$ be squarefree and monic of degree $`n\ge2`$, and put $`\mu=\min_{f'(c)=0}|f(c)|>0`$. Suppose $`\beta>0`$ satisfies
> ``` math
> \mathcal H^1(\partial C)\le\beta\sigma^{1/n}
> ```
> for every $`0<\sigma<\mu`$ and every component $`C`$ of $`\{|f|\le\sigma\}`$. Then two distinct roots of $`f`$ are joined inside $`K_\mu=\{|f|\le\mu\}`$ by a rectifiable path of length at most $`\beta\mu^{1/n}`$.*

The Lean proof assumes the two-component split at the first critical level that this proof constructs. Lean takes this input as a hypothesis (`SubcriticalSplitExists`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.subcritical_perimeter_path_paper`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L265)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.subcritical_perimeter_path`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L245)

```lean
theorem subcritical_perimeter_path {f : ℂ → ℂ} {μ P : ℝ} (hP : 0 ≤ P)
    (hsplit : SubcriticalSplitExists f μ P) :
    HasDistinctConnectionAtMost f μ P
```

where [`HasDistinctConnectionAtMost`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L239) is

```lean
def HasDistinctConnectionAtMost (f : ℂ → ℂ) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ f a = 0 ∧ f b = 0 ∧ ConnectedAtMost f R L a b
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.connectedAtMost_half_perimeter`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L203)

```lean
theorem connectedAtMost_half_perimeter {f : ℂ → ℂ} {R H : ℝ} {a c : ℂ}
    (h : JordanArcDatum f R H a c) : ConnectedAtMost f R (H / 2) a c
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.halfPerimeterJoin_of_jordanArcDatum`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L216)

```lean
theorem halfPerimeterJoin_of_jordanArcDatum {f : ℂ → ℂ} {R : ℝ} {U : Set ℂ}
    (h : ∀ H : ℝ, μH[(1 : ℝ)] (frontier U) ≤ ENNReal.ofReal H →
      ∀ p ∈ U, ∀ q ∈ frontier U, JordanArcDatum f R H p q) :
    HalfPerimeterJoin f R U
```

where [`HalfPerimeterJoin`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L183) is

```lean
def HalfPerimeterJoin (f : ℂ → ℂ) (R : ℝ) (U : Set ℂ) : Prop :=
  ∀ H : ℝ, μH[(1 : ℝ)] (frontier U) ≤ ENNReal.ofReal H →
    ∀ p ∈ U, ∀ q ∈ frontier U, ConnectedAtMost f R (H / 2) p q
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.half_perimeter_selection`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L166)

```lean
theorem half_perimeter_selection {du dv lenA1 lenA2 lenA' uv H : ℝ}
    (hsplit : du + dv = uv) (hchord : uv ≤ lenA')
    (htotal : lenA1 + lenA2 + lenA' ≤ H) :
    min (du + lenA1) (dv + lenA2) ≤ H / 2
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.connectedAtMost_trans`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L86)

```lean
theorem connectedAtMost_trans {f : ℂ → ℂ} {R L₁ L₂ : ℝ} {a c b : ℂ}
    (h₁ : ConnectedAtMost f R L₁ a c) (h₂ : ConnectedAtMost f R L₂ c b)
    (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) :
    ConnectedAtMost f R (L₁ + L₂) a b
```

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.connectedAtMost_symm`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L62)

```lean
theorem connectedAtMost_symm {f : ℂ → ℂ} {R L : ℝ} {a b : ℂ}
    (h : ConnectedAtMost f R L a b) : ConnectedAtMost f R L b a
```

where [`ConnectedAtMost`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L24) is

```lean
def ConnectedAtMost (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ ≤ R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L
```

8. [`ErdosProblems.Erdos1041.PaperCompleteR21.connectedAtMost_mono`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L56)

```lean
theorem connectedAtMost_mono {f : ℂ → ℂ} {R L L' : ℝ} {a b : ℂ}
    (h : ConnectedAtMost f R L a b) (hLL : L ≤ L') : ConnectedAtMost f R L' a b
```

where [`ConnectedAtMost`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L24) is

```lean
def ConnectedAtMost (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ ≤ R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L
```

The assumed input [`SubcriticalSplitExists`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/SubcriticalPerimeterPath.lean#L230) is

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

## Theorem 5.1 (the cubic case), page 20

> *Let $`f(z)=\prod_{j=1}^{3}(z-z_j)`$ with $`|z_j|<1`$, the roots listed with multiplicity. Then two listed root occurrences are joined inside $`\{|f|<1\}`$ by a polygonal path of length strictly below $`2`$. If $`f`$ is squarefree the two are distinct.*

The Lean declaration below states a result at least as strong as this one. The Lean statement has the same hypotheses and conclusion as the printed one.

[`ErdosProblems.Erdos1041.PaperCubicCompletion.cubic_paper_complete`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCubicCompletion.lean#L297)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cubic_paper_complete` | [E1041_02/Challenge.lean, line 182](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_02/Challenge.lean#L182) | [CubicPath.lean, line 18](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_02/CubicPath.lean#L18) | [E1041_02](../evidence/comparator/replay-35882032091/receipt-E1041_02.json) |

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

## Theorem 6.1 (separation of one simple critical value), page 21

> *Let $`P`$ be a polynomial of degree $`n\ge3`$ whose leading coefficient has modulus one, with
> ``` math
> P(0)=1,\qquad P'(0)=0,\qquad P''(0)\ne0.
> ```
> Fix $`w_0\in[0,1]`$ and $`S>\max(w_0,1-w_0)`$. Suppose every other critical point $`d\ne0`$ satisfies
> ``` math
> |P(d)-w_0|\ge S.                                      \tag{4}
> ```
> Put $`p=w_0(1-w_0)`$. The two local solutions of $`P(Z(\xi))=1-\xi^2`$, $`Z(0)=0`$, continue along the real segment to one injective root-to-root connector $`\Gamma`$. Its endpoints are distinct roots, $`\Gamma\subseteq\{|P|\le1\}`$, and
> ``` math
> \begin{equation*}
> \label{eq:disk-family-length}
>  \operatorname{length}(\Gamma)^2
>  \le 2\Bigl(\frac{S}{n-1}\Bigr)^{2/n}
>  \log\!\frac{S^2+S+p}{S^2-S+p}.                       \tag{5}
> \end{equation*}
> ```
> Consequently the connector is shorter than $`2`$ whenever
> ``` math
> \begin{equation*}
> \label{eq:disk-family-coefficient}
>  \Bigl(\frac{S}{n-1}\Bigr)^{2/n}
>  \log\!\frac{S^2+S+p}{S^2-S+p}<2.                    \tag{6}
> \end{equation*}
> ```*

The Lean proof assumes the connector and area construction that this proof produces. Lean takes this input as a hypothesis (`DiscSepBergmanArea`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_separation_long`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L344)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_squared_length_le`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L305)

```lean
theorem discSep_squared_length_le {n : ℕ} {w₀ S L area : ℝ}
    (hw₀ : 0 ≤ w₀) (hS : max w₀ (1 - w₀) < S)
    (hBergman : L ^ 2 ≤ 2 / Real.pi *
      Real.log ((1 + discSepQsq S (w₀ * (1 - w₀))) /
        (1 - discSepQsq S (w₀ * (1 - w₀)))) * area)
    (hArea : area ≤ Real.pi * (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ))) :
    L ^ 2 ≤ 2 * discSepCoefficient n S (w₀ * (1 - w₀))
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_length_lt_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L334)

```lean
theorem discSep_length_lt_two {M L : ℝ} (hL : 0 ≤ L) (hbound : L ^ 2 ≤ 2 * M)
    (hM : M < 2) : L < 2
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_bergman_factor`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L179)

```lean
theorem discSep_bergman_factor {S p : ℝ} (hS : 0 < S) (hden : 0 < S ^ 2 - S + p) :
    (1 + discSepQsq S p) / (1 - discSepQsq S p)
      = (S ^ 2 + S + p) / (S ^ 2 - S + p)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_target_starShaped`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L209)

```lean
theorem discSep_target_starShaped {a S : ℝ} (ha : 0 ≤ a) (haS : a < S) {ξ : ℂ}
    (hξ : ‖ξ ^ 2 - (a : ℂ)‖ < S) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((t : ℂ) * ξ) ^ 2 - (a : ℂ)‖ < S
```

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_mobius_norm_lt`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L238)

```lean
theorem discSep_mobius_norm_lt {a S : ℝ} (ha : 0 ≤ a) (haS : a < S) {w : ℂ}
    (hw : ‖w - (a : ℂ)‖ < S) :
    ‖(S : ℂ) * w‖ < ‖(S : ℂ) ^ 2 + (a : ℂ) * w - (a : ℂ) ^ 2‖
```

The assumed input [`DiscSepBergmanArea`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L293) is

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

## Corollary 6.2 (uniform radius $`4/3`$), page 24

> *Inequality <a href="#eq:disk-family-coefficient" data-reference-type="eqref" data-reference="eq:disk-family-coefficient">[eq:disk-family-coefficient]</a> holds for every $`n\ge3`$, every $`w_0\in[0,1]`$, and every $`4/3\le S\le2`$. Thus, if $`f`$ is monic with roots in the open unit disc, $`c`$ is a simple critical point with $`v=f(c)\ne0`$ and $`|v|<1`$, and
> ``` math
> \left|\frac{f(d)}v-w_0\right|\ge\frac43
> ```
> for every other critical point $`d`$, then two roots of $`f`$ are joined inside $`\{|f|<1\}`$ by a curve of length strictly below $`2`$.*

The Lean proof assumes the connector and area construction in the proof of Theorem 6.1. Lean takes this input as a hypothesis (`DiscSepBergmanArea`); it is not proved in Lean.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSepCoefficient_lt_two`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L645)

```lean
theorem discSepCoefficient_lt_two {n : ℕ} (hn : 3 ≤ n) {S p : ℝ}
    (hS : 4 / 3 ≤ S) (hS2 : S ≤ 2) (hp0 : 0 ≤ p) :
    discSepCoefficient n S p < 2
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_uniform_radius`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L702)

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

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_ratio_le_branch`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L629)

```lean
theorem discSep_ratio_le_branch {S p : ℝ} (hS : 1 < S) (hp : 0 ≤ p) :
    (S ^ 2 + S + p) / (S ^ 2 - S + p) ≤ (S + 1) / (S - 1)
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.discSep_branch_le_seven`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L637)

```lean
theorem discSep_branch_le_seven {S : ℝ} (hS : 4 / 3 ≤ S) : (S + 1) / (S - 1) ≤ 7
```

The assumed input [`DiscSepBergmanArea`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CriticalValueSeparationTransport.lean#L293) is

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

<a id="prop-sharp-collinear-chebyshev-comparator"></a>

## Theorem 7.1 (Chebyshev comparison), page 27

> *Let $`m\ge0`$, let $`p\in\mathbb R[X]`$ be monic of degree $`m+2`$, and let
> ``` math
> -1<c_0<\cdots<c_m<1,\qquad |c_i|\le1.
> ```
> Suppose $`p(-1)=p(1)=0`$ and $`p(c_i)p(c_{i+1})<0`$ for $`0\le i<m`$. Then
> ``` math
> \min_{0\le i\le m}|p(c_i)|\le C_{m+2}.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/SharpCollinearChebyshev.lean#L133)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `exists_peak_le_comparisonBound` | [E1041_03/Challenge.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L42) | [PaperStatementsI.lean, line 18](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsI.lean#L18) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-sharp-collinear-diameter"></a>

## Theorem 7.2 (a sharp bound for collinear roots), page 27

> *Let $`f`$ be a monic polynomial of degree $`n\ge2`$ whose zero occurrences are collinear, and let $`D`$ be their diameter. Some two adjacent zero occurrences are joined by a segment of length at most $`D`$ on which
> ``` math
> |f(z)|\le
>  \frac{(D/2)^n}{2^{n-1}\cos^n(\pi/(2n))}.          \tag{9}
> ```
> The constant in *(9)* is best possible in every degree. Equality is attained by affine images of the zeros of $`T_n`$ whose extreme zeros have distance $`D`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L367)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter_monic`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L967)

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

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.exists_collinear_factorisation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L928)

```lean
theorem exists_collinear_factorisation (base dir : ℂ) :
    ∀ (n : ℕ) (f : ℂ[X]), f.IsMonicOfDegree n →
      (∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) →
      ∃ y : Fin n → ℝ, f = ∏ k : Fin n, (X - C (base + dir * (y k : ℂ)))
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.exists_gap_le_comparisonBound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L212)

```lean
theorem exists_gap_le_comparisonBound {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1) (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤ comparisonBound (m + 2)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_equality_attained`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L836)

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

6. [`ErdosProblems.Erdos1041.PaperCompleteR21.chebyshev_configuration_attains`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L769)

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

7. [`ErdosProblems.Erdos1041.PaperCompleteR21.monicScaledChebyshev_eq_prod`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L684)

```lean
theorem monicScaledChebyshev_eq_prod (m : ℕ) :
    monicScaledChebyshev (m + 2) = ∏ i : Fin (m + 2), (X - C (chebNode m i))
```

8. [`ErdosProblems.Erdos1041.PaperCompleteR21.collinearDiameterBound_sharpConstant`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L871)

```lean
theorem collinearDiameterBound_sharpConstant {n : ℕ} (hn : 2 ≤ n) :
    CollinearDiameterBound n
      (1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n))
```

9. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharpConstant_le_of_collinearDiameterBound`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L878)

```lean
theorem sharpConstant_le_of_collinearDiameterBound {n : ℕ} (hn : 2 ≤ n) {K : ℝ}
    (hK : CollinearDiameterBound n K) :
    1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) ≤ K
```

<a id="thm-sharp-collinear-diameter-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `sharp_collinear_root_diameter` | [E1041_03/Challenge.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L86) | [PaperStatementsE.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L31) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `sharp_collinear_root_diameter_monic` | [E1041_03/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L99) | [PaperStatementsE.lean, line 43](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L43) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `exists_collinear_factorisation` | [E1041_03/Challenge.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L75) | [PaperStatementsE.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L22) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `exists_gap_le_comparisonBound` | [E1041_03/Challenge.lean, line 141](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L141) | [PaperStatementsS.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsS.lean#L31) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `sharp_collinear_equality_attained` | [E1041_03/Challenge.lean, line 151](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L151) | [PaperStatementsS.lean, line 39](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsS.lean#L39) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `chebyshev_configuration_attains` | [E1041_03/Challenge.lean, line 129](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L129) | [PaperStatementsS.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsS.lean#L20) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `monicScaledChebyshev_eq_prod` | [E1041_03/Challenge.lean, line 147](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L147) | [PaperStatementsS.lean, line 36](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsS.lean#L36) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `collinearDiameterBound_sharpConstant` | [E1041_03/Challenge.lean, line 70](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L70) | [PaperStatementsE.lean, line 18](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L18) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `sharpConstant_le_of_collinearDiameterBound` | [E1041_03/Challenge.lean, line 81](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L81) | [PaperStatementsE.lean, line 27](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L27) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-collinear-erdos-1041"></a>

## Corollary 7.3 (collinear Erdős case), page 28

> *If the zero occurrences of a monic polynomial of degree $`n\ge2`$ lie on one line in the open unit disc, two of them are joined by a curve of length strictly below $`2`$ inside $`\{|f|<1\}`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.collinear_erdos_1041`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L515)

```lean
theorem collinear_erdos_1041 {n : ℕ} (hn : 2 ≤ n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (y : Fin n → ℝ) (f : ℂ[X]) (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ))))
    (hdisc : ∀ k : Fin n, ‖base + dir * (y k : ℂ)‖ < 1) :
    ∃ j k : Fin n, j ≠ k ∧
      ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow f.eval 1 2
        (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))
```

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.collinear_erdos_1041_monic`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L984)

```lean
theorem collinear_erdos_1041_monic {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ))
    (hdisc : ∀ z ∈ f.roots, ‖z‖ < 1) :
    ∃ a b : ℂ, a ∈ f.roots ∧ b ∈ f.roots ∧
      ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow f.eval 1 2 a b
```

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.exists_collinear_factorisation`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L928)

```lean
theorem exists_collinear_factorisation (base dir : ℂ) :
    ∀ (n : ℕ) (f : ℂ[X]), f.IsMonicOfDegree n →
      (∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) →
      ∃ y : Fin n → ℝ, f = ∏ k : Fin n, (X - C (base + dir * (y k : ℂ)))
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/CollinearDiameterWhole.lean#L367)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `collinear_erdos_1041` | [E1041_03/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L181) | [PaperStatementsT.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsT.lean#L21) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `collinear_erdos_1041_monic` | [E1041_03/Challenge.lean, line 189](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L189) | [PaperStatementsT.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsT.lean#L28) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `exists_collinear_factorisation` | [E1041_03/Challenge.lean, line 75](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L75) | [PaperStatementsE.lean, line 22](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L22) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |
| `sharp_collinear_root_diameter` | [E1041_03/Challenge.lean, line 86](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_03/Challenge.lean#L86) | [PaperStatementsE.lean, line 31](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_03/PaperStatementsE.lean#L31) | [E1041_03](../evidence/comparator/replay-35882032091/receipt-E1041_03.json) |

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

## Theorem 7.4 (a consequence of three moment identities), page 29

> *Suppose
> ``` math
> \sum_{i=0}^4x_i=-r,\qquad
>  \sum_{i=0}^4(2x_i^2-s_i)=r^2,\qquad
>  \sum_{i=0}^4(4x_i^3-3s_ix_i)=-r^3.              \tag{10}
> ```
> Then at least one of the ten pairs $`0\le i<j\le4`$ satisfies $`E_i<1`$ and $`E_j<1`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.primitiveInterior_exists_two_tailEnergy_lt_one`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PrimitiveQuinticInteriorTail.lean#L272)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `primitiveInterior_exists_two_tailEnergy_lt_one` | [E1041_04/Challenge.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L54) | [PaperStatementsM.lean, line 14](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsM.lean#L14) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-primitive-quintic-two-tail"></a>

## Theorem 7.5 (a quintic with two missing coefficients), page 29

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

1. [`ErdosProblems.Erdos1041.PaperCompleteR21.primitive_quintic_two_tail`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/PrimitiveQuinticClosedDisc.lean#L260)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR21.primitive_quintic_two_tail_of_polynomial`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/PrimitiveQuinticClosedDisc.lean#L313)

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

3. [`ErdosProblems.Erdos1041.PaperCompleteR21.two_tails_closedDisc_of_ne_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/PrimitiveQuinticClosedDisc.lean#L93)

```lean
theorem two_tails_closedDisc_of_ne_zero {a b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z)
    (hw : ∀ i, ‖w i‖ ≤ 1) (ha : a ≠ 0) :
    ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1
```

4. [`ErdosProblems.Erdos1041.PaperCompleteR21.tail_le_one_and_eq_iff_of_leading_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/PrimitiveQuinticClosedDisc.lean#L199)

```lean
theorem tail_le_one_and_eq_iff_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (hw : ∀ i, ‖w i‖ ≤ 1)
    (i : Fin 5) :
    ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1)
```

5. [`ErdosProblems.Erdos1041.PaperCompleteR21.tail_norm_of_leading_zero`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR21/PrimitiveQuinticClosedDisc.lean#L82)

```lean
theorem tail_norm_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (i : Fin 5) :
    ‖b * w i + c‖ = ‖w i‖ ^ 5
```

<a id="thm-primitive-quintic-two-tail-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `primitive_quintic_two_tail` | [E1041_04/Challenge.lean, line 117](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L117) | [PaperStatementsU.lean, line 24](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsU.lean#L24) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |
| `primitive_quintic_two_tail_of_polynomial` | [E1041_04/Challenge.lean, line 134](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L134) | [PaperStatementsU.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsU.lean#L40) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |
| `two_tails_closedDisc_of_ne_zero` | [E1041_04/Challenge.lean, line 171](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L171) | [PaperStatementsV.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsV.lean#L30) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |
| `tail_le_one_and_eq_iff_of_leading_zero` | [E1041_04/Challenge.lean, line 160](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L160) | [PaperStatementsV.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsV.lean#L21) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |
| `tail_norm_of_leading_zero` | [E1041_04/Challenge.lean, line 166](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L166) | [PaperStatementsV.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsV.lean#L26) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-cubic-safe-root-spoke"></a>

## Theorem 7.6 (a contained radial segment for a cubic), page 31

> *If $`r,s,v\in\mathbb C`$ have modulus below one, at least one $`u\in\{r,s,v\}`$ satisfies
> ``` math
> \left|(tu-r)(tu-s)(tu-v)\right|\le1
>  \qquad(0\le t\le1).
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.cubic_has_safe_root_spoke`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/CubicQuotientFiberCase.lean#L161)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `cubic_has_safe_root_spoke` | [E1041_04/Challenge.lean, line 181](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L181) | [PaperStatementsJ.lean, line 16](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsJ.lean#L16) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="thm-translated-cubic-quotient-fibres"></a>

## Theorem 7.7 (a cubic composed with a power map), page 31

> *Let $`q\ge2`$, $`h\in\mathbb C`$, $`P`$ be monic cubic, and
> ``` math
> f(z)=P((z-h)^q).
> ```
> If every zero of $`f`$ lies in the open unit disc and $`f`$ has at least two distinct zero values, then two zeros are joined through $`h`$ by a two-segment path of length below $`2`$ inside $`\{|f|<1\}`$. Equivalently this closes the coefficient family
> ``` math
> (z-h)^{3q}+A(z-h)^{2q}+B(z-h)^q+C
> ```
> in every degree $`3q\ge6`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperCubicFibres.complete_translated_cubic_quotient_fibres`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCubicFibres.lean#L240)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `complete_translated_cubic_quotient_fibres` | [E1041_02/Challenge.lean, line 212](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_02/Challenge.lean#L212) | [CubicPath.lean, line 54](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_02/CubicPath.lean#L54) | [E1041_02](../evidence/comparator/replay-35882032091/receipt-E1041_02.json) |

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

<a id="res-critical-value-budget"></a>

## Theorem 8.1 (a mean bound for critical values), page 41

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

The Lean declarations below together state a result at least as strong as this one. The Lean statement has the same hypotheses and conclusion as the printed one.

1. [`ErdosProblems.Erdos1041.PaperCompleteR20.critical_value_three_budgets`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR20/CriticalMeanWhole.lean#L14)

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

2. [`ErdosProblems.Erdos1041.PaperCompleteR20.critical_value_three_budgets_sharp`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR20/CriticalMeanWhole.lean#L36)

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

<a id="res-critical-value-budget-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `critical_value_three_budgets` | [E1041_04/Challenge.lean, line 199](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L199) | [PaperStatementsO.lean, line 21](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsO.lean#L21) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |
| `critical_value_three_budgets_sharp` | [E1041_04/Challenge.lean, line 221](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L221) | [PaperStatementsP.lean, line 23](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsP.lean#L23) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-reflected-critical-value"></a>

## Lemma 8.2 (reflected-derivative bound), page 42

> *If $`f`$ is monic of degree $`n\ge2`$ with roots in the closed unit disk, and $`c_1,\ldots,c_{n-1}`$ list its critical points with multiplicity, then
> ``` math
> \begin{equation}
> \label{eq:critical-reflected-product}
>  |f(c_j)|\le\prod_{k=1}^{n-1}|1-\overline{c_j}c_k|.
> \end{equation}
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.PaperReflectedCompletion.reflected_critical_value`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperReflectedCompletion.lean#L254)

```lean
theorem reflected_critical_value : ReflectedCriticalValue
```

where [`ReflectedCriticalValue`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperAnalyticTargets.lean#L95) is

```lean
def ReflectedCriticalValue : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ), 2 ≤ n → p.Monic →
    p.natDegree = n → RootsInClosedDisc p 0 1 → CriticalEnumeration p c →
      ∀ j, ‖p.eval (c j)‖ ≤ ∏ k, ‖1 - conj (c k) * c j‖
```

<a id="res-reflected-critical-value-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `reflected_critical_value` | [E1041_04/Challenge.lean, line 250](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L250) | [PaperStatementsW.lean, line 25](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsW.lean#L25) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-value"></a>

## Theorem 9.1 (value equation), page 55

> *Let $`f`$ be a polynomial and $`z:I\to\mathbb C`$ a differentiable curve on an interval $`I`$, with $`f'(z(t))\ne0`$ and $`z'(t)=-f(z(t))/f'(z(t))`$ throughout $`I`$. For $`w=f\circ z`$, one has $`w'(t)=-w(t)`$ on $`I`$.*

The Lean declaration below states a result at least as strong as this one. The Lean statement allows any function $f$ with a complex derivative at each $z(t)$, $t\in I$, of which a polynomial is a case, and adds the integrated form $f(z(t))=e^{-(t-t_0)}f(z(t_0))$ for $t,t_0\in I$.

[`ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_value_whole`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR20/NewtonRealTime.lean#L52)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `newton_real_value_whole` | [E1041_04/Challenge.lean, line 275](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L275) | [PaperStatementsQ.lean, line 40](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsQ.lean#L40) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-ray"></a>

## Corollary 9.2 (ray separation), page 56

> *Let $`a<b`$ and let the value trajectory $`t\mapsto f(z(t))`$ be continuous on $`[a,b]`$. Assume the Newton equation and $`f'(z(t))\ne0`$ on $`(a,b)`$ only. Then
> ``` math
> f(z(b))=e^{a-b}f(z(a)).
> ```
> If these endpoint values are nonzero, they lie on one positive ray. Therefore critical points with values on distinct positive rays cannot be endpoints of such a finite connection. The trajectory in the $`z`$ plane need not be radial.*

The Lean declaration below states a result at least as strong as this one. The Lean statement allows any function $f$ with a complex derivative at each $z(t)$, $a<t<b$, of which a polynomial is a case. It gives $f(z(b))=e^{a-b}f(z(a))$ and that the two endpoint values lie on one positive ray, which excludes endpoints whose values lie on distinct positive rays.

[`ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_endpoint_whole`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/PaperCompleteR20/NewtonRealTime.lean#L69)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `newton_real_endpoint_whole` | [E1041_04/Challenge.lean, line 264](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L264) | [PaperStatementsQ.lean, line 30](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsQ.lean#L30) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-locus"></a>

## Theorem 10.1 (ray-collision locus), page 57

> *Let $`a\ne b`$ be complex. Every common translation $`\beta`$ for which $`a+\beta`$ and $`b+\beta`$ lie on the same positive ray has the form
> ``` math
> \beta=\frac{ra-b}{1-r},
>   \qquad r\in\mathbb{R}_{>0},\ r\ne1 .
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos1041.translated_samePositiveRay_parameterization`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos1041/NewtonFlowRaySeparation.lean#L107)

```lean
theorem translated_samePositiveRay_parameterization
    {a b shift : ℂ} (hab : a ≠ b)
    (hray : SamePositiveRay (a + shift) (b + shift)) :
    ∃ r : ℝ, 0 < r ∧ r ≠ 1 ∧
      shift = ((r : ℂ) * a - b) / ((1 - r : ℝ) : ℂ)
```

<a id="res-locus-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `translated_samePositiveRay_parameterization` | [E1041_04/Challenge.lean, line 294](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E1041_04/Challenge.lean#L294) | [PaperStatementsN.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E1041_04/PaperStatementsN.lean#L20) | [E1041_04](../evidence/comparator/replay-35882032091/receipt-E1041_04.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-attachment-aware-reeb"></a>

## Theorem 11.1 (inverse sheets with distinct critical-value arguments), page 59

> *Let $`f`$ be monic, and let $`U`$ be a component of $`\{|f|<1\}`$ containing $`k\ge2`$ roots, counted with multiplicity. Suppose every critical point of $`f`$ in $`U`$ is simple, its critical value is nonzero, and these critical values have pairwise distinct arguments and pairwise distinct moduli. All preimages and sheets below are taken inside $`U`$, and only critical points in $`U`$ determine the cuts. Then:*
> 
> 1.  *$`-\log|f|:U\mathbin{\backslash}f^{-1}(0)\to(0,\infty)`$ is a proper excellent Morse function, with exactly $`k-1`$ nondegenerate saddles;*
> 
> 2.  *cutting $`\mathbb D\smallsetminus\{0\}`$ along the critical-value rays decomposes its preimage in $`U`$ into conformal strips;*
> 
> 3.  *cutting each ray only from its critical value to the unit circle gives $`k`$ conformal sheets, one per root, whose critical transpositions form a tree;*
> 
> 4.  *for each critical point $`c\in U`$, the two inverse lifts of $`[0,f(c)]`$ join two roots through $`c`$ inside $`U\cap\{|f|\le|f(c)|\}`$, and the union of these arcs is an embedded geometric realisation of that tree.*
> 
> *Small neighbourhoods of the saddles can be chosen with diameter $`O(\sqrt\delta)`$ at value radius $`\delta`$.*

**No Lean proof of the whole statement.** In Lean, the ray-disjointness, level-separation and saddle-scale steps of the proof are checked, and the Morse, monodromy and strip statements are not.
