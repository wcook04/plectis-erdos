# Formal evidence: Reciprocal Mersenne Subseries, Section 13

Part of the [evidence record](../erdos257-mersenne-reasoning-surface.md) of the paper [erdos257-mersenne-reasoning-surface.pdf](../../paper/257/erdos257-mersenne-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="thm-257-logarithmic-counterexample"></a>

## Theorem 13.1 (arithmetic logarithmic counterexample), page 138

> *For every integer $`H\ge2`$ and every real $`A_0\ge0`$, there are a squarefree positive integer $`L`$ and a finite nonempty set $`F`$ of distinct squarefree positive integers such that
> ``` math
> \min F>\max\{L,A_0\},\qquad
>  \kappa_1(F;1)\le\frac{30\log2}{H},\qquad
>  \mathbb P_L(U_F>1)\ge1-e^{-1}.
> ```
> For these $`F,L`$, some $`R\ge0`$ satisfies $`\mathscr D_{L;R,L}\mathbf1_{\{U_F>1\}}>1/2`$. Consequently, no absolute constant $`C`$ satisfies
> ``` math
> \begin{equation*}
>  \mathscr D_{L;R,M}\mathbf1_{\{U_F>t\}}
>  \le C(1+L/M)\kappa_1(F;t)
>  \tag{E}
> \end{equation*}
> ```
> uniformly in finite $`F`$, positive integers $`L,M`$, integers $`R\ge0`$, and $`0<t\le1`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.arithmetic_logarithmic_counterexample`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCounterexampleAssembly.lean#L1645)

```lean
theorem arithmetic_logarithmic_counterexample (H : ℕ) (hH : 2 ≤ H) (A₀ : ℝ) (hA₀ : 0 ≤ A₀) :
    ∃ (L : ℕ) (F : Finset ℕ),
      0 < L ∧ Squarefree L ∧ F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      (∀ a ∈ F, 0 < a ∧ Squarefree a) ∧
      (∀ a ∈ F, max (L : ℝ) A₀ < (a : ℝ)) ∧
      L ∣ F.lcm id ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ) ∧
      1 - Real.exp (-1) ≤ condExceedProb F L ∧
      ∃ R : ℕ, 1 / 2 < dyadicMean L R L (exceedInd F)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.no_absolute_dyadic_kappaOne_constant`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCounterexampleAssembly.lean#L1859)

```lean
theorem no_absolute_dyadic_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ (F : Finset ℕ), F.Nonempty → (0 : ℕ) ∉ F →
      ∀ (L M : ℕ), 0 < L → 0 < M → ∀ (R : ℕ) (t : ℝ), 0 < t → t ≤ 1 →
        dyadicMean L R M (fun N => if t < framePotential F N then (1 : ℝ) else 0)
          ≤ C * (1 + (L : ℝ) / (M : ℝ)) * kappaOne F t
```

<a id="thm-257-logarithmic-counterexample-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `arithmetic_logarithmic_counterexample` | [E257_38/Challenge.lean, line 194](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L194) | [PaperStatementsAC.lean, line 42](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsAC.lean#L42) | [E257_38](../../evidence/comparator/replay-35882032091/receipt-E257_38.json) |
| `no_absolute_dyadic_kappaOne_constant` | [E257_38/Challenge.lean, line 211](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L211) | [PaperStatementsAC.lean, line 58](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsAC.lean#L58) | [E257_38](../../evidence/comparator/replay-35882032091/receipt-E257_38.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-257-logarithmic-separation"></a>

## Corollary 13.2 (finite-functional separation), page 140

> *For every finite nonempty $`F`$, with $`Q=\operatorname{lcm}(F)`$,
> ``` math
> \begin{equation}
>  K_*(F)\ge\max_{\ell\mid Q}
>    \mathbb P\bigl(U_F(N)>1\mid\ell\mid N\bigr),
>  \label{eq:257-arithmetic-cover-lower}
> \end{equation}
> ```
> where $`N`$ is uniform modulo $`Q`$. The supports of Theorem 13.1 satisfy $`K_*(F)\ge1-e^{-1}`$ and $`\kappa_1(F;1)\le30\log2/H`$. In particular, no absolute $`C`$ gives $`K_*(F)\le C\kappa_1(F;1)`$ for all finite nonempty $`F`$, even after all covering sets, exponents, coefficients and positive weights have been optimised.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos257.PaperCompleteR21.sup_condExceedProb_le_paperCoverCost`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCoverLowerBoundPaperForm.lean#L40)

```lean
theorem sup_condExceedProb_le_paperCoverCost (F : Finset ℕ) (hF : 0 ∉ F)
    (hne : (F.lcm id).divisors.Nonempty) :
    (F.lcm id).divisors.sup' hne (fun ℓ => condExceedProb F ℓ)
      ≤ paperCoverCost (F : Set ℕ)
```

2. [`ErdosProblems.Erdos257.PaperCompleteR21.exists_support_paperCoverCost_ge`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCounterexampleAssembly.lean#L1900)

```lean
theorem exists_support_paperCoverCost_ge (H : ℕ) (hH : 2 ≤ H) :
    ∃ F : Finset ℕ, F.Nonempty ∧ (0 : ℕ) ∉ F ∧
      1 - Real.exp (-1) ≤ paperCoverCost (F : Set ℕ) ∧
      kappaOne F 1 ≤ 30 * Real.log 2 / (H : ℝ)
```

3. [`ErdosProblems.Erdos257.PaperCompleteR21.no_absolute_paperCoverCost_kappaOne_constant`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/ArithmeticCounterexampleAssembly.lean#L1912)

```lean
theorem no_absolute_paperCoverCost_kappaOne_constant :
    ¬ ∃ C : ℝ, ∀ F : Finset ℕ, F.Nonempty → (0 : ℕ) ∉ F →
      paperCoverCost (F : Set ℕ) ≤ C * kappaOne F 1
```

<a id="cor-257-logarithmic-separation-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `sup_condExceedProb_le_paperCoverCost` | [E257_38/Challenge.lean, line 283](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L283) | [PaperStructuresBS.lean, line 208](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStructuresBS.lean#L208) | [E257_38](../../evidence/comparator/replay-35882032091/receipt-E257_38.json) |
| `exists_support_paperCoverCost_ge` | [E257_38/Challenge.lean, line 272](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L272) | [PaperStructuresBS.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStructuresBS.lean#L195) | [E257_38](../../evidence/comparator/replay-35882032091/receipt-E257_38.json) |
| `no_absolute_paperCoverCost_kappaOne_constant` | [E257_38/Challenge.lean, line 278](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L278) | [PaperStructuresBS.lean, line 202](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStructuresBS.lean#L202) | [E257_38](../../evidence/comparator/replay-35882032091/receipt-E257_38.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="prop-257-logarithmic-initial-interval"></a>

## Proposition 13.3 (ordinary initial intervals), page 141

> *For every finite nonempty $`F`$, integer $`X\ge1`$, and $`0<t\le1`$,
> ``` math
> \frac1X\#\{1\le N\le X:U_F(N)>t\}
>  \le\frac{2}{\log(4/3)}\kappa_1(F;t).
> ```*

The Lean declaration below states this result or one that implies it. The Lean statement has the same hypotheses and conclusion as the printed one, with $F$ a finite nonempty set of positive integers, $U_F(N)=\sum_{a\in F}2^{N\bmod a}/(2^a-1)$ and $\kappa_1(F;t)$ the infimum of the same linear programme.

[`ErdosProblems.Erdos257.PaperCompleteR21.logarithmic_initial_interval`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos257/PaperCompleteR21/LogarithmicInitialInterval.lean#L491)

```lean
theorem logarithmic_initial_interval (F : Finset ℕ) (hFne : F.Nonempty) (hF : 0 ∉ F)
    (X : ℕ) (hX : 1 ≤ X) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ((((Finset.Icc 1 X).filter (fun N => t < framePotential F N)).card : ℝ)) / (X : ℝ)
      ≤ 2 / Real.log (4 / 3 : ℝ) * kappaOne F t
```

<a id="prop-257-logarithmic-initial-interval-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `logarithmic_initial_interval` | [E257_38/Challenge.lean, line 205](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E257_38/Challenge.lean#L205) | [PaperStatementsAC.lean, line 53](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E257_38/PaperStatementsAC.lean#L53) | [E257_38](../../evidence/comparator/replay-35882032091/receipt-E257_38.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
