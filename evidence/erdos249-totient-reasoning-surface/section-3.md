# Formal evidence: The Binary Totient Series, Section 3

Part of the [evidence record](../erdos249-totient-reasoning-surface.md) of the paper [erdos249-totient-reasoning-surface.pdf](../../paper/249/erdos249-totient-reasoning-surface.pdf), which explains what the Lean and Comparator checks establish.

<a id="thm-goodbasegap"></a>

## Theorem 3.5 (Irrationality from one bound on the good indices), page 18

> 1.  *Suppose that for every $`h\ge1`$ and every $`A`$ there are $`X`$, $`L`$ with $`16(2X+h+L+2)\le2^L`$ and a nonempty finite set $`T`$ of integers in $`[A,2X)`$ with
>     ``` math
>     \sum_{N\in T}\operatorname{Re}E(h,N,L)\le\tfrac{9}{10}\,\#T.
>     ```
>     Then $`S\notin\mathbb{Q}`$ ([`irrational_totient_series_of_support_gap`](https://github.com/wcook04/plectis-erdos/blob/24edbddbe2bd68e920327a701aad0b9dd0d69675/lean/ErdosProblems/ArgumentGraph/Results/Erdos249Endpoint.lean#L44)).*
> 
> 2.  *Take $`s=26`$, $`\eta=1/1000`$ and $`L=L(X)`$. Suppose that for every $`h\ge1`$ there are arbitrarily large $`X`$ with
>     ``` math
>     \operatorname{Re}\sum_{N\in\mathcal G}E\bigl(h,N,L(X)\bigr)
>        \le\tfrac{603}{1000}X.
>     ```
>     Then $`S\notin\mathbb{Q}`$ ([`irrational_totient_series_of_goodBase_gap`](https://github.com/wcook04/plectis-erdos/blob/24edbddbe2bd68e920327a701aad0b9dd0d69675/lean/ErdosProblems/ArgumentGraph/Results/Erdos249Endpoint.lean#L100)).*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_support_gap`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/ArgumentGraph/Results/Erdos249Endpoint.lean#L44)

```lean
theorem irrational_totient_series_of_support_gap
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧ T.Nonempty ∧ (∀ N ∈ T, A ≤ N ∧ N < 2 * X) ∧
      (∑ N ∈ T, windowFirstCos h N L) ≤ (9 / 10 : ℝ) * T.card) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

2. [`ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/ArgumentGraph/Results/Erdos249Endpoint.lean#L100)

```lean
theorem irrational_totient_series_of_goodBase_gap
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re ≤ (603 / 1000 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
```

<a id="thm-goodbasegap-comparator"></a>

**Comparator:** not yet compared.
