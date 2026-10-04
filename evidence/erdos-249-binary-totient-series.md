# Formal evidence: Integral Relations among Totient Sections

This record belongs to the paper [erdos-249-binary-totient-series.pdf](../paper/249/erdos-249-binary-totient-series.pdf). For every result it lists the Lean declarations that state it, and the recorded Comparator check where there is one. The paper's verification concordance uses this result mapping.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`436f55ebdafa`](https://github.com/wcook04/plectis-erdos/tree/436f55ebdafa67e4af0fff79f621c13f2ded12bf) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35935225572](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35935225572) at corpus commit [`cc7e541cf208`](https://github.com/wcook04/plectis-erdos-lean/tree/cc7e541cf2081c6fef5a5e377d52e365e33b01eb) (tag `paper-evidence-2026-09-24`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 2 results: 2 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 2 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below. Comparator checks separately declared statements, the axiom budget and kernel acceptance; it does not establish novelty, significance or peer review.

<a id="thm-kkernelrank"></a>

## Theorem 1.1 (A basis through each finite level), page 2

> *Let $`k\ge2`$ and $`e\ge1`$ be integers, write $`F^{(k)}_{j,r}(n)=\varphi(k^jn+r)`$, and put
> ``` math
> V_{k,e}=\operatorname{span}_{\mathbb{Q}}
>  \{\,F^{(k)}_{j,r}:0\le j\le e,\ 0\le r<k^j\,\}.
> ```
> Then $`\dim_{\mathbb{Q}}V_{k,e}=k^e+1`$, and
> ``` math
> \mathcal B_{k,e}
>  =\{F^{(k)}_{0,0},F^{(k)}_{1,0}\}
>  \cup\{\,F^{(k)}_{j,r}:1\le j\le e,\ 1\le r<k^j,\ k\nmid r\,\}
> ```
> is a basis. Every omitted section reduces to a basis element by an explicit scalar: $`F^{(k)}_{j,0}=k^{j-1}F^{(k)}_{1,0}`$ for $`j\ge1`$, and if $`r=k^tu`$ with $`t=\max\{s:k^s\mid r\}\ge1`$ and $`k\nmid u`$, then
> ``` math
> F^{(k)}_{j,r}=C_k(t,u)\,F^{(k)}_{j-t,u},
>  \qquad
>  C_k(t,u)=k^t\prod_{\substack{p\mid k\\ p\nmid u}}\Bigl(1-\tfrac1p\Bigr).
> ```*

The Lean declaration below states this result or one that implies it. The Lean reduction $F^{(k)}_{j,k^tu}=k^t\prod_{p\mid k,\,p\nmid u}(1-\tfrac1p)\,F^{(k)}_{j-t,u}$ holds for every $u\ge0$ and every $1\le t<j$, with no requirement that $k\nmid u$ or that $t$ be maximal; the printed reduction is its case $t=\max\{s:k^s\mid r\}$, $k\nmid u$, where $r<k^j$ forces $t<j$. The dimension $k^e+1$, the basis $\mathcal B_{k,e}$ and the identity $F^{(k)}_{j,0}=k^{j-1}F^{(k)}_{1,0}$ are stated as printed.

[`ErdosProblems.Erdos249.PaperCompleteR8.displayed_all_base_kernel`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos249/PaperCompleteR8/FullKernelAssemblies.lean#L35)

```lean
theorem displayed_all_base_kernel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily k e))) =
      k ^ e + 1 ∧
    (∃ b : Module.Basis (AllBaseCanonicalIndex k e) ℚ
        (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily k e))),
      ∀ i, (b i : ℕ → ℚ) = allBaseCanonicalFamily k e i) ∧
    (∀ j : ℕ, 1 ≤ j →
      allBaseTotientKernelSeq k j 0 =
        (k ^ (j - 1) : ℚ) • allBaseTotientKernelSeq k 1 0) ∧
    (∀ j t u : ℕ, 1 ≤ t → t < j →
      allBaseTotientKernelSeq k j (k ^ t * u) =
        ((k : ℚ) ^ t * missingEulerProduct k u) •
          allBaseTotientKernelSeq k (j - t) u)
```

<a id="thm-kkernelrank-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `displayed_all_base_kernel`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_29/Challenge.lean#L84) (E249_29, line 84), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_29/CompleteKernelBases.lean#L26) (CompleteKernelBases.lean, line 26), [replay report](../evidence/comparator/replay-35935225572/receipt-E249_29.json) (E249_29)

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-integral-normal-form"></a>

## Corollary 3.1 (Integral coordinates and all integral relations), page 5

> *Let $`k\ge2`$ and $`e\ge1`$. The retained family is a $`\mathbb{Z}`$-basis of the module generated by the sections through level $`e`$. Index the sections by their level and residue, retaining distinct indices even when they define equal sequences. For each omitted index $`i`$, write the scalar reduction as $`F_i=a_iF_{j(i)}`$, where $`j(i)`$ is retained and $`a_i`$ is a nonnegative integer. In the free abelian group with one generator $`E_i`$ for each of these indices, the vectors
> ``` math
> R_i=E_i-a_iE_{j(i)}\qquad(i\text{ omitted})
> ```
> form a $`\mathbb{Z}`$-basis of the kernel of evaluation $`E_i\mapsto F_i`$. In particular, every integral relation has a unique integral expression in these elementary relations, and their rank is $`\sum_{j=1}^{e-1}k^j`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR8.displayed_integral_normal_form`](https://github.com/wcook04/plectis-erdos/blob/436f55ebdafa67e4af0fff79f621c13f2ded12bf/lean/ErdosProblems/Erdos249/PaperCompleteR8/KernelRelationBasis.lean#L398)

```lean
theorem displayed_integral_normal_form (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    (∃ c : Module.Basis (AllBaseCanonicalIndex k e) ℤ (IntegralChannelSpan k e),
      ∀ i, (c i : ℕ → ℚ) = allBaseCanonicalFamily k e i) ∧
    (∃ b : Module.Basis (OmittedIntegralChannel k e hk he) ℤ
        (IntegralRelations k e hk he),
      ∀ o, ∃ j : AllBaseCanonicalIndex k e, ∃ a : ℕ,
        allBaseThroughLevelFamily k e o.val = (a : ℤ) • allBaseCanonicalFamily k e j ∧
        (b o : AllBaseThroughLevelIndex k e →₀ ℤ) =
          Finsupp.single o.val 1 - Finsupp.single (retainedChannel k e hk he j) (a : ℤ)) ∧
    Module.finrank ℤ (IntegralRelations k e hk he) =
      ∑ j ∈ Finset.range (e - 1), k ^ (j + 1)
```

<a id="cor-integral-normal-form-comparator"></a>

**Comparator: passed** (run 35935225572, corpus commit `cc7e541cf208`).

For each Lean declaration: the Challenge (the target, stated from Mathlib alone), the Solution (our proof) and the replay report.

- `displayed_integral_normal_form`: [Challenge](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/PalomarCorpus/E249_29/Challenge.lean#L195) (E249_29, line 195), [Solution](https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/Solutions/PalomarCorpus/E249_29/TotientKernelBasis.lean#L66) (TotientKernelBasis.lean, line 66), [replay report](../evidence/comparator/replay-35935225572/receipt-E249_29.json) (E249_29)

Challenge for `displayed_integral_normal_form`:

```lean
theorem displayed_integral_normal_form (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    (∃ c : Basis (CanonicalIndex k e) ℤ (IntegralChannelSpan k e),
      ∀ i, (c i : ℕ → ℚ) = canonicalFamily k e i) ∧
    (∃ b : Basis (OmittedIntegralChannel k e hk he) ℤ (IntegralRelations k e),
      ∀ o, ∃ j : CanonicalIndex k e, ∃ a : ℕ,
        throughLevelFamily k e o.val = (a : ℤ) • canonicalFamily k e j ∧
        (b o : ThroughLevelIndex k e →₀ ℤ) =
          Finsupp.single o.val 1 - Finsupp.single (retainedChannel k e hk he j) (a : ℤ)) ∧
    finrank ℤ (IntegralRelations k e) =
      ∑ j ∈ Finset.range (e - 1), k ^ (j + 1) := by sorry
```
