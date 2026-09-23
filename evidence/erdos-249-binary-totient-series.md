# Formal evidence: Bases and Integral Relations for the $k$-Kernel of Euler's Totient

This record belongs to the paper [erdos-249-binary-totient-series.pdf](../paper/249/erdos-249-binary-totient-series.pdf). For every result it lists the Lean declarations that state it, and the independent Comparator check where there is one. The margin marks in the paper link here.

- **Lean.** Every declaration is quoted from [plectis-erdos](https://github.com/wcook04/plectis-erdos) at commit [`c91562bd574a`](https://github.com/wcook04/plectis-erdos/tree/c91562bd574a387cde904481e609c7b4cacebb14) and is checked there by Lean's kernel (`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25`).
- **Comparator.** For a compared result, each declaration was stated a second time, from Mathlib alone, as a *Challenge* in [plectis-erdos-lean](https://github.com/wcook04/plectis-erdos-lean), and a *Solution* that uses our proof was checked against it by [Comparator](https://github.com/leanprover/comparator), which also confirms that only the axioms `propext`, `Quot.sound`, `Classical.choice` are used. All checks below come from replay run [35882032091](https://github.com/wcook04/plectis-erdos-lean/actions/runs/35882032091) at corpus commit [`a2faa350b45a`](https://github.com/wcook04/plectis-erdos-lean/tree/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3) (tag `paper-evidence-2026-09-23`); both the default Lean kernel and the independent `nanoda` kernel accepted every entry. The replay's own report for each entry is kept in this repository and linked from each check. A Challenge shows `sorry` because it states the target without proving it.
- **Counts.** 8 results: 8 with a Lean proof of the whole statement, 0 whose Lean proof assumes a named input (marked with a dagger), 0 without a Lean proof of the whole statement; 8 compared.

These checks establish that the stated propositions are proved. Whether each is the right proposition is for the reader to judge against the paper's statement, which is reproduced below.

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

[`ErdosProblems.Erdos249.PaperCompleteR8.displayed_all_base_kernel`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR8/FullKernelAssemblies.lean#L35)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `displayed_all_base_kernel` | [E249_29/Challenge.lean, line 84](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_29/Challenge.lean#L84) | [CompleteKernelBases.lean, line 26](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_29/CompleteKernelBases.lean#L26) | [E249_29](../evidence/comparator/replay-35882032091/receipt-E249_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-basis"></a>

## Corollary 1.2 (Dyadic basis), page 3

> *The family
> ``` math
> \{\varphi_{0,0},\varphi_{1,0}\}
>  \cup\{\varphi_{j,r}:j\ge1,\ 0<r<2^j,\ r\text{ odd}\},
>  \qquad \varphi_{j,r}(n)=\varphi(2^jn+r),
> ```
> is a basis for the rational span of the full dyadic kernel. Every rational relation is generated by the scalar reductions. The complete level-zero truncation has dimension one.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR8.displayed_full_dyadic_basis`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR8/FullKernelAssemblies.lean#L156)

```lean
theorem displayed_full_dyadic_basis :
    (∃ b : Module.Basis TotientOddCoreIndex ℚ
        (Submodule.span ℚ (Set.range fullTotientKernelFamily)),
      ∀ i, (b i : ℕ → ℚ) = oddCoreTotientKernelFamily i) ∧
    (∃ b : Module.Basis FullOmitted ℚ FullRelations,
      ∀ o, ∃ j : TotientOddCoreIndex, ∃ a : ℕ,
        fullTotientKernelFamily o.val = (a : ℚ) • oddCoreTotientKernelFamily j ∧
        (b o : TotientDyadicKernelIndex →₀ ℚ) =
          Finsupp.single o.val 1 - Finsupp.single (fullRetainedChannel j) (a : ℚ)) ∧
    (∀ e : ℕ, 1 ≤ e → Module.finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1) ∧
    Module.finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily 2 0))) = 1
```

<a id="res-basis-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `displayed_full_dyadic_basis` | [E249_29/Challenge.lean, line 99](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_29/Challenge.lean#L99) | [CompleteKernelBases.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_29/CompleteKernelBases.lean#L41) | [E249_29](../evidence/comparator/replay-35882032091/receipt-E249_29.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="cor-integral-normal-form"></a>

## Corollary 1.3 (Integral coordinates and all integral relations), page 3

> *Let $`k\ge2`$ and $`e\ge1`$. The retained family is a $`\mathbb{Z}`$-basis of the module generated by the sections through level $`e`$. Index the sections by their level and residue, retaining distinct indices even when they define equal sequences. For each omitted index $`i`$, write the scalar reduction as $`F_i=a_iF_{j(i)}`$, where $`j(i)`$ is retained and $`a_i`$ is a nonnegative integer. In the free abelian group with one generator $`E_i`$ for each of these indices, the vectors
> ``` math
> R_i=E_i-a_iE_{j(i)}\qquad(i\text{ omitted})
> ```
> form a $`\mathbb{Z}`$-basis of the kernel of evaluation $`E_i\mapsto F_i`$. In particular, every integral relation has a unique integral expression in these elementary relations, and their rank is $`\sum_{j=1}^{e-1}k^j`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR8.displayed_integral_normal_form`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR8/KernelRelationBasis.lean#L398)

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

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `displayed_integral_normal_form` | [E249_29/Challenge.lean, line 195](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_29/Challenge.lean#L195) | [TotientKernelBasis.lean, line 66](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_29/TotientKernelBasis.lean#L66) | [E249_29](../evidence/comparator/replay-35882032091/receipt-E249_29.json) |

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

<a id="cor-periodic-freezing"></a>

## Corollary 1.4 (Periodic coefficients), page 4

> *Let $`L_1,\ldots,L_s`$ be pairwise nonproportional affine forms with integer coefficients and positive slopes. If $`w_1,\ldots,w_s`$ are rational-valued periodic sequences, then
> ``` math
> \sum_i w_i(n)\varphi(L_i(n))=0\quad\text{for all sufficiently large }n
>  \quad\Longrightarrow\quad w_i(n)=0\quad\text{for every }i,n.
> ```*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR20.periodic_freezing_integer_affine`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR20/PeriodicIntegerAffine.lean#L24)

```lean
theorem periodic_freezing_integer_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : ι → ℤ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → (a i : ℤ) * b j ≠ (a j : ℤ) * b i)
    (w : ι → ℕ → ℚ)
    (hperiodic : ∀ i, ∃ q : ℕ, 0 < q ∧ ∀ n, w i (n + q) = w i n)
    (hrel : ∃ N₀, ∀ n, N₀ ≤ n →
      ∑ i, w i n * (Nat.totient (integerAffineValue a b i n) : ℚ) = 0) :
    ∀ i n, w i n = 0
```

<a id="cor-periodic-freezing-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `periodic_freezing_integer_affine` | [E249_30/Challenge.lean, line 51](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_30/Challenge.lean#L51) | [PaperStatementsAE.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_30/PaperStatementsAE.lean#L155) | [E249_30](../evidence/comparator/replay-35882032091/receipt-E249_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-residueseries"></a>

## Theorem 2.1 (Residue series and dyadic observables), page 5

> *For every $`m\ge3`$,
> ``` math
> \sum_{n\ge1}\frac{\varphi(n)\bmod m}{2^n}\notin\mathbb{Q}.
> ```
> For $`k\ge1`$ and $`f:\mathbb{Z}/2^k\mathbb{Z}\to\mathbb{Q}`$, the series $`\sum_{n\ge1}f(\varphi(n)\bmod2^k)2^{-n}`$ is rational exactly when $`f`$ is constant on the even residue classes. If that constant is $`c`$, its value is $`3f(1)/4+c/4`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables.short_note_residue_theorem`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR7/RationalObservableClassification.lean#L276)

```lean
theorem short_note_residue_theorem :
    (∀ m : ℕ, 3 ≤ m → Irrational (totientResidueValue m)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ f : ZMod (2 ^ k) → ℚ,
      ((∃ q : ℚ,
        (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
          2 ^ (n + 1)) = (q : ℝ)) ↔
        ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ f : ZMod (2 ^ k) → ℚ, ∀ c : ℚ,
      (∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = c) →
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        2 ^ (n + 1)) = ((3 * f 1 / 4 + c / 4 : ℚ) : ℝ))
```

<a id="res-residueseries-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `short_note_residue_theorem` | [E249_30/Challenge.lean, line 77](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_30/Challenge.lean#L77) | [RationalObservableClassification.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_30/RationalObservableClassification.lean#L41) | [E249_30](../evidence/comparator/replay-35882032091/receipt-E249_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="lem-bounded-pulse"></a>

## Lemma 2.2 (An isolated nonzero coefficient between long zero blocks), page 6

> *Let $`a_n\in\mathbb{Z}`$ satisfy $`|a_n|\le C`$. Suppose that for arbitrarily large $`L`$ there is $`N>L`$ such that $`a_N\ne0`$ and $`a_{N+t}=0`$ for $`0<|t|\le L`$. Then $`\sum_{n\ge1}a_n2^{-n}`$ is irrational.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR7.bounded_isolated_pulse`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR7/PeriodicAndPulse.lean#L106)

```lean
theorem bounded_isolated_pulse
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L₀ : ℕ, ∃ L N : ℕ, L₀ ≤ L ∧ L < N ∧ a N ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (N - j) = 0 ∧ a (N + j) = 0) :
    Irrational (∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (n + 1))
```

<a id="lem-bounded-pulse-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `bounded_isolated_pulse` | [E249_30/Challenge.lean, line 62](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_30/Challenge.lean#L62) | [PaperStatementsAE.lean, line 363](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_30/PaperStatementsAE.lean#L363) | [E249_30](../evidence/comparator/replay-35882032091/receipt-E249_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-fulldepth"></a>

## Theorem 3.1 (Propagation of one nonintegral tail difference), page 7

> *Fix $`d\ge1`$ and $`N\ge0`$. If $`\Delta_d(N)\notin\mathbb{Z}`$, then every sufficiently late pair $`\{t,t+1\}`$ contains an $`m`$ such that $`K(md,N,md)`$ holds. Consequently
> ``` math
> \exists t\ge1:\ K(td,N,td)
>  \quad\Longleftrightarrow\quad\Delta_d(N)\notin\mathbb{Z}.
> ```
> Requiring this for every $`d\ge1,N\ge0`$ is equivalent to $`S\notin\mathbb{Q}`$.*

The Lean declaration below states this result.

[`ErdosProblems.Erdos249.PaperCompleteR7.fullDepth_amplification`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/PaperCompleteR7/ShortNoteAssemblies.lean#L35)

```lean
theorem fullDepth_amplification :
    (∀ d N : ℕ, 0 < d →
      (totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ)) →
      ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
        certifiedKill (t * d) N (t * d) ∨
          certifiedKill ((t + 1) * d) N ((t + 1) * d)) ∧
    (∀ d N : ℕ, 0 < d →
      ((∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
        totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ))) ∧
    ((∀ d : ℕ, 0 < d → ∀ N : ℕ,
        ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
```

<a id="res-fulldepth-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `fullDepth_amplification` | [E249_30/Challenge.lean, line 106](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_30/Challenge.lean#L106) | [PaperStatementsM.lean, line 18](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_30/PaperStatementsM.lean#L18) | [E249_30](../evidence/comparator/replay-35882032091/receipt-E249_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.

<a id="res-rankonefloor"></a>

## Theorem 4.1 (A lower bound for the rank-one quotients), page 10

> *For $`e\ge1`$ and $`Y\ge4`$, the denominator of $`Q(e,Y)`$ is positive, and the unique minimiser is $`(e,Y)=(1,5)`$. Every admissible quotient and every nonempty finite positive weighted average of such quotients satisfies
> ``` math
> Q-\Theta_2>\frac{21}{320}.
> ```
> The uniform bound $`Q-\Theta_2>1/15`$ is false already at $`(1,5)`$.*

The Lean declarations below together state this result.

1. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOne_denominator_pos`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSharpFloor.lean#L25)

```lean
theorem rankOne_denominator_pos {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    0 < mobiusMersennePrefix Y (2 * e + 2)
```

2. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_ge_one_five`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSharpFloor.lean#L530)

```lean
theorem rankOneSubrankQuotient_ge_one_five
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient 1 5 ≤ rankOneSubrankQuotient e Y
```

3. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_eq_one_five_iff`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSharpFloor.lean#L546)

```lean
theorem rankOneSubrankQuotient_eq_one_five_iff
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient e Y = rankOneSubrankQuotient 1 5 ↔
      e = 1 ∧ Y = 5
```

4. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSharpFloor.lean#L636)

```lean
theorem rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (21 : ℝ) / 320 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2
```

5. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSharpFloor.lean#L667)

```lean
theorem positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (21 : ℝ) / 320 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2
```

6. [`ErdosProblems.Erdos249.RankOneSubrankObstruction.rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen`](https://github.com/wcook04/plectis-erdos/blob/c91562bd574a387cde904481e609c7b4cacebb14/lean/ErdosProblems/Erdos249/RankOneSharpFloor.lean#L617)

```lean
theorem rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen :
    rankOneSubrankQuotient 1 5 - mobiusMersenneTheta 2 <
      (1 : ℝ) / 15
```

<a id="res-rankonefloor-comparator"></a>

**Comparator: passed** (run 35882032091, corpus commit `a2faa350b45a`).

| Lean declaration | Challenge (the target, from Mathlib alone) | Solution (our proof) | Replay report |
|---|---|---|---|
| `rankOne_denominator_pos` | [E249_30/Challenge.lean, line 139](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_30/Challenge.lean#L139) | [RankOneDenominator.lean, line 20](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_30/RankOneDenominator.lean#L20) | [E249_30](../evidence/comparator/replay-35882032091/receipt-E249_30.json) |
| `rankOneSubrankQuotient_ge_one_five` | [E249_33/Challenge.lean, line 104](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_33/Challenge.lean#L104) | [RankOneSharpFloor.lean, line 15](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_33/RankOneSharpFloor.lean#L15) | [E249_33](../evidence/comparator/replay-35882032091/receipt-E249_33.json) |
| `rankOneSubrankQuotient_eq_one_five_iff` | [E249_30/Challenge.lean, line 149](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_30/Challenge.lean#L149) | [RankOneSharpFloor.lean, line 28](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_30/RankOneSharpFloor.lean#L28) | [E249_30](../evidence/comparator/replay-35882032091/receipt-E249_30.json) |
| `rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty` | [E249_30/Challenge.lean, line 155](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_30/Challenge.lean#L155) | [RankOneSharpFloor.lean, line 41](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_30/RankOneSharpFloor.lean#L41) | [E249_30](../evidence/comparator/replay-35882032091/receipt-E249_30.json) |
| `positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty` | [E249_30/Challenge.lean, line 161](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_30/Challenge.lean#L161) | [RankOneSharpFloor.lean, line 79](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_30/RankOneSharpFloor.lean#L79) | [E249_30](../evidence/comparator/replay-35882032091/receipt-E249_30.json) |
| `rankOneSubrankQuotient_one_five_sub_theta_two_lt_one_div_fifteen` | [E249_30/Challenge.lean, line 127](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/PalomarCorpus/E249_30/Challenge.lean#L127) | [PaperStatementsBG.lean, line 74](https://github.com/wcook04/plectis-erdos-lean/blob/a2faa350b45ae08d0e70f5a6ec54943018f8c2b3/Solutions/PalomarCorpus/E249_30/PaperStatementsBG.lean#L74) | [E249_30](../evidence/comparator/replay-35882032091/receipt-E249_30.json) |

Each Challenge states the same proposition as the Lean declaration it targets, with every definition it uses restated from Mathlib alone.
