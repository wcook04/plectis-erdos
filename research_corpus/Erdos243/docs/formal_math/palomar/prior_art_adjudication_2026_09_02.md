# Prior-art adjudication for five flagship claims

Audit date: **2026-09-02**. Adversarial read-only pass. The working assumption
throughout was that a published paper already contains the theorem, and each
section records what was searched before that assumption was released.

Evidence bands used below follow the CLAUDE.md grounding contract:

- `verified_current` — checked this pass by reading the Lean file, the archived
  primary source, or a live fetch on 2026-09-02.
- `embedded_evidence` — supported by a quotation pasted into this document.
- `reported_prior` — asserted by a repository artifact and not re-derived here.

Every Lean statement below was read from disk this pass. Every primary source
below was read either from `annexes/` (hash-pinned local copy) or from a live
fetch on 2026-09-02. Where a source was not obtained, the section says so and
returns `unknown` rather than a firstness claim.

One global caveat. A `Challenge.lean` in this repository carries `sorry` **by
design**: it is the source-independent statement a Comparator must accept, and
the proof lives in the sibling `Solution.lean`. Challenge-file `sorry` counts
are therefore not evidence of an unproved claim. The `Solution.lean` files for
#257, #249, #269, and both #1041 packets each have zero `sorry`. #1049 is the
exception and is treated separately in §5.

---

## 1. Erdős #257 — all-base reciprocal-summable irrationality

### Our exact statement

`formal_math/erdos257_period_noncollapse/ExternalVerification257ReciprocalSupport/Challenge.lean`,
transported without weakening by `Solution.lean` from
`Erdos257PeriodNoncollapse/AllBaseReciprocalSupportIrrationality.lean`
(`sorry` count 0):

```lean
theorem irrational_supportPowerSeries_of_summable_reciprocal
    (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hA : A.Infinite)
    (hsum : Summable (supportReciprocalTerm A)) :
    Irrational (supportPowerSeries b A)
```

where `supportPowerSeries b A = ∑' a, 1_A(a) · 1/(b^a − 1)` and
`supportReciprocalTerm A a = 1_A(a) · 1/a`. In words: for every infinite
`A ⊆ ℕ` with `∑_{a∈A} 1/a < ∞` and every integer `b ≥ 2`, the sum
`∑_{a∈A} 1/(b^a − 1)` is irrational. No pairwise-coprimality, periodicity,
density, growth, or powerful-support hypothesis is present.

Evidence band: `verified_current`.

### Closest primary antecedent

**P. Erdős, "On the irrationality of certain series", The Mathematics Student
36 (1968; issued 1969), 222–226.** Local hash-pinned copy:
`annexes/erdos-1968-irrationality-certain-series/`. Read this pass.

Printed theorem, p. 222, quoted from the archived scan:

> "THEOREM. Let (n_i, n_j)=1, ∑ 1/n_i < ∞. Then ∑ 1/(t^{n_i} − 1) is
> irrational for every t ≥ 2."

Immediately following sentence, same page:

> "By more complicated arguments one can show that the condition (n_i, n_j)=1
> is superfluous. We do not give the details since I do not think that the
> condition ∑ 1/n_i < ∞ is very relevant."

Closing remark, printed p. 226:

> "If we do not assume (n_i, n_j)=1 the proof becomes more complicated. We have
> to use the result that if the fractional part of t^n α takes on infinitely
> many different values, then α is irrational."

Evidence band: `embedded_evidence`.

### Side-by-side

| | Erdős 1968, printed theorem | Erdős 1968, stated extension (no proof printed) | Ours |
|---|---|---|---|
| Support | infinite `A`, pairwise coprime | infinite `A`, coprimality dropped | infinite `A`, no arithmetic hypothesis |
| Reciprocal mass | `∑ 1/a < ∞` | `∑ 1/a < ∞` | `∑ 1/a < ∞` |
| Base | **every integer `t ≥ 2`** | every integer `t ≥ 2` | every integer `b ≥ 2` |
| Conclusion | `∑ 1/(t^a − 1)` irrational | same | same |
| Proof | printed | withheld | complete, Lean-checked, kernel-verified |

### The finding that changes the framing

Erdős's **printed** theorem is already all-base. The base-two framing on
erdosproblems.com is an artefact of how problem #257 is posed, and it is not a
limitation of Erdős's 1968 result. The packet README at
`ExternalVerification257ReciprocalSupport/README.md` currently says the source
theorem "strengthens the historical base-two no-coprimality statement to every
integer base at least two" and that "Erdős stated the no-coprimality extension
in the base-two setting". Both sentences are wrong against the primary source.
The repository's own adjudicated route
`prior_art_routes/reciprocal_summable_supports_base_two_v0.json` already records
the correct reading ("Erdős (1968/1969), p. 222, proves the pairwise-coprime
reciprocal-summable theorem for every integer base t at least two") and lists
"all-base no-coprimality theorem" under `discouraged_terminology`. The README and
the route disagree, and the route is right.

The only hypothesis our theorem removes relative to Erdős's printed theorem is
pairwise coprimality. That is exactly the hypothesis Erdős said he could remove.

### Other candidates checked and cleared

- **Kovač–Tao, arXiv:2406.17593v4, Acta Math. Hungar. 175 (2025), 572–608.**
  Theorem 2.3 constructs rational sums, quoted verbatim from the v4 HTML:
  "Suppose that m is a positive integer, while 2⩽t₁<t₂<⋯<tₘ are integers such
  that ∑ₖ 1/(tₖ−1)>1. Then there exist sets A₁,…,Aₘ⊆ℕ such that at least one of
  them is infinite and that ∑ₖ ∑_{n∈Aₖ} 1/(tₖⁿ−1) is a rational number." This
  needs `m ≥ 2` distinct bases (for `m = 1` the condition `1/(t−1) > 1` fails at
  every `t ≥ 2`), and the constructed sets have divergent reciprocal mass. The
  same paper says: "We do not know how to solve the original question implied by
  Erdős." No conflict, and no antecedent.
- **Duverney–Tachiya, "Refinement of the Chowla–Erdős method and linear
  independence of certain Lambert series" (2019).** Local copy read. Their class
  `E` demands `gcd(e_i,e_j)=1` and `e_n ≤ n^μ`, and Corollary 1.2 applies to the
  multiplicative closures `F_s(E)`, which are reciprocal-divergent. Disjoint
  regime, coprimality retained. Incomparable, not an antecedent.
- **Borwein (1991/1992), `∑ 1/(q^n − r)`.** Full series only, no sparse-support
  version. Confirmed by the erdosproblems.com #257 discussion, where the
  odd-index subseries is derived from Borwein and the even-index one from Erdős
  1948, both by reindexing the full series.
- **Tao–Teräväinen, arXiv:2512.01739.** Settles `A` = primes and `A` = prime
  powers. `∑_p 1/p` diverges, so this lies outside our hypothesis entirely.
- **Kaneko–Suzuki–Tachiya, "Refinements of Erdős's irrationality criterion for
  certain sparse infinite series", arXiv:2601.20743 (28 Jan 2026), Int. J.
  Number Theory.** Abstract read live. Their applications are
  `∑ d(n)^k/t^{σ(n)}` and `∑ d(n)^k/t^{φ(n)}`. Their sparsity is sparsity of the
  coefficient support, and `f_A(n) = #{d | n : d ∈ A}` is supported on
  `⋃_{a∈A} aℕ`, which has positive density. Adjacent, and it does not contain
  our statement. Confidence medium: the full text was not read this pass.
- **Barreto–Kang–Kim–Kovač–Zhang, arXiv:2601.21442; Koizumi, arXiv:2504.05933;
  Crmarić–Kovač, arXiv:2504.18712.** All Ahmes-series or doubly-exponential
  regimes. Not Lambert subseries.
- **erdosproblems.com #257 discussion, fetched live 2026-09-02** (6 comments,
  page last edited 15 April 2026). The mathematical content is Tachiya's
  period-2 criterion, the Erdős and Borwein reindexings, and Kovač's fat-Cantor
  measure heuristic. Nobody has posted the reciprocal-summable no-coprimality
  theorem.

### Relation

**matched** against Erdős's own stated extension in Erdős 1968.
**strictly_stronger_than_prior** against the printed theorem in the same paper.
The statement is Erdős's; the complete proof is ours.

Confidence: **high** for the statement identity and the base-generality
correction (primary text read this pass); **medium-high** that no independent
published proof of the no-coprimality extension exists, since the search covered
arXiv, the problem page, and the four named literature families but is not
exhaustive over 1968–2026 journal-only number theory.

**What our paper must say.** Erdős stated this exact theorem in 1968 for every
integer base at least two and withheld the proof of the case without pairwise
coprimality. Our contribution is a complete machine-checked proof of that
withheld case, and the all-base quantifier is Erdős's own.

---

## 2. Erdős #1041 — lemniscate path, sharp constant 2 under separation

### The problem, verified live

erdosproblems.com/1041, fetched 2026-09-02, status **FALSIFIABLE / open**,
0 proof claims, 47 comments, page last edited 06 December 2025:

> "Let f(z)=∏_{i=1}^n(z−z_i) ∈ ℂ[z] with |z_i| < 1 for all i. Must there always
> exist a path of length less than 2 in {z : |f(z)| < 1} which connects two of
> the roots of f?" Reference [EHP58, p.139].

### Our exact statements

**(a) Conditional sharp constant.**
`ErdosProblems/Erdos1041/FirstMergeCriticalValueSeparation.lean`, exposed
through `ExternalVerification1041FirstMergeCriticalValueSeparation/`
(`Solution.lean` `sorry` count 0):

```lean
noncomputable def firstMergeSquaredCoefficient (n : ℕ) (S : ℝ) : ℝ :=
  (1 + S) ^ ((2 : ℝ) / (n : ℝ)) * Real.log (S / (S - 1))

theorem firstMerge_length_lt_two_of_squared_bound
    {n : ℕ} {S length : ℝ}
    (hbound : length ^ 2 ≤ 4 * firstMergeSquaredCoefficient n S)
    (hthreshold : firstMergeSquaredCoefficient n S < 1) :
    length < 2

theorem firstMerge_exact_convenient_thresholds :
    (∀ n : ℕ, 3 ≤ n → firstMergeSquaredCoefficient n 4 < 1) ∧
    (∀ n : ℕ, 4 ≤ n → firstMergeSquaredCoefficient n 3 < 1) ∧
    (∀ n : ℕ, 7 ≤ n → firstMergeSquaredCoefficient n 2 < 1)
```

Read this pass. Two boundary facts matter for any public statement. First, the
threshold for `S = 4` is `n ≥ 3`, not "all n". Second, the Lean file proves the
numerical kernel and the consumer implication; it does **not** prove the
analytic hypothesis `length² ≤ 4·firstMergeSquaredCoefficient n S`. The
analytic continuation, univalence, area formula, and Pólya area-capacity
inequality that produce that bound remain ordinary mathematics, as the module
docstring itself states.

**(b) Unconditional constant-factor bound.**
`ErdosProblems/Erdos1041/UnconditionalConstantFactorBound.md`, Theorem 1,
quoted from the file:

> "Two zero occurrences of `f` are joined by a possibly degenerate path of
> length at most `(71/10) μ^{1/n} = (71/10) cap(K_μ)` lying inside
> `K_{2μ} = {z : |f(z)| ≤ 2μ}`."

with `μ = min{|f(c)| : f'(c) = 0}`. This is ordinary repository-authored
mathematics, not Lean-checked, and it does not answer #1041: the path lives in
`K_{2μ}` rather than `K_μ`, and `(71/10)μ^{1/n}` can exceed 2.

Evidence band: `verified_current` for the Lean, `verified_current` for the note
text, `reported_prior` for the correctness of the note's proof.

### Closest primary antecedents

1. **Venkata Siddharth Pendyala, "A Degree-Four Lemniscate Path Theorem",
   arXiv:2606.24875 (23 June 2026).** Abstract fetched live 2026-09-02 and also
   held at `annexes/arxiv-2606-24875-pendyala-degree-four-lemniscate-path/`:
   "We prove the degree-four case of a path problem of Erdős, Herzog, and
   Piranian. If f is monic of degree four and all zeros of f, counted with
   multiplicity, lie in the open unit disk, then two zeros from this list can be
   joined inside {z:|f(z)|<1} by a possibly degenerate polygonal path of length
   less than 2."
2. **Venkata Siddharth Pendyala, "Shortest paths in polynomial lemniscate
   sublevel sets and a problem of Erdős", arXiv:2606.19178 (17 June 2026).**
   Abstract fetched live: with `E_f = {|z| ≤ 1, |f(z)| ≤ 1}` and `S(n)` the
   largest possible shortest path in `E_f` from 0 to `∂𝔻`, "for all sufficiently
   large n, c√(log n) ≤ S(n) ≤ πn with an absolute constant c>0."
3. **P. Erdős, F. Herzog, G. Piranian, "Metric properties of polynomials",
   J. Analyse Math. 6 (1958), 125–148, DOI 10.1007/BF02790232, Problem 5 on
   printed p. 139.** Origin of the problem; proves only that the sublevel set has
   a component containing at least two roots. Local copy at
   `annexes/erdos-herzog-piranian-1958-metric-properties-of-polynomials/`.
4. **"shtuka", "A Short Path Joining Two Zeros Inside a Polynomial
   Lemniscate", manuscript posted 17 and 24 March 2026,
   `https://shtuka123.github.io/1041/main.pdf`.** A claimed resolution of the
   general problem. Terence Tao's review on the problem page, 20:48 on 24 March
   2026, fetched live this pass, rates it "plausibly correct" and lays out its
   four ingredients: the EHP component lemma; an integral bound
   `∫_U |f'/f| dA ≤ 2πm` (Proposition 4, derived from the area formula and the
   Pólya inequality); a Morse-gradient-flow tree through the `m` zeros of total
   length at most `(1/2π)∫_U |f'/f| dA` (Proposition 12); and a combinatorial
   tree-to-path lemma (Lemma 17). Tao's review also flags that "the AI-generated
   article cites almost none of the extensive literature on lemniscates".

Evidence band: `embedded_evidence` for 1, 2 and 4; `reported_prior` for the EHP
1958 page locator.

### Side-by-side

| | Pendyala 2606.24875 | Pendyala 2606.19178 | shtuka Mar 2026 | Ours (a) | Ours (b) |
|---|---|---|---|---|---|
| Degree | exactly 4 | all large n | all n (claimed) | `n ≥ 3` / `4` / `7` by regime | all `n ≥ 2` |
| Hypothesis | none beyond zeros in open disk | zeros in closed disk | none (claimed) | critical-value separation `S = 4, 3, 2` | none |
| Constant | `< 2`, sharp | `c√log n ≤ S(n) ≤ πn` | `< 2` (claimed) | `< 2`, sharp | `71/10` |
| Ambient set | `{|f| < 1}` | `E_f` | `{|f| < 1}` | `{|f| < 1}` after normalisation | `K_{2μ}`, a dilated sublevel set |
| Status | published preprint | published preprint | contested | conditional theorem, numerical kernel in Lean | ordinary proof, not formalised |

### What Pendyala settles and what our separation theorem settles

Pendyala 2606.24875 settles Erdős #1041 unconditionally and completely for
degree four, with no hypothesis on the critical spectrum. Our separation theorem
settles every degree above the stated threshold, and only for polynomials whose
critical values are separated at scale `S`. Neither implies the other: degree
four with a near-tie in the critical spectrum is Pendyala's and outside ours,
and degree 40 with `S = 4` separation is ours and outside Pendyala's. Pendyala
2606.19178 is about a different quantity, the longest shortest path from the
origin to the unit circle inside `E_f`, and its `πn` upper bound is
degree-dependent, so it neither implies nor is implied by our degree-free
`71/10` bound.

The genuine hazard is the shtuka manuscript, whose mechanism overlaps ours
substantially: EHP component lemma, a Pólya-inequality area bound, and a
length budget assembled from it. If Proposition 12 stands, the general problem is
solved and both our results are subsumed. `prior_art_routes/erdos1041_lemniscate_short_path_v0.json`
records an exact Cassini countermodel to Proposition 12 of the March draft (and
Proposition 7 of the shorter draft), namely that the Cassini level-length tail
`4(√(a²+a) − a)` falls below the root distance `2a` for `a > 4/5`, with a strict
deficit above `4/25` at `a = 9/10`. This pass did not re-derive that inequality;
it is `reported_prior`. The public status on erdosproblems.com as of
2026-09-02 remains open with zero accepted proof claims.

Adjacent and non-competing: Tao, "The maximal length of the
Erdős–Herzog–Piranian lemniscate in high degree", arXiv:2512.12455 (Dec 2025),
concerns the arclength of `{|p| = 1}`, a different EHP question; and
Ghosh–Ramachandran, J. Math. Anal. Appl. 540 (2024) 128571, arXiv:2312.13673,
concerns the number of components. Eremenko–Hayman, Pommerenke, and Dubinin were
searched by name and by the capacity-and-lemniscate keyword family; no
degree-free root-connecting path bound was located in that literature this pass,
and that is recorded as an unfinished search rather than an absence.

### Relation

**incomparable** to Pendyala 2606.24875 and to Pendyala 2606.19178.
**unknown** relative to the shtuka manuscript, which claims a strictly stronger
result whose load-bearing proposition is contested.

Confidence: **high** for the incomparability with both Pendyala papers
(abstracts read verbatim); **low-to-medium** for the shtuka disposition, since
the manuscript's current revision was not read this pass and the countermodel was
not re-derived.

### What our paper must say

Pendyala's June 2026 preprint settles degree four with no hypothesis on the
critical spectrum, and our theorem settles every degree above the stated
threshold under a critical-value separation hypothesis. A general-degree
manuscript by an anonymous author has been circulating since March 2026 and its
tree-budget proposition remains contested, so any claim of ours must be stated
against that open question rather than around it.

---

## 3. Erdős #249 — dyadic totient kernel basis and rank

### Our exact statement

`ExternalVerification249DyadicTotientKernel/Challenge.lean`, transported by
`Solution.lean` (`sorry` count 0):

```lean
theorem dyadicTotientKernelOddCoreBasisAndFiniteRanks :
    LinearIndependent ℚ oddCoreTotientKernelFamily ∧
      Submodule.span ℚ (Set.range fullTotientKernelFamily) =
        Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) ∧
      ∀ e : ℕ, 1 ≤ e →
        Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)) =
          Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) ∧
        finrank ℚ (Submodule.span ℚ
            (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1
```

with `totientKernelSeq j r n = φ(2^j n + r)`. In words: the family consisting of
the two zero-residue base channels together with one channel per odd residue at
every positive level is `ℚ`-linearly independent, spans the same subspace as all
dyadic sections `f_{j,r}(n) = φ(2^j n + r)`, and the complete unreduced
truncation through level `e` has `ℚ`-rank exactly `2^e + 1` for every `e ≥ 1`.

Evidence band: `verified_current`.

**Scope correction.** The brief for this adjudication described the claim as
including "non-2-regularity". No Lean declaration in
`ExternalVerification249DyadicTotientKernel/` states non-regularity, and the
package README does not claim it either. Non-2-regularity is a corollary
(unbounded `ℚ`-rank forces the `ℤ`-module generated by the 2-kernel to fail to be
finitely generated), and it should be treated as a downstream remark, not as
part of the flagship statement.

### Closest primary antecedent

**Michael Coons, "(Non)Automaticity of number theoretic functions", J. Théor.
Nombres Bordeaux 22 (2010), no. 2, 339–352.** Local copy at
`annexes/coons-2010-nonautomaticity-number-theoretic-functions/`, read this pass.

> "Theorem 3.2. The function ϕ(n) is not k–regular for any k ≥ 2."

Proof, printed p. 349, from the Dirichlet series `∑ φ(n)n^{-s} = ζ(s−1)/ζ(s)`
and the density of poles of `1/ζ(s)` in `R(0,1;T)`. Coons also states in his
concluding section that the `k`-kernel is infinite as shown in that paper.

Supporting framework: **J.-P. Allouche and J. Shallit, "The ring of k-regular
sequences", Theoret. Comput. Sci. 98 (1992), 163–197**, local copy at
`annexes/allouche-shallit-1992-ring-k-regular-sequences/`, which owns the
`k`-kernel and `k`-regular definitions Coons uses.

Evidence band: `embedded_evidence` for Coons Theorem 3.2.

### Side-by-side

| | Coons 2010, Thm 3.2 | Ours |
|---|---|---|
| Object | `φ` as a `k`-regular sequence candidate | the `ℚ`-span of `{φ(2^j n + r)}` |
| Bases | every `k ≥ 2` | `k = 2` only |
| Conclusion | `φ` is not `k`-regular; `k`-kernel infinite | explicit spanning basis, and exact rank `2^e + 1` through level `e` |
| Method | Dirichlet series `ζ(s−1)/ζ(s)`, pole density | CRT-Dirichlet separated minors, parity-separated evaluation matrix |
| Precision | qualitative (not finitely generated) | quantitative (exact finite ranks and the complete relation normal form) |

Coons subsumes and strictly exceeds the non-regularity remark. Coons does not
compute a rank, does not exhibit a spanning family, and does not identify which
dyadic sections are redundant. Our statement that even-residue channels account
for every repetition, and that the exact rank through level `e` is `2^e + 1`, was
not located in any source this pass.

### Other candidates checked and cleared

- **Eric Li, "Rank Amplification for Shifted Equal Values of Euler's Totient
  Function", arXiv:2606.23681 (22 June 2026).** Local annex. Despite the word
  "rank" in the title, it counts `n ≤ x` with `φ(n) = φ(n+h)`. Unrelated object.
- **Bell**, in the `k`-regular sequence literature, is cited by Coons as a source
  of thanks rather than of a competing totient computation. No totient
  `k`-kernel rank paper by Bell was located.
- **Martin, "Simultaneous totient inequalities" (arXiv:math/0603053).** Local
  annex. Supplies the affine-totient separation mechanism used in our proof, and
  states no kernel-rank theorem.
- **erdosproblems.com #249 discussion, fetched live 2026-09-02** (2 comments,
  page last edited 28 September 2025). The comments give the convolution identity
  `∑ φ(n)/2^n = ∑ μ(n)/(2^n−1)² + 1/2` (Steve Fan, 16 May 2026) and the
  irrationality of the powers-of-two subseries (Zeraoulia Rafik, 15 May 2026).
  Neither concerns the dyadic kernel rank.
- A direct search for `"2-kernel"` or `"k-kernel"` of the Euler totient with
  explicit basis or rank returned nothing on topic. That search was weak, and the
  result is recorded as an unfinished search.

### Relation

**strictly_weaker_than_prior** for the non-2-regularity remark, which Coons 2010
proves for every `k ≥ 2`.
**unknown** for the explicit odd-core basis and the exact rank `2^e + 1`; no
antecedent was located, and the search was not exhaustive.
Composite relation for the flagship statement as written: **incomparable**.

Confidence: **high** that Coons owns non-regularity (theorem read verbatim);
**medium** that no explicit dyadic-kernel basis exists in the literature, since
`k`-regular sequence papers are numerous and were not swept systematically.

### What our paper must say

Coons proved in 2010 that Euler's totient is not `k`-regular for any `k ≥ 2`, so
non-regularity is settled prior art and belongs in the introduction as a
citation. Our contribution is the explicit odd-core spanning family and the exact
rank `2^e + 1` of the truncation through level `e`, which pins down the complete
linear-relation structure that non-regularity leaves undetermined.

---

## 4. Erdős #269 — rank phase transition from two to three primes

### Our exact statements

Two-generator half, `ErdosProblems/Erdos269/KernelCarryRank.lean`:

```lean
theorem twoPrimeKernelQ_eq_outer_product {p q : ℕ} (hp : 1 < p) (hq : 1 < q) (i j : ℕ) :
    twoPrimeKernelQ p q i j
      = ((p ^ i * q ^ Nat.log q (p ^ i) : ℕ) : ℚ)⁻¹
        * ((p ^ Nat.log p (q ^ j) * q ^ j : ℕ) : ℚ)⁻¹

theorem twoPrimeKernelQ_minor_two_eq_zero ... : (every 2×2 minor) = 0
```

Three-generator half,
`ExternalVerification269ThreePrimeStructure/Challenge.lean`, transported by
`Solution.lean` (`sorry` count 0):

```lean
theorem smoothPrefixLcm_eq_threePrimeHeight ... :
    smoothPrefixLcm p q r x = threePrimeHeight p q r x

theorem threePrimeKernel_infiniteRank_and_noFiniteSeparation
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ, ∃ I J : Fin n → ℕ,
        Function.Injective I ∧ Function.Injective J ∧
          ∀ k : ℕ, (Matrix.det fun a b : Fin n =>
            threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
      (∀ d : ℕ, ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
            ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k)
```

together with the explicit `{2,3,5}` minor `= −1/15`.

Evidence band: `verified_current`.

### Closest primary antecedent

**Steve Fan, comment on erdosproblems.com problem #269, 05:22 on 26 June 2026.**
Fetched live 2026-09-02 from `https://www.erdosproblems.com/forum/thread/269`.
Quoted verbatim:

> "Here is a short proof of the case |P|=2, which actually shows that S is
> transcendental. Let P = {p₁<p₂<...<p_k}. Then each aₙ is of the form
> p₁^{i₁}⋯p_k^{i_k}, where i₁,...,i_k ≥ 0, and
> lcm[a₁,...,aₙ] = ∏_{j=1}^{k} p_j^{⌊log aₙ / log p_j⌋}."

He then specialises to `P = {p<q}`, sets `β = log q / log p`, and obtains

> "S = ∑_{i,j≥0} p^{−i−⌊jβ⌋} q^{−j−⌊iβ^{−1}⌋} = S₁S₂"

with `S₁ = ∑_{i≥0} p^{−i} q^{−⌊iβ^{−1}⌋}` and `S₂ = ∑_{j≥0} p^{−⌊jβ⌋} q^{−j}`,
relates `S₂` to the Hecke–Mahler series, and concludes transcendence of `S`. He
closes:

> "This argument does not seem to generalize immediately to |P|≥3, since S does
> not factor nicely in the first place."

Evidence band: `embedded_evidence`.

### Side-by-side

| | Fan, 26 June 2026 | Ours |
|---|---|---|
| LCM identity | stated for **every** `k`, `lcm = ∏_j p_j^{⌊log aₙ/log p_j⌋}` | proved in Lean for `k = 3` |
| Two primes | `S = S₁S₂`, then `S` transcendental via Hecke–Mahler | kernel is an outer product, every `2×2` minor vanishes |
| Three primes | "does not factor nicely" (qualitative remark) | nonsingular `n×n` minors for **every** `n`, uniformly in the third layer; no finite separable representation of any rank `d` |
| Conclusion type | arithmetic (transcendence) | linear-algebraic (rank / non-separability) |
| Erdős #269 | open for `k ≥ 3` | open for `k ≥ 3` |

Two consequences for our framing. First, `smoothPrefixLcm_eq_threePrimeHeight`
is a Lean formalisation of an identity Fan states publicly for all `k`, so it is
prior art and must be cited rather than presented as a finding. Second, our
two-prime outer-product theorem is strictly weaker than Fan's two-prime result:
he gets transcendence of the sum, we get the algebraic factorisation that
underlies it.

The genuinely unlocated part is the quantitative three-prime statement. Fan
observed that the factorisation fails; our theorem proves that it fails at every
finite rank simultaneously, in every layer, which is a strictly stronger
obstruction than a failure to factor.

### Other candidates checked and cleared

- **Erdős, letter to the editor, Fibonacci Quarterly 12 (1974), p. 335**, in
  which he says he can prove irrationality when duplicate summands are removed.
  Local annex `erdos-1974-letter-running-lcm-series`. No rank statement.
- **Erdős, "On the irrationality of certain series: problems and results",
  New advances in transcendence theory (Durham 1986), 1988, p. 106**, which calls
  the infinite-`P` case a "simple exercise". No rank statement.
- Searches for Hankel-type or rank results on running-LCM or smooth-number series
  returned nothing on topic. Recorded as an unfinished search.
- The full #269 thread (7 comments) was read. The other mathematical content is
  Fan's infinite-`P` proof (11 Oct 2025, corrected after a remark by Thomas
  Bloom) and old-bielefelder's observation that Fan's `k=2` argument works for
  arbitrary coprime `r, s`. Nothing on three primes.

### Relation

**matched** for the running-LCM identity and for the two-prime outer-product
structure, both anticipated by Fan on 26 June 2026, and our two-prime statement
is additionally **strictly_weaker_than_prior** since Fan reaches transcendence.
**unknown** for the three-prime infinite-rank and no-finite-separation theorem;
no antecedent located, and Fan's own remark suggests none exists.

Confidence: **high** for the Fan comparison (post read verbatim, live);
**medium-high** that the three-prime rank theorem is unanticipated, since a
public comment thread plus keyword search is a thin sweep of the smooth-number
literature.

### What our paper must say

Steve Fan posted the general running-LCM factorisation and the two-prime
transcendence proof on the problem page on 26 June 2026, so the LCM identity and
the two-generator outer-product structure are his and must be cited as such. Our
contribution is the quantitative form of the obstruction he observed, namely that
three distinct prime generators force nonsingular minors of every order in every
layer and admit no finite separable representation.

---

## 5. Erdős #1049 — exact Hankel q-order and leading coefficient

### Our exact statement

Target claim, from
`ErdosProblems/Erdos1049/research_packet.json` and
`ErdosProblems/Erdos1049/HankelQOrderComputationalLab.md`:

> For every rank `N`, Zudilin's normalized Hankel determinant `V_N^*` at
> `x = z = 1` has `q`-order **exactly** `N(N−1)(2N−1)/6` and leading coefficient
> **exactly** `(N!)²(N+1)!/2^N`.

What is actually in Lean, `ErdosProblems/Erdos1049/AdelicHeightBridge.lean`
(`sorry` count 0, read this pass):

```lean
def zudilinSharpHankelQOrder (N : ℕ) : ℤ := ∑ j ∈ Finset.range N, (j : ℤ) ^ 2

theorem six_mul_zudilinSharpHankelQOrder (N : ℕ) :
    6 * zudilinSharpHankelQOrder N = (N : ℤ) * ((N : ℤ) - 1) * (2 * (N : ℤ) - 1)

theorem zudilinSharpHankelOrderAndCoeff_algebraicAssembly (N : ℕ) :
    6 * zudilinSharpHankelQOrder N = (N : ℤ) * ((N : ℤ) - 1) * (2 * (N : ℤ) - 1) ∧
      2 ^ N * (∏ j ∈ Finset.range N, zudilinTransformedRowCoeff j) =
        (N.factorial) ^ 2 * (N + 1).factorial
```

with the module's own docstring:

> "This theorem assembles the closed forms, but it deliberately does not identify
> a formal power-series determinant with these data; that source-facing
> row-operation bridge remains the end-to-end formalisation boundary."

and, for the transformed rows:

> "**Complete first transformed-row initial monomial, in every column.** ...
> Rows `j ≥ 2` are not claimed here."

**Evidence class, stated precisely.** The exactness claim is verified by exact
integer power-series computation for ranks `1 ≤ N ≤ 7` (checker
`scripts/check_zudilin_hankel_qorder.py`, receipt
`state/formal_math/erdos257_period_noncollapse/erdos1049_hankel_qorder_receipt.json`,
`reported_prior` since the checker was not run this pass). The general-`N`
statement is an ordinary-mathematics argument whose Lean formalisation is
incomplete: transformed row `1` is proved in every column, rows `j ≥ 2` are open,
and the identification of the power-series determinant with the assembled closed
forms is open. Any public statement that says "proved for every rank `N`" without
that qualification would overstate the artifact.

### Closest primary antecedent

**Wadim Zudilin, "On the irrationality of generalized q-logarithm", Research in
Number Theory 2 (2016), Article 15, DOI 10.1007/s40993-016-0042-x,
arXiv:1601.02688, Section 4.** Local hash-pinned TeX source at
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`, read this
pass. Verbatim, source lines 278–305:

> "Our crucial observation here is that the q-expansion of `V_n^*` starts from at
> least `q^{n(n−1)(2n−1)/6}`, so that `|V_n^*| ≤ |q|^{n³/3} exp(O(n²))`."

followed by the backward-shift operator `D_l = (N;q)_l = ∏_{j=0}^{l−1}(I − q^j N)`
and Lemma 1: "for `n ≥ l` the q-expansion of `D_l w_n` starts at least from
`nl − l(l−1)/2`."

Evidence band: `embedded_evidence`.

**Citation correction.** The brief named "Zudilin 2004 (q-harmonic / q-Apéry)".
`annexes/zudilin-2004-heine-q-harmonic-series/` is Zudilin, "Heine's basic
transform and a permutation group for q-harmonic series", Acta Arith. 111.2
(2004), and it contains no Hankel determinant material (checked this pass). The
antecedent for this claim is the 2016 paper.

### Side-by-side

| | Zudilin 2016, §4 | Ours |
|---|---|---|
| Statement | `ord_q V_N^* ≥ N(N−1)(2N−1)/6` | `ord_q V_N^* = N(N−1)(2N−1)/6` |
| Direction of use | lower bound on order, hence upper bound `\|V_N^*\| ≤ \|q\|^{N³/3}e^{O(N²)}` | equality, hence **no** additional analytic decay is available |
| Leading coefficient | not stated | `(N!)²(N+1)!/2^N` |
| Mechanism | backward-shift `D_l`, row transformation, Lemma 1 | associated-graded transformed-row coefficients, tail reciprocals, a Vandermonde leading matrix |
| Evidence | published proof | exact computation for `N ≤ 7`; general `N` ordinary and partly formalised |

The mathematical value of the upgrade is a negative one, and that is worth
stating plainly: equality closes off the hope that hidden cancellation in the
normalised Hankel determinant supplies extra cubic decay, so any improvement to
the height deficit must come from arithmetic denominator extraction or a
different integral model.

### Other candidates checked and cleared

- **Van Assche (arXiv:math/0101187, little q-Legendre and Lambert series)** and
  **Krattenthaler–Rivoal–Zudilin (arXiv:math/0311033, q-analogues of zeta values
  and Eisenstein series)**: local annexes present. Neither is an exact evaluation
  of `V_N^*`. Searches for exact Hankel evaluations with matching leading
  coefficients returned only unrelated determinant-evaluation literature.
- **Bundschuh–Väänänen, Compositio Math. 91 (1994), 175–199, Theorem 2**: this
  is the external analytic engine used elsewhere in the #1049 programme, per
  `prior_art_routes/erdos1049_rational_base_lambert_v0.json`. It owns an
  irrationality implication, not a Hankel-order evaluation.
- Hankel determinants of the `τ(n)` generating series: searched, nothing located
  bearing on this determinant.

### Relation

**strictly_stronger_than_prior**. Zudilin 2016 proves an inequality on the
`q`-order; our claim upgrades it to an equality and adds an exact leading
coefficient. The strengthening is real and its evidence class is mixed.

Confidence: **high** that Zudilin 2016 states only the inequality (TeX read
verbatim); **high** that no exact evaluation was located; **medium** for the
general-`N` mathematics, since the Lean formalisation of rows `j ≥ 2` and of the
determinant identification is incomplete and the exact verification stops at rank
7.

### What our paper must say

Zudilin's 2016 backward-shift argument gives the lower bound
`ord_q V_N^* ≥ N(N−1)(2N−1)/6`, and our result upgrades that to an equality with
the exact leading coefficient `(N!)²(N+1)!/2^N`. The equality is verified
exactly through rank seven, the general-rank argument is ordinary mathematics
whose formalisation stops at the first transformed row, and its consequence is
that no additional cubic analytic decay is hiding in this determinant.

---

## Summary table

| # | Claim | Closest primary antecedent | Relation | Confidence |
|---|---|---|---|---|
| 257 | `∑_{a∈A} 1/(b^a−1)` irrational for every infinite reciprocal-summable `A` and every integer `b ≥ 2` | Erdős, Math. Student 36 (1968), 222–226: printed theorem (coprime, every `t ≥ 2`) plus stated-but-unproved extension dropping coprimality | **matched** to the stated extension; **strictly_stronger_than_prior** than the printed theorem. The all-base quantifier is Erdős's, not ours | High for statement identity; medium-high for absence of an independent published proof |
| 1041 | sharp constant `2` under critical-value separation (`S=4, n≥3`; `S=3, n≥4`; `S=2, n≥7`), plus unconditional `(71/10)μ^{1/n}` inside `K_{2μ}` | Pendyala, arXiv:2606.24875 (degree four, unconditional, `<2`); Pendyala, arXiv:2606.19178 (`c√log n ≤ S(n) ≤ πn`); shtuka manuscript (general, contested) | **incomparable** to both Pendyala papers; **unknown** relative to the contested general manuscript | High for Pendyala; low-medium for shtuka |
| 249 | odd-core basis for all dyadic sections of `φ`, exact rank `2^e+1` through level `e` | Coons, J. Théor. Nombres Bordeaux 22 (2010), 339–352, Thm 3.2: `φ` is not `k`-regular for any `k ≥ 2` | **strictly_weaker_than_prior** for the non-regularity remark; **unknown** for the explicit basis and exact ranks; composite **incomparable** | High for Coons; medium for the basis being unanticipated |
| 269 | two primes give an outer-product kernel, three give nonsingular minors of every order and no finite separation | Steve Fan, erdosproblems.com #269 comment, 26 June 2026: general-`k` LCM identity, `k=2` factorisation `S = S₁S₂`, transcendence via Hecke–Mahler | **matched** (and **strictly_weaker_than_prior**) for the LCM identity and two-prime half; **unknown** for the three-prime rank theorem | High for Fan; medium-high for the three-prime half |
| 1049 | `ord_q V_N^* = N(N−1)(2N−1)/6` exactly, leading coefficient `(N!)²(N+1)!/2^N` | Zudilin, Res. Number Theory 2 (2016), Art. 15, arXiv:1601.02688, §4: `ord_q V_N^* ≥ N(N−1)(2N−1)/6` | **strictly_stronger_than_prior** | High for the antecedent; medium for the general-`N` evidence class |

## Substrate corrections this pass surfaced

1. `ExternalVerification257ReciprocalSupport/README.md` describes Erdős's 1968
   theorem as base-two and calls the all-base transfer a local strengthening.
   The primary source proves it for every `t ≥ 2`. The repository's own
   `prior_art_routes/reciprocal_summable_supports_base_two_v0.json` already has
   the correct reading. The README should be brought into line with the route.
2. The #269 packet should cite Steve Fan for the running-LCM identity rather
   than presenting the three-prime case of it as a finding.
3. The #249 flagship statement should not carry non-2-regularity, which Coons
   settled in 2010 for every `k`.
4. The #1049 antecedent is Zudilin 2016, not Zudilin 2004.
5. The #1041 threshold for `S = 4` is `n ≥ 3` as proved in Lean, not "all `n`".

## Searches run

arXiv metadata and abstract fetches for 2406.17593, 2606.24875, 2606.19178,
2606.23681, 2601.20743, 2601.21442, 2504.05933, 2504.18712, 2312.13673,
2512.12455, 1601.02688. Live fetches of the erdosproblems.com discussion threads
for #257, #249, #269, #1041 on 2026-09-02. Local hash-pinned primary sources read
from `annexes/` for Erdős 1968, Duverney–Tachiya 2019, Coons 2010, Zudilin 2016,
Zudilin 2004, and the archived erdosproblems pages for #249, #257, #269, #1041.
Keyword sweeps for: Ahmes series irrationality; Lambert subseries; `k`-kernel and
`k`-regular Euler totient; running-LCM and smooth-number rank results;
Erdős–Herzog–Piranian path and constant-factor lemniscate bounds; exact Hankel
determinant evaluations in the Krattenthaler, Rivoal, Van Assche, and Zudilin
families.

Two searches were weak and are recorded as unfinished rather than as absence:
the explicit `k`-kernel basis literature for arithmetic functions, and the
classical potential-theoretic lemniscate literature (Eremenko–Hayman,
Pommerenke, Dubinin) for degree-free root-connecting path bounds.

---

## Second pass 2026-09-02 (night)

Audit date: **2026-09-02**, night pass. Scope: the six claim groups named in the
night's wave brief, which are the claims the corpus is closest to publishing and
which the first pass of this document did not cover. The working assumption
again was that a published paper already contains the theorem.

Machine-readable companion: `prior_art_dispositions_v1.json` in this directory
(schema `prior_art_dispositions_v1`), one record per claim key, joinable by
`claim_key`.

Dispositions used: `new` (no antecedent found after a named search),
`extends <cite>` (strictly stronger than a printed statement), `matches <cite>`
(already proved elsewhere), `weaker_than <cite>` (never present as new),
`unresolved` (a named search that could not be completed).

Live fetches this pass. `erdosproblems.com` returns HTTP 403 to the plain fetch
tool; every page below was retrieved with an explicit browser user agent on
2026-09-02 and converted to text locally. Problem pages and forum threads read
in full: `/68`, `/243`, `/249`, `/251`, `/257`, `/269`, `/1041`, `/1049` and the
matching `/forum/thread/<n>` pages.

---

### A1. #1049 — `F(31/4)` is irrational

**Our exact statement.** `ErdosProblems/Erdos1049/ZudilinRationalHomogenisationDerivation.md`, §2,
read this pass:

> "**Theorem (authored; conditional on Zudilin 2004 Lemma 7 and Lemma 2).**
> Let `a > b ≥ 1` be coprime integers with `log b / log a < C_0/C_1 = 0.405683…`.
> Then `h_{a/b}(1) = Σ_{m≥1} 1/((a/b)^m − 1) ∉ Q`. In particular `F((31/4)^r)` is
> irrational for every `r ≥ 1`, since `log 4/log 31 = 0.40370 < 81/200 < θ*`."

Evidence band: `verified_current` for the text; the correctness of the argument
is `reported_prior` (an adversarial pass on 2026-09-02 attacked seven points and
broke none; no kernel check).

**Disposition: `extends Bundschuh–Väänänen 1994, Theorem 2, second half`.**

**Antecedent.** P. Bundschuh and K. Väänänen, "Arithmetical investigations of a
certain infinite product", Compositio Math. **91** (1994), 175–199, Theorem 2,
printed p. 177. Local hash-pinned copy
`annexes/numdam-cm-1994-91-bundschuh-vaananen-infinite-product/source.pdf`,
page images read this pass. Verbatim:

> "THEOREM 2. Let v, q, λ and α be as in Theorem 1, and suppose further
> λ < 3/(2 + 3π^{−2}). Then there exists an effectively computable γ ∈ R_+,
> independent of **a**, such that for each **a** = ^t(a_0, a_1) ∈ K² with h(**a**)
> sufficiently large we have the inequality
> |a_0 E_q(α) + a_1 E'_q(α)|_v ≥ |**a**|_v h(**a**)^{−3d/(3−λ(2+3π^{−2}))d_v − γ(log h(**a**))^{−1/2} log log h(**a**)}.
> In the special case α = −1 we may even allow λ < (1/2 + 1/π²)^{−1}, and then we
> can say
> |a_0 E_q(−1) + a_1 E'_q(−1)|_v ≥ |**a**|_v h(**a**)^{−d/(1−λ(2^{−1}+π^{−2}))d_v − γ*(log h(**a**))^{−1/2} log log h(**a**)}"

and, p. 177, the identification that makes α = −1 our series:

> "L_q(z) := E'_q(z)/E_q(z) = Σ_{j=1}^∞ (q^j + z)^{−1} … Now, the linear
> independence of E_q(α) and E'_q(α) over Q is equivalent with the irrationality
> of L_q(α), and this is exactly Borwein's [4] nice result giving a positive
> answer to a question of Erdős [7]."

Evidence band: `embedded_evidence`.

**The precise delta.** For `q = a/b` in lowest terms, `λ = log a / log(a/b)`, so
Bundschuh–Väänänen's admissible region for the q-harmonic series is
`log b / log a < 1/2 − 1/π² = 0.3986788…`. Ours is
`log b / log a < C_0/C_1 = 0.4056830…`. The delta is the strip
`(0.3986788, 0.4056830]`, and `31/4` sits inside it at
`log 4 / log 31 = 0.4036985…`. Nothing else changes: same series, same shape of
hypothesis, same conclusion.

**Three qualifications that must appear wherever this is claimed.**

1. **Zudilin has already announced the shape.** W. Zudilin, "On the irrationality
   of generalized q-logarithm", Res. Number Theory **2** (2016), Art. 15,
   arXiv:1601.02688, §2, closing paragraph (TeX source read this pass, lines
   200–202):

   > "Finally, we remark that the results can be given for non-integer p = r/s,
   > |p| > 1, as well under a customary in such situations assumption
   > log|r| > c log|s| for some computable constant c > 0."

   The constant is not named there and no proof is given, so the region is not
   printed anywhere. What our theorem adds over that remark is the explicit
   constant `c = C_1/C_0 = 2.46497868…` and therefore a decidable membership
   test for any given base. It is not a new kind of statement.
2. **A second published rational-base region exists and is weaker.** D. Duverney,
   "À propos de la série Σ_{n=1}^{+∞} x^n/(q^n − 1)", J. Théor. Nombres Bordeaux
   **8** (1996), 173–181, Théorème 2, printed p. 174 (PDF fetched live from
   numdam this pass, page image read):

   > "THÉORÈME 2. Soit K = Q[i√d] ou K = Q. Soit q ∈ K, avec q = r/s, r, s ∈ R.
   > On suppose que : (4) δ = log|s|/log|r| < (1/3)(1 − 3/π²). Alors
   > Σ_{n=1}^{+∞} 1/(q^n − 1) ∉ K."

   `(1/3)(1 − 3/π²) = 0.2320…`, well inside Bundschuh–Väänänen's region.
   Duverney's Théorème 1 (general `x`) has the still smaller threshold
   `(1/4)(3 − √(5 + 24/π²)) = 0.06847…`. Both must be cited; neither reaches
   `31/4`.
3. **The evidence class is the weakest of any claim in this document.** The
   theorem is conditional on Zudilin 2004 Lemma 7 (a statement in `Z[p]`) and
   Lemma 2, is not kernel-checked, and rests on a reconstruction of a Type B
   derivation. The finite part `θ* > 81/200` is Lean-checked in
   `ZudilinHeightRegion.lean`; the analytic part is not.

**Other candidates checked and cleared.**

- **W. Zudilin, "Heine's basic transform and a permutation group for q-harmonic
  series", Acta Arith. **111**:2 (2004), 153–164.** Annex
  `annexes/zudilin-2004-heine-q-harmonic-series/`, read this pass. §2 opens
  "Throughout the paper p = 1/q ∈ Z \ {0, ±1}", and Theorem 1 is the
  irrationality-exponent bound `μ(h_p(1)) ≤ 2.46497868…` for integer `p`. There
  is no rational-base statement in the paper. It supplies the forms, not the
  result.
- **P. Bundschuh and W. Zudilin, "Irrationality measures for certain
  q-mathematical constants", Math. Scand. **101**:1 (2007), 104–122.** Abstract
  and Theorem 1 checked live: `q ∈ Z \ {0, ±1}`.
- **P. Bundschuh and K. Väänänen, "Quantitative linear independence of an
  infinite product and its derivatives", Manuscripta Math. **129**:4 (2009),
  423–436.** Abstract checked live: "q ≠ 0, ±1 being a fixed integer".
- **T. Matala-aho, K. Väänänen and W. Zudilin, "New irrationality measures for
  q-logarithms", Math. Comp. **75** (2006), no. 254, 879–889.** Not on arXiv and
  the AMS full text is paywalled; the abstract-level material located gives
  irrationality measures (e.g. `Ln_q(2)`) and no rational-base region. Recorded
  below as an unfinished search.
- **J. Koizumi and A. Yokoi, "Apéry-type approximations and irrationality
  measures for certain q-series", arXiv:2608.26918 (27 Aug 2026).** Abstract
  fetched live: "for every integer x with |x| ≥ 2, the values at r = x^{−1}".
  Reciprocal-integer argument only; the q-harmonic series with rational base is
  not covered.
- **erdosproblems.com/1049 and its forum thread, fetched live 2026-09-02**
  (3 comments, page last edited 28 September 2025). The whole thread is
  RomanLeLan asking for a scan of Chowla's 1947 paper and Thomas Bloom supplying
  the Internet Archive link. Nothing mathematical, and no rational-base claim.
  Status **OPEN**, 0 proof claims.

**Searches run.** Web searches: `Matala-aho Väänänen Zudilin "New irrationality
measures for q-logarithms" Math. Comp. 2006`; `Zudilin "Remarks on irrationality
of q-harmonic series" Manuscripta Mathematica 2002`; `Duverney "À propos de la
série" "q^n-1" Journal de théorie des nombres de Bordeaux 1996 numdam`;
`irrationality "q-harmonic series" rational q "p/r" non-integer base Lambert
series log denominator condition`; `"q-mathematical constants" Bundschuh Zudilin
Math Scand 2007`; `Bundschuh Väänänen "Quantitative linear independence of an
infinite product and its derivatives"`. Sources fetched:
`numdam.org/item/JTNB_1996__8_1_173_0.pdf` (read as page images);
`math.ru.nl/~wzudilin/publications.html`; `arxiv.org/abs/2608.26918`;
`api.semanticscholar.org` citation list for arXiv:1601.02688 (7 citing works,
enumerated below under A2). Local primary sources read: Bundschuh–Väänänen 1994
(page images 3–4), Zudilin 2004 (`extracted.md`), Zudilin 2016 (`source.tex`,
whole file). Bibliography of Zudilin 2016 read entry by entry and each q-series
irrationality reference checked for a rational-base hypothesis.

**Confidence: medium-high** that no printed rational-base region reaches
`log 4 / log 31`, since the three standing regions (Duverney 1996,
Bundschuh–Väänänen 1994, Zudilin 2016's unquantified remark) were read directly
and the surrounding bibliography was walked; **medium** overall, because
Matala-aho–Väänänen–Zudilin 2006 was not read in full and because the claim's
own proof is unverified by any kernel.

---

### A2. #1049 — sharp all-rank Hankel order and leading coefficient

**Our exact statement.** `ord_q V_N^* = N(N−1)(2N−1)/6` exactly, with leading
coefficient `(N!)²(N+1)!/2^N`, for every rank `N`.

**Disposition: `extends Zudilin 2016, §4`.** Unchanged from §5 of the first pass
of this document, which quoted the antecedent verbatim from
`annexes/arxiv-1601-02688-zudilin-generalized-q-logarithm/source.tex`:

> "Our crucial observation here is that the q-expansion of `V_n^*` starts from at
> least `q^{n(n−1)(2n−1)/6}`, so that `|V_n^*| ≤ |q|^{n³/3} exp(O(n²))`."

**What this pass adds.** The brief asked for "anything citing it". The Semantic
Scholar citation graph for arXiv:1601.02688 was fetched live on 2026-09-02 and
returns seven citing works: Koizumi–Yokoi 2026 (arXiv:2608.26918, Apéry-type
approximations, reciprocal-integer arguments); Anđelić–da Fonseca–Kızılateş–
Terzioglu 2025 (higher-order Gauss Fibonacci numbers, uses the generalized
q-logarithm only as a generating function); Dixit–Kumar–Pathak 2022/2023 (linear
independence of q-exponential values for Pisot–Vijayaraghavan q); Dixit–Maji 2018
(a three-parameter q-series identity, partition-theoretic); and Zudilin's own
arXiv:1507.05697 in two versions. None evaluates `V_N^*` exactly, and none states
a leading coefficient. No antecedent added, no antecedent removed.

**Searches run.** Semantic Scholar graph API citation listing for
arXiv:1601.02688 (100-result limit, seven returned), plus the first pass's
sweeps over Van Assche, Krattenthaler–Rivoal–Zudilin and exact Hankel
determinant evaluations.

**Confidence: high** for the antecedent and for the citation sweep;
**medium** for the general-`N` mathematics, unchanged from the first pass, since
the exact verification stops at rank 7 and the Lean formalisation stops at the
first transformed row.

---

### B1. #257 — the 1/21 fatal-branch dichotomy

**Our exact statement.** `ErdosProblems/Erdos257/research_packet.json`,
`exact_results` id `one_over_twenty_one_fatal_aligned_branch_classification`,
read this pass:

> "Non-membership is equivalent to one explicit branch carrying a fatal greedy
> witness, finite skipped support and hence cofinite selected support, eventual
> full quotient/rational-greedy alignment, and eventual occupation of every
> doubling block. Equivalently, 1/21 belongs to the Mersenne achievement set
> exactly when this fatal/cofinite/aligned branch is impossible. This is an exact
> logical classification, not a proof that the branch is impossible or that 1/21
> is represented."

**Disposition: `new`, and it must not be published as a result.**

No antecedent was located. The whole `1/21` literature is this repository's own;
`1/21` does not appear anywhere on erdosproblems.com/257, in Erdős 1948, in
Erdős 1968, in Borwein 1991/1992, or in Duverney–Tachiya 2019. The reason to
record a disposition at all is the opposite hazard.

**Why it must not be published as a result.** The statement is an equivalence
between an open membership question and a conjunction of open branch conditions.
The corpus's own sweep says so:
`docs/formal_math/comparator_architecture/discovery/erdos257_anchored_results.md`,
"Deliberately excluded (checked, and they fail the anchor test)", reads:

> "**Everything in the `1/2` and `1/21` lanes.** … are all conditional theorems
> whose hypothesis carries the whole difficulty … Bare iffs and reductions by the
> rubric's own exclusion."

That agrees with the standing editorial rule recorded for this programme, that a
reduction is not a result. The claim's place is a lemma inside a paper whose
headline is the all-base reciprocal-summable theorem, or nowhere.

**Searches run.** erdosproblems.com/257 and `/forum/thread/257` fetched live
2026-09-02 (6 comments, page last edited 15 April 2026) and read in full: the
mathematical content is Vjeko Kovač's 30 Oct 2025 refutation of the
`Σ 1/(2^n − t_n)` variant, Quanyu Tang's 5 Sep 2025 Tachiya period-2 citation,
Kovač's reply reducing the even and odd cases to Erdős and Borwein, Kovač's
25 Aug 2025 fat-Cantor remark, and Kovač's 9 Aug 2025 remark citing Boes–Darst–
Erdős for fat Cantor sets containing no rationals. Nothing about `1/21`, greedy
membership, or branch classification.

**Confidence: high** that no antecedent exists (the object is repository-local);
**high** that the statement is a reduction rather than a result.

---

### B2. #257 — the general rational membership criterion

**Our exact statement.** Same packet, id
`rational_greedy_skip_cofinality_characterization`:

> "For every nonnegative rational q, Lean proves that q belongs to the Mersenne
> achievement set if and only if its canonical greedy orbit omits infinitely many
> positive exponents, equivalently if and only if the actual greedy branch skips
> at arbitrarily late ranks. The forward implication uses irrationality of the
> full Erdős–Borwein constant… This is a general rational normal form, not a
> proof of cofinal skips for 1/2, 1/21, or any other unresolved target, and it
> does not decide Erdős Problem 257."

**Disposition: `new` for the statement as written, on a search that did not
close.**

**What was found instead.** The ambient theory is classical and must be cited
rather than rediscovered. The set in question is the achievement set (set of
subsums) of the sequence `1/(2^n − 1)`, and the achievement set literature owns
the trichotomy that governs it: Guthrie–Nymann, and the later
Banakh / Bartoszewicz / Głąb / Marchwicki line, prove that an achievement set is
a finite union of closed intervals, a Cantor set, or a Cantorval. Kakeya (1914)
owns the interval/Cantor conditions. On the problem page itself Vjeko Kovač
already frames `1/21`'s ambient object correctly (9 Aug 2025, fetched live):

> "The set S = { Σ_{n∈A} 1/(2^n − 1) : A ⊆ N } appearing in [257] now has empty
> interior … Namely, the above set S still has positive Lebesgue measure, i.e.,
> it is a fat Cantor set. Thus, S 'almost surely' contains, say, at least one of
> the dyadic rationals 1/2, 1/4, 1/8, … However, this argument alone cannot be
> turned into a rigorous proof, since there exist fat Cantor sets containing no
> rational numbers; a nonconstructive proof was given by Boes, Darst, and Erdős."

The reverse direction of our criterion (a point of a Cantor-type achievement set
is reached exactly when the greedy remainder is exhausted) is the standard greedy
lemma for such sets and should be presented as folklore. The genuinely local part
is the forward direction, which spends irrationality of the Erdős–Borwein
constant to rule out finitely many omissions.

**Searches run.** `"achievement set" OR "set of subsums" series greedy algorithm
characterization membership Cantor set Nymann Sáenz Banakh Bartoszewicz Głąb`;
`subsums of series greedy algorithm criterion "x belongs to the set of subsums"
if and only if infinitely many omitted terms`; erdosproblems.com/257 thread as
above.

**Search not completed.** The achievement-set corpus (Guthrie–Nymann;
Bartoszewicz–Głąb–Marchwicki; "Achievement sets of reciprocals of complete
sequences", Results Math. 2023; "On Kakeya conditions for achievement sets") was
identified but not read. A greedy membership criterion of exactly this shape is
the kind of statement that corpus would carry as a lemma. Until it is read, the
honest reading is `new` at **medium** confidence, not firstness.

---

### C1. #249 — explicit rational basis of the totient 2-kernel, rank `2^e + 1`

**Our exact statement.** Unchanged from §3 of the first pass:
`LinearIndependent Q oddCoreTotientKernelFamily`, equality of the two spans, and
`finrank Q (span (range (totientKernelThroughLevelFamily e))) = 2^e + 1` for
every `e ≥ 1`.

**Disposition: `extends Coons 2010, Theorem 3.2` on the qualitative axis, and
`new` for the basis and the exact rank, on a search that did not close.**

**Antecedent.** M. Coons, "(Non)Automaticity of number theoretic functions",
J. Théor. Nombres Bordeaux **22** (2010), no. 2, 339–352. Annex
`annexes/coons-2010-nonautomaticity-number-theoretic-functions/extracted.md`,
read again this pass. Theorem 3.2: "The function φ(n) is not k–regular for any
k ≥ 2", proved on printed p. 349 from `Σ φ(n)n^{−s} = ζ(s−1)/ζ(s)` and the
density of poles of `1/ζ(s)`. Coons's §1 also carries the definition our claim
reuses verbatim:

> "Define the k–kernel of T as the set T(k) = {(t(k^l n + r))_{n≥0} : l ≥ 0 and
> 0 ≤ r < k^l}. Given k ≥ 2, we say a sequence T is k–automatic if and only if
> the k–kernel of T is finite."

So Coons owns the object and owns infinitude of the kernel. He computes no rank,
exhibits no spanning family, and does not say which dyadic sections are
redundant. Our delta is the finite-level quantity: rank exactly `2^e + 1`, with
the even-residue channels identified as the entire redundancy.

**Searches run.** `Allouche Shallit k-kernel dimension rank Euler totient
function regular sequence`; `Jason Bell k-regular sequences kernel dimension
rank multiplicative function`; `"k-kernel" rank basis Euler totient function
2-adic dyadic sections phi(2^j n + r)`; `"2-kernel" OR "dyadic kernel" rank
dimension arithmetic function truncated level formula 2^e+1`; `Allouche Shallit
"Automatic Sequences" book phi Euler totient not automatic kernel infinite
example`. erdosproblems.com/249 and `/forum/thread/249` fetched live.

**Search not completed.** Allouche's 1992 paper and Yazdani's thesis, both cited
inside Coons 2010 as the sources for the non-automaticity technique, were located
only through secondary summaries and were not read. Jason Bell's work on
`k`-regular sequences addresses growth exponents and joint spectral radii rather
than finite-level rank, but was likewise not read in full.

**Confidence: high** for Coons; **medium-low (0.55)** that the explicit basis and
the exact rank have no antecedent.

---

### C2. #249 — all-rung strict log-concavity of the signed Möbius–Mersenne ladder

**Our exact statement.** `Θ_r Θ_{r+2} < Θ_{r+1}²` at every rung, killing any
nonnegative Stieltjes representation.

**Disposition: `new` for the log-concavity, `matches` for the underlying
series identity, on a search that did not close.**

**Antecedent for the object, not the theorem.** The series the ladder is built on
is already public. erdosproblems.com/249 forum thread, fetched live 2026-09-02,
Steve Fan, 19:01 on 16 May 2026:

> "Though perhaps very obvious, it may be worth mentioning that the convolution
> identity φ = μ ∗ id yields Σ_{n≥1} φ(n)/2^n = Σ_{n≥1} μ(n)/(2^n − 1)² + 1/2."

That is the `Σ_n μ(n)/(2^n − 1)²` family the ladder indexes. It is Fan's, it is
dated, and it must be cited rather than presented as ours. The first pass of this
document already recorded that comment; this pass records that it is the object
of the log-concavity claim, not merely adjacent.

No log-concavity, Hankel-positivity or moment-representation result for this
family was located.

**One mathematical flag for the authors, not a citation.** Stieltjes moment
sequences are log-convex, not log-concave. A statement that strict log-concavity
"kills any nonnegative Stieltjes representation" is only correct if `Θ_r` is
being compared against the right moment class; check the polarity against the
internal draft before it is printed.

**Searches run.** `log-concavity Hankel determinant Mobius Mersenne series moment
problem Stieltjes`; `"log-concave" moment sequence Mobius function totally
positive arithmetic`; erdosproblems.com/249 thread in full (2 comments, page last
edited 28 September 2025).

**Confidence: high (0.9)** that Fan owns the identity; **medium-low (0.5)** that
no log-concavity antecedent exists, since the search terms were narrow.

---

### D1. #68 — the companion-orbit rationality boundary

**Our exact statement.** `ErdosProblems/Erdos68/research_packet.json`,
`exact_results` id `companion_constant_full_floor_one_residue_normal_form`, read
this pass:

> "Let C = Σ_{n≥2} 1/(n!(n!−1)) = S − e + 2. Under a hypothetical rational value
> S = a/b, every sufficiently large m has m!(S+2) divisible by m … Hence
> floor(m!C) congruent to −2 modulo m eventually. Conversely, the congruence is
> exactly the canonical factorial-digit condition d_m(C) = m−2 for m ≥ 3; if it
> holds eventually, the tail identity Σ_{m>N}(m−2)/m! = 1/N! − Σ_{m>N} 1/m! shows
> C + (e−2) = S is rational. Thus S is irrational exactly when floor(m!C) misses
> −2 modulo m cofinally."

The same row records its own boundary: "The complete infinite-tail equivalence is
presently the analytic argument recorded in CarryCongruenceLab, not a claim that
the cofinal miss producer has been proved."

**Disposition: `extends` the classical factorial-base rationality criterion.**

**Antecedent.** The criterion that a real number is rational exactly when its
canonical factorial-base (Cantor series) digits vanish from some index on. Due to
Cantor, "Über die einfachen Zahlensysteme", Z. Math. Phys. **14** (1869),
121–128; standard modern reference J. Galambos, *Representations of Real Numbers
by Infinite Series*, Lecture Notes in Math. 502, Springer 1976, Chapter 1. One
direction is the observation that `S = a/b` makes `m! S` an integer for `m ≥ b`;
the other is the tail bound.

**The precise delta.** Our statement is that criterion transported along an
explicit companion telescope. Because `e − 2 = Σ_{n≥2} 1/n!` has factorial-base
digit 1 at every index, subtracting it from a rational whose digits eventually
vanish borrows at every place and produces digit `m − 2` eventually; that is
where the `−2` comes from. The delta is the telescope `C = S − e + 2` (Lean-
checked as `companion_constant_telescope_and_lower_window_certificate`), the
identification of the digit value, and the observation that the same shape
survives for the whole family `Σ 1/(n! + t)` after a sign adjustment. The
difficulty is entirely in the unproved cofinal-miss producer, so this is a
reduction in the same sense as B1, and the same editorial rule applies.

**Other candidates checked and cleared.**

- **erdosproblems.com/68 and `/forum/thread/68`, fetched live 2026-09-02.**
  Status **OPEN**, page last edited 28 September 2025, **0 comments**. There is
  no criterion of any kind recorded there, and therefore nobody has posted this
  one.
- **The erdosproblems.com survey thread `blog:4`** ("Paul Erdős and irrationality
  problems for series", Vjeko Kovač, 2 February 2026), fetched live this pass,
  discusses #68 at length as fully open, with Wilson's-theorem divisor probes and
  Bessel/Siegel–Shidlovsky detours in the comments, and states:

  > "Erdős asked if Σ_{n=2}^{∞} 1/(n!−1) is irrational and this is still an open
  > problem [68], despite the fact that we can today compute as many digits of
  > this number as we wish."

  No floor-mod-`m` criterion appears in the thread.
- **arXiv:2601.21442** ("Irrationality of rapidly converging series: a problem of
  Erdős", Jan 2026), **arXiv:2504.18712** (super-polynomially decaying series),
  **arXiv:2406.17593** (Ahmes series), **arXiv:1206.0340** (Vandehey, an
  incomplete argument of Erdős on `Σ d(n)x^n`). All fetched and checked; none
  mentions `n! − 1`, none carries a floor-mod criterion, and 2601.21442
  explicitly leaves the `n! − 1` case open.
- **Sondow's irrationality-criterion machinery** (the Smarandache–Kempner
  function `S(n) = min{k : n | k!}` and `|e − m/n| > 1/(S(n)+1)!`) was searched
  directly and is a different shape.

**Searches run.** `Sondow floor(m! x) mod m irrationality criterion factorial
series`; `Hancl Sobkova irrationality sum 1/(n!-1) factorial denominator`;
`Erdos problem sum 1/(n!-1) irrational denominator lower bound rational`;
`"n!-1" irrationality 2025 2026 arxiv Erdos series factorial`; `Sondow Cahen
criterion "e is irrational" geometric proof mod m floor factorial`; `"Erdos
problem 68" OR "sum 1/(n!-1)" 2026 arxiv preprint partial result companion
series`.

**Search not completed.** The Hančl / Hančl–Sobková / Hančl–Tijdeman corpus on
linearly unrelated sequences was reached only through search digests, never
fetched.

**Confidence: high** that the classical criterion is the right ancestor;
**medium (0.6)** that no published paper states this companion form.

---

### D2. #68 — the finite denominator exclusions

**Our exact statements.** `q ∤ 299999!` (packet id
`kempner_index_denominator_exclusion`, Lean-checked consumer with a finite
certificate input) and `q ≥ 2^39991 > 10^12039` (packet id
`certified_continued_fraction_denominator_exclusion`, 23,449 partial quotients
each forced by a rigorous rational bracket at `B = 80000` bits).

**Disposition: `new` as numbers, on a classical method.**

The method is textbook: if `S = a/q` then the continued fraction terminates and
`q ≥ q_{n+1}` for any certified prefix of length `n+1`; and a non-unit carry at
index `m` forces the Smarandache–Kempner function of `q` to be at least `m`. No
published denominator bound for `Σ_{n≥2} 1/(n! − 1)` was located anywhere: not on
the problem page (0 comments), not in the February 2026 survey thread, not in
OEIS material for the constant, not in the four recent arXiv papers listed under
D1.

**Framing constraint.** Finite exclusions of this species have already been read
by an external moderator as not bankable. They belong in a computational section,
never in an abstract, and never as the lead.

**Searches run.** As under D1, plus the OEIS entry for the constant reached
through search digest only.

**Confidence: medium (0.5)**. This is the weakest absence claim in the document:
a narrow computational exclusion is exactly what a keyword search misses, and it
could sit unpublished in someone's note.

---

### E0. #1041 — correction to §2 of the first pass: the shtuka manuscript is withdrawn by its author

§2 of this document, written earlier on 2026-09-02, recorded the disposition
against the anonymous "shtuka" manuscript as **unknown**, "since the manuscript's
current revision was not read this pass and the countermodel was not re-derived".
That is now settled and the answer is not unknown.

The manuscript was fetched this pass from `https://shtuka123.github.io/1041/main.pdf`
(HTTP 200, 598,762 bytes, 48 pages). Its PDF metadata gives
`CreationDate: Tue Mar 24 18:27:36 2026 GMT` and the same `ModDate`: the file has
never been revised. Its Proposition 12, p. 16, reads:

> "Proposition 12. Let 0 ≤ c < 2α, and let V be a connected component of {u > c}
> containing exactly m zeros of f. … Then for every ε > 0 there exists a finite
> embedded tree G_ε ⊂ V containing all m zeros of f in V and satisfying
> len(G_ε) ≤ (1/2π)∫_{2α}^{∞} P_v(t) dt + ε."

Terence Tao, erdosproblems.com/1041 thread, 04:44 on 25 March 2026, fetched live:

> "I now believe that there is a serious issue with Proposition 12, in that the
> topological claims made by the AI are not actually correct. In particular, the
> invocation of Lemma 8 on page 21 is unjustified, and likely unjustifiable,
> because the boundary of the sets S outside of flow-line sides will typically be
> contained in more than two level sets."

The author conceded, same thread, 20:17 on 26 March 2026:

> "I agree, after some more inspection I believe that even the statement of Prop
> 12, (not just the proof) is incorrect, and so this strategy is doomed to fail.
> I am exploring some more analytic alternatives, but have not had success yet.
> Thanks everyone for your comments!"

A second general-degree attempt, posted by kasko37 on 22 April 2026
(`https://www.overleaf.com/read/bsngbyycrrbd#10ebf2`, "GPT-5.4 Thinking announces
the solution"), was broken five days later by Nat Sothanaphan, 18:49 on
27 April 2026:

> "With the new GPT-5.5 release, I've run standard check which decisively found a
> serious gap. In proof of Lemma 6, the subharmonicity is oddly applied to
> conclude |φ'(r)| ≤ (1/2π)∫_0^{2π}|φ'(re^{iθ})| dθ. (LHS should be at the circle
> center i.e. |φ'(0)|.) GPT's opinion is that this is not easily repairable.
> Also, Ho Boon Suan has earlier messaged me with his own check which pointed out
> this same exact gap."

The newest comment on the thread is Venkata Pendyala's own announcement of the
quartic case, 02:16 on 24 June 2026. The problem page shows **OPEN**, 0 proof
claims.

Consequence for our framing. The general problem is open, no general-degree
manuscript stands, and the first pass's "genuine hazard" has evaporated. The
Cassini countermodel recorded in
`prior_art_routes/erdos1041_lemniscate_short_path_v0.json` is no longer
load-bearing for the disposition, because the author withdrew the proposition
independently. Nothing subsumes E1 or E2.

Evidence band: `embedded_evidence`.

---

### E1. #1041 — first-merge critical-value separation with exact thresholds

**Our exact statement.** `ErdosProblems/Erdos1041/FirstMergeCriticalValueSeparation.lean`,
read this pass at current HEAD:

```lean
noncomputable def firstMergeSquaredCoefficient (n : ℕ) (S : ℝ) : ℝ :=
  (1 + S) ^ ((2 : ℝ) / (n : ℝ)) * Real.log (S / (S - 1))

theorem firstMerge_exact_convenient_thresholds :
    (∀ n : ℕ, 3 ≤ n → firstMergeSquaredCoefficient n 4 < 1) ∧
    (∀ n : ℕ, 4 ≤ n → firstMergeSquaredCoefficient n 3 < 1) ∧
    (∀ n : ℕ, 6 ≤ n → firstMergeSquaredCoefficient n 2 < 1)
```

with the module's own sharpness note at line 166: "`3^(2/n) log 2 < 1`. Six is
sharp, since `3^(2/5) log 2` exceeds one." Recomputed here:
`3^{1/3} log 2 = 0.99969…` and `3^{2/5} log 2 = 1.07566…`.

**Correction to §2 of the first pass.** That section quoted the `S = 2` threshold
as `7 ≤ n`. The current source says `6 ≤ n` and proves sharpness at 6; the change
landed in commit `e4cd1d63ef`, "Erdos 1041: the radius-2 threshold is sharp at
degree 6". Publish `n ≥ 6`, not `n ≥ 7`.

**Disposition: `new`, with one citation gap that must be closed first.**

No published critical-value-separation criterion of this shape was located. The
literature that surrounds the mechanism is about a different Erdős problem, the
arclength of `{|p| = 1}` (problem #114), and is listed under E2.

**The citation gap.** Tao's 25 March 2026 comment on the #1041 thread, fetched
live, derives the area bound our own capacity-closure step uses from a named
paper:

> "By Theorem 1 of this paper of Dubinin (a Pólya type inequality), this area is
> at most `s^{2/m}` times the area of `U`; and by the classical Pólya inequality,
> `U` has area at most `π`."

V. N. Dubinin, "Some inequalities for polynomials and rational functions
associated with lemniscates", is not in the bibliography of
`ErdosProblems/papers/erdos-1041-lemniscate-newton-flow.tex`, whose bibliography
carries only `bloom`, `ehp1958`, `march2026`, `june2026`, `pendyala2026shortest`
and `polya1928`. Dubinin's Theorem 1 must be cited before any external
submission, and its full text must be read to confirm it does not already contain
a sharper form of the area input. It was not obtained this pass.

**Relation to Pendyala.** Unchanged from the first pass: **incomparable** to
arXiv:2606.24875 (degree four, unconditional) and to arXiv:2606.19178 (a
different quantity, the longest shortest path from the origin to the unit circle
inside `E_f`). Pendyala's full arXiv listing was enumerated this pass
(31 items; the math.CV ones are 2606.17097, 2606.19178, 2606.24875, 2606.24907,
2607.04100) and contains no general-degree root-pair result.

**Searches run.** `Venkata Siddharth Pendyala arxiv lemniscate polynomial path
Erdos`; `arxiv_api.py search --author "Pendyala" -n 20`; `Dubinin Polya inequality
level set area conformal capacity`; `Dubinin symmetrization Polya inequality level
set area polynomial paper Tao cited`; full read of the 47-comment #1041 thread;
live fetch of `shtuka123.github.io/1041/main.pdf` with `pdfinfo` and `pdftotext`;
`github.com/shtuka123/1041` commit API (404, no revision history exists).

**Search not completed.** Dubinin's paper itself, and the classical
potential-theoretic lemniscate literature (Pommerenke, Eremenko–Hayman) for a
degree-free root-connecting bound. The latter was already recorded as unfinished
in the first pass and is now partly closed by E2 below.

**Confidence: high** that no general-degree solution stands; **medium-high** that
the separation criterion has no antecedent, contingent on Dubinin.

---

### E2. #1041 — the unconditional `(71/10) μ^{1/n}` constant-factor bound

**Our exact statement.** `ErdosProblems/Erdos1041/UnconditionalConstantFactorBound.md`,
Theorem 1, and `erdos-1041-lemniscate-newton-flow.tex` at `\label{res:constant-factor-path}`:
two zero occurrences of `f` are joined by a possibly degenerate path of length at
most `(71/10) μ^{1/n} = (71/10) cap(K_μ)` lying inside `K_{2μ}`, with
`μ = min{|f(c)| : f'(c) = 0}`. Ordinary mathematics, not Lean-checked, and it
does not answer #1041.

**Disposition: `new`, against a large adjacent literature that measures a
different object.**

**What the adjacent literature actually bounds.** Every classical lemniscate
length result located this pass bounds the arclength of the level curve
`{|p(z)| = 1}`, which is Erdős problem #114, not the length of a path joining two
roots:

- Pommerenke: `|E(p)| ≤ 74n²`.
- P. Borwein, "The arc length of the lemniscate `|p(z)| = 1`" (1995): `≤ 8πen`.
- A. Eremenko and W. Hayman, Michigan Math. J. **46** (1999), no. 2, 409–415:
  `≤ 9.173 n`.
- A. Fryntov and F. Nazarov, arXiv:0808.0717: asymptotically sharp `2n + o(n)`,
  extremal at `p(z) = z^n − 1`.
- T. Tao, arXiv:2512.12455 (Dec 2025): resolves the #114 conjecture for large `n`.

These share the Stokes/area-integral toolkit with our step but bound a different
quantity, so none is an antecedent. No paper giving any constant-factor
root-to-root path bound in arbitrary degree was located.

**Searches run.** `arxiv 0808.0717 length Erdos-Herzog-Piranian lemniscates`;
`Eremenko Hayman length lemniscate polynomial`; `Pommerenke metric properties
lemniscate Erdos Herzog Piranian`; `Borwein arc length of the lemniscate
polynomial`; local reads of the EHP 1958 annex, Ghosh–Ramachandran
(arXiv:2312.13673) and Pritsker (arXiv:1307.6196).

**Confidence: high** that the #114 family is not an antecedent (abstracts and
bounds read); **medium-high** that no constant-factor root-pair bound exists.

---

### E3. #1041 — `(S)_n` for `n ≤ 5`

**Our exact statement.** For monic `f` of degree `n` with minimum enclosing root
radius `R` and critical points `c_1, …, c_{n−1}`:
`Σ_j |f(c_j)|^{1/n} ≤ (n−1) R`, proved for `n = 2, 3, 4, 5` through
`FP_{n−1} ⇒ (S)_n`, with equality on `(z − τ)^n − λ`.

**Disposition: `unresolved`, and the name is a hazard.**

`docs/formal_math/palomar/longitudinal_truth_2026_09_01.md` §2 item 3 describes
this as "the arithmetic-mean strengthening of Schur–Fekete". No paper, textbook
or survey establishing a named "Schur–Fekete inequality" of this form was
located. What the searches returned instead was the Fekete–Szegő inequality
(coefficients of univalent functions), the Schur inequality (a symmetric
inequality in three nonnegative reals), Gauss–Lucas (a containment statement, not
a magnitude bound), and the Siebeck–Marden theorem (degree three). A grep of the
Erdős–Herzog–Piranian 1958 annex for "Schur", "Fekete" and "critical" returns
zero matches, and the string "Schur" does not appear in
`erdos-1041-lemniscate-newton-flow.tex` at all; the paper says "Fekete chain" and
"near-Fekete bridge", which are different objects.

Two separate obligations follow. First, establish what the classical inequality
actually is and cite it by its real name, or drop the comparison. Second, until
that is done the claim cannot be described as a strengthening of anything,
because the thing it strengthens has not been identified. This is not a novelty
kill; it is an unfinished attribution.

**Searches run.** `Schur inequality Fekete critical values polynomial arithmetic
mean refinement`; `"Schur" "Fekete" inequality critical points polynomial
circumradius maximum modulus`; `"critical points" polynomial "geometric mean"
inequality Marden Geometry of Polynomials capacity`; greps of the EHP annex and
of our own tex.

**Confidence: high** that no literature referent for the name was found;
**low** that the mathematical statement is unanticipated, because without the
right classical name the search could not be aimed.

---

### F1. #269 — three-prime rank and no finite separation

**Our exact statement.** Unchanged from §4 of the first pass:
`threePrimeKernel_infiniteRank_and_noFiniteSeparation`, giving nonsingular `n × n`
minors for every `n`, uniformly in the third layer, and the nonexistence of a
finite separable representation of any rank `d`, together with the explicit
`{2,3,5}` minor `= −1/15`.

**Disposition: `new`.**

The problem is **OPEN** (page last edited 28 December 2025) and Steve Fan's
comment of 05:22 on 26 June 2026 remains the newest post on the thread, which was
re-read this pass under both sort orders to confirm ordering. His closing
sentence is unchanged:

> "This argument does not seem to generalize immediately to |P| ≥ 3, since S does
> not factor nicely in the first place."

Nothing later addresses a three-prime kernel, minors, rank, or separability. The
attribution obligations recorded in the first pass stand: the general-`k`
running-LCM identity and the two-prime factorisation with transcendence through
Hecke–Mahler are Fan's.

**Other candidates checked.** Bugeaud–Laurent, "Transcendence of Hecke–Mahler
series" (arXiv:2412.07908), PDF fetched and read: two-variable only, with no
linear independence in three or more variables, no Hankel rank for multi-variable
kernels, and no non-separable kernel representation. arXiv:2203.12901
(Bugeaud–Laurent, continued fraction expansion of Hecke–Mahler values) could not
be decoded by the fetch tool and was **not read**; the abstract-level summary
likewise describes two-variable transcendence only.

**Searches run.** `Hecke-Mahler series rank transcendence Bugeaud Laurent`;
`"running lcm" series irrationality rank matrix three primes`; `Steve Fan
mathematician Hecke-Mahler smooth numbers arxiv`; `"Hecke-Mahler" three variables
kernel rank nonseparable p-adic subspace theorem generating function`;
erdosproblems.com/269 and its thread in full.

**Search not completed.** arXiv:2203.12901 full text.

**Confidence: medium.** This is a fast-moving corner (Bugeaud–Laurent's
transcendence paper is from late 2024/2025), so absence of evidence is weaker
here than for older problems.

---

### F2. #251 — free-pair equivalence, and the countermodel with `tsum = 32`

**Problem statement, verified live.** erdosproblems.com/251, **OPEN**, page last
edited 28 September 2025: "Is `Σ p_n/2^n` irrational?", with the further Erdős
conjectures that `Σ p_n^k/2^n` is irrational for every `k` and that
`g_n ≥ 2`, `g_n = o(p_n)` forces `Σ p_n/(g_1⋯g_n)` irrational.

**Our exact statements.** Packet id `free_pair_lattice_and_irrationality_equivalence`:
for any integer-digit dyadic tail recurrence, at and beyond an odd-denominator
state with reduced denominator `d`, `T_M − T_N ∈ Z` iff `N ≡ M mod orderOf(2 : ZMod d)`,
the offset being free; and `Irrational (T 0) ↔ (P)` where `(P)` is
`CofinalFreePairNonintegral`. Packet id
`polynomial_gap_countermodel_series_value_tsum`: for `g_n = 2(n² + 4n + 2)`,
`tsum_{n≥0} g_{n+1}/2^{n+1} = 32`.

**Disposition of the equivalence: `new`, on a search that did not close.**
**Disposition of the `tsum = 32` countermodel: `new` but novelty-free.**

**On the equivalence.** No antecedent was located under this name or shape. The
closest published "iff" in the neighbourhood is J.-C. Schlage-Puchta, "The
irrationality of some number theoretical series", arXiv:1105.1451, Theorem 2,
which is about periodic base-`b` digit expansions and a different object:

> "Theorem 2. Let b ≥ 2 be an integer, not a proper power. Let g : N → R be a
> continuous non-decreasing function such that g(n+1)/g(n) → 1. Let f : N → N be
> non-decreasing with f(n+1)/f(n) ∼ g(n), and denote by α the real number … 
> Suppose α is rational. Then g converges to some constant c, c is a power of b,
> and f(n+1) = cf(n) + O(1)."

Its Theorem 3 is the linear-independence result for `S_k = Σ p_n^k/n!`, which is
the neighbouring Erdős statement, not ours. The equivalence is a repository-local
normal form; the search that would kill it (a systematic sweep of the dyadic
tail-recurrence and Bézivin-style functional-equation literature) was not run.

**On the countermodel.** `tsum = 32` is an elementary telescope,
`Σ_{j≤N} g_j/2^j = 32 − T_N/2^N` with `T_N = 2(N+4)²`, and its role is internal:
it kills our own `h = 1` adjacent-small-mismatch producer. It carries no priority
claim and must never be presented as a result about #251.

**What did change on the problem page and must be absorbed.** The `g_n` conjecture
printed under #251 has been refuted. Vjeko Kovač, thread comment 11:13 on
15 April 2026, with a write-up at
`https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_problem_251.pdf`, Theorem 1:

> "There exists a sequence of integers (g_n)_{n≥1} with g_n ≥ 2 and g_n = o(p_n)
> such that Σ_{n=1}^∞ p_n/(g_1⋯g_n) = 1. Consequently, the above irrationality
> statement is false."

The construction is a telescoping choice of an auxiliary integer sequence `c_n`
with `c_{n+1} ≡ −p_n (mod c_n)`. It is mechanically the same species of
telescoping construction as our `tsum = 32` countermodel, applied to the
neighbouring conjecture and published first. Any #251 surface of ours that still
states the `g_n` conjecture as open is stale, and any presentation of a
telescoping countermodel as a novelty must cite Kovač's note.

**Searches run.** erdosproblems.com/251 page and full thread; fetch and full read
of Kovač's PDF; fetch and read of arXiv:1105.1451; `"free pair" irrationality tail
shift equivalence series prime denominators`.

**Confidence: high** for the Kovač comparison (source read in full);
**low-to-medium** for the free-pair equivalence, since the sweep was thin.

---

### F3. #243 — bounded-negative rigidity and the CRT bounded-rise barrier

**Problem statement, verified live.** erdosproblems.com/243, **OPEN**, page last
edited 21 January 2026: `1 ≤ a_1 < a_2 < ⋯` integers with `lim a_n/a_{n−1}² = 1`
and `Σ 1/a_n ∈ Q` force `a_n = a_{n−1}² − a_{n−1} + 1` for large `n`. The page
already cites Erdős–Straus and Duverney, and the thread already cites Koizumi.

**Our exact statements.** Packet id `bounded_negative_part_rigidity`: under exact
natural D/C dynamics, eventual strict centring `|E_n| < C_n`, normalised vanishing
`E_n/C_n → 0` and eventual boundedness of `(−E_n)_+`, the signed centred state
satisfies `E_n = 0` eventually, and the composed consumer then yields
`a_{n+1} = a_n² − a_n + 1` eventually. Packet id `strict_rise_crt_barrier`: a
natural state tending to infinity with upward increments bounded by `B` cannot, at
every strict rise, avoid all earlier members of an infinite pairwise-coprime
modulus family.

**Disposition of "counterexample errors are negative infinitely often":
`matches Koizumi, arXiv:2504.05933, Proposition 19(2)` (equivalently the
contrapositive of Badea's theorem). This clause must be demoted.**
**Disposition of bounded-negative rigidity as a whole: `extends` the same
proposition.**
**Disposition of the CRT bounded-rise barrier: `new`, on a search that did not
close.**

**Antecedent, read this pass** from the local annex
`annexes/arxiv-2504-05933-koizumi-doubly-exponential-reciprocal-sum/extracted.md`,
Junnosuke Koizumi, "Irrationality of the reciprocal sum of doubly exponential
sequences", arXiv:2504.05933:

> "**Proposition 19**. Let r be a positive rational number, and (ε_n) be the gap
> sequence of the pseudo-greedy expansion of r. Suppose that one of the following
> conditions is satisfied: (1) liminf_{n→∞} ε_n ∏_{k=1}^{n−1}(1 − ε_k) ≥ 0.
> (2) ε_n ≥ 0 holds for n ≫ 0. Then, we have ε_n = 0 for n ≫ 0."

and Corollary 20, which names the two hypotheses as Erdős–Straus 1963 and Badea
respectively:

> "**Corollary 20**. Let (a_n) be a sequence of positive integers satisfying
> lim a_n²/a_{n+1} = 1 and Σ 1/a_n ∈ Q. Suppose that one of the following
> conditions is satisfied: (1) (Erdős–Straus) liminf (a_1a_2⋯a_{n−1}/a_n)(1 −
> a_n²/a_{n+1}) ≥ 0. (2) (Badea) a_{n+1} ≥ a_n² − a_n + 1 holds for n ≫ 0. Then,
> a_{n+1} = a_n² − a_n + 1 holds for n ≫ 0."

Contraposing Proposition 19(2) against Koizumi's Corollary 10 (which gives
`ε_n → 0`): a genuine counterexample must have `ε_n < 0` infinitely often. That is
the "negative infinitely often" clause of our claim, and it is published. It is
also, through Corollary 20(2), nothing more than the contrapositive of Badea's
1987 theorem.

**The precise delta that survives.** Badea and Koizumi's Proposition 19(2) assume
the sign is eventually nonnegative. Ours assumes only that the *negative part* is
eventually bounded, which admits sign changes of bounded depth at every scale.
That is a strictly weaker hypothesis reaching the same conclusion, so the theorem
is a genuine strengthening. Similarly, Proposition 19(1) contraposes to a weighted
negativity statement, `liminf ε_n ∏(1 − ε_k) < 0`, which is Erdős–Straus's own
`limsup > 0` restated; "unbounded along the negatives" and "divergent normalised
negative mass" are not entailed by it and no antecedent was found for them.

**The CRT bounded-rise barrier.** No antecedent located. Koizumi's Lemma 15 uses a
modular recurrence `e_n ≡ d_n (mod c_n)`, `c_{n+1} = c_n − e_n`, which is
CRT-flavoured but is not this statement. Tao's thread comment of 01:39 on
11 September 2025 sketches a structurally similar `(b_n, c_n)` recurrence and
explicitly disclaims rigour: "the recurrence looks quite difficult to analyze …
and I see no plausible way to rigorously prove the claim."

**Other candidates checked.** D. Duverney, "Irrationality of fast converging
series of rational numbers", J. Math. Sci. Univ. Tokyo **8** (2001), 275–316,
Corollary 3.2, fetched and read: an iff under the extra hypothesis
`Σ (a_{n+1}/a_n² − 1) < ∞`, already printed on the problem page. Erdős–Straus,
"Some number theoretic results", Pacific J. Math. **36** (1971), 635–646, fetched;
its statement is folded into Duverney's Corollary 3.3/3.4.

**Searches run.** `Koizumi "pseudo-greedy expansion" rational number Egyptian
fraction arxiv 2504.05933`; `Erdos Straus 1963 "Some number theoretic results"
a_n^2 limsup lcm irrationality`; `Badea sequence a_{n+1} >= a_n^2 - a_n + 1
rational sum reciprocals theorem`; erdosproblems.com/243 page and full thread;
direct fetches of the Duverney and Erdős–Straus PDFs.

**Search not completed.** Badea's original paper (C. Badea, Glasgow Math. J.,
1987) was reached only through Koizumi's citation and was not read directly.

**Confidence: high** for the Koizumi/Badea overlap (proposition read verbatim);
**medium** that bounded-negative rigidity strictly exceeds it, since the mapping
between our `E_n/C_n` and Koizumi's `ε_n` was not re-derived this pass;
**low** for the CRT barrier being unanticipated.

---

## Second-pass summary table

| Key | Problem | Claim | Disposition | Antecedent |
|---|---|---|---|---|
| `A1_1049_f31over4_irrational` | 1049 | `F(31/4)` irrational; region `log b/log a < 0.405683` | **extends** | Bundschuh–Väänänen 1994, Thm 2 second half (region `< 0.398679`); shape pre-announced by Zudilin 2016 §2; Duverney 1996 Thm 2 weaker at `0.23201` |
| `A2_1049_hankel_sharp_order` | 1049 | `ord_q V_N^* = N(N−1)(2N−1)/6`, coefficient `(N!)²(N+1)!/2^N` | **extends** | Zudilin 2016 §4 (inequality only); 7 citing works checked, none relevant |
| `B1_257_twentyone_fatal_branch` | 257 | exact `1/21` fatal-branch dichotomy | **new** (reduction, not a result) | none located |
| `B2_257_rational_membership_criterion` | 257 | rational membership ⟺ cofinal greedy skips | **new** | none located; achievement-set corpus not read |
| `C1_249_totient_kernel_basis_rank` | 249 | odd-core basis, rank `2^e + 1` | **extends** / **new** | Coons 2010 Thm 3.2 owns non-regularity and the kernel definition |
| `C2_249_mobius_mersenne_log_concavity` | 249 | all-rung strict log-concavity | **new** (theorem) / **matches** (object) | Steve Fan, erdosproblems.com/249, 16 May 2026, owns the series identity |
| `D1_68_companion_orbit_boundary` | 68 | `S ∈ Q ⟺ ⌊m!C⌋ ≡ −2 (mod m)` eventually | **extends** | classical factorial-base rationality criterion (Cantor 1869; Galambos 1976, Ch. 1) |
| `D2_68_finite_denominator_exclusions` | 68 | `q ∤ 299999!`, `q > 10^12039` | **new** (numbers), classical method | none located; #68 page has 0 comments |
| `E0_1041_shtuka_withdrawn` | 1041 | status of the general-degree manuscript | **resolved as withdrawn** | shtuka, erdosproblems.com/1041, 26 Mar 2026 |
| `E1_1041_critical_value_separation` | 1041 | thresholds `4/3/2`, `S = 2` sharp at `n ≥ 6` | **new** | none located; Dubinin Thm 1 is an uncited input |
| `E2_1041_constant_factor_path` | 1041 | `(71/10) μ^{1/n}` inside `K_{2μ}` | **new** | #114 arclength family (Pommerenke, Borwein, Eremenko–Hayman, Fryntov–Nazarov, Tao) bounds a different object |
| `E3_1041_S_n_arithmetic_mean` | 1041 | `(S)_n` for `n ≤ 5` | **unresolved** | "Schur–Fekete" has no located literature referent |
| `F1_269_three_prime_rank` | 269 | infinite rank, no finite separation | **new** | Fan's 26 Jun 2026 comment leaves `\|P\| ≥ 3` open |
| `F2_251_free_pair_equivalence` | 251 | `Irrational (T 0) ↔ (P)` | **new** | none located; Schlage-Puchta 2011 Thm 2 is a different object |
| `F2b_251_countermodel_tsum_32` | 251 | polynomial-gap series value `= 32` | **new but novelty-free** | Kovač, "On the Erdős problem #251", Thm 1, is the published telescoping construction in this neighbourhood |
| `F3a_243_negative_infinitely_often` | 243 | counterexample errors negative infinitely often | **matches** | Koizumi arXiv:2504.05933 Prop 19(2); Badea 1987 contrapositive |
| `F3b_243_bounded_negative_rigidity` | 243 | bounded negative part forces Sylvester | **extends** | same proposition, with the nonnegativity hypothesis weakened to bounded negativity |
| `F3c_243_crt_bounded_rise_barrier` | 243 | CRT bounded-rise barrier | **new** | none located; Koizumi Lemma 15 is adjacent |

## What must be demoted before publication

1. **#243, "any counterexample has canonical centred errors negative infinitely
   often".** Published. It is the contrapositive of Koizumi's Proposition 19(2),
   itself the Badea case of his Corollary 20. Present only the bounded-negative
   strengthening, and cite Koizumi and Badea for the sign statement.
2. **#249, the Möbius–Mersenne series identity.** Steve Fan's, 16 May 2026, on the
   problem page. Cite it; claim only the log-concavity, and check the
   log-concave-versus-log-convex polarity against the Stieltjes class first.
3. **#251, the `g_n = o(p_n)` conjecture printed under the problem.** Refuted by
   Kovač in April 2026. Any surface of ours that still calls it open is stale, and
   the `tsum = 32` countermodel must not be presented as a novelty in the same
   neighbourhood.
4. **#1041, `(S)_n` described as "an arithmetic-mean strengthening of
   Schur–Fekete".** The named antecedent could not be found to exist. Either name
   the real classical inequality or drop the comparison.
5. **#1041, the `S = 2` threshold.** Publish `n ≥ 6` with sharpness at 6, not the
   `n ≥ 7` recorded in §2 of this document.
6. **#257 and #68 reductions (`B1`, `B2`, `D1`).** These are equivalences whose
   hypotheses carry the whole difficulty. The corpus's own legibility rubric
   excludes them, and an external moderator has already ruled that reductions are
   not results. They belong inside a paper, never as a headline.
7. **#1049, `F(31/4)`.** Not a demotion of the statement, but of its evidence
   class. It is conditional on Zudilin 2004 Lemmas 7 and 2, is not kernel-checked,
   and Zudilin 2016 §2 already announced that a rational-base extension exists
   with a computable constant. Publish it as an explicit constant for an
   announced extension, not as a new kind of theorem.

## Searches this pass could not complete

- Matala-aho–Väänänen–Zudilin, "New irrationality measures for q-logarithms",
  Math. Comp. **75** (2006), 879–889: not on arXiv, AMS full text paywalled, and
  no author copy located. It is the one remaining place a rational-base region
  better than `0.398679` could be printed.
- Dubinin, "Some inequalities for polynomials and rational functions associated
  with lemniscates", Theorem 1: cited by Tao on the #1041 thread as the source of
  the area input our own argument uses, never obtained.
- The achievement-set corpus (Guthrie–Nymann; Bartoszewicz–Głąb–Marchwicki;
  "Achievement sets of reciprocals of complete sequences", Results Math. 2023;
  "On Kakeya conditions for achievement sets"), which is where a greedy membership
  criterion of the shape of `B2` would live.
- Allouche 1992 and Yazdani's thesis, both cited inside Coons 2010, for an
  explicit `k`-kernel basis or finite-level rank.
- The Hančl / Hančl–Sobková / Hančl–Tijdeman corpus on linearly unrelated
  sequences, for a #68 criterion or denominator bound.
- Badea, Glasgow Math. J. (1987), read only through Koizumi's citation.
- arXiv:2203.12901 (Bugeaud–Laurent), full text could not be decoded.

---

## Addendum, 2026-09-02 (late night): two searches closed, one found and one not found

Both items were the highest-value entries on the "could not complete" list above.
One is now closed with a primary source read in full. One is recorded as **not
found** after the routes below were exhausted.

### Addendum A1. Matala-aho–Väänänen–Zudilin 2006 — FOUND, and it does not touch our region

**T. Matala-aho, K. Väänänen and W. Zudilin, "New irrationality measures for
q-logarithms", Math. Comp. 75 (2006), no. 254, 879–889, S 0025-5718(05)01812-0.**
Open PDF at
`https://www.ams.org/journals/mcom/2006-75-254/S0025-5718-05-01812-0/S0025-5718-05-01812-0.pdf`
(HTTP 200, 190,229 bytes, 11 pages), fetched and read this pass. The earlier
404 was against the wrong article stem; the DOI is `10.1090/S0025-5718-05-01812-0`,
not the `-06-01830-X` stem guessed from the volume listing.

Abstract, verbatim, printed p. 879:

> "The three main methods used in diophantine analysis of q-series are combined
> to obtain new upper bounds for irrationality measures of the values of the
> q-logarithm function `ln_q(1 − z) = Σ_{ν=1}^∞ z^ν q^ν/(1 − q^ν)`, `|z| ⩽ 1`,
> when `p = 1/q ∈ Z \ {0, ±1}` and `z ∈ Q`."

Introduction, printed p. 880, verbatim:

> "Our main results include the case of general rational z satisfying |z| ⩽ 1 as
> well as the case z = −1 of `ln_q(2)`. Another special case, z = 1 in (1), of
> the q-harmonic series, is considered in [Z2]. Our present methods do not allow
> us to sharpen the result in [Z2], where the arithmetic group structure approach
> (specific for z = 1) is used."

Theorem 1, p. 880: `μ(ln_q(1 − z)) ⩽ 3.76338419…` for `z ∈ Q`, `0 < |z| ⩽ 1`,
`q = p^{−1}`, `p ∈ Z \ {0, ±1}`. Theorem 2, p. 880:
`μ(ln_q(2)) ⩽ 2.93832530…`, same hypothesis on `p`.

Two findings, both favourable to the disposition already recorded.

1. **Integer base only.** The hypothesis `p = 1/q ∈ Z \ {0, ±1}` is carried in
   the abstract, in both theorem statements, and in the standing convention at
   the head of §3 ("To the end of Section 3, the integer p stands for 1/q").
   There is no rational-base region anywhere in the paper, so it cannot beat
   `0.398679`.
2. **It explicitly declines the q-harmonic case.** `[Z2]` is Zudilin, Acta Arith.
   111:2 (2004) — the Heine paper our own derivation consumes. The authors say
   in print that their methods do not sharpen it. That is a stronger negative
   than the search was looking for: the three-method combination that produced
   the best `q`-logarithm measures of its decade was applied to `z = 1` and did
   not improve on the very result our theorem homogenises.

**Consequence.** The last route by which a printed rational-base region could
have reached `log 4 / log 31 = 0.403699` is closed. Row `A1` moves from
confidence **medium** to **high**, and its `searches_not_completed` list is now
empty. The disposition itself is unchanged: **extends Bundschuh–Väänänen 1994,
Theorem 2, second half**, with Zudilin 2016 §2 owning the announced shape and
Duverney 1996 Théorème 2 the weaker printed region.

**Routes used.** `ams.org` article stem corrected from the CrossRef DOI carried
on Zudilin's own publications page (entry 40,
`http://dx.doi.org/10.1090/S0025-5718-05-01812-0`); direct PDF fetch with a
browser user agent; `pdftotext -layout`. Zudilin's homepage lists no author copy
for this entry, and none was needed.

### Addendum E1. Dubinin's lemniscate inequalities, Theorem 1 — NOT FOUND

The paper is now pinned bibliographically and its Theorem 1 statement is still
not in hand.

**Bibliographic record, verified.** V. N. Dubinin, "Some inequalities for
polynomials and rational functions associated with lemniscates". English
translation: *Journal of Mathematical Sciences* **193**:1 (2013), 45–54,
DOI `10.1007/s10958-013-1432-4`, published online 24 July 2013, print August
2013 (CrossRef record fetched live this pass, single author, 16 references).
Russian original: *Zapiski Nauchnykh Seminarov POMI* **404** (2012), 83–99, in
"Analytical theory of numbers and theory of functions, Part 27", ed.
G. V. Kuz'mina and O. M. Fomenko, POMI, St. Petersburg, 2012, 262 pp.
(volume record confirmed on `mathnet.ru`; the volume page numbers 83–99 come
from a search digest and were **not** confirmed against a mathnet contents
listing, so treat that page range as `reported_prior`). This is the paper Tao
links from the erdosproblems.com/1041 thread; the anchor href behind "this paper
of Dubinin" was extracted from the thread HTML this pass and resolves to the
Springer DOI above.

**What could not be obtained.** The text of Theorem 1. Routes tried and their
outcomes:

- Springer article page: HTTP 303 to `idp.springer.com`, paywalled, abstract
  elided.
- Semantic Scholar record for the DOI: `openAccessPdf.status = CLOSED`,
  `abstract: null`, `citationCount: 2`.
- Both citing papers checked. arXiv:2608.27047 ("Smale's Mean Value Conjecture
  and its Dual Conjecture for Complex Polynomials", 2026) cites a **different**
  Dubinin paper, the 2010 finite-increment theorem, and does not quote the
  lemniscate area inequality. The other citation, "On the Harmonic Measure and
  Capacity of Rational Lemniscates" (2015), has no arXiv id in the graph record.
- Dubinin's own arXiv preprint of this material, **arXiv:1204.1404**, "On the
  lemniscate components containing no critical points of a polynomial except for
  its zeros" (6 April 2012, 8 pages), was fetched and read in full. It is the
  *other* theorem of the POMI paper, not the area one. Its single Theorem reads:

  > "Theorem. Let P be a polynomial of degree not exceeding n and let E be a
  > connected component of the lemniscate |P(z)| ≤ 1 containing no critical
  > points of the polynomial P different from its zeros. Then, for any point
  > z ∈ E\{a}, |(z − a)P'(z)/P(z)| ≤ n, where a is the zero of the polynomial P
  > belonging to the component E. Equality in (1) is attained for any point z in
  > the case where P(z) = cz^n, c ≠ 0."

  No area statement appears in the preprint. The POMI paper therefore contains
  at least one theorem that never reached arXiv.
- `mathnet.ru`: the volume-404 general-information page resolves, but neither the
  contents listing nor the author search surfaced a Dubinin entry, so no
  `mi.mathnet.ru` paper id and no free full-text PDF was located.
- Pendyala's three math.CV preprints on this problem family (arXiv:2606.17097,
  2606.24875, 2606.24907) were downloaded and searched: **zero** occurrences of
  "Dubinin" in any of them.

**Best available paraphrase, to be used only as a placeholder.** Terence Tao,
erdosproblems.com/1041 thread, 02:45 on 25 March 2026, fetched live:

> "By Theorem 1 of this paper of Dubinin (a Polya type inequality), this area is
> at most `s^{2/m}` times the area of `U`; and by the classical Polya inequality,
> `U` has area at most `π`."

**Standing obligation, unchanged and now sharper.** Dubinin's Theorem 1 is an
input to our own #1041 capacity-closure step and is absent from the bibliography
of `erdos-1041-lemniscate-newton-flow.tex`. The citation can now be written
correctly from the record above. The statement still must be read before the
paper claims anything sharp about the area input, because a paywalled theorem we
have only seen paraphrased cannot be relied on to be exactly what the paraphrase
says. The cheapest remaining routes are an institutional Springer copy, a
`mathnet.ru` full-text PDF found by browsing the volume-404 contents in Russian,
or an author request.
