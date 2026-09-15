# Duverney–Tachiya source closure: Refinement of the Chowla–Erdős method

This source-evidence record binds Duverney and Tachiya's squarefree Lambert
series result to the release's #257 prior-art map. It records the exact
specialisation and its hypotheses; it is attribution and claim-boundary
evidence, not proof authority for this release.

## Stable identity and bound artifact

- **Authors and title:** Daniel Duverney and Yohei Tachiya, *Refinement of
  the Chowla–Erdős method and linear independence of certain Lambert series*.
- **Publication identity:** *Forum Mathematicum* **31** (2019), no. 6,
  1557–1566. DOI: [10.1515/forum-2018-0299](https://doi.org/10.1515/forum-2018-0299).
- **Official route:** the [author-hosted preprint PDF](https://danielduverney.fr/documents/theorie-des-nombres/DuverneyTachiya190522.pdf),
  dated 23 May 2019 in its TeX metadata.
- **Bound artifact:**
  `duverney-tachiya-2019-lambert.pdf`,
  SHA-256 `63e117c607868089e4ac6d41dc330ad742b3721f062c52d8ca92070425ae3f5e`;
  81,546 bytes; 11 PDF pages. It was retrieved from the author route and
  read directly.

The first page identifies both authors, the title, affiliations, abstract,
and publication context. No explicit redistribution grant for this local
acquisition copy was verified.

## Read state and exact locators

`read_complete` for all 693 extracted-text lines across the 11-page PDF. PDF
pages 4 and 10 were also visually checked at the theorem/example and proof
locators; the typeset source is legible, and the page images control the
claim boundary if extraction loses a symbol.

On 2026-09-15 every page was re-read from page images. The hypothesis of
Corollary 1.2 on PDF p. 4 is the product `|q| L <= s`, as its proof on PDF
p. 10 confirms; the earlier record of this hypothesis as `|q|^L <= s` was a
transcription error and is corrected below.

- **Main irrationality mechanism:** PDF pp. 2–3, Theorem 1.1, assumes the
  divisibility condition (H1) along a pairwise-coprime sequence `E` and the
  growth condition (H2). If `sum theta(n)/q^n` is rational, it concludes
  infinitely many prescribed residue classes contain zeros of `theta`.
  PDF p. 3, Theorem 1.2, lifts this to linear dependence among finitely
  many base powers for several arithmetic functions.
- **Support-family definitions:** PDF p. 3, equation (1.11), defines
  `F_s(E)` as the integers whose exponents in the elements of `E` are below
  `s`. Taking `E` to be the primes and `s=2` makes `F_2(E)` the squarefree
  positive integers.
- **Index selection by averaging:** PDF pp. 5–6, Section 2, proof of
  Theorem 1.1. The Chinese-remainder system (2.3) fixes a start `eta_k`; the
  progression `u_(k,i) = i A H_k + eta_k` is (2.6); the local coefficient mass
  `mu_(k,i)` is averaged over `0 <= i <= M_k` using (H2), which bounds its
  minimum `tau_k` in (2.7); an index attaining the minimum is (2.8), and its
  bounds (2.9) control the tail `V_k` on PDF p. 7, (2.13).
- **Exact #257-relevant corollary:** PDF p. 4, Corollary 1.2, states that if
  `|q| L <= s` (the product of `|q|` and `L = lcm(1,...,ell)`), then `1` and
  the Lambert values over `F_s(E)` at bases `q^j`, with exponents `n^i`,
  `1 <= i <= ell`, `1 <= j <= h`, are linearly independent over `Q`; for
  `s = infinity` this holds for every integer `q` with `|q| > 1`. The product
  reading is confirmed by the proof on PDF p. 10, which sets
  `gamma = |q| L - 1` and uses `(1 + floor(|q|L/i - 1/i))^m = |q|^m (L/i)^m`.
  For the squarefree family use `E=primes`, `s=2`, `ell=1`, and `q=2`; then
  `L=1` and the condition is met. With `E=primes` and `s=infinity`, `F_s(E)`
  is every positive integer, so the perfect `i`th-power supports are
  irrational at every integer base.
- **Concrete squarefree family:** PDF p. 4, Example 1.1, writes the
  resulting family explicitly as
  `1, sum |mu(n)|/(2^n-1), sum |mu(n)|/(2^(2n)-1), ...`, and states its
  linear independence. The proof of Corollary 1.2 is on PDF pp. 10–11;
  equations (4.2)–(4.4) identify the divisor-weighted functions and the
  proof verifies the required divisibility and growth hypotheses.
- **Conjectural context:** PDF p. 4 recalls the Erdős–Graham conjecture for
  arbitrary increasing supports and says Corollary 1.2 gives irrationality
  for a large variety of sets. This is context, not a proof of the universal
  fixed-base statement.
- **End matter:** PDF p. 11 records the references and acknowledgments,
  including Erdős (1948), Erdős (1968/1969), and Erdős–Graham. The reference
  list is attribution evidence, not a priority adjudication.

## Attribution and claim ceiling

### Supports

- Attribution to Duverney and Tachiya of the linear-independence theorem for
  Lambert series over `F_s(E)` under `|q| L <= s`, PDF p. 4, Corollary 1.2,
  with proof on pp. 10–11.
- Attribution of the averaging selection of the index in the proof of
  Theorem 1.1, PDF pp. 5–6, (2.3)–(2.9), which the #257 note cites as the
  antecedent of the selection step in its displacement averaging.
- Attribution of the squarefree specialisation `F_2(primes)` and the
  independent family at bases `2^j`, PDF p. 4, Example 1.1.
- The divisibility/growth hypotheses and the support construction that make
  the specialisation applicable, PDF pp. 3–4 and 10–11.
- The publication identity, official retrieval route, exact digest, and
  page-level locators recorded above.

### Does not support

- Irrationality of every infinite fixed-base Lambert subseries, arbitrary
  integer bases for the squarefree support, a solution of universal Erdős
  #257, or a rational squarefree counterexample.
- A claim that the release's measure-one geometry, greedy interfaces, finite
  certificates, Lean declarations, Comparator verdicts, Palomar assurance,
  novelty, priority, significance, acceptance, or peer review follows from
  this paper.
- Any theorem about the Euler-totient series or the #249 totient kernel.
  The source concerns arithmetic functions satisfying (H1)/(H2), with the
  displayed application using `|mu|` on squarefree support.

## Negative checks

The complete 11-page PDF was checked for the release's Lean declarations,
Comparator theorem names, totient-kernel rank/basis statements, Erdős #249,
and a proof of universal #257; none occurs. The exact squarefree result is
the `q=2`, `s=2`, `ell=1` specialisation above, not a universal-base theorem.

## Redistribution disposition

The author-hosted PDF is publicly retrievable, but no explicit redistribution
grant for this local copy was verified. The binary therefore remains
`working_tree_only` with `link_and_digest_only` disposition, is excluded from
the public candidate, and has `permission_evidence_status: not_verified` in
the disposition manifest. The official route and exact digest preserve
reproducibility without asserting permission to redistribute the PDF.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the #257 prior-art map and claim
  ceiling.
- [`paper/257/erdos-257-mersenne-support-subseries.tex`](../../../paper/257/erdos-257-mersenne-support-subseries.tex),
  the perfect-power remark in the introduction, the paragraph after the
  weighted-support theorem, the squarefree-support paragraph, and the
  bibliography entry.
- [`paper/reasoning-parts/erdos257/a257_front.tex`](../../../paper/reasoning-parts/erdos257/a257_front.tex),
  the averaging-antecedents paragraph and the universal-direction remark.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the retrieval
  and digest notice.

The allowed outward statement is therefore: Duverney and Tachiya prove the
linear independence of `1` and the squarefree Lambert values at bases `2^j`
in their stated family, while their hypotheses and conclusion do not settle
the universal fixed-base #257 problem for arbitrary bases or the release's
formal claims.
