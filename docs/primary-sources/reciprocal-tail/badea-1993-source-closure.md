# C. Badea source closure: A theorem on irrationality of infinite series

This source-evidence record binds the published positive-rational-series
criterion relevant to the #243 prior-art boundary. It is attribution and
claim-boundary evidence, not proof authority for this release, and it does not
solve Erdős #243.

## Stable identity and bound artifact

- **Author and title:** C. Badea, *A theorem on irrationality of infinite
  series and applications*.
- **Publication identity:** *Acta Arithmetica* **63** (1993), no. 4,
  313–323. DOI: [10.4064/aa-63-4-313-323](https://doi.org/10.4064/aa-63-4-313-323).
  The article's final page records receipt on 9 December 1991 and revision on
  20 September 1992.
- **Official routes:** the [IMPAN publication record](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/63/4/107785/a-theorem-on-irrationality-of-infinite-series-and-applications), which labels the article “Free download under CC-BY license,” and the [publisher-hosted PDF](https://matwbn.icm.edu.pl/ksiazki/aa/aa63/aa6342.pdf).
  The PDF was retrieved from the latter route and read directly.
- **Bound artifact:**
  [`badea-1993-infinite-series.pdf`](badea-1993-infinite-series.pdf), SHA-256
  `ff03df05829b9c38edf78232410f60993fd61d578057d1e42c0f1b67fba34e1f`;
  150131 bytes; 11 pages, printed pp. 313–323. It remains a local
  working-tree evidence copy rather than a public-release artifact.

The publisher's page-level CC-BY indication is preserved as retrieval and
license context, but no artifact-exact redistribution record was separately
captured for this local copy. The current manifest therefore remains
`link_and_digest_only` and does not include the binary in the public candidate.

## Read state and exact locators

`read_complete` for all 11 pages: all 470 extracted-text lines were read. The
title and Theorem A (printed p. 313), Theorem 2.1/2.10 and Corollary 2.2
(printed pp. 314–316), the applications (printed pp. 317–322), and the
references/end matter (printed pp. 322–323) were visually checked. The
publisher-layout PDF is legible; printed page numbers are the locators used
below.

- **Theorem A:** printed p. 313. For convergent series of positive rational
  terms `sum b_n/a_n`, with positive integer sequences and the strict
  inequality `a_(n+1) > (b_(n+1)/b_n)a_n^2 - (b_(n+1)/b_n)a_n + 1` eventually,
  the sum is irrational. The equality recurrence is exhibited on pp. 313–314
  as a sharp rational boundary.
- **General comparison theorem:** printed pp. 314–316, Theorem 2.1 and
  Theorem 2.10. The paper defines block products `S_k(N)` and weighted block
  sums `R_k(N)`, gives a trichotomy, and proves that rationality plus eventual
  non-strict inequality forces equality eventually.
- **Direct corollary:** printed p. 316, Corollary 2.2. For a rational
  `sum b_n/a_n`, if the eventual inequality
  `a_(n+1) >= (b_(n+1)/b_n)a_n^2 - (b_(n+1)/b_n)a_n + 1` holds, then equality holds
  for all sufficiently large `n`.
- **Applications:** printed pp. 317–319, Corollaries 3.2 and 3.4 apply the
  positive-term criterion to reciprocal sums over generalized Fibonacci and
  Lucas sequences; pp. 319–321 treat alternating positive-denominator series
  and Oppenheim-expansion consequences. Printed pp. 322–323 contain the
  bibliography and author address.

## Attribution and claim ceiling

### Supports

- The exact positive-rational-series inequality/equality criterion in Theorem
  A, Theorem 2.10, and Corollary 2.2, with the printed locators above.
- The fact that Badea's 1993 theorem generalizes the positive-term Sylvester
  boundary and supplies the stated recurrence consequences for its own
  hypotheses.
- The publication identity, official retrieval routes, publisher's page-level
  license indication, digest, and page-level locators recorded above.

### Does not support

- A proof of unrestricted Erdős #243, a result for arbitrary growth-limit
  sequences, or a resolution of the mixed-sign or unbounded-negative regimes.
- The release's Lean declarations, state-system proofs, comparator rows, or
  any claim that those formal results are copied from Badea.
- Novelty, priority, significance, acceptance, peer review, or permission to
  redistribute this local copy beyond the disposition recorded above.

## Negative checks

The complete article (printed pp. 313–323) was checked for Lean declarations,
the release's theorem names, an unrestricted proof of #243, and any claim
about the release's #249/#257 results; none occurs. Badea's results require
positive rational terms and explicit eventual inequalities, so they do not
widen the open-problem boundary.

## Redistribution disposition

The publisher record advertises free download under a CC-BY license, but the
current release record does not assert an artifact-exact redistribution grant
for this local PDF. The binary therefore remains `working_tree_only` with
`link_and_digest_only` disposition, is excluded from the public candidate, and
has `permission_evidence_status: not_verified` in the disposition manifest.
The official routes and exact digest preserve reproducibility while keeping
the permission boundary explicit.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the #243 prior-art map.
- [`THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the human-readable
  source-artifact notice.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.

The allowed outward statement is therefore: Badea's 1993 paper gives a
positive-term rationality/equality criterion under explicit term inequalities;
it is adjacent prior art for #243 and does not settle unrestricted #243 or
establish any release novelty claim.
