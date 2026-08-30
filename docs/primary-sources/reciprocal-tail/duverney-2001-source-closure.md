# Daniel Duverney source closure: Irrationality of Fast Converging Series

This source-evidence record binds the published source used for the signed
#243 criterion cited by the reciprocal-tail note. It is attribution and
claim-boundary evidence, not proof authority for this release, and it does not
solve Erdős #243.

## Stable identity and bound artifact

- **Author and title:** Daniel Duverney, *Irrationality of Fast Converging
  Series of Rational Numbers*.
- **Publication identity:** *Journal of Mathematical Sciences, University of
  Tokyo* **8** (2001), 275–316. The article records receipt on September 13,
  2000.
- **Official route:** the [University of Tokyo journal PDF](https://www.ms.u-tokyo.ac.jp/journal/pdf/jms080206.pdf).
  This is the typeset source read for the record.
- **Bound artifact:**
  [`duverney-2001-fast-converging-series.pdf`](duverney-2001-fast-converging-series.pdf),
  SHA-256
  `f8ab2039c94959b21ede4616e399a4159dbc7ca7d2865c7567a2f82a148115f6`;
  251001 bytes; 42 pages, printed pp. 275–316. It remains a local
  working-tree evidence copy rather than a public-release artifact.

## Read state and exact locators

`read_complete` for all 42 pages: all 2,265 extracted-text lines were read.
The title page (printed p. 275), Corollary 3.2 (printed p. 287), and the
references/end matter (printed pp. 314–315) were also visually checked. The
typeset PDF is legible; the printed page numbers are the locators used below.

- **Historical setup:** printed pp. 275–280, especially Theorem 2.1 on
  Sylvester expansions, Theorem 2.2 on Ahmes series under a limsup and LCM
  bound, and Theorem 2.3 on the Erdős–Straus perturbed doubly-exponential
  family. The article states Erdős's question as equation (2.15).
- **General conditional criterion:** printed pp. 285–287, Theorem 3.1 and its
  proof develop a rationality-forced recurrence with auxiliary integer
  approximants `p_n/q_n` under the fast-convergence hypotheses (1.3) with
  `alpha < 1/7`.
- **Signed #243 criterion:** printed p. 287, Corollary 3.2 assumes positive
  integer `u_n` with `u_n -> infinity` and the displayed one-sided condition
  `sum_{n>=0}(u_(n+1)/u_n^2 - 1) < infinity`. For signs `a_n` in `{-1, 1}`, it
  states that `sum a_n/u_n` is rational if and only if, for all sufficiently
  large `n`,
  `u_(n+1) = u_n^2 - (a_(n+1)/a_n)u_n + a_(n+2)/a_(n+1)`.
- **Proof boundary:** printed pp. 299–300, section 5.2 derives Corollary 3.2
  from Theorem 3.1 by reducing `p_n/q_n`, bounding the successive numerator
  factors, and using the convergence of the condition in (3.6). The article
  then gives the Erdős–Straus specialisation as Corollary 3.3 on p. 300.
- **End matter:** printed pp. 314–315 contain the references, including the
  original Erdős–Straus source and Badea's theorem; p. 316 contains the
  author's address.

The source's condition (3.6) is not written with absolute values. An absolute
convergence hypothesis is a stronger sufficient specialization, but it must
not be attributed to Duverney as the exact hypothesis of Corollary 3.2.

## Attribution and claim ceiling

### Supports

- The exact statement and printed locator of Corollary 3.2, including its
  one-sided summability condition, signed numerators, and eventual signed
  recurrence.
- The relationship of Corollary 3.2 to Theorem 3.1 and the all-positive
  specialisation relevant to the #243 note.
- The source identity, official retrieval route, digest, and page-level
  locators recorded above.

### Does not support

- A proof of unrestricted Erdős #243, a resolution of its mixed-sign or
  unbounded-negative regimes, or any release theorem about #249 or #257.
- The release's Lean declarations, state-system proofs, comparator rows, or
  any claim that those formal results are copied from Duverney.
- Novelty, priority, significance, acceptance, peer review, or a claim that
  Corollary 3.2 is the first signed criterion of this kind.

## Negative checks

The complete article (printed pp. 275–316) was checked for Lean declarations,
the release's theorem names, an unrestricted proof of #243, and any claim
about the release's #249/#257 results; none occurs. Corollary 3.2 is a
conditional result with its own fast-convergence and sign hypotheses, so it
does not widen the open-problem boundary.

## Redistribution disposition

The PDF is publicly retrievable from the University of Tokyo journal site, but
no explicit redistribution grant for this local copy was verified. The binary
therefore remains `working_tree_only` with `link_and_digest_only` disposition,
is excluded from the public candidate, and has
`permission_evidence_status: not_verified` in the disposition manifest. The
official route and exact digest preserve reproducibility without asserting
permission to redistribute the article.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the #243 prior-art entry.
- [`erdos-243-reciprocal-tail-rigidity.md`](../../papers/full-text/erdos-243-reciprocal-tail-rigidity.md),
  the source-aware exposition and its corrected Corollary 3.2 hypothesis.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.

The allowed outward statement is therefore: Duverney's Corollary 3.2 gives a
conditional signed recurrence criterion under the exact one-sided summability
condition printed on p. 287; it does not settle unrestricted #243 or
establish any release novelty claim.
