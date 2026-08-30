# Junnosuke Koizumi source closure: reciprocal sums of doubly exponential sequences

This source-evidence record binds the published external source used by the
#243 reciprocal-tail note. It is attribution and claim-boundary evidence, not
proof authority for this release, and it does not solve Erdős #243.

## Stable identity and bound artifact

- **Author and title:** Junnosuke Koizumi, *Irrationality of the reciprocal
  sum of doubly exponential sequences*.
- **Publication identity:** *Integers* **26** (2026), Paper A28, 17 pages.
  The title page records RIKEN iTHEMS as the author's affiliation and gives
  received 9 October 2025, accepted 15 January 2026, and published 20
  February 2026. The article DOI is
  [10.5281/zenodo.18714404](https://doi.org/10.5281/zenodo.18714404).
- **Official routes:** the [published journal PDF](https://math.colgate.edu/~integers/aa28/aa28.pdf)
  and the [arXiv v1 record](https://arxiv.org/abs/2504.05933) with its
  [preprint PDF](https://arxiv.org/pdf/2504.05933). The local artifact is the
  published PDF, not a silently substituted preprint.
- **Bound artifact:**
  [`koizumi-2026-integers-a28.pdf`](koizumi-2026-integers-a28.pdf), SHA-256
  `9ad8561399e36bb4f17368064dc4765a90f164d85b65330c466e79fc716624df`;
  334539 bytes; 17 pages. It was retrieved from the official journal PDF
  route and read directly.

The published article is the preferred source for attribution. The note's
existing bracketed aliases retain the arXiv-v1 numbering; the crosswalk below
keeps those references auditable against the final article.

## Read state and exact locators

`read_complete` for the bound 17-page PDF. All 1,017 extracted-text lines were
read. PDF pp. 1, 2, 10, 11, 14, 15, and 17 were also visually checked. The
typeset source is legible; no OCR reconstruction is used for the claim
boundary.

- **Main approximation theorem:** PDF pp. 1–2, Theorem 1, assumes positive
  integer terms, finite reciprocal sum, and
  `|a_n^2/a_(n+1) - beta| <= 1/3`; it gives the nearest-integer recovery of
  `a_n` from the reciprocal tail and `beta`, plus convergence of the error
  when the ratio tends to `beta`.
- **Problem and pseudo-greedy bridge:** PDF pp. 3–4 state Erdős–Graham's
  Question 1 and Koizumi's Conjecture 1, define the pseudo-greedy expansion
  and gap sequence, and explain the open boundary. PDF p. 9, Corollary 3,
  gives the eventual pseudo-greedy representation and gap convergence to
  zero when `a_n^2/a_(n+1) -> 1` and the reciprocal sum is finite.
- **Local state mechanism:** PDF p. 10, Lemmas 2–3, gives the gap-to-next-term
  recurrence and `epsilon_n = 0` propagation. PDF pp. 11–12, Lemma 4 and its
  proof, introduces positive integer `c_n`, denominator `d_n`, integer `e_n`,
  the congruence/centering range, the updates `c_(n+1)=c_n-e_n` and
  `d_(n+1)=d_n a_n`, and the estimate `c_n = O(1.5^n)`.
- **Equivalence and conditional endpoint:** PDF pp. 12–13, Theorem 3,
  proves equivalence of Conjecture 1 and Question 1. PDF pp. 14–15,
  Proposition 1(1–2), proves eventual zero gaps under its two sign/product
  conditions; the same pages state Corollary 4, the corresponding recurrence
  conclusion under the Erdős–Straus product condition or eventual
  `a_(n+1) >= a_n^2-a_n+1`. PDF p. 16, Remark 3, records the
  `1+o(n^-1)` sufficient condition attributed to Erdős–Straus.
- **End matter:** PDF p. 17 gives the bibliography, including the cited
  Erdős–Straus and Badea sources. The title-page dates and DOI above are the
  publication-source identity, not evidence of peer review or priority beyond
  the printed record.

## Final-article / arXiv-v1 locator crosswalk

The checked final article renumbers material that the paper currently cites by
arXiv-v1 labels:

| Published article | arXiv v1 used by the note | Role |
| --- | --- | --- |
| Corollary 3, p. 9 | Corollary 10, p. 8 | eventual pseudo-greedy transfer and gap convergence |
| Lemma 3, p. 10 | Lemma 13, p. 9 | zero-gap absorption |
| Lemma 4, pp. 11–12 | Lemma 15, p. 9 | rational state coordinates and updates |
| Theorem 3, pp. 12–13 | Theorem 16, pp. 10–11 | equivalence with the Erdős–Graham question |
| Proposition 1, pp. 14–15 | Proposition 19, pp. 12–13 | eventual nonnegative-gap descent |
| Corollary 4, pp. 14–15 | Corollary 20, pp. 12–13 | conditional recurrence criteria |
| Remark 3, p. 16 | Remark 21, p. 13 | Erdős–Straus sufficient rate |

The crosswalk is bibliographic normalization only; it does not upgrade a
preprint citation into a new theorem or change the note's claim ceiling.

## Attribution and claim ceiling

### Supports

- The published source's positive-integer pseudo-greedy framework and its
  normalized-gap conclusion under the ratio-limit and summability hypotheses.
- The exact canonical-coordinate dictionary used by the note to compare
  Koizumi's `(c_n,d_n,e_n)` with its `(C_n,D_n,E_n)` state, with the sign
  convention stated in the note.
- Prior art for zero-gap absorption (Lemma 3), eventual nonnegative-gap
  descent (Proposition 1(2)), and the conditional recurrence statements in
  Proposition 1/Corollary 4, subject to the published/preprint crosswalk.
- The source's publication identity, dates, DOI, official retrieval routes,
  and exact page-level locators above.

### Does not support

- A solution of Erdős #243 or the release's global exclusion of mixed-sign or
  unbounded-negative state orbits. Koizumi states the corresponding conjecture
  as open; the release's missing global negative-mass/repair-payment producer
  remains outside this source.
- The release's Lean declarations, integer-state proofs, finite-cylinder
  computations, or any claim that those formal results are copied from
  Koizumi. The coordinate bridge is explanatory prose; it is not a formal
  import of Koizumi's analytic proof.
- Any result about Erdős #249 or #257, novelty, priority, significance,
  acceptance, or peer review.

## Negative checks

The full published PDF (pp. 1–17) was checked for Lean declarations, the
release's theorem names, and a proof of the unrestricted Erdős–Graham
question; none occurs. The explicit open statement in the introduction and
the equivalence/conditional results on pp. 12–16 delimit the source's reach.
The proof pages do not supply the release's global mixed-sign exclusion, and
the bibliography on p. 17 does not establish a priority or novelty claim.

## Redistribution disposition

The journal PDF is publicly retrievable, but no explicit redistribution grant
for this local copy was verified. The binary therefore remains
`working_tree_only` with `link_and_digest_only` disposition, is excluded from
the public candidate, and has `permission_evidence_status: not_verified` in
the disposition manifest. The DOI, journal route, arXiv route, and digest are
preserved for reproducibility without asserting permission to redistribute the
PDF.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the #243 prior-art entry.
- [`erdos-243-reciprocal-tail-rigidity.md`](../../papers/full-text/erdos-243-reciprocal-tail-rigidity.md),
  the source-aware exposition and its preprint-v1 aliases.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.

The allowed outward statement is therefore: Koizumi's published article
supplies the normalized-gap and canonical-coordinate bridge used conditionally
by this note, and records conditional recurrence criteria, but it leaves the
unrestricted #243 question open and does not formalize the release's Lean
development.
