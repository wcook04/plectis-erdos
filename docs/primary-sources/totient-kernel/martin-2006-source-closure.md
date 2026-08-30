# Greg Martin source closure: simultaneous inequalities among values of the Euler phi-function

This source-evidence record binds the public antecedent used for the
release's affine-totient comparison. It is attribution and claim-boundary
evidence, not proof authority for this release.

## Stable identity and bound artifact

- **Author and title:** Greg Martin, *Simultaneous inequalities among values
  of the Euler phi-function*.
- **Version and route:** arXiv:math/0603053v1 [math.NT], submitted 2 March
  2006. The [arXiv record](https://arxiv.org/abs/math/0603053) and its
  [official PDF](https://arxiv.org/pdf/math/0603053) are the authoritative
  public retrieval routes checked here. The record also exposes the arXiv
  DOI [10.48550/arXiv.math/0603053](https://doi.org/10.48550/arXiv.math/0603053).
- **Bound artifact:**
  [`martin-2006-simultaneous-phi-inequalities.pdf`](martin-2006-simultaneous-phi-inequalities.pdf),
  SHA-256
  `8d967dc3018c325cf3b4a099fa916e369f4b9a915bf2ccad398d359e3b4f0705`;
  105369 bytes; 8 pages. The copy was retrieved from the official arXiv PDF
  route and read directly.

The source is cited as an arXiv preprint. No separate journal publication or
redistribution grant is asserted by this record.

## Read state and exact locators

`read_complete` for the bound PDF. All 396 extracted-text lines across the
eight pages were read. PDF pp. 1, 2, and 8 were also visually checked; the
typeset source is legible and no OCR reconstruction is being used for the
claim boundary.

- **Scope and main theorem:** PDF p. 1 gives the title, author, abstract, and
  the start of Theorem 1. PDF p. 2 completes Theorem 1: for positive integer
  slopes and integer intercepts satisfying
  (a_i b_j\ne a_j b_i), every prescribed chain of simultaneous ratio gaps
  among the values φ(a_i n+b_i) occurs on a set of positive lower density.
  The same page records the symmetry/nonproportionality discussion.
- **Corollaries:** PDF p. 2 states Corollary 2 for arbitrary strict-order
  patterns among consecutive φ-values. PDF pp. 2–3 state Corollary 3 for
  comparisons of two nonproportional affine forms and complete Corollary 4,
  which transfers Theorem 1 and Corollaries 2–3 from φ to σ. The proof of
  Corollary 4 gives the product lower bound and the reversed ordering used
  for σ.
- **Proof architecture:** PDF pp. 3–7 contain the proof and its gcd and
  density lemmas, including Lemmas 5 and 6 on p. 4 and the subsequent
  construction/counting argument. These are source context only; they are
  not imported as Lean proof authority.
- **Bibliographic boundary:** PDF p. 8 contains the references and the
  author's University of British Columbia affiliation. The source itself
  makes no claim that it proves the release's finite dyadic theorem.

### Negative checks

The full PDF (pp. 1–8) was checked for the release's theorem names, Lean
declarations, Erdős #249/#257, and a CRT–Dirichlet–determinant construction;
none occurs. More narrowly, pp. 1–3 contain the statement-level scope of
Theorem 1 and Corollaries 2–4, while pp. 3–7 contain only Martin's
analytic/gcd/density proof. Those locators support the boundary that the
source supplies comparison input but not the release's finite-base theorem,
formal proof, or endpoint solution. PDF p. 8's bibliography and author block
were checked for publication/priority evidence; no separate venue or
priority claim is asserted here.

## Attribution and claim ceiling

### Supports

- Attribution of the positive-lower-density ratio-comparison input for
  nonproportional affine forms to Martin's Theorem 1.
- The symmetry-based availability of strict orderings and the source's
  φ-to-σ transfer in Corollary 4.
- The source identity, version, exact public routes, and the locators above
  for the prior-art comparison.

### Does not support

- The release's Lean declarations, finite CRT–Dirichlet–determinant
  derivation, zero-residue/composite-base layers, or final all-base
  independence theorem.
- Any result about Erdős #249 or #257 beyond the stated comparison boundary.
- Novelty, priority, significance, peer review, acceptance, or a claim that
  Martin directly states the release's linear-independence theorem. The
  release's formal result is a separately formalised interpretation of this
  broader comparison input.

## Redistribution disposition

The arXiv routes permit public retrieval, but no explicit redistribution
grant for this local copy was verified. The binary therefore remains
`working_tree_only` with `link_and_digest_only` disposition, is excluded from
the public candidate, and has `permission_evidence_status: not_verified` in
the disposition manifest. The digest and official routes are preserved for
reproducibility without asserting permission to redistribute the PDF.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the affine-totient prior-art
  comparison.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.

The allowed outward statement is therefore: Martin proves a stronger
positive-density comparison theorem for nonproportional affine φ-progressions
and transfers it to σ; this release separately formalises its own finite
arithmetic/independence statement and does not claim that Martin states or
formalises that Lean result.
