# Michael Coons source closure: (Non)Automaticity of number theoretic functions

This source-evidence record binds the published non-
`k`-regularity result for Euler's totient to the full-kernel boundary in the
release's #249 exposition. It is attribution and claim-boundary evidence, not
proof authority for this release.

## Stable identity and bound artifact

- **Author and title:** Michael Coons, *(Non)Automaticity of number
  theoretic functions*.
- **Published identity:** *Journal de Théorie des Nombres de Bordeaux* 22
  (2010), no. 2, pp. 339--352, DOI [10.5802/jtnb.718](https://doi.org/10.5802/jtnb.718).
  The [journal record](https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.718/)
  and its [official PDF](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.718.pdf)
  are the authoritative public retrieval routes checked here. The author's
  [arXiv record](https://arxiv.org/abs/0810.3709) is an alternate public
  preprint route, not the identity of the bound artifact below.
- **Bound artifact:**
  [`coons-2010-nonautomaticity.pdf`](coons-2010-nonautomaticity.pdf),
  SHA-256
  `04f9d06111f787acd6f322b6b375f6ba898ee964aa98725e12ce17274b907c7a`;
  795513 bytes; 15 PDF pages. The copy was retrieved from the official
  journal PDF route and read directly.

The PDF's front matter identifies the journal, volume, year, pages, author,
and article, and carries the journal's all-rights-reserved notice. The source
is therefore cited as a published journal article; no redistribution grant is
asserted for this local acquisition copy.

## Read state and exact locators

`read_complete` for the bound PDF. All 724 extracted-text lines across the 15
PDF pages were read. PDF pp. 1--2, 10--11, and 15 were also visually checked;
the typeset source is legible and no OCR reconstruction is being used for the
claim boundary.

- **Definitions and scope:** Printed pp. 339--340 (PDF pp. 2--3) define the
  `k`-kernel and `k`-automatic sequences and introduce the number-theoretic
  functions considered, including Euler's totient `φ`. These pages establish
  the source's terminology and the distinction between automatic and regular
  sequences.
- **Regularity framework:** Printed p. 348 (PDF p. 10) defines a
  `k`-regular sequence as one whose `k`-kernel is finitely generated as a
  `ℤ`-module. The same page states Theorem 3.1, the meromorphic-continuation
  property for Dirichlet series of `k`-regular sequences, and Corollary 3.1,
  the non-regularity criteria used in the next theorem.
- **Totient theorem:** Printed p. 349 (PDF p. 11) states **Theorem 3.2**:
  “The function `φ(n)` is not `k`-regular for any `k ≥ 2`.” Its proof uses
  the identity
  `∑_{n≥1} φ(n)n^{-s} = ζ(s−1)/ζ(s)` for `Re s > 2`, together with the
  zero-counting input and Corollary 3.1. This is the exact external source
  support for the release's attribution of the full totient-kernel
  non-finite-generation boundary.
- **Bibliographic and rights boundary:** Printed p. 352 (PDF p. 15) gives
  the references, author affiliation, and contact block. The PDF's opening
  notice records the journal's copyright and restricts reproduction beyond
  private use; these pages were checked before assigning the conservative
  disposition below.

### Negative checks

The complete PDF was checked for the release's Lean module names, exact finite
rank formula `2^e + 1`, an explicit finite-level basis, a CRT--Dirichlet--
determinant construction, Erdős Problem #249, and the repository's theorem
names; none occurs. The source states the global non-`k`-regularity theorem,
not the release's finite-level rank, basis, relation normal form, Lean proof,
or the separate all-base conditional theorem.

## Attribution and claim ceiling

### Supports

- Attribution of the theorem that Euler's totient function is not
  `k`-regular for any integer `k ≥ 2` to Coons, Theorem 3.2, printed p. 349.
- The source-level definition of `k`-regularity as finite generation of the
  `k`-kernel over `ℤ`, printed p. 348.
- The Dirichlet-series identity and proof mechanism used by Coons for the
  totient non-regularity theorem, printed p. 349.
- The published bibliographic identity, official retrieval routes, exact
  local digest, and conservative rights posture recorded above.

### Does not support

- The release's Lean declarations, finite CRT--Dirichlet--determinant
  derivation, explicit dyadic basis, exact finite-level rank, or relation
  normal form.
- The all-base affine-totient independence theorem attributed to Martin, or
  any composite-base reduction in the release.
- A direct proof that a particular finite truncation has rank `2^e + 1`.
- Novelty, priority, significance, peer review, acceptance, or a claim that
  the global non-`k`-regularity theorem settles Erdős Problem #249.

The release's further statement that this global result corresponds to
infinite-dimensionality of the full integer-valued totient-kernel span is a
separately authored/formalised bridge and must not be presented as a finite
rank theorem stated by Coons.

## Redistribution disposition

The official journal PDF is publicly retrievable, but its front matter says
that reproduction beyond strictly private use is prohibited. No explicit
redistribution grant for this local copy was verified. The binary therefore
remains `working_tree_only` with `link_and_digest_only` disposition, is
excluded from the public candidate, and has
`permission_evidence_status: not_verified` in the disposition manifest. The
digest and official routes are preserved for reproducibility without
asserting permission to redistribute the PDF.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the totient-kernel prior-art and
  attribution map.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the public
  notice and retrieval table.

The allowed outward statement is therefore: Coons proves that Euler's
totient is not `k`-regular for any `k ≥ 2`; this supplies global
non-finite-generation prior-art context. The release separately formalises
finite-level dyadic structure and does not claim that Coons states or proves
those finite-level conclusions.
