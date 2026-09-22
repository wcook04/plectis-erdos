# Michael Coons source closure: Regular sequences and the joint spectral radius

This source-evidence record binds the published growth-exponent theorem for
regular sequences that the release cites when it distinguishes a basis of a
kernel span from a redundant spanning family, together with the evaluation
argument of its appendix. It is attribution and claim-boundary evidence, not
proof authority for this release.

## Stable identity and bound artifact

- **Author and title:** Michael Coons, *Regular sequences and the joint
  spectral radius*.
- **Published identity:** *International Journal of Foundations of Computer
  Science* 28 (2017), no. 2, pp. 135--140, DOI
  [10.1142/S0129054117500095](https://doi.org/10.1142/S0129054117500095).
  The DOI and bibliographic fields were checked against the Crossref record
  and the author's [publication list](https://mcoons-math.github.io/papers.html).
- **Version and route:** arXiv:1511.07535v1 [math.CO], submitted 24 November
  2015. The [arXiv record](https://arxiv.org/abs/1511.07535) and its
  [official PDF](https://arxiv.org/pdf/1511.07535v1) are the public retrieval
  routes checked here; the record also exposes the arXiv DOI
  [10.48550/arXiv.1511.07535](https://doi.org/10.48550/arXiv.1511.07535).
- **Bound artifact:**
  `coons-2017-joint-spectral-radius.pdf`,
  SHA-256
  `03fbaca88796cc63f376d2e6e4680ec94632143794df871066df501b5675e7ef`;
  127459 bytes; 5 PDF pages. A fresh download from the official arXiv v1 PDF
  route has this digest, and the copy was read directly.

The locators below use the numbering and pages of the arXiv version. The
journal version was not inspected, so no locator relies on its pagination.

## Read state and exact locators

`read_complete` for the bound PDF. All five pages were read and visually
checked; the typeset source is legible and no OCR reconstruction is being
used for the claim boundary.

- **Definitions and main theorem:** PDF p. 1 defines the `k`-kernel, calls a
  sequence `k`-regular when the vector space spanned by its `k`-kernel over a
  field `K` of characteristic zero is finite-dimensional, defines the growth
  exponent and the joint spectral radius, and states **Theorem 1**: for a
  `k`-regular sequence that is not eventually zero, the base-`k` logarithm of
  the joint spectral radius of any collection of matrices associated to a
  basis of the kernel span equals the growth exponent.
- **Upper bound from any spanning set:** PDF p. 2 notes that Theorem 1 holds
  over any Noetherian ring, in particular `ℤ`, with module bases, and states
  **Proposition 4**: matrices associated to any spanning set of the kernel
  span give the upper bound. The same page constructs the matrices associated
  to a basis.
- **Lower bound from a basis, and the comparison:** PDF p. 3 states
  **Proposition 6**, the matching lower bound for infinitely many `n`, which
  requires a basis; proves Theorem 1; records that Proposition 4 holds for any
  spanning set while Proposition 6 requires a basis; and states
  **Corollary 7**: the joint spectral radius for a basis is at most that for
  any collection of matrices associated to the sequence.
- **Strictness and the evaluation argument:** PDF p. 4 gives an example in
  which a redundant spanning set has strictly larger joint spectral radius.
  **Appendix A**, which begins on the same page, shows that for a basis
  `g_1, …, g_d` of the kernel span the evaluation vectors
  `(g_1(i), …, g_d(i))` span `K^d`, because a vector orthogonal to all of
  them would give a linear relation among the basis sequences.
- **Bibliographic boundary:** PDF p. 5 completes Appendix A and gives the
  acknowledgements, the references, and the author's University of Newcastle
  affiliation.

### Negative checks

The complete PDF was checked for Euler's totient, the symbol `φ`, Erdős
Problem #249, finite-level kernel ranks, and the release's theorem and Lean
declaration names; none occurs. The source concerns `k`-regular sequences and
states no result about a non-regular sequence.

## Attribution and claim ceiling

### Supports

- Attribution of the theorem that, for a `k`-regular sequence, matrices
  associated to a basis of the kernel span compute the growth exponent
  through their joint spectral radius, to Coons, Theorem 1, PDF p. 1.
- Attribution of the upper bound from any spanning set, and of the comparison
  between bases and spanning sets, to Proposition 4 (PDF p. 2) and
  Corollary 7 (PDF p. 3), with the strictness example on PDF p. 4.
- The evaluation argument of Appendix A (PDF p. 4): the evaluation vectors of
  a basis of sequences span the coefficient space.
- The published bibliographic identity, official retrieval routes, exact
  local digest, and conservative rights posture recorded here.

### Does not support

- Any statement about Euler's totient or its non-regularity. That theorem is
  Coons 2010, Theorem 3.2, recorded in
  [`coons-2010-source-closure.md`](coons-2010-source-closure.md).
- The release's finite-level basis, exact ranks, section-map description,
  integral relation module, Lean declarations, or any result about Erdős
  Problem #249.
- An application of the growth theorem to the totient, which is not regular.
- Novelty, priority, significance, peer review, or acceptance.

The equivalence used in the #249 short note, between finite generation of the
`ℤ`-module generated by an integer-valued kernel and finite dimension of its
rational span, is stated and proved there; the appendix is cited for the
evaluation argument that the proof uses.

## Redistribution disposition

The arXiv routes permit public retrieval under arXiv's non-exclusive
distribution licence, which grants no redistribution right for this local
copy. The binary therefore remains `working_tree_only` with
`link_and_digest_only` disposition, is excluded from the public candidate,
and has `permission_evidence_status: not_verified` in the disposition
manifest. The digest and official routes are preserved for reproducibility
without asserting permission to redistribute the PDF.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the totient-kernel prior-art and
  attribution map.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the public
  notice and retrieval table.
- The #249 short note and the #249 reasoning record, which cite Theorem 1,
  Proposition 4, Corollary 7, and Appendix A.

The allowed outward statement is therefore: Coons proves that for a
`k`-regular sequence the growth exponent is determined by the joint spectral
radius of matrices associated to a basis of the kernel span, while a spanning
family gives only an upper bound; the release cites this to explain why an
explicit basis is the natural finite-level object, and does not apply the
theorem to the non-regular totient.
