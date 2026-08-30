# Han Wang (2026) primary-source closure

This record binds the locally acquired arXiv:2606.24972v4 PDF and e-print
source archive. The two artifacts were read directly; their versioned title
and authorship are not inferred from a bibliography or an abstract index.

## Bound artifacts and stable metadata

- **PDF:** *Sparse Polynomial-Weighted Expansions*, Han Wang, arXiv:2606.24972v4
  [math.NT], dated 24 August 2026 on the printed first page. Official route:
  <https://arxiv.org/pdf/2606.24972v4>. SHA-256:
  `3a57af1af21e5e9d25793333383d30f89ceadb08c4e2009a1ac497dc118f8b5b`.
  The PDF has 10 pages and was read in full for this closure.
- **Source archive:** the v4 e-print archive at
  <https://arxiv.org/abs/2606.24972v4>. SHA-256:
  `2d507f030082dc5ca3f661d49fa96925cffe7fbe11287a897ed9b7b2efdfe6c2`.
  Its `00README.json` names `EP260_v5.tex` as the top-level source member;
  that member was read at the exact locators below.
- **Redistribution posture:** `link_and_digest_only`; no permission or licence
  grant was found in the read artifacts. The local copies are retained as
  working-tree evidence and are excluded from the public candidate. Citation,
  arXiv availability, and a source archive do not by themselves grant
  redistribution permission.

## Exact support locators

The v4 PDF supports the following source-specific statements:

- Printed p. 1 gives the title, sole author “HAN WANG”, arXiv version/date,
  abstract, and the stated polynomial-weighted fixed-base setting. The
  introduction identifies the binary linear Erdős consequence as a
  consequence of this source's theorem, not as a result about Erdős #249 or
  #257.
- Printed p. 2, Theorem 1.1 (“Polynomial-window density”), states that for an
  infinite `S`, nonzero `p` in `Q[x]`, integer `b >= 2`, and rational
  `sum_{n in S} p(n)b^(-n)`, there are `c > 0` and `N0` such that
  `|S intersect (N,N+W]| >= cW` for `N^theta <= W <= N` and sufficiently large
  `N`.
- Printed p. 3, Corollary 1.2 (“Density and gaps”), states the positive lower
  density and logarithmic gap consequences, including the binary linear
  sparse-support consequence. Printed p. 3, Lemma 2.1 (“Carries and gaps”),
  gives, for sufficiently large `N`, `R_N in Z`,
  `R_(N+1) = b R_N - Q w(N+1)d_(N+1)`, the polynomial carry bound, and the
  logarithmic support-gap bound.
- Printed p. 5, Lemma 2.4 (“Polynomial locking”), gives the rational polynomial
  graph and integer-valued-polynomial denominator control for nonrare prefixes.
  Printed p. 5, its proof records the determinant/divisibility step used to
  force the graph.
- Printed p. 6, equation (7), gives the normalized leading-coefficient map
  `mu -> b^g mu - 1`; Lemma 2.5 gives the interior/exterior dichotomy and the
  at-most-one interior successor-gap statement. Printed p. 6, Proposition 3.1
  bounds the exterior contribution under the displayed window hypotheses.
- Printed p. 10, the proof of Theorem 1.1 combines the preceding estimates and
  explicitly states the uniform range `N^theta <= W <= N`; the disclosure
  names the author's responsibility for the claims and cites formalisation
  commit `e708b58` as a source-specific artefact.
- In `EP260_v5.tex`, lines 21–22 repeat the title and sole-author metadata;
  lines 162–183 contain the source theorem corresponding to printed p. 2,
  including its hypotheses and uniform window range.

## Attribution and claim ceiling

Both bound v4 artifacts identify **Han Wang** alone. They do not support a
two-author “Wang–Grau Ribas” attribution, the v2 title *Positive dyadic density
for rational weighted binary expansions*, or a claim that the v4 artifact is a
paper by two authors. A consumer using the v4 evidence must cite the v4 title,
version, and sole-author attribution, or bind any different metadata to a
separately read source version.

The artifacts support only their stated weighted fixed-base density, density/
gap, carry, locking, and interior/exterior results with the exact hypotheses
above. They do **not** support the local arbitrary-coefficient converse,
tempered-orbit uniqueness, an endpoint for Erdős #249 or #257, a transfer from
Erdős #260 to either release problem, or any novelty, priority, peer-review,
acceptance, or significance claim about this repository's Lean abstractions.

## Non-support locators

- The printed p. 1 classification and keywords identify the source as Erdős
  Problem 260; neither the abstract nor the introduction identifies Erdős
  #249 or #257 as a target. The printed p. 2 Theorem 1.1 is conditional on
  rationality of the weighted fixed-base series and therefore is not an
  endpoint assertion for either release problem.
- Printed p. 3, Corollary 1.2 records the source's binary-linear consequence
  under its own support-growth hypothesis; it does not identify the totient
  series of #249 or all infinite-support subseries of #257. Printed pp. 5–10
  develop and close the source's polynomial-window argument, not a transfer
  theorem to those problems.
- The source's final disclosure on printed p. 10 describes AI assistance and
  a formalisation commit for this source's theorem. It contains no peer-review,
  acceptance, priority, or independent significance determination for the
  release corpus. Those claims are therefore outside the read-source support
  boundary, not unresolved implications of its theorem.

No outward v4 consumer is asserted here beyond this source record. Existing
release citations that name a different Wang version remain separate
version-specific obligations and must not silently inherit v4 metadata.
