# Han Wang v2 source closure: Positive dyadic density

This is a version-specific source-evidence record for the weighted-binary
carry comparison. It must remain separate from the later v4 record, whose
title and statement differ. Neither version is evidence for Erdős #249 or
#257, or for a solution of either release problem.

## Stable identity and disposition

- **Author:** Han Wang (the checked v2 artifact identifies no co-author).
- **Title:** *Positive dyadic density for rational weighted binary
  expansions*.
- **Version:** arXiv:2606.24972v2 [math.NT], 15 July 2026.
- **Official retrieval routes:** [arXiv v2 record](https://arxiv.org/abs/2606.24972v2)
  and [arXiv v2 PDF](https://arxiv.org/pdf/2606.24972v2).
- **Checked artifact:**
  [`wang-2026-v2-positive-dyadic-density.pdf`](wang-2026-v2-positive-dyadic-density.pdf),
  SHA-256
  `c0b75ab662c82026b67ac0ce781c25f7d2f80e12c4b5cb6d63557add35a3ff25`;
  32 pages. The artifact is retained as working-tree evidence and excluded
  from the public candidate.
- **Redistribution posture:** `link_and_digest_only`; no redistribution
  permission or licence grant was verified. ArXiv availability, citation,
  and the exact digest do not themselves authorize redistribution.

## Read state and exact locators

The exact v2 PDF was read from the repository's historical source object,
restored to the canonical working-tree-only path, and checked by text
extraction and visual inspection of the title page, theorem pages, carry page,
and references page.

- **Identity and scope:** printed p. 1 gives the title, sole author, arXiv
  version/date, abstract, classification, and keywords. The source explicitly
  frames its result around Erdős Problem 260 and weighted binary expansions.
- **Positive dyadic density:** printed p. 2, Theorem 1.1, states that for
  infinite support `S` and rational weighted value `eta = P/Q` in lowest terms,
  every sufficiently large dyadic block has a positive support proportion
  depending only on `Q`.
- **Source's stated consequence:** printed pp. 2--3, Corollary 1.2 and its
  proof, derive the irrationality of the displayed series under
  `a_n/n -> infinity` and label it Erdős Problem 260.
- **Integral carry mechanism:** printed p. 5, Proposition 3.1, states
  `R_N in Z`, `R_(N+1) = 2 R_N - Q (N+1) d_(N+1)`, and
  `0 <= R_N <= Q (N + 2)`, with `R_N >= 1` for infinite support; the proof
  derives integrality and the linear bound from the tail representation.
- **Gap and window machinery:** printed pp. 6--9 give the dyadic gap bound,
  weighted window-threshold pairs, the sparse-block lower bound, and the
  bounded-excess estimate. Printed pp. 10--24 give the prefix-collinearity,
  interior/exterior slope split, counting estimates, and the contradiction
  closing Theorem 1.1.
- **End matter:** printed pp. 25--32 contain the elementary appendices,
  uniformity details, concluding remarks, and bibliography; they were read as
  part of the source boundary.

## Attribution and claim boundary

The v2 title block identifies Han Wang alone. It does not support a
“Wang--Grau Ribas” attribution, and it must not inherit the later v4 title
*Sparse Polynomial-Weighted Expansions*. Any consumer using a different
version must bind that version to a separately read source record.

### Supports

- The forward rationality-forced integral carry recurrence and its linear
  carry bound in the source's weighted-binary setting.
- The v2 source's positive dyadic-density theorem and its stated Erdős #260
  consequence, only as claims made under the hypotheses printed in that
  source.
- The source-specific sparse-window, affine-line, and interior/exterior
  counting mechanisms identified by the locators above.

### Does not support

- Any result for Erdős #249 or #257, including the totient series, selected
  Mersenne-support series, or a transfer from #260 to either endpoint.
- The release's arbitrary-coefficient converse, tempered-orbit uniqueness,
  Lean declarations, repository assurance, or a local theorem.
- Novelty, priority, significance, peer review, acceptance, or a “first
  proof” claim for the release.
- The v4 title, v4 polynomial-window statement, or a two-author attribution.

The source's references and its historical assertions are retained as the
author's bibliography, not independently adjudicated priority evidence.

## Direct consumers

- This v2 source closure.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  which records the exact digest, official routes, working-tree-only status,
  and exclusion from the public candidate.

No other current consumer is asserted. Future consumers may use only the
version-specific supports and limits above and must not silently merge v2 and
v4 metadata.
