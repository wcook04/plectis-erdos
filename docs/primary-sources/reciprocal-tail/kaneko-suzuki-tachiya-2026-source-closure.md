# Kaneko–Suzuki–Tachiya source closure: sparse arithmetic-function series

This source-evidence record closes the nearby 2026 sparse-series mechanism in
the release's prior-art scan. It records the exact hypotheses and the
denominator/coefficient boundary; it is attribution and claim-boundary
evidence, not proof authority for this release.

## Stable identity and bound artifact

- **Authors and title:** Hajime Kaneko, Yuta Suzuki, and Yohei Tachiya,
  *Refinements of Erdős's irrationality criterion for certain sparse infinite
  series*.
- **Bound publication identity:** arXiv:2601.20743v1, dated 28 January 2026;
  [abstract and source record](https://arxiv.org/abs/2601.20743) and
  [PDF](https://arxiv.org/pdf/2601.20743).
- **Bound artifact:**
  [`kaneko-suzuki-tachiya-2026-sparse-series.pdf`](kaneko-suzuki-tachiya-2026-sparse-series.pdf),
  SHA-256 `a5eac0ee53fbd2db8e8931384f578e2a72c6a8eb0727cb3ef228f5ea0064ed6b`;
  571,434 bytes; 20 PDF pages. The complete extracted text was read and the
  theorem, application, proof, and reference pages were visually checked.

No explicit redistribution grant for this local arXiv acquisition copy was
verified.

## Read state and exact locators

`read_complete` for all 1,126 extracted-text lines across the 20-page PDF.
PDF pages 2–5 and 18–20 were visually checked; these contain the quoted
Erdős criterion, the paper's main criteria and arithmetic-function examples,
and the final proofs and references.

- **Quoted prior criterion:** PDF p. 2, Theorem A, restates Erdős's Lemma 4'
  for integer sequences `a,b`, with nonnegative `a`, infinite support, growth,
  sparsity, and a spacing condition, concluding irrationality of
  `Σ(a(n)+b(n))/t^n`. The paper states that the details of this earlier proof
  had been omitted and supplies a complete derivation in Section 5, PDF
  pp. 18–19.
- **Fundamental sparse criterion:** PDF p. 3, Theorem 1, treats a Pisot or
  Salem number `q` and algebraic-integer sequences in `Q(q)` under support,
  mass, density, averaged-tail, and spacing hypotheses, concluding that
  `Σ(a(n)+b(n))/q^n` does not lie in `Q(q)`. Its proof is Section 2, PDF
  pp. 6–11, via norm estimates and tail windows.
- **Concise criterion:** PDF p. 3, Theorem 2, replaces the averaged-tail
  condition with exponential-growth and summatory conditions. The proof is
  Section 3, PDF pp. 11–13.
- **Rational-integer specialization:** PDF p. 5, Theorem 3, gives the
  rational-integer form for `t≥2`, with explicit growth, summatory, support,
  and spacing hypotheses. It is the criterion used in the arithmetic-function
  applications.
- **Arithmetic-function applications:** PDF p. 5, Corollary 3, states that
  for a nonnegative integer-valued sequence `f` with infinite support and
  `Σ_{n≤x}f(n)=O(x(log x)^δ)`, both
  `Σ_{n≥1} f(n)/t^{σ(n)}` and
  `Σ_{n≥1} f(n)/t^{φ(n)}` are irrational for every integer `t≥2`. PDF p. 5,
  Example 3, applies this to `f(n)=d(n)^k`; PDF p. 6, Example 4, gives
  further combinations involving `σ`, `φ`, `ω`, and `Ω`. The proof of
  Corollary 3 is PDF pp. 18–19 and explicitly groups terms by the value of
  `σ` or `φ`.
- **Transcendence boundary:** PDF p. 4, Corollary 2 and Example 2, give
  transcendence-or-degree alternatives for sparse supports under the stated
  growth and gap hypotheses. These are not irrationality results for every
  infinite support.
- **End matter:** PDF pp. 19–20 record the references and author affiliations.
  The source attributes Theorem A to Erdős [1, Lemma 4'] and distinguishes
  its new criteria from that earlier result.

## Attribution and claim ceiling

### Supports

- Attribution to Kaneko, Suzuki, and Tachiya of the Pisot/Salem sparse-series
  criteria (Theorems 1–3, PDF pp. 3–5; proofs pp. 6–13).
- Attribution of the arithmetic-function denominator results in Corollary 3
  and Examples 3–4 (PDF pp. 5–6, proof pp. 18–19), including the nearby
  `d(n)^k/t^{φ(n)}` family.
- The exact hypothesis boundary: nonnegative infinite-support coefficients,
  summatory/growth/support conditions, and `σ(n)` or `φ(n)` in the exponent.
- Publication identity, arXiv route, exact local digest, and page-level
  locators recorded above.

### Does not support

- Irrationality of the release's coefficient-weighted ordinary-base series
  `Σ φ(n)/2^n`; here `φ(n)` is used as a denominator exponent in the
  Corollary 3 family, not as the coefficient of `2^{-n}`.
- A proof for arbitrary infinite supports, the universal fixed-base Erdős
  #257 problem, the #249 Möbius row, or any transfer from the sparse criteria
  to the release's gcd-moment identities.
- The release's periodic-divisor certificate, measure-one geometry, greedy
  interfaces, finite death certificates, Lean declarations, Comparator
  verdicts, Palomar assurance, or release acceptance.
- Novelty, priority, significance, peer review, or equivalence between the
  paper's Pisot/Salem norm argument and the release's formalized mechanisms.

## Negative checks

The complete preprint was checked for the release's Lean declaration names,
Comparator/Palomar machinery, the ordinary-base `Σφ(n)/2^n` theorem, Erdős
#249, and a proof of universal #257; none occurs. The nearby `φ(n)` result is
the exponent-denominator family stated in Corollary 3, not the release's
coefficient-weighted ordinary-base series.

## Redistribution disposition

The arXiv PDF is publicly retrievable, but no explicit redistribution grant for
this local acquisition copy was verified. The binary therefore remains
`working_tree_only` with `link_and_digest_only` disposition, is excluded from
the public candidate, and has `permission_evidence_status: not_verified` in
the disposition manifest. The arXiv route and exact digest preserve
reproducibility without asserting permission to redistribute the PDF.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the nearby sparse-series row and
  its denominator/coefficient boundary.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the retrieval
  and digest notice.

The allowed outward statement is therefore: Kaneko, Suzuki, and Tachiya prove
new sparse-series irrationality criteria and, under explicit growth and
support hypotheses, irrationality of families with `σ(n)` or `φ(n)` in the
denominator exponent; that nearby result does not establish irrationality of
the release's ordinary-base coefficient series or solve either Erdős problem.
