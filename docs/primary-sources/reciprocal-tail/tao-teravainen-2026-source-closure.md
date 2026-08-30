# Tao–Teräväinen source closure: prime-support irrationality

This source-evidence record binds Tao and Teräväinen's unconditional
prime-support irrationality theorem to the release's #257 prior-art map. It
records the exact theorem, proof boundary, and source disposition; it is
attribution and claim-boundary evidence, not proof authority for this release.

## Stable identity and bound artifact

- **Authors and title:** Terence Tao and Joni Teräväinen, *Quantitative
  correlations and some problems on prime factors of consecutive integers*.
- **Publication identity:** arXiv:2512.01739v2 [math.NT], 25 April 2026.
  The source gives the authors' affiliations and contact addresses on its
  final page; no separate journal publication was identified in the artifact.
- **Official routes:** [arXiv abstract/version page](https://arxiv.org/abs/2512.01739v2)
  and [official PDF](https://arxiv.org/pdf/2512.01739v2).
- **Bound artifact:**
  [`tao-teravainen-2026-prime-support.pdf`](tao-teravainen-2026-prime-support.pdf),
  SHA-256 `ce10e83b10c6544e1dbff037a5e4efa0e387892e0fc596ae09dce76025d7b41e`;
  2,133,534 bytes; 61 PDF pages. It was retrieved from the official arXiv
  PDF route and read directly.

No explicit redistribution grant for this local acquisition copy was verified.

## Read state and exact locators

The extracted text was checked across the full 3,974-line extraction. PDF
pages 4, 44, 56, and 61 were also visually inspected at the theorem, proof,
closing estimate, and bibliography/affiliation locators; the page images
control the claim boundary if extraction loses a symbol.

- **Exact release-relevant theorem:** PDF p. 4, Theorem 1.3 (Erdős #69),
  equation (1.7), states
  `sum_{n>=1} omega(n)/2^n = sum_p 1/(2^p - 1) = 0.5169428...`
  and proves that this number is irrational. The source explicitly identifies
  this as the prime-support case of the Erdős–Graham conjecture listed as
  Problem #257.
- **Scope stated by the source:** the same page says that the method can be
  modified for `sum omega(n)/b^n` for every integer base `b >= 2`, and that a
  similar argument can establish the prime-power `Omega` series, but leaves
  the details of those modifications to the interested reader. Those remarks
  are not a proof locator for the release and are not promoted to closed
  theorem claims here.
- **Proof entry:** PDF p. 44 begins Section 5, “Application to an irrationality
  problem of Erdős,” and starts the contradiction from rationality of the
  displayed base-2 series. Equations (5.1)–(5.3), pp. 45–46, shift and dilate
  the rationality congruence using `omega(pn) = omega(n) + 1 - 1_{p|n}`.
- **Cancellation mechanism:** PDF pp. 45–46, equations (5.4)–(5.8), choose a
  prime Hilbert cube, impose congruences on `n`, and take an alternating sum
  so the first `K` reciprocal shifts cancel. Equations (5.9)–(5.15),
  pp. 46–47, turn the resulting congruence into expectations of prime-divisor
  variables `X_p`.
- **Contradictory variance reduction:** PDF pp. 47–49, equations (5.16)–
  (5.21), control the Taylor/correlation errors `kappa_1,...,kappa_5`,
  derive an upper bound on `sum_{p in S_1} Var X_p`, and state Technical
  Reduction Theorem 5.1, whose lower bound contradicts it.
- **Parameter and prime-cube input:** PDF pp. 49–50, equations (5.22)–(5.31),
  set the scales. PDF p. 50, Lemma 5.2, supplies distinct primes in a dyadic
  interval with the required distinct near-shift values. The proof continues
  through PDF pp. 50–56, treating near, far, and very-far shifts and closing
  the error estimates; PDF p. 56 records the final Selberg-sieve estimate.
- **Auxiliary theorem boundary:** PDF pp. 24–34, Theorem 3.1 and its proof,
  provide the quantitative two-point correlation estimate used by the
  irrationality argument. This is an analytic input to the source proof, not
  a formalized component of the release.
- **Attribution end point:** PDF p. 61 contains the bibliography and author
  affiliations. In particular, reference [46] is K. Pratt's conditional
  prime-tuples result; Tao–Teräväinen's Theorem 1.3 is the unconditional
  result recorded above.

## Attribution and claim ceiling

### Supports

- Attribution to Tao and Teräväinen of the irrationality of the prime-support
  series at base 2, PDF p. 4, Theorem 1.3 / equation (1.7), with proof on
  pp. 44–56.
- Attribution of the identity between the `omega` series and the Lambert
  prime-support sum, as displayed in PDF p. 4, equation (1.7); the release's
  own identity bridge remains separately formalised.
- Attribution of the quantitative correlation input used in the proof,
  PDF pp. 24–34, Theorem 3.1, without importing that theorem as a release
  declaration.
- The arXiv version, official retrieval routes, exact digest, and page-level
  locators recorded above.

### Does not support

- A source-proven proof of the squarefree-support series for every base
  `b >= 2`; the source only states that the method can be modified and leaves
  those details to the reader.
- Irrationality for prime powers, arbitrary infinite supports, or a universal
  solution of Erdős #257; the prime-power statement is likewise only described
  as a similar argument with details omitted.
- Any claim that this paper proves the release's measure-one geometry, greedy
  interfaces, finite certificates, Lean declarations, Comparator verdicts,
  Palomar assurance, novelty, priority, significance, acceptance, or peer
  review.
- Any theorem about the Euler-totient series or the #249 totient kernel.

## Negative checks

The complete 61-page artifact was checked for the release's Lean declaration
names, Comparator theorem names, Palomar verdicts, totient-kernel rank/basis
statements, Erdős #249, and a proof of universal #257. None occurs. The exact
closed result is Theorem 1.3's base-2 prime-support specialization, not the
source's reader-left extensions.

## Redistribution disposition

The arXiv PDF is publicly retrievable, but no explicit redistribution grant
for this local copy was verified. The binary therefore remains
`working_tree_only` with `link_and_digest_only` disposition, is excluded from
the public candidate, and has `permission_evidence_status: not_verified` in
the disposition manifest. The official routes and exact digest preserve
reproducibility without asserting permission to redistribute the PDF.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the #257 prior-art map and claim
  ceiling.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the retrieval
  and digest notice.

The allowed outward statement is therefore: Tao and Teräväinen prove the
irrationality of the prime-support Lambert series at base 2, while the source's
remarks about other bases and prime powers do not close the universal fixed-
base #257 problem or any of the release's formal acceptance surfaces.
