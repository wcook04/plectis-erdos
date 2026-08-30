# Erdős (1988) source closure: problem statements and an LCM theorem

This source-evidence record binds Paul Erdős's 1988 problems-and-results
article to the release's #257 prior-art map. It distinguishes the printed
open subseries question from the separate theorem proved in the article; it
is attribution and claim-boundary evidence, not proof authority for this
release.

## Stable identity and bound artifact

- **Author and title:** P. Erdős, *On the irrationality of certain series:
  problems and results*.
- **Publication identity:** in A. Baker (ed.), *New Advances in
  Transcendence Theory*, Cambridge University Press, 1988, pp. 102–109.
  The article's references identify the Erdős–Graham book as the source of
  several of the further problems discussed.
- **Official routes:** [Cambridge chapter DOI](https://doi.org/10.1017/CBO9780511897184.009)
  and [Renyi-hosted scan](https://users.renyi.hu/~p_erdos/1988-22.pdf).
- **Bound artifact:**
  [`erdos-1988-problems-and-results.pdf`](erdos-1988-problems-and-results.pdf),
  SHA-256 `b2bfc375d04b65332d6b8817633ff3968283a3f33c1f1ace366b03ac9fab8c88`;
  553,229 bytes; eight PDF pages, printed pp. 102–109. It was retrieved from
  the Renyi-hosted route and read directly.

No explicit redistribution grant for this local acquisition copy was verified.

## Read state and exact locators

The complete eight-page OCR text layer was checked, and PDF pages containing
printed pp. 103, 105, 106, and 109 were visually checked against the scan.
The page images control the claim boundary where the OCR introduces glyph
errors in formulas.

- **Earlier full-support theorem and open problems:** printed p. 102 recalls
  Erdős's irrationality theorem for the divisor-weighted full-support series
  `sum_{n>=1} d(n)/t^n` for every integer `t > 1`, and records several
  irrationality questions that were still open in this article. It also
  records Borwein's then-current result for `sum 1/(q^n+r)` with rational
  `r`.
- **Squarefree and sparse context:** printed p. 103 states the question for
  the increasing sequence of squarefree numbers, and says that the analogous
  arbitrary-subsequence assertion should hold. This is stated as an
  expectation/question, not proved there.
- **Direct #257-family problem statement:** printed p. 105, in the list of
  further problems from Erdős–Graham, asks for an increasing sequence
  `n_1 < n_2 < ...` whether `sum_k 1/(2^{n_k}-1)` is irrational, and also
  asks a stronger bounded-perturbation variant. This is the historical open
  subseries formulation corresponding to the release's universal #257
  setting; the article does not claim to solve it.
- **A separate proved prime/LCM result:** printed p. 106 first notes that if
  `p_1 < p_2 < ...` is an infinite sequence of primes and `a_1 < a_2 < ...`
  are the integers composed of those primes, then
  `sum_{n>=1} 1/[a_1,...,a_n]` is irrational, where the brackets denote the
  least common multiple. It then proves the following broader theorem:
  for an increasing integer sequence `a_n`, if for every sufficiently large
  `x` one has
  `A(x) = sum_{a_n < x} 1 > (1 - log 2 + epsilon)x` for some `epsilon > 0`,
  then `sum_{n>=1} 1/c(n)` is irrational, where `c(n)` is the least common
  multiple of the `a_i < n`.
- **Proof locator for the LCM theorem:** printed pp. 106–108 assume a
  rational value, choose integers with large prime factors, and use the
  resulting distinct prime divisors and tail bounds to contradict the first
  omitted term. Printed p. 109 gives the references, including Erdős (1948),
  Erdős–Graham (1980), and the earlier Erdős–Straus work.

## Attribution and claim ceiling

### Supports

- Attribution to Erdős of the printed open subseries question on p. 105:
  whether every increasing infinite support gives irrational
  `sum_k 1/(2^{n_k}-1)`.
- Attribution to Erdős of the density/LCM irrationality theorem on p. 106,
  with proof on pp. 106–108, including its prime-generated LCM specialization.
- Attribution of the historical full-support divisor-series context on p. 102
  and the squarefree-subsequence question on p. 103.
- The publication identity, official retrieval routes, exact digest, and
  page-level locators recorded above.

### Does not support

- A proof of the universal #257 assertion. The p. 105 subseries statement is
  posed as a question, and no arbitrary-support Lambert theorem is proved in
  this article.
- Irrationality of the release's prime-support or squarefree-support series,
  or any claim that the separate LCM theorem applies to the Mersenne
  denominators without an additional argument.
- Any claim that the article proves the release's measure-one geometry, greedy
  interfaces, finite certificates, Lean declarations, Comparator verdicts,
  Palomar assurance, novelty, priority, significance, acceptance, or peer
  review.
- Any theorem about the Euler-totient series or the #249 totient kernel.

## Negative checks

The complete eight-page artifact was checked for the release's Lean
declaration names, Comparator theorem names, Palomar verdicts, totient-kernel
rank/basis statements, and a proof of universal #257. None occurs. The
article's directly relevant #257-family passage is an open problem on p. 105;
the proved result on pp. 106–108 is an LCM-denominator theorem with a
different hypothesis.

## Redistribution disposition

The Renyi-hosted scan is publicly retrievable, but no explicit redistribution
grant for this local acquisition copy was verified. The binary therefore
remains `working_tree_only` with `link_and_digest_only` disposition, is
excluded from the public candidate, and has
`permission_evidence_status: not_verified` in the disposition manifest. The
official routes and exact digest preserve reproducibility without asserting
permission to redistribute the scan.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the #257 historical prior-art map
  and claim ceiling.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the retrieval
  and digest notice.

The allowed outward statement is therefore: Erdős's 1988 article records the
arbitrary-support Mersenne-subseries question as open and proves a separate
density/LCM irrationality theorem; it does not settle universal Erdős #257 or
the release's formal claims.
