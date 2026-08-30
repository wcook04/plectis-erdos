# Borwein source closure: full-support `q`-series irrationality

This source-evidence record binds Peter B. Borwein's full-support
irrationality theorems to the release's prior-art map. It records the exact
published scope and the Mersenne specialization; it is attribution and
claim-boundary evidence, not proof authority for this release.

## Stable identity and bound artifact

- **Author and title:** Peter B. Borwein, *On the irrationality of certain
  series*.
- **Publication identity:** *Mathematical Proceedings of the Cambridge
  Philosophical Society* **112** (1992), 141–146. DOI:
  [10.1017/S030500410007081X](https://doi.org/10.1017/S030500410007081X).
  The printed article records receipt on 12 November 1991 and revision on 11
  December 1991.
- **Official routes:** the [Cambridge Core article](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/on-the-irrationality-of-certain-series/2C16AFBB2ECE3A21B3F32EA727FB7F11)
  and [author-hosted PDF](https://www.cecm.sfu.ca/~pborwein/PAPERS/P59.pdf).
- **Bound artifact:**
  [`borwein-1992-irrationality.pdf`](borwein-1992-irrationality.pdf),
  SHA-256 `a16577df6a135f2e4d8471dac2916860c4c646bfb130683ddd97ba73a2e1cca2`;
  3,425,078 bytes; six PDF pages, printed pp. 141–146. It was retrieved from
  the author route and read directly.

No explicit redistribution grant for this local acquisition copy was verified.

## Read state and exact locators

The PDF is an image scan with no usable text layer. All six page images were
visually checked, with the typeset pages serving as the authoritative reading
surface for the theorem statements, proof bounds, and bibliography.

- **Abstract and publication scope:** printed p. 141 states that the series
  `sum_{n>=1} 1/(q^n+r)` and
  `sum_{n>=1} (-1)^n/(q^n+r)` are irrational and not Liouville when `q` is an
  integer with `q != 0, +-1` and `r` is a nonzero rational avoiding the poles
  `r = -q^n`.
- **Full-support Mersenne context:** printed p. 141 recalls Erdős's
  irrationality of `sum_{n>=1} 1/(2^n-1) = sum_{n>=1} d(n)/2^n` and identifies
  the theorem as a full-support `q^n+c` extension; it also recalls the
  Erdős–Graham question for `1/(2^n-3)`.
- **Theorem 1:** printed p. 142 states that for an integer `q` with `|q|>1`
  and a nonzero rational `c`, subject to `c != -q^n`,
  `sum_{n>=1} 1/(q^n+c)` is irrational. The proof uses the contour integral
  `F_n(q)` displayed on p. 142 and the denominator/error lemmas on
  pp. 142–144.
- **Proof closure for Theorem 1:** printed pp. 143–144 establish the integral
  form and its nonvanishing/error estimate; p. 144 concludes that the
  rational-coefficient Lambert-type series is irrational after the integer
  denominator scaling.
- **Theorem 2:** printed p. 145 states the alternating analogue: for integer
  `q` with `|q|>1` and nonzero rational `c` avoiding `-q^n`,
  `sum_{n>=1} (-1)^n/(q^n+c)` is irrational. The page gives the corresponding
  contour integral and the proof continues to p. 146.
- **Non-Liouville conclusion:** printed p. 146 states that the estimates in
  Theorems 1 and 2 also give a uniform rational-approximation lower bound, so
  the numbers are not Liouville. The references on p. 146 identify Erdős
  (1948), Erdős–Graham (1980), and Erdős (1988) as historical sources.
- **Release specialization:** Theorem 1 with `q=2` and `c=-1` contains the
  full-support Mersenne value `sum_{n>=1} 1/(2^n-1)`. This is a specialization
  over all positive indices, not a subseries over an arbitrary support.

## Attribution and claim ceiling

### Supports

- Attribution to Borwein of the full-support irrationality theorem for
  `sum 1/(q^n+c)` and its alternating companion, printed pp. 142 and 145,
  with proofs on pp. 142–146.
- Attribution of the full-support Mersenne specialization `q=2`, `c=-1`,
  printed p. 141 and by Theorem 1 on p. 142.
- Attribution of the stronger “not Liouville” conclusion, printed p. 146.
- The publication identity, official retrieval routes, exact digest, and
  page-level locators recorded above.

### Does not support

- Irrationality of arbitrary infinite subseries or arbitrary support sets;
  the paper sums over every positive index `n`.
- A universal solution of Erdős #257, a squarefree-support theorem, or a
  prime-support theorem. The full-support Mersenne specialization is only
  the `A = N` case of the broader Lambert-series setting.
- Any claim that the paper proves the release's measure-one geometry, greedy
  interfaces, finite certificates, Lean declarations, Comparator verdicts,
  Palomar assurance, novelty, priority, significance, acceptance, or peer
  review.
- Any theorem about the Euler-totient series or the #249 totient kernel.

## Negative checks

All six printed pages were checked for the release's Lean declaration names,
Comparator theorem names, Palomar verdicts, totient-kernel rank/basis
statements, Erdős #249, and arbitrary-support #257 claims. None occurs. The
relevant result is the full-support `q^n+c` theorem, not an arbitrary-support
extension.

## Redistribution disposition

The author-hosted PDF is publicly retrievable, but no explicit redistribution
grant for this local copy was verified. The binary therefore remains
`working_tree_only` with `link_and_digest_only` disposition, is excluded from
the public candidate, and has `permission_evidence_status: not_verified` in
the disposition manifest. The official routes and exact digest preserve
reproducibility without asserting permission to redistribute the scan.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the historical prior-art map and
  claim ceiling.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the retrieval
  and digest notice.

The allowed outward statement is therefore: Borwein proves irrationality (and
non-Liouville behavior) for the full-support `q^n+c` series and its alternating
variant, including the full-support Mersenne value, but this does not settle
arbitrary support subsets or universal Erdős #257.
