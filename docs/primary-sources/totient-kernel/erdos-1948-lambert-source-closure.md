# P. Erdős source closure: On arithmetical properties of Lambert series

This source-evidence record binds the 1948 full-support divisor-weighted
Lambert theorem to the release's prior-art map and records its explicit
negative boundary for Euler's totient series. It is attribution and
claim-boundary evidence, not proof authority for this release.

## Stable identity and bound artifact

- **Author and title:** P. Erdős, *On arithmetical properties of Lambert
  series*.
- **Published identity:** *Journal of the Indian Mathematical Society* (N.S.)
  **12** (1948), pp. 63--66. The [official author-hosted PDF](https://users.renyi.hu/~p_erdos/1948-04.pdf)
  is the authoritative public retrieval route checked here.
- **Bound artifact:**
  [`erdos-1948-lambert.pdf`](erdos-1948-lambert.pdf), SHA-256
  `f263898827e415f8027be8d2082e6e24a13d2cc9fb006076baab282272ed21e3`;
  603601 bytes; 4 scanned PDF pages. The copy was retrieved from the
  official route and read directly.

The scan identifies the author, University of Syracuse affiliation, receipt
date 8 July 1948, journal pagination, and the article title. No explicit
redistribution grant for this local acquisition copy was verified.

## Read state and exact locators

`read_complete` for the bound scan. All 144 extracted-text lines across the
four pages were read, and all four pages were visually checked because the
scan's text layer is imperfect. The mathematical boundary below follows the
page images where OCR punctuation or symbols are ambiguous.

- **Definitions and theorem:** Printed p. 63 (PDF p. 1) defines
  `f(x) = Σ_{n≥1} x^n/(1−x^n)` and `g(x) = Σ_{n≥1} x^n/(1−x^n) sin(nπ/2)`,
  notes Chowla's earlier result for `g(1/t)`, and states Erdős's theorem:
  for every integer `|t| > 1`, both `f(1/t)` and `g(1/t)` are irrational.
  Since `f(x) = Σ_{r≥1} d(r)x^r`, this is the full-support
  divisor-weighted Lambert theorem used for the Erdős--Borwein row.
- **Positive-base proof:** Printed pp. 63--65 (PDF pp. 1--3) construct
  congruences using consecutive primes, force long blocks of zero digits in
  the base-`t` expansion, and choose the translate `y₀` by the divisor-count
  estimates labelled (1)--(6). These pages support the stated divisor-series
  theorem and its proof mechanism, not a totient-series conclusion.
- **Negative-base boundary:** Printed p. 66 (PDF p. 4) says the negative-`t`
  case is similar but omits the details needed to ensure a non-finite
  expansion. The same page then lists the analogous series with Euler's
  function `φ(n)`, the sum-of-divisors function, and the number of prime
  factors, and states that these problems “seem to present difficulties.”
  This is an explicit non-support locator for any claim that this paper proves
  irrationality of `Σ φ(n)/t^n`.

### Negative checks

The complete scan was checked for the release's Lean declarations, exact
totient-kernel rank formula, Comparator theorem names, Erdős Problem #249,
and a proof of the Euler-totient series; none occurs. The paper proves the
divisor-weighted `f(1/t)` and the sine-weighted `g(1/t)` theorem, but does not
prove the analogous totient series and explicitly marks it as difficult.

## Attribution and claim ceiling

### Supports

- Attribution of the full-support Erdős--Borwein divisor series
  `Σ_{r≥1} d(r)/t^r` to Erdős's 1948 theorem, printed p. 63.
- The prime-congruence and long base-expansion-zero mechanism used in that
  theorem, printed pp. 63--65.
- The exact source-level warning that the analogous Euler-totient series is
  not proved there and “seem[s] to present difficulties,” printed p. 66.
- The published identity, official retrieval route, exact local digest, and
  conservative redistribution posture recorded above.

### Does not support

- Irrationality of `Σ_{n≥1} φ(n)/t^n`, the release's #249 totient series, or
  any totient-kernel rank, basis, or Lean theorem.
- The release's Comparator verdicts, source fidelity, novelty, priority,
  significance, peer review, acceptance, or resolution of an open Erdős
  problem.
- The omitted negative-`t` details as a reusable proof of another series;
  only the positive-base theorem is fully detailed in the source.

The release must therefore cite Erdős 1948 for the full-support
divisor-weighted Lambert row only, while retaining the p. 66 difficulty note
as a ceiling against attributing the unresolved totient series to this paper.

## Redistribution disposition

The official author-hosted scan is publicly retrievable, but no explicit
redistribution grant for the local copy was verified. The binary therefore
remains `working_tree_only` with `link_and_digest_only` disposition, is
excluded from the public candidate, and has
`permission_evidence_status: not_verified` in the disposition manifest. The
digest and official route are preserved for reproducibility without asserting
permission to redistribute the scan.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the full-support prior-art map and
  corrected totient boundary.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the public
  notice and retrieval table.

The allowed outward statement is therefore: Erdős proves irrationality of the
full-support divisor-weighted Lambert series at integer bases `|t|>1`; the
same paper explicitly leaves the analogous Euler-totient series as difficult.
