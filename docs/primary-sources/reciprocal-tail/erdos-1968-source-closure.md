# Erdős source closure: On the irrationality of certain series

This source-evidence record binds Erdős's pairwise-coprime support theorem to
the release's #257 prior-art map. It records the theorem's explicit hypotheses
and the paper's conjectural extensions; it is attribution and claim-boundary
evidence, not proof authority for this release.

## Stable identity and bound artifact

- **Author and title:** P. Erdős, *On the irrationality of certain series*.
- **Published identity:** *The Math Student* **36**, 222–226. The scanned
  article records “Received: 13-12-1965”; the release bibliography dates the
  paper to 1968 (the archive filename is `1969-09.pdf`).
- **Official route:** the [P. Erdős archive PDF](https://users.renyi.hu/~p_erdos/1969-09.pdf),
  which is the scan read for this record.
- **Bound artifact:**
  [`erdos-1968-series.pdf`](erdos-1968-series.pdf), SHA-256
  `340fff6a8a70d2125587ebc62e8157258ed30a86bb19afe25257bb1cb2126e57`;
  436234 bytes; 5 scanned PDF pages, printed pp. 222–226. It was retrieved
  from the official archive route and read directly.

The title page identifies the author, title, receipt date, and printed page
222. No explicit redistribution grant for this local acquisition copy was
verified.

## Read state and exact locators

`read_complete` for all 247 extracted-text lines across the five-page scan.
All five pages were visually checked because the OCR layer misreads several
symbols and subscripts; the page images control the mathematical boundary.

- **Full-support and conjectural context:** printed p. 222 (PDF p. 1) recalls
  Erdős's earlier theorem that
  `sum d(n)/t^n = sum 1/(t^n-1)` is irrational for every integer `t >= 2`.
  It then states the unproved conjecture for the distinct-prime-factor
  function and says that no rational infinite single-base subseries example
  is known. The page states the theorem: if the positive integers
  `n_1 < n_2 < ...` are pairwise coprime and `sum 1/n_i < infinity`, then
  `sum_i 1/(t^(n_i)-1)` is irrational for every integer `t >= 2`.
- **Unproved extensions:** the same p. 222 paragraph says that pairwise
  coprimality can supposedly be removed by more complicated arguments but
  does not give those details. It also presents weaker growth conditions as
  expectations, not as proved hypotheses or conclusions.
- **Additional open examples:** printed p. 223 (PDF p. 2) says the recurrence
  `u_(n+1) = t u_n + t - 1` does not yield a proved irrationality result for
  arbitrary positive integral `u_1`, even at `t=2`, and notes that the
  factorial series `sum 1/(n!-1)` was not known to the author there.
- **Coefficient identity and congruences:** printed pp. 223–224 (PDF pp. 2–3),
  equations (3)–(9), rewrite the selected-support series using the divisor
  count `V*(m)` and choose congruences so that `V*(y+i)=t^i` for a prescribed
  block. Pairwise coprimality is used explicitly in constructing the
  congruences and their modulus.
- **Long zero block and non-termination:** printed pp. 224–225 (PDF pp. 3–4),
  equations (5), (6), and (10)–(14), select a residue translate with a long
  block of zero digits in the base-`t` expansion while bounding the later
  contribution. This completes the proof of the stated pairwise-coprime
  theorem.
- **Closing boundary:** printed p. 226 (PDF p. 5) says the proof without the
  pairwise-coprime assumption is more complicated and is not supplied. It
  records a possible Brun-method weakening and explicitly says the all-primes
  case is not handled. The reference on that page identifies Erdős's 1948
  Lambert-series paper.

## Attribution and claim ceiling

### Supports

- Attribution to Erdős of the irrationality theorem for pairwise-coprime
  supports with convergent reciprocal support sum, at every integer base
  `t >= 2`, printed p. 222 with proof on pp. 223–225.
- The divisor-count coefficient identity, congruence construction, and
  long-base-`t` zero-block mechanism in the proof, printed pp. 223–225.
- The paper's explicit record of the unproved pairwise-coprimality removal,
  the unresolved all-primes case, and the other open examples, printed
  pp. 222–223 and 226.
- The publication identity, official retrieval route, exact digest, and
  page-level locators recorded above.

### Does not support

- The universal fixed-base #257 statement for every infinite support: the
  proved theorem has pairwise-coprime support and `sum 1/n_i < infinity`.
- The claimed removal of pairwise coprimality, the all-primes case, or any
  weaker growth condition as a theorem; the paper supplies no proof for those
  statements.
- The release's measure-one geometry, greedy interfaces, finite certificates,
  Lean declarations, Comparator verdicts, Palomar assurance, novelty,
  priority, significance, acceptance, or peer review.
- Any theorem about the Euler-totient series or the #249 totient kernel.

## Negative checks

The complete five-page scan was checked for the release's Lean declarations,
Comparator theorem names, totient-kernel rank/basis statements, Erdős #249,
and a proof of universal #257; none occurs. The explicit p. 222 theorem and
the p. 226 disclaimer are the source ceiling. The OCR text was not treated as
authoritative where it conflicts with the page images.

## Redistribution disposition

The archive scan is publicly retrievable, but no explicit redistribution grant
for this local copy was verified. The binary therefore remains
`working_tree_only` with `link_and_digest_only` disposition, is excluded from
the public candidate, and has `permission_evidence_status: not_verified` in
the disposition manifest. The official route and exact digest preserve
reproducibility without asserting permission to redistribute the scan.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the #257 prior-art map and claim
  ceiling.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the retrieval
  and digest notice.

The allowed outward statement is therefore: Erdős proved irrationality for
pairwise-coprime supports with convergent reciprocal mass at every integer base
`t >= 2`; his paper explicitly leaves the coprimality-free and all-primes
extensions without proof, so it does not settle universal #257 or the
release's formal claims.
