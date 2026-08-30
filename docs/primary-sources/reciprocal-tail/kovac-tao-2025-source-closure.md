# Kovač–Tao source closure: On several irrationality problems for Ahmes series

This source-evidence record binds Kovač and Tao's published Ahmes-series
results to the release's #257 prior-art map. It is attribution and
claim-boundary evidence, not proof authority for this release.

## Stable identity and bound artifact

- **Authors and title:** Vjekoslav Kovač and Terence Tao, *On several
  irrationality problems for Ahmes series*.
- **Publication identity:** *Acta Mathematica Hungarica* **175** (2025), no.
  2, 572–608. The article DOI is
  [10.1007/s10474-025-01528-0](https://doi.org/10.1007/s10474-025-01528-0).
- **Official routes:** the [arXiv v4 record](https://arxiv.org/abs/2406.17593)
  and its [v4 PDF](https://arxiv.org/pdf/2406.17593v4). The v4 source is dated
  14 July 2025; the journal DOI identifies the published article.
- **Bound artifact:**
  [`kovac-tao-2025-ahmes-series.pdf`](kovac-tao-2025-ahmes-series.pdf),
  SHA-256 `5ef233db5bf94a072de7e094e6d42864ba2d1f639e7cb951c02b4cf1d3d52b57`;
  550706 bytes; 28 PDF pages. It was retrieved from the arXiv v4 PDF route
  and read directly.

The PDF title page identifies both authors, the arXiv version, the date, the
abstract, and the article contents. No explicit redistribution grant for this
local acquisition copy was verified.

## Read state and exact locators

`read_complete` for all 1,768 extracted-text lines across the 28-page PDF.
The title/contents page and PDF pp. 2, 4, 5, 10, 11, 13, 14, and 28 were also
visually checked. The source is typeset and legible; the page images control
the claim boundary if extraction loses a symbol.

- **Problem setting and growth boundary:** PDF p. 2 defines Ahmes series and
  records the sufficient condition
  `lim a_k^(1/2^k) = infinity` for irrationality, the shifted Sylvester
  counterexamples with rational reciprocal sum, and the resulting sharpness
  observation. The authors state that their purpose is to show what elementary
  methods can reach and to provide a reference for later work.
- **Lambert subseries:** PDF pp. 4–5, §2.1.2, defines the subseries
  `sum_{n in A} 1/(t^n - 1)` and the full series, attributes irrationality of
  the full series for integer `t >= 2` to Chowla's conjecture and Erdős's
  proof, and records Erdős's and Erdős–Graham's speculation that an infinite
  single-base subseries might be rational. The same pages say the original
  question is unresolved and display the prime-support series as another open
  problem.
- **Strict-tail geometry:** PDF p. 13, Remark 4.1, proves
  `sum_{ell>n} 1/(t^ell-1) < 1/(t^n-1)` for every integer `t >= 2` and uses it
  to show that distinct supports give distinct subsums and that the subsums
  form a Cantor set. This is the exact antecedent used by the release's
  #257 fixed-base geometry discussion. The remark does not assert a measure
  formula.
- **Merged multi-base construction:** PDF p. 5, Theorem 2.3, assumes
  `sum_{k=1}^m 1/(t_k-1) > 1` and produces sets for several bases whose
  *merged* sum is rational; its proof is on PDF pp. 13–14. The paper itself
  notes that repeated terms can occur, so this is not a fixed-base Ahmes
  counterexample and does not settle #257.
- **Irrationality-sequence results:** PDF pp. 6–7, Theorems 2.4–2.7,
  characterize several growth regimes for perturbed reciprocal sequences,
  including the statement that suitable super-exponential growth gives Type
  3 irrationality sequences and that the factorial question remains open.
  These results concern irrationality sequences, not the release's universal
  fixed-base support problem.
- **Higher-dimensional and infinite-dimensional results:** PDF pp. 8–10,
  Theorems 2.8 and 2.11, give non-empty-interior and rationality constructions
  for tuples of shifted Ahmes sums and for all rational shifts. They are
  important adjacent context but do not prove a single-base irrationality
  theorem for every infinite support.
- **End matter:** PDF p. 28 gives the references and author affiliations,
  including the original Erdős, Erdős–Straus, and Erdős–Graham sources. The
  bibliographic record is attribution evidence, not a priority adjudication.

## Attribution and claim ceiling

### Supports

- Prior art for the strict-tail inequality, injectivity of fixed-base Lambert
  subsums, and their Cantor-set structure, PDF p. 13, Remark 4.1.
- The published authors' statement of the unresolved fixed-base subseries
  question and the prime-support open example, PDF pp. 4–5.
- The merged multi-base rational-sum construction under its explicit mass
  hypothesis, PDF p. 5, Theorem 2.3, with proof pp. 13–14.
- The growth and shifted-Sylvester context for Ahmes-series irrationality
  questions, PDF p. 2 and §§2.1.2–2.1.3.
- The publication identity, arXiv version, official routes, digest, and
  page-level locators recorded above.

### Does not support

- Irrationality of every infinite fixed-base Lambert/Mersenne subseries, a
  solution of Erdős #257, or a decision about the targets `1/2` and `1/21`.
- A fixed-base rational counterexample from Theorem 2.3: its conclusion is a
  merged sum over several bases and allows repeated terms.
- The release's measure-one claim, greedy interfaces, finite death
  certificates, Lean declarations, Comparator verdicts, Palomar assurance,
  novelty, priority, significance, acceptance, or peer review.
- Any conclusion about the Euler-totient series or the #249 totient kernel;
  the paper studies Ahmes/Lambert subseries rather than that kernel.

## Negative checks

The complete PDF was checked for the release's Lean declarations, Comparator
theorem names, totient-kernel rank/basis statements, Erdős #249, and a proof
of universal #257; none occurs. Remark 4.1 supplies strict-tail/Cantor
geometry only. The paper's explicit unresolved single-base question and its
multi-base qualification prevent a stronger attribution.

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

The allowed outward statement is therefore: Kovač and Tao prove the strict
tail/Cantor structure for fixed-base Lambert subsums and give several adjacent
Ahmes-series constructions, while explicitly leaving the universal fixed-base
subseries question open; their results do not settle #257 or the release's
formal claims.
