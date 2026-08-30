# Erdős–Straus source closure: On the irrationality of certain Ahmes series

This source-evidence record binds the original source used by the #243
reciprocal-tail note. It is attribution and claim-boundary evidence, not proof
authority for this release, and it does not solve Erdős #243.

## Stable identity and bound artifact

- **Authors and title:** P. Erdős and E. G. Straus, *On the irrationality of
  certain Ahmes series*.
- **Publication identity:** *Journal of the Indian Mathematical Society*
  (N.S.) **27** (1964), 129–133. The scan's title page records “Received
  January 22, 1964.”
- **Official route:** the [P. Erdős archive PDF](https://users.renyi.hu/~p_erdos/1964-19.pdf).
  This is the scanned source read for the record.
- **Bound artifact:**
  [`erdos-straus-1964-ahmes-series.pdf`](erdos-straus-1964-ahmes-series.pdf),
  SHA-256
  `349d491423317417b6a2ecaa6799aba5923b514d52f5f6bd4e343249f90836d9`;
  286458 bytes; 5 pages, printed pp. 129–133. It remains a local
  working-tree evidence copy rather than a public-release artifact.

## Read state and exact locators

`read_complete` for all 5 scanned pages: all 225 extracted-text lines were
read, and each page was visually checked. The scan is the authority where
OCR/extraction is degraded.

- **Theorem 1 and proof:** printed pp. 129–130. Under the displayed
  limsup condition `lim sup n_k^2/n_(k+1) ≤ 1` and boundedness of
  `N_k/n_(k+1)`, the source characterises rationality of the Ahmes series by
  the eventual recurrence `n_(k+1) = n_k^2 - n_k + 1`. Equations (4)–(9)
  give the proof's denominator and recurrence steps.
- **Intermediate criterion:** printed p. 131, Theorem 2, together with the
  surrounding necessary-condition discussion and examples.
- **Theorem 3 and proof:** printed p. 132 and continuing onto p. 133. The
  exact stronger hypothesis is
  `lim sup (N_k/n_(k+1)) · (n_(k+1)^2/n_(k+2) - 1) ≤ 0`, alongside the same
  first limsup condition. The conclusion is that the reciprocal sum is
  rational if and only if the Sylvester recurrence holds for all sufficiently
  large `k`. The source explicitly says the Theorem 1 hypotheses imply this
  product condition, but not conversely.
- **Examples and end matter:** printed pp. 132–133, Examples 1–3 give
  applications to perturbed doubly exponential sequences, a quadratic
  recurrence, and a prime-modulus criterion; p. 133 gives the bibliography
  and the authors' affiliations.

The printed indexing in Theorem 3 is the relevant boundary for the note: the
prefix quotient is `N_k/n_(k+1)`, while the next ratio is
`n_(k+1)^2/n_(k+2) - 1`. A catalogue or survey display that retains the same
prefix quotient but prints `n_k^2/n_(k+1) - 1` has shifted the second factor by
one; this record follows the original printed theorem.

## Attribution and claim ceiling

### Supports

- The exact original theorem, its printed indexing, assumptions, conclusion,
  proof location, and the stated implication between its two criteria.
- The classical conditional rationality/recurrence criterion used as the
  source boundary in the #243 note, including the examples on pp. 132–133.
- The source identity, official retrieval route, digest, and page-level
  locators recorded above.

### Does not support

- A proof of the unrestricted Erdős #243 problem, a resolution of its
  mixed-sign or unbounded-negative regimes, or any release theorem about
  #249 or #257.
- The release's Lean declarations, state-system proofs, comparator rows, or
  any claim that those formal results are copied from Erdős–Straus.
- Novelty, priority, significance, acceptance, peer review, or a claim that
  this source is the first treatment of any related criterion.

## Negative checks

The complete scanned article (printed pp. 129–133) was checked for Lean
declarations, the release's theorem names, an unrestricted proof of #243, and
any claim about the release's #249/#257 results; none occurs. Theorem 3 is
conditional and its printed hypotheses and eventual-recurrence conclusion
are the ceiling of what this source supports.

## Redistribution disposition

The PDF is publicly retrievable from the author's archive, but no explicit
redistribution grant for this local copy was verified. The binary therefore
remains `working_tree_only` with `link_and_digest_only` disposition, is
excluded from the public candidate, and has
`permission_evidence_status: not_verified` in the disposition manifest. The
official route and exact digest preserve reproducibility without asserting
permission to redistribute the scan.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the #243 prior-art entry.
- [`erdos-243-reciprocal-tail-rigidity.md`](../../papers/full-text/erdos-243-reciprocal-tail-rigidity.md),
  the source-aware exposition and its exact Theorem 3 locator.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.

The allowed outward statement is therefore: Erdős–Straus's original Theorem 3
provides the conditional Ahmes-series criterion and the exact next-index
product condition used to correct the #243 note's indexing boundary; it does
not settle unrestricted #243 or establish any release novelty claim.
