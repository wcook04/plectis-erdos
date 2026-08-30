# Erdős–Herzog–Piranian source closure: metric properties of polynomials

This source-evidence record binds the historical comparison source used by the
Erdős #1041 prior-art route. It is attribution and claim-boundary evidence,
not proof authority, and it does not solve #1041.

## Stable identity and bound artifact

- **Authors and title:** P. Erdős, F. Herzog, and G. Piranian, *Metric
  Properties of Polynomials*.
- **Publication identity:** *Journal d’Analyse Mathématique* **6** (1958),
  125–148, DOI [10.1007/BF02790232](https://doi.org/10.1007/BF02790232),
  [Springer article record](https://link.springer.com/article/10.1007/BF02790232).
  The publisher record gives the issue date as December 1958 and the receipt
  date as 8 October 1957.
- **Bound artifact:**
  [`erdos-herzog-piranian-1958-source.pdf`](erdos-herzog-piranian-1958-source.pdf),
  SHA-256 `bff39876de5e152b5a0d2b622eb6f9ca0c747d401ceea68146cfa2b2b5f28ce9`;
  841421 bytes; 24 scanned pages corresponding to printed pages 125–148.
  The scan was recovered from the repository's historical Git object and its
  identity was checked against the publisher record before reading.

## Read state and exact locators

`read_complete` for the bound scan. All 1,017 extracted-text lines across the
24 pages were read. The title/summary page (PDF p. 1, printed p. 125), the
target boundary (PDF p. 15, printed p. 139), and the references/added-in-proof
page (PDF p. 24, printed p. 148) were also visually checked. OCR is degraded in
places; the printed-page scan is authoritative for the target wording.

- **Notation and scope:** printed p. 125 defines the polynomial
  `f(z) = product (z - z_v)` and the lemniscate set `E(f)` by `|f(z)| < 1`;
  the summary places the component and path questions in the paper's later
  sections.
- **Immediate input:** printed pp. 136–139, Section 5, establishes the local
  context in which zeros lie in the closed unit disk and records that a
  component of `E` contains at least two zeros.
- **Exact open boundary:** printed p. 139 (PDF p. 15), immediately after that
  component discussion, states Problem 5 asking whether, with all zeros in the
  unit disk, a path of length less than 2 inside `E` can join two zeros.
- **Continuation check:** printed pp. 139–148 proceed through further component
  and diameter questions, proofs, references, and the added-in-proof note;
  none answers Problem 5.

## Claim ceiling

### Supports

- The historical formulation of the polynomial short-path question used as
  the nearest classical boundary in the #1041 Bergman-geodesic dossier.
- The unit-disk zero hypothesis, the local definition of `E(f)`, and the
  component-with-two-zeros input described at printed p. 139.
- Attribution of that formulation to Erdős, Herzog, and Piranian, with the
  exact journal, volume, pages, DOI, and receipt/issue dates above.

### Does not support

- An answer to Problem 5, a universal path-below-two theorem, or a sharp
  equality family.
- The release's Bergman-area geodesic inequality, Green/Blaschke bridge,
  tied Newton-face construction, multiply connected coverage, or Lean
  verification.
- Any claim that the release solved Erdős #1041, or any novelty, priority,
  significance, peer-review, or acceptance claim.

## Redistribution disposition

The publisher route is a subscription/paywall article record and supplies no
redistribution grant for this scan. The binary therefore remains
`working_tree_only` with `link_and_digest_only` disposition, is excluded from
the public candidate, and has `permission_evidence_status: not_verified` in
the disposition manifest. The exact digest and official retrieval route are
preserved for reproducibility without asserting permission to redistribute.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the #1041 prior-art paragraph.
- [`docs/primary-sources/redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.

The allowed outward statement is therefore: Erdős–Herzog–Piranian state the
printed-p.139 short-path question for lemniscates whose zeros lie in the unit
disk. The source supplies the open-problem boundary and attribution, not the
release's geometric theorem or a solution.
