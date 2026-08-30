# Luca–Tachiya source closure: periodic Lambert series

This source-evidence record closes the periodic-coefficient antecedent used in
the release's #257 prior-art map. The bound artifact is an institutional RIMS
reprint that explicitly restates the authors' earlier 2014 theorem and gives a
complete proof of its nonnegative-coefficient linear-independence extension.
It is attribution and claim-boundary evidence, not proof authority for this
release.

## Stable identity and bound artifact

- **Authors and bound title:** Florian Luca and Yohei Tachiya, *Linear
  independence results for the values of divisor functions series*.
- **Bound publication identity:** RIMS Kôkyûroku No. 2014 (2017),
  *Analytic Number Theory and Related Areas*, pp. 138–150.
- **Original antecedent identified by the authors:** F. Luca and Y. Tachiya,
  *Irrationality of Lambert series associated with a periodic sequence*,
  *International Journal of Number Theory* **10** (2014), 623–636, DOI
  [10.1142/S1793042113501121](https://doi.org/10.1142/S1793042113501121).
- **Official open route for the bound artifact:** [RIMS PDF](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/2014-14.pdf).
  The publisher's [original article record](https://doi.org/10.1142/S1793042113501121)
  was also checked; its PDF route was not retrievable in this environment
  (HTTP 403), so this record does not pretend that the bound copy is the
  journal PDF.
- **Bound artifact:**
  [`luca-tachiya-2014-periodic.pdf`](luca-tachiya-2014-periodic.pdf),
  SHA-256 `0acc2bf11481a63fa37bb6fd726f85da7d090e4ab7419f73fffb5884838b24cf`;
  54,900 bytes; 13 PDF pages. The artifact was retrieved from the RIMS route,
  its full extracted text was read, and theorem/proof/reference pages were
  visually checked.

The bound copy's first page identifies the authors, title, abstract, and
conference-publication context. No explicit redistribution grant for this
local acquisition copy was verified.

## Read state and exact locators

`read_complete` for all 810 extracted-text lines across the 13-page PDF.
PDF pages 2–4 and 12–13 were visually checked; these correspond to printed
pp. 139–141 and 149–150 and control the theorem, examples, proof, and
reference claims below.

- **Earlier irrationality theorem:** printed p. 139, Theorem A, explicitly
  labels and restates the authors' earlier Theorem 1.1. If
  `a₁(n)` is a purely periodic integer sequence, not identically zero, and
  `a₂(n)=Σ_{d|n} a₁(d)`, then
  `f₂(q⁻¹)=Σ_{n≥1} a₁(n)/(qⁿ−1)` is irrational for every integer `q` with
  `|q|>1`. The same page defines the recursively generated `a_ℓ` and the
  Lambert-series power series.
- **Nonnegative linear-independence theorem:** printed p. 139, Theorem 1,
  states that for a purely periodic sequence of nonnegative integers `a₁`,
  not identically zero, and `a_ℓ(n)=Σ_{d|n}a_{ℓ−1}(d)`, the `m` numbers
  `1` and `f_ℓ(q⁻¹)=Σ_{n≥1}a_ℓ(n)q⁻ⁿ` for `ℓ=2,…,m` are linearly independent
  over `Q`, for every integer `|q|>1`.
- **Divisor-function specialization:** printed p. 140, Example 1, applies
  Theorem 1 to `a₁(n)=1` and records linear independence of `1` and
  `Σ_{n≥1}d_ℓ(n)q⁻ⁿ = Σ_{n≥1}d_{ℓ−1}(n)/(qⁿ−1)` for `ℓ=2,…,m`.
- **Odd-support specialization:** printed p. 140, Example 2, takes
  `a₁(2k−1)=1` and `a₁(2k)=0`, and gives linear independence of `1`,
  `Σ_{n≥1}1/(q^{2n−1}−1)`, and the recursively generated divisor-convolution
  Lambert values. This is a concrete periodic indicator-support example.
- **Proof architecture and attribution boundary:** printed p. 140, Remark 1,
  says the nonnegative proof is elementary in the relevant sense and does not
  use the Alford–Granville–Pomerance result needed in the authors' previous
  paper. Lemmas 1–8 occupy printed pp. 140–149; the proof of Theorem 1 is
  printed pp. 149–150. In particular, pp. 144–148 construct CRT-controlled
  indices, force a small shifted tail under a rationality assumption, and
  obtain a contradiction from nonnegative divisor convolutions; pp. 149–150
  finish the linear-independence contradiction.
- **Original-paper attribution:** printed p. 150, reference [3], identifies
  the earlier work as *Irrationality of Lambert series associated with a
  periodic sequence*, *Int. J. Number Theory* 10 (2014), 623–636. The source
  therefore supports attribution of the earlier periodic irrationality result
  to Luca and Tachiya, while the bound copy directly supports the restated
  theorem and the complete nonnegative proof.

## Attribution and claim ceiling

### Supports

- Luca–Tachiya's direct periodic-coefficient antecedent: Theorem A, printed
  p. 139, as an explicit restatement of their earlier theorem.
- The stronger nonnegative purely-periodic linear-independence theorem:
  Theorem 1, printed p. 139, with proof on printed pp. 149–150 and supporting
  lemmas on pp. 140–149.
- The full-support divisor-function and odd-support indicator examples:
  printed p. 140, Examples 1 and 2.
- The stated distinction between the nonnegative proof and the earlier
  signed/rational-coefficient proof using Alford–Granville–Pomerance:
  printed p. 140, Remark 1.
- Publication identity, original DOI, official RIMS retrieval route, exact
  local digest, and page-level locators recorded above.

### Does not support

- A proof that every infinite support gives an irrational fixed-base Lambert
  subseries, a solution of universal Erdős #257, or any assertion that the
  release's particular Möbius/prime support is covered merely because it is
  periodic in another representation.
- The release's periodic-divisor certificate, finite tail certificates,
  measure-one geometry, greedy interfaces, Lean declarations, Comparator
  verdicts, Palomar assurance, or release acceptance.
- A full mixed-sign theorem from the bound copy: Theorem 1 assumes
  nonnegative `a₁`; Theorem A is only a restated earlier result and does not
  reproduce that earlier proof in this artifact.
- Priority, novelty, significance, peer review, or equivalence between the
  release proof and Luca–Tachiya's method.

## Negative checks

The complete bound artifact was checked for the release's Lean declaration
names, Comparator/Palomar machinery, totient-kernel claims, Erdős #249, and a
proof of universal #257; none occurs. The source is a periodic Lambert-series
antecedent with recursive divisor convolutions, not a release-validation
artifact.

## Redistribution disposition

The RIMS PDF is publicly retrievable, but no explicit redistribution grant for
this local copy was verified. The binary therefore remains `working_tree_only`
with `link_and_digest_only` disposition, is excluded from the public
candidate, and has `permission_evidence_status: not_verified` in the
disposition manifest. The official RIMS route and exact digest preserve
reproducibility without asserting permission to redistribute the PDF. The
publisher DOI is retained as the authoritative journal identity; it is not
represented as an accessible local copy.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the periodic prior-art row and
  claim ceiling.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the retrieval
  and digest notice.

The allowed outward statement is therefore: Luca and Tachiya's named source
restates their earlier irrationality theorem for nonzero purely periodic
integer coefficients and proves a stronger linear-independence theorem for
nonnegative purely periodic coefficients, with explicit divisor-function and
odd-support examples; those results remain distinct from the release's
periodic-divisor certificate, mixed-sign dichotomy, and universal #257 claim.
