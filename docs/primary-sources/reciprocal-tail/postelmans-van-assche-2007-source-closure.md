# Postelmans–Van Assche source closure: q-zeta linear independence

This source-evidence record closes the q-zeta antecedent cited for the
constant-weight squared-Lambert anchor. It records the exact theorem and the
prime-index condition used in its proof; it is attribution and claim-boundary
evidence, not proof authority for this release.

## Stable identity and bound artifact

- **Authors and title:** Kelly Postelmans and Walter Van Assche,
  *Irrationality of ζ_q(1) and ζ_q(2)*.
- **Publication identity:** *Journal of Number Theory* **126** (2007), no. 1,
  119–154, DOI [10.1016/j.jnt.2006.11.011](https://doi.org/10.1016/j.jnt.2006.11.011).
- **Bound artifact:** [arXiv:math/0604312v1](https://arxiv.org/abs/math/0604312v1),
  submitted 13 April 2006; [PDF](https://arxiv.org/pdf/math/0604312v1).
- **Local artifact:**
  [`postelmans-van-assche-2007-q-zeta.pdf`](postelmans-van-assche-2007-q-zeta.pdf),
  SHA-256 `1687777a636088e1065fd7de469b8cc163f3cb146198419388d9a72eab785df9`;
  292,893 bytes; 34 PDF pages. The complete extracted text was read and
  theorem/proof/reference pages were visually checked.

The preprint is a public arXiv copy of the journal article. No separate
redistribution grant beyond the public arXiv availability was verified for
this local acquisition copy.

## Read state and exact locators

`read_complete` for all 2,332 extracted-text lines across the 34-page PDF.
PDF pages 3 and 29–33 were visually checked; these are the theorem statement,
cyclotomic nonvanishing argument, and final approximation estimates.

- **q-zeta definition and specialization:** PDF p. 1, equation (1.1), defines
  `ζ_q(s)=Σ_{n≥1} n^{s−1}q^n/(1−q^n)` for `|q|<1`. PDF p. 2 then restricts
  to `q=1/p` with integer `p>1`, so `ζ_q(1)=Σ_{n≥1}1/(p^n−1)` and
  `ζ_q(2)=Σ_{n≥1}n/(p^n−1)`.
- **Simultaneous irrationality inputs:** PDF p. 2, Theorems 1.1 and 1.2,
  construct integer common-denominator rational approximants for `ζ_q(1)`
  and `ζ_q(2)` and prove nonzero errors tending to zero. Their construction
  uses multiple little q-Jacobi polynomials and Hermite–Padé approximation;
  the detailed constructions and estimates are in Sections 2–5.
- **Main linear-independence theorem:** PDF p. 3, Theorem 1.3, states that
  `1`, `ζ_q(1)`, and `ζ_q(2)` are linearly independent over `Q` for
  `q=1/p`, `p` an integer greater than one. This is stronger than the two
  individual irrationality statements.
- **Proof mechanism:** PDF p. 3, Lemma 1.2, gives the common-approximation
  criterion: for every nonzero integer triple and infinitely many indices,
  the corresponding integer combination is nonzero while the two
  approximation errors tend to zero. PDF pp. 29–32, Section 6.1, verifies
  nonvanishing using cyclotomic-polynomial congruences for indices with
  `2n−1` prime and greater than the relevant coefficient; PDF p. 33,
  Section 6.2, verifies the two errors tend to zero. Together these pages
  complete the proof of Theorem 1.3.
- **Constant-weight release connection:** The release independently proves
  `L₂(1)=ζ_{1/2}(2)−ζ_{1/2}(1)`. Applying Theorem 1.3 at `p=2` therefore
  establishes irrationality of that constant-weight value, because a rational
  difference would give a nontrivial rational linear relation among
  `1,ζ_{1/2}(1),ζ_{1/2}(2)`. This transfer is an application of the source
  theorem to the release identity, not a theorem stated in the source.
- **End matter:** PDF pp. 33–34 list the cited antecedents and publication
  references. The arXiv copy's Section 6 heading on PDF p. 29 controls the
  proof-section locator; references in secondary prose that call this
  preprint's proof “Section 7” are not used here.

## Attribution and claim ceiling

### Supports

- Attribution to Postelmans and Van Assche of the q-zeta linear-independence
  theorem: Theorem 1.3, PDF p. 3, proved in Section 6, PDF pp. 29–33.
- The hypotheses `q=1/p` and integer `p>1`, the q-zeta series definitions,
  and the simultaneous rational-approximation method: PDF pp. 1–3 and
  Sections 2–6.
- The constant-weight q-zeta consequence at `q=1/2` after using the release's
  separately formalised squared-Lambert identity.
- Publication identity, arXiv route, exact local digest, and page-level
  locators recorded above.

### Does not support

- Irrationality of the Möbius-weighted value `L₂(μ)=S−1/2`, any transfer from
  the constant-weight row to the Möbius row, or a solution of Erdős #249 or
  #257.
- The release's periodic-divisor certificate, measure-one geometry, greedy
  interfaces, finite death certificates, Lean declarations, Comparator
  verdicts, Palomar assurance, or release acceptance.
- A theorem for arbitrary algebraic `q` from this paper's Theorem 1.3; the
  stated linear-independence result is restricted to reciprocal integers.
- Novelty, priority, significance, peer review, or equivalence between the
  Hermite–Padé/cyclotomic proof and the release's gcd-moment formalization.

## Negative checks

The complete preprint was checked for the release's Lean declaration names,
Comparator/Palomar machinery, totient-kernel claims, Erdős #249, and a proof
of universal #257; none occurs. The source proves a q-zeta linear-independence
result, not a release-validation or Möbius-support result.

## Redistribution disposition

The arXiv PDF is publicly retrievable, but no explicit redistribution grant for
this local acquisition copy was verified. The binary therefore remains
`working_tree_only` with `link_and_digest_only` disposition, is excluded from
the public candidate, and has `permission_evidence_status: not_verified` in
the disposition manifest. The arXiv route, DOI, and exact digest preserve
reproducibility without asserting permission to redistribute the PDF.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the q-zeta prior-art row and
  constant-weight claim ceiling.
- [`docs/papers/full-text/erdos249-257-main-paper.md`](../../papers/full-text/erdos249-257-main-paper.md),
  the appendix identity and citation locator.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the retrieval
  and digest notice.

The allowed outward statement is therefore: Postelmans and Van Assche prove
that `1, ζ_q(1), ζ_q(2)` are linearly independent for reciprocal-integer
`q=1/p` with `p>1`; at `q=1/2`, the release's separately formalised identity
turns this into irrationality of the constant-weight squared-Lambert anchor,
without implying anything about the Möbius row or universal Erdős problems.
