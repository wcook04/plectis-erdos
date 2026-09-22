# Junnosuke Koizumi and Anju Yokoi source closure: Apéry-type approximations for q-series

This source-evidence record binds an external source cited by both #243
reciprocal-tail manuscripts for the shape of approximation criteria for
irrationality. It is attribution and claim-boundary evidence, not proof
authority for this release, and it does not bear on Erdős #243.

## Stable identity and read artifact

- **Authors and title:** Junnosuke Koizumi and Anju Yokoi, *Apéry-type
  approximations and irrationality measures for certain q-series*.
- **Publication identity:** arXiv preprint arXiv:2608.26918v1 [math.NT], 37 pages, stamped 27 August 2026.
- **Official routes:** the [arXiv record](https://arxiv.org/abs/2608.26918)
  and its [HTML rendering](https://arxiv.org/html/2608.26918v1).
- **Read artifact:** the arXiv v1 PDF, SHA-256
  `1195067c4a6c653be6ea887d4c34475f7c4010e7228bc773561bff9b48a040ef`;
  515606 bytes; 37 pages. No copy is stored in this repository.

## Read state and exact locators

`read_partial`: PDF pp. 1–6 and 12–14 were read directly; the other pages
were not read for this record.

- **Main theorem:** PDF p. 4, Theorem 1.4: for every integer `x` with `|x| >= 2` the values `psi(1/x)`, `Delta(1/x)` and `B_4(1/x)` of three q-series are irrational, with irrationality-measure bounds `18/7`, `18 pi^2/(7 pi^2 - 24)` and `3`.
- **Approximation criterion:** PDF p. 13, Lemma 3.4, with proof on p. 14: integer pairs `(A_n, B_n)` with `|A_n| + |B_n| <= X^(kappa n^2 + o(n^2))` and `0 < |B_n xi - A_n| <= X^(-lambda n^2 + o(n^2))` make `xi` irrational, and a nonvanishing determinant `A_n B_(n+1) - A_(n+1) B_n` gives `mu(xi) <= 1 + kappa/lambda`.
- **Integrality step:** PDF p. 14, the proof of Lemma 3.4 uses that `q |B_n xi - A_n| = |p B_n - q A_n|` is a positive integer when `xi = p/q`.
- **Role in the source:** PDF p. 12, the opening of Section 3 states that its tools serve the irrationality proofs of the later sections.

## Attribution and claim ceiling

### Supports

- The manuscripts' description of Lemma 3.4 as a quantitative form of the
  irrationality criterion by nonzero integer linear forms that tend to zero,
  applied in the source to values of q-series.
- The publication identity, official routes and page-level locators above.

### Does not support

- Any statement about Erdős #243, reciprocal sums of doubly exponential
  sequences, the reciprocal-tail state, the cubic-rate theorem or the
  release's Lean declarations.
- Any claim that the #243 arguments use Lemma 3.4 or the source's
  approximations. The manuscripts cite the lemma to describe that class of
  criteria; their proofs work with the integer tail directly.
- Novelty, priority, significance, acceptance or peer review.

## Negative checks

The pages read contain no statement about Erdős #243, Sylvester's sequence or
reciprocal sums of doubly exponential sequences. Pages outside pp. 1–6 and
12–14 are not claimed checked.

## Redistribution disposition

No copy of the PDF is kept in this repository. The disposition ledger records
this note as a citation-only source record; the arXiv routes and the digest
above are preserved for reproducibility without asserting permission to
redistribute the PDF.

## Direct consumers

- [`erdos-243-reciprocal-tail-rigidity.md`](../../papers/full-text/erdos-243-reciprocal-tail-rigidity.md),
  the remark after the cubic-rate theorem.
- [`erdos243-reciprocal-tail-reasoning-surface.md`](../../papers/full-text/erdos243-reciprocal-tail-reasoning-surface.md),
  the position paragraph of the cubic-rate section.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the citation-only source-record list.

The allowed outward statement is therefore: Lemma 3.4 of Koizumi and Yokoi
states a quantitative form of the approximation criterion for irrationality,
used in their paper for values of q-series; the #243 manuscripts cite it to
describe that class of criteria and do not rely on it.
