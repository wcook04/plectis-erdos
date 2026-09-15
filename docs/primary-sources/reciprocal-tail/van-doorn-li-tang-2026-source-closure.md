# Wouter van Doorn, Yanyang Li and Quanyu Tang source closure: matching integers to distinct multiples

This source-evidence record binds an external source cited by both #243
reciprocal-tail manuscripts at the Chinese remainder lemma on blocks of
consecutive multiples. It is attribution and claim-boundary evidence, not
proof authority for this release, and it does not bear on Erdős #243.

## Stable identity and read artifact

- **Authors and title:** Wouter van Doorn, Yanyang Li and Quanyu Tang,
  *Optimal bounds for an Erdős problem on matching integers to distinct
  multiples*.
- **Publication identity:** arXiv preprint arXiv:2603.28636v1 [math.CO], 8 pages, submitted 30 March 2026. The arXiv record states that the paper solves Problem #650 on Bloom's Erdős problems website.
- **Official routes:** the [arXiv record](https://arxiv.org/abs/2603.28636)
  and its [HTML rendering](https://arxiv.org/html/2603.28636v1).
- **Read artifact:** the arXiv v1 PDF, SHA-256
  `3e81146033fe4e7caeaa64e6667a99f19bfa823a5ae747cb8a7aeedd24b69bb8`;
  518783 bytes; 8 pages. No copy is stored in this repository.

## Read state and exact locators

`read_complete`: all eight PDF pages were read directly from the page images.

- **Problem statement:** PDF p. 1 defines `f(m)` as the largest `r` such that, for every set `A = {a_1 < ... < a_m}` of positive integers and every real `x`, there are distinct `c_1, ..., c_r` in `A` and distinct integers `b_1, ..., b_r` with `x < b_i < x + 2a_m` and `c_i | b_i`, and records the question as Erdős Problem #650.
- **Matching reformulation:** PDF p. 2 recasts `f(m)` as the minimum, over `A` and `x`, of the maximum matching size in the bipartite graph `G(A, x)` joining `a` in `A` to an integer `b` in `(x, x + 2a_m)` whenever `a | b`.
- **Main theorem:** PDF p. 2, Theorem 2.1: `f(m) = min(m, ceil(2 sqrt(m)))` for every positive integer `m`.
- **Upper-bound construction:** PDF p. 4, Theorem 3.1, proves `f(st) <= s + t` with the set `alpha_(i,j) = M + i + jD`; Claim 3.2 on the same page proves that `gcd(alpha_(i,j), alpha_(k,l))` divides `i - k`. PDF p. 5 applies the generalised Chinese remainder theorem to obtain `x_0` congruent to `i` modulo every `alpha_(i,j)`, stating that its compatibility condition is exactly Claim 3.2.
- **Lower bound:** PDF p. 3, Lemma 2.3, is a generalisation of Hall's theorem; PDF pp. 5–7, Theorem 4.1 and its proof, bound neighbourhood sizes through an injection into a product of the two halves of the neighbourhood.
- **Formalisation record:** PDF p. 2, Section 1.1, and PDF p. 7, Section 5, describe the AI-assisted workflow and the Lean formalisation of every result in the paper, including a gap in the first draft of the Case 2 injection that the formal proof repaired.

## Attribution and claim ceiling

### Supports

- The manuscripts' description of Erdős Problem #650 as the problem of
  matching a set of integers to distinct multiples in an interval, and of
  Theorem 2.1 as its solution with the optimal count
  `min(k, ceil(2 sqrt(k)))` for a set of `k` positive integers.
- The manuscripts' description of the upper-bound construction as Chinese
  remaindering for moduli that need not be pairwise coprime, with Claim 3.2
  supplying the divisibility of residue differences that the generalised
  theorem requires (PDF pp. 4–5).
- The publication identity, official routes and page-level locators above.

### Does not support

- Any statement about Erdős #243, reciprocal sums of doubly exponential
  sequences, the reciprocal-tail state, the first-crossing obstruction or the
  release's Lean declarations.
- Any claim that the #243 lemma on consecutive multiples follows from, or
  implies, a result of the source. The manuscripts cite the construction as
  the same Chinese remaindering device; the #243 lemma assumes pairwise
  coprime moduli and carries its own one-line proof.
- Novelty, priority, significance, acceptance or peer review.

## Negative checks

The eight pages contain no statement about Erdős #243, Sylvester's sequence,
Ahmes series or reciprocal sums.

## Redistribution disposition

No copy of the PDF is kept in this repository. The disposition ledger records
this note as a citation-only source record; the arXiv routes and the digest
above are preserved for reproducibility without asserting permission to
redistribute the PDF.

## Direct consumers

- [`erdos-243-reciprocal-tail-rigidity.md`](../../papers/full-text/erdos-243-reciprocal-tail-rigidity.md),
  the remark after the consecutive-multiples lemma.
- [`erdos243-reciprocal-tail-reasoning-surface.md`](../../papers/full-text/erdos243-reciprocal-tail-reasoning-surface.md),
  the remark after the lemma on shifted blocks of consecutive multiples.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the citation-only source-record list.

The allowed outward statement is therefore: van Doorn, Li and Tang solve
Erdős Problem #650 by determining the optimal matching count, and their
extremal construction places consecutive multiples by Chinese remaindering for
moduli that need not be pairwise coprime; the #243 manuscripts cite this as the
same device as their pairwise coprime lemma and do not rely on it.
