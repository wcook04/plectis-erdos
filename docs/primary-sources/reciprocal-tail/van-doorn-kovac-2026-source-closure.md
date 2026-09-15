# Wouter van Doorn and Vjekoslav Kovač source closure: lacunary sequences representing rational intervals

This source-evidence record binds an external source cited by both #251
prime-gap dyadic manuscripts beside the interval-filling and
divisibility-chain steps of their sparse rationalisation construction. It is
attribution and claim-boundary evidence. The manuscripts cite it for
comparison, and their proofs do not invoke its results.

## Stable identity and read artifact

- **Authors and title:** Wouter van Doorn and Vjekoslav Kovač, *Lacunary
  sequences whose reciprocal sums represent all rational numbers in an
  interval*.
- **Publication identity:** *Acta Arithmetica* **223** (2026), 275–295, DOI
  [10.4064/aa251001-13-1](https://doi.org/10.4064/aa251001-13-1), published
  online 15 April 2026. The Crossref record for this DOI (publisher: Institute
  of Mathematics, Polish Academy of Sciences) gives the title, both authors,
  the journal, ISSN 0065-1036 (print) and 1730-6264 (electronic), and the
  online date; it carries no volume or page fields. The volume and page range
  are taken from the publisher's article page, which the Crossref record names
  as its resource, and they agree with the journal reference on the arXiv
  record.
- **arXiv version read:** arXiv:2509.24971v3 [math.NT], stamped 3 December
  2025 on PDF p. 1. The arXiv record carries the comment "17 pages, 1 figure.
  v3: minor changes to the exposition". PDF p. 1 gives the 2020 Mathematics
  Subject Classification as primary 11D68 and secondary 11B05, 11B13, 40A05.
- **Official routes:** the [arXiv v3 record](https://arxiv.org/abs/2509.24971v3),
  the [arXiv v3 PDF](https://arxiv.org/pdf/2509.24971v3) and the
  [journal DOI](https://doi.org/10.4064/aa251001-13-1).
- **Read artifact:** the arXiv v3 PDF, SHA-256
  `39ae910cad2f4e186ea9d6ea42f3cc657e5bd8e27e54fcc6c59ec45815cbe4ac`;
  274901 bytes; 17 pages. It is byte-identical to the arXiv v3 PDF route as
  fetched on 15 September 2026. No copy is stored in this repository.
- **Numbering:** statement, equation and page numbers below follow arXiv v3,
  whose printed page numbers equal its PDF page numbers. The journal
  pagination was not read. Both #251 bibliography entries state that their
  statement numbers follow arXiv version 3.

## Read state and exact locators

`read_complete`: all seventeen PDF pages were read directly from the page
images, with the extracted text layer checked against them.

- **Problem and main theorem:** PDF p. 1 quotes Conjecture 4 of Bleicher and
  Erdős (1976), which asks whether finite sums of reciprocals from a sequence
  with `n_(i+1)/n_i > c > 1` can contain every rational number in some
  interval, and identifies the question with Problem #355 on Bloom's Erdős
  problems website; Definition 1 defines `lambda`-lacunary sequences. PDF p. 2,
  display (1.2), defines `P((x_i))` as the set of finite subsums, and
  Theorem 1 states: (a) for every `lambda` in `(1, 2)` there is a
  `lambda`-lacunary sequence of positive integers whose finite reciprocal sums
  contain every rational number in `[0, 2]`; (b) the sequence can also satisfy
  `n_(i+1)/n_i -> 2` and represent every rational number in `(0, 2]` by
  infinitely many finite sets; (c) no 2-lacunary sequence has finite
  reciprocal sums containing every rational number of a non-empty open
  interval. The abstract on PDF p. 1 states that this disproves the conjecture
  of Bleicher and Erdős.
- **Optimal filled length and large jumps:** PDF p. 2, Definition 2 and
  Theorem 2, with the statement ending on PDF p. 3: for `lambda` in `(1, 2)`,
  the supremal filled length is `R(lambda) = sum 1/a_i` with `a_1 = 1` and
  `a_(i+1) = ceil(lambda a_i)`; `R(lambda) -> infinity` as `lambda -> 1+`,
  `R(lambda) -> 2` as `lambda -> 2-`, and `R(lambda) = 0` for `lambda >= 2`.
  Figure 1 on PDF p. 3 graphs `R` on `(1, 2)`. PDF p. 3, Theorem 3: for
  `Lambda >= 2` and `1 < lambda < Lambda/(Lambda - 1)` there is a
  `lambda`-lacunary sequence with `n_(i+1) > Lambda n_i` for infinitely many
  `i` whose finite reciprocal sums contain every rational number in
  `[0, sum 1/n_i)`.
- **Finite and infinite sums:** PDF p. 4 relates the finite-sum set to the
  achievement set of all subsums and states that the Crmarić–Kovač and
  Kovač–Tao papers concern infinite sums of unit fractions, from which no
  results are needed.
- **Necessary conditions:** PDF p. 5, Lemma 4, with proof on PDF pp. 5–6:
  the achievement set is compact with empty interior when `x_i >= sum_(j>i) x_j`
  for every `i` (2.1) and the inequality is strict for infinitely many `i`
  (2.2). PDF p. 6, Corollary 5, with proof on PDF pp. 6–7, proves Theorem 1(c).
  PDF p. 7 records Kakeya's criterion that the achievement set of a decreasing
  summable positive sequence is a single segment exactly when
  `x_i <= sum_(j>i) x_j` for every `i`, and Corollary 6 derives the necessary
  inequality (2.4), `1/n_i <= sum_(j>i) 1/n_j` for every `i`.
- **Lemma 7, dense filling:** statement on PDF p. 7; proof by induction on
  `m` on PDF pp. 7–8. For real numbers `x_1 > x_2 > ... > x_m > 0` with
  `x_i <= x_(i+1) + ... + x_m + x_m` for `1 <= i <= m - 1`, the subsums over
  subsets of `{1, ..., m}` divide `[0, x_1 + ... + x_m]` into sub-intervals of
  length at most `x_m`. PDF p. 7 notes the resemblance to Lemma 1 of each of
  two 1964 papers of Graham.
- **Proposition 8, sufficient conditions:** statement on PDF p. 8. For a
  strictly increasing sequence of positive integers `n_i` and an infinite
  increasing sequence of distinguished indices `m_k`, assume (1) every positive
  integer divides some `n_i`; (2) for every `k`, `n_(m_k)` is divisible by
  every `n_j` with `j < m_k`; (3) inequality (3.1),
  `1/n_i <= sum_(j=i+1)^(m_k) 1/n_j + 1/n_(m_k)` for all `k` and
  `m_(k-1) <= i < m_k`. Then `P((1/n_i)) = [0, sum 1/n_i) ∩ Q`. If in addition
  (3.2) holds for infinitely many `k`, every rational number in
  `(0, sum 1/n_i)` has infinitely many representations. The remark after the
  statement allows a divergent series, read as infinity. The proof runs from
  PDF p. 8 to PDF p. 9: hypotheses (1) and (2) give `K` such that the reduced
  denominator of `q` divides `n_(m_K)`; summing (3.1) over successive blocks
  gives the hypothesis of Lemma 7 for `m = m_K`; and because every subsum is an
  integer multiple of `1/n_m` by hypothesis (2), the subsums reach every point
  of `[0, sum_(i<=m) 1/n_i] ∩ (1/n_m)Z`, including `q`.
- **Remark 9:** PDF p. 9: condition (3.1) holds automatically when
  `n_(i+1) <= 2 n_i` for every `i` (3.3), and (3.2) follows when in addition
  `n_(i+1) < 2 n_i` for infinitely many `i` (3.4).
- **Constructions:** PDF p. 10, Lemma 10, gives for every `lambda` in `(1, 2)`
  and every positive integer `Q` a multiple `N` of `Q` with a chain of divisors
  from 1 to `N` whose consecutive ratios lie in `[lambda, 2]`. The proof of
  Theorem 1 on PDF pp. 10–11 applies Proposition 8 to a sequence whose
  distinguished terms are `n_(m_k) = N_1 N_2 ... N_k`, where `N_k` is divisible
  by the product of the first `k` primes, so that `n_(m_k)` is divisible by
  `p_1^k p_2^(k-1) ... p_k` (PDF p. 11). PDF pp. 11–12 list 27 terms of a
  `3/2`-lacunary example. PDF p. 12, Lemma 11, and the proof of Theorem 2 on
  PDF pp. 12–13; PDF p. 13 computes `R(3/2)` to 50 decimal digits from 287
  terms. PDF pp. 14–15 prove Theorem 3, and PDF p. 15 shows that no
  `lambda`-lacunary sequence with `lambda >= Lambda/(Lambda - 1)` has its
  properties.
- **Appendix and end matter:** PDF p. 15, Theorem 12, restates Eppstein's
  theorem for sets closed under doubling that contain a multiple of each odd
  number, with an alternative proof by the same technique on PDF pp. 15–16.
  PDF p. 16 carries the acknowledgments, which credit Bloom's Erdős problems
  website with helping to initiate the project, and references [1] to [10];
  PDF p. 17 carries references [11] to [19] and the authors' affiliations in
  Groningen and at the University of Zagreb.

## Attribution and claim ceiling

### Supports

- The manuscripts' description of Lemma 7 and Proposition 8: dense filling
  (Lemma 7, PDF p. 7) combined with a divisibility chain among distinguished
  terms (Proposition 8, hypotheses (1) and (2), PDF p. 8) makes the finite
  reciprocal sums equal to every rational number in `[0, sum 1/n_i)`. The
  chain is a direct consequence of hypothesis (2), since `m_(k-1) < m_k` gives
  `n_(m_(k-1)) | n_(m_k)`. Every positive integer divides `n_(m_k)` for all
  large `k` by hypotheses (1) and (2) together, and the proof on PDF p. 8 opens
  with this step for the reduced denominator of `q`.
- The reasoning record's remark, in its paired-corrections proof, that the
  distinguished terms of Proposition 8 form a divisibility chain and are
  eventually divisible by every fixed positive integer, at the same locators.
- The short note's description of this interval filling as a recent precedent
  for sums of unit fractions: the source concerns finite sums of distinct unit
  fractions (PDF pp. 1–2).
- The publication identity, arXiv version, official routes, digest and
  page-level locators above.

### Does not support

- Any statement about Erdős #251, the series `sum p_n 2^(-n)`, prime
  numerators, consecutive prime gaps, dyadic tails or irrationality. The
  source proves no irrationality result.
- Any claim that the #251 sparse rationalisation theorem, its factorial
  schedule, its eventual congruence preservation or its density-zero support
  follows from, or implies, Proposition 8. Proposition 8 concerns finite sums
  of reciprocals of one integer sequence, and PDF p. 4 states that no results
  are needed from references [5] and [16], which concern infinite sums of unit
  fractions. The manuscripts cite it as a related construction and state the
  chain property of their factorial moduli directly.
- Any claim that the source's construction uses factorial moduli. The proof of Theorem 1
  takes the distinguished terms to be the products `N_1 N_2 ... N_k` from
  Lemma 10, with `N_k` divisible by the first `k` primes (PDF pp. 10–11).
- The statement numbers, pagination or wording of the journal version, which
  was not read.
- Novelty, priority, significance, acceptance or peer review.

## Negative checks

The seventeen pages contain no series with prime numerators, no statement
about prime gaps, no irrationality theorem and no mention of Erdős #251. The
only Erdős problem number in the paper is #355 (PDF p. 1). Primes enter only
as divisors and moduli: Graham's reciprocal basis containing all large primes
and squares (PDF p. 1), the powers of a prime in the motivating remark
(PDF p. 2), the primes larger than `n_(i_0)` that divide no term in the proof
of Corollary 5 (PDF p. 7), the products of the first `k` primes in the
constructions (PDF pp. 10–11, 13 and 14), and the title of Sun's conjecture
on unit fractions involving primes in reference [17] (PDF p. 17).

## Redistribution disposition

No copy of the PDF is kept in this repository. The disposition ledger records
this note as a citation-only source record; the arXiv and DOI routes and the
digest above are preserved for reproducibility without asserting permission
to redistribute the PDF.

## Direct consumers

- [`erdos-251-prime-gap-dyadic-series.md`](../../papers/full-text/erdos-251-prime-gap-dyadic-series.md),
  the paragraph "Relation to prior work" in the introduction and the
  bibliography entry.
- [`erdos251-prime-gap-reasoning-surface.md`](../../papers/full-text/erdos251-prime-gap-reasoning-surface.md),
  the paragraph "Relation to prior work" in the introduction, the schedule
  step of the proof in the subsection "Paired corrections and cumulative
  congruences", and the bibliography entry.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the citation-only source-record list.

The allowed outward statement is therefore: van Doorn and Kovač disprove the
conjecture of Bleicher and Erdős recorded as Erdős Problem #355 by
constructing, for every `lambda` in `(1, 2)`, a `lambda`-lacunary sequence
whose finite reciprocal sums contain every rational number in `[0, 2]`; their
Proposition 8 obtains every rational number in `[0, sum 1/n_i)` from dense
filling (Lemma 7) and a divisibility chain among distinguished terms that
eventually absorbs every positive integer. The #251 manuscripts cite this as a
related construction beside their own factorial moduli, and nothing in the
source concerns prime numerators or decides Erdős #251.
