# Erdős–Graham (1980) source closure: Lambert-series context and open boundaries

This source-evidence record binds P. Erdős and R. L. Graham's 1980
monograph to the release's historical #249/#257 prior-art map. It separates
the full-support identities the source records from the open sparse-series
questions and from the release's separately formalised results.

## Identity and retrieval

- **Authors:** Paul Erdős and Ronald L. Graham.
- **Title:** *Old and New Problems and Results in Combinatorial Number
  Theory*.
- **Publication identity:** Monographie no. 28 of *L'Enseignement
  Mathématique*, Université de Genève, 1980, 128 printed pages.
- **Official retrieval route:** [UCSD-hosted author/source scan](https://mathweb.ucsd.edu/~ronspubs/80_11_number_theory.pdf), listed from
  [Ron Graham's paper index](https://mathweb.ucsd.edu/~ronspubs/).
- **Acquisition digest:** the locally inspected 124-page PDF at
  `docs/primary-sources/reciprocal-tail/erdos-graham-1980-old-new-problems.pdf`
  has SHA-256 `0cbf0c32f0ab1e1c71db5121a88bac905bf976c4a6ab6bb6d7d9cf9ddd184ed3`
  and size 5,253,644 bytes. PDF pages 1–124 correspond to the monograph's
  printed pages 3–128 after the cover and contents leaves.
- **Reading status:** the complete scan was rasterised and OCR-reviewed;
  printed pp. 60–66 were manually checked against the page images because
  the source has no embedded text layer.

No explicit redistribution grant for this local acquisition copy was
verified.

## Exact support

1. **Section 7 identification (printed p. 60; PDF p. 56).** The source
   begins its “Irrationality and Transcendence” discussion and states that it
   will treat special series requiring special methods, rather than claiming
   a general irrationality theorem.
2. **Divisor and totient full-support boundary (printed p. 61; PDF p. 57).
   ** The source records that the full-support divisor-weighted series
   `sum_{n>=1} d(n)/2^n` is irrational, while saying that the analogous
   `sum_{n>=1} phi(n)/2^n` could not then be proved irrational. It also
   records further questions about bounded arithmetic-function weights as
   unresolved or conjectural.
3. **Full-support Mersenne identity (printed p. 62; PDF p. 58).** The source
   writes the identity
   `sum_{n>=1} 1/(2^n - 1) = sum_{n>=1} d(n)/2^n`
   and states that this value is known to be irrational. On the same page it
   says that the analogous `sum_{n>=1} 1/(2^n - 3)` and
   `sum_{n>=1} 1/(n! - 1)` were not known to be irrational at the time.
4. **Squarefree reciprocal question (printed p. 63; PDF p. 59).** The
   source says that the reciprocal sum over squarefree numbers should be
   irrational but that it had no proof, then records related representation
   questions. This is an explicit open boundary, not a theorem.
5. **Adjacent LCM-denominator result (printed p. 65; PDF p. 61).** For a set
   of primes `Q`, the source states that the reciprocal sum over the least
   common multiples of the initial integers whose prime factors lie in `Q`
   is irrational when `Q` is infinite, and asks what happens for finite `Q`
   with more than one element. This is a different denominator mechanism
   from the release's Mersenne sparse-support series.
6. **Section boundary (printed p. 66; PDF p. 62).** The source moves from
   these irrationality questions to its Diophantine Problems section; the
   displayed examples on this page remain separate special series and do not
   supply a general sparse-support criterion.

## Relation to the release

- The source is historical prior art for the full-support divisor Lambert
  identity and for the state of the binary totient irrationality question.
- Its full-support Mersenne identity is relevant background for Problem #257,
  but it does not address arbitrary increasing sparse supports.
- Its squarefree passage is useful negative evidence for any claim that the
  older literature already settled squarefree-support irrationality.
- The source's LCM result is adjacent context only; no equality or implication
  to the release's Mersenne denominators is asserted.

## Non-support and attribution ceiling

- The monograph does not state Erdős Problems #249 or #257 by those modern
  numbers, and it does not prove the release's universal sparse-support
  assertion.
- It does not prove irrationality of the binary totient series, any finite
  totient-kernel rank or basis, the release's denominator bound, or its tail
  certificate equivalence.
- It contains no Lean declarations, Comparator or Palomar verdicts, release
  acceptance cells, or priority claim for the release's formal results.
- The attribution ceiling is the full-support divisor/Mersenne identity and
  the explicitly recorded totient, squarefree, and adjacent-series problem
  boundaries at the printed pages above. No novelty or priority claim is
  made for the release's separate formal mechanisms.

## Negative checks

The complete OCR extraction was checked for the release's Lean declaration
names, Comparator theorem names, Palomar verdicts, finite totient-kernel
rank/basis statements, and a proof of arbitrary sparse Mersenne-subseries
irrationality. None occurs. The directly relevant statements are the
full-support identity on printed p. 62 and the open boundaries on printed pp.
61 and 63.

## Redistribution disposition

The UCSD-hosted scan is publicly retrievable, but no explicit redistribution
grant for this local acquisition copy was verified. The binary therefore
remains `working_tree_only` with `link_and_digest_only` disposition, is
excluded from the public candidate, and has
`permission_evidence_status: not_verified` in the disposition manifest. The
official retrieval route and exact digest preserve reproducibility without
asserting permission to redistribute the scan.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the historical #249/#257 map and
  claim ceiling.
- [`redistribution-dispositions.json`](../redistribution-dispositions.json),
  the artifact-level public-release disposition record.
- [`docs/THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md), the retrieval
  and digest notice.
