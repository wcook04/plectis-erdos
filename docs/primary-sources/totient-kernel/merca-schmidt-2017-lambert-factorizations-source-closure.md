# Primary-source closure: Merca–Schmidt (2017)

## Identity and retrieval

- **Authors:** Mircea Merca and Maxie D. Schmidt.
- **Title:** “Generating Special Arithmetic Functions by Lambert Series Factorizations.”
- **Publication:** *Contributions to Discrete Mathematics* 14 (2019), no. 1, pp. 31–45; the official journal PDF identifies the 2019 University of Calgary copyright.
- **Preprint:** arXiv:1706.00393v2, dated 4 August 2017.
- **Persistent and publication routes:** [arXiv:1706.00393](https://arxiv.org/abs/1706.00393); [arXiv PDF](https://arxiv.org/pdf/1706.00393); [official journal PDF](https://cdm.ucalgary.ca/article/download/62425/53773).
- **Acquisition digest:** the locally inspected 19-page arXiv v2 PDF at `docs/primary-sources/totient-kernel/merca-schmidt-2017-lambert-factorizations.pdf` has SHA-256 `9ccec235f1dd44c2b2d5447252d7c5a907ef3cf7518439b363c6f144a9c21019` and size 321,695 bytes.
- **Reading status:** the complete arXiv source was read from its text layer. The preprint’s printed pages are PDF pages 1–19; the official journal PDF is a separately typeset 15-page publication copy.

## Exact support

1. **Lambert-series transform (Introduction, equation (1), arXiv PDF pp. 1–2; journal PDF pp. 31–32).** For `|q| < 1`, the paper writes `sum_{n>=1} a_n q^n/(1-q^n) = sum_{m>=1} b_m q^m`, with `b_m = sum_{d|m} a_d`. This is the divisor-convolution transform underlying the source’s later matrix formulas.
2. **Classical arithmetic-function examples (Introduction, equation (2), arXiv PDF p. 2; journal PDF p. 32).** The source records the Lambert expansions for the Möbius function, Euler’s totient function, generalized divisor sums, Liouville’s function, the von Mangoldt function, the squarefree indicator `|mu|`, and Jordan’s totient. In particular, it states `sum phi(n) q^n/(1-q^n) = q/(1-q)^2`.
3. **Partition factorization theorem (Introduction, equation (3), arXiv PDF p. 3; journal PDF p. 32).** The paper gives the generalized factorization of `sum a_n q^n/(1 +/- q^n)` through the Euler product and the partition-counting quantities `s_o(n,k)` and `s_e(n,k)` for partitions into distinct parts with odd or even numbers of parts.
4. **Matrix representation (Section 1.2, equations (4)–(6), arXiv PDF pp. 3–4; journal PDF pp. 33–34).** It defines the lower-triangular matrices `A_n` from the partition-difference entries, expresses the coefficient vector `a_n` using `A_n^(-1)`, and gives the block recurrence for `A_(n+1)^(-1)`.
5. **Inverse-matrix recurrences (Proposition 2.1 and Corollary 2.2, arXiv PDF pp. 6–8; journal PDF pp. 36–38).** The source proves recursive and nested exact formulas for the inverse entries `s_(n,j)^(-1)`, while separately flagging a matrix-power expansion as computationally obtained without an induction proof in the article.
6. **Exact inverse-entry formula (Theorem 3.2, arXiv PDF pp. 9–11; journal PDF pp. 39–41).** For `1 <= k <= n`, the paper proves `s_(n,k)^(-1) = sum_{d|n} p(d-k) mu(n/d)`, where `p` is Euler’s partition function. It also gives the resulting Lambert generating function for the inverse entries.
7. **Finite formulas for special functions (Corollary 3.3, arXiv PDF pp. 12–13; journal PDF pp. 42–43).** The corollary expands `phi(n)`, `mu(n)`, `lambda(n)`, `Lambda(n)`, `|mu(n)|`, and `J_t(n)` as finite divisor sums involving shifted partition values and the inverse-matrix component sequences. The paper notes that corresponding average-order formulas follow by summing over `n`.
8. **Further exact and boundary results (Propositions 3.5–3.8 and Section 4, arXiv PDF pp. 14–18; journal PDF pp. 43–45).** The source records partition subsequences for upper-triangular, prime, prime-square, and relatively-prime product indices, then gives generalized Lambert-factorization variants and lists congruence, inverse-entry, and average-order questions as future work.

## Relation to the release

- Equation (2) is direct prior art for the classical totient Lambert identity used as transform background in the release. It supplies the external identity, not the release’s finite-level totient-kernel rank, basis, relation normal form, or #249 conclusion.
- The source’s Möbius/partition matrix formulas are an external arithmetic-function mechanism. They are not the release’s Lean declarations, and no equality between its matrices and a local kernel is asserted without a separately checked bridge.
- The article is a collaborative synthesis of earlier Merca and Schmidt factorization results. Its theorem/proposition/conjecture labels and the explicit distinction between proved formulas and computationally obtained observations are preserved in this closure.

## Non-support and attribution ceiling

- The paper does **not** state Erdős Problems #249 or #257, the release’s totient-kernel rank, Lean declarations, Comparator, or Palomar.
- Its Lambert identities do not prove the release’s coefficient-weighted constant is irrational, do not provide the release’s denominator bound or tail-certificate equivalence, and do not settle any open sparse-support problem.
- The attribution ceiling is the stated Lambert-series factorization, partition/matrix identities, inverse-entry formula, finite arithmetic-function formulas, and the source’s explicit conjecture/future-work boundaries. No novelty or priority claim is made for the release’s separate formal results.

## Redistribution disposition

The arXiv preprint and official journal PDF provide stable retrieval routes, but no explicit redistribution grant for this acquisition copy was verified. The artifact is therefore `working_tree_only`, `link_and_digest_only`, `public_candidate_inclusion: false`, with `permission_evidence_status: not_verified`; the public candidate must use the official retrieval routes rather than ship the binary.

## Direct consumers

- `docs/PRIOR_ART.md`
- `docs/primary-sources/redistribution-dispositions.json`
- `docs/THIRD_PARTY_NOTICES.md`
