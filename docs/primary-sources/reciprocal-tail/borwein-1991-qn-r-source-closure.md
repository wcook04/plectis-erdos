# Primary-source closure: Borwein (1991)

## Identity and retrieval

- **Author:** Peter B. Borwein.
- **Title:** “On the Irrationality of sum 1/(q^n + r).”
- **Publication:** *Journal of Number Theory* 37 (1991), no. 3, pp. 253–259; the issue is dated March 1991.
- **Persistent identifier:** DOI [10.1016/S0022-314X(05)80041-1](https://doi.org/10.1016/S0022-314X(05)80041-1).
- **Publisher record:** [ScienceDirect article record](https://www.sciencedirect.com/science/article/pii/S0022314X05800411).
- **Inspected full-text route:** [author’s reprint PDF](https://www.cecm.sfu.ca/~pborwein/PAPERS/P51.pdf); the publisher record remains the bibliographic authority.
- **Acquisition digest:** the locally inspected seven-page scan at `docs/primary-sources/reciprocal-tail/borwein-1991-qn-r.pdf` has SHA-256 `d75c70c327de69c7f3c5436968898ef155d8995fea6bad748c3194229892bdf0` and size 3,094,938 bytes.
- **Reading status:** all seven scanned pages were read through their rendered pages with OCR-assisted transcription. Printed pages 253–259 are PDF pages 1–7.

## Exact support

1. **Main series and theorem statement (abstract and Theorem 4, PDF pp. 1 and 5–6; printed pp. 253 and 257–258).** The source considers `sum_{n>=1} 1/(q^n + r)` and proves that when `q` is an integer greater than one, `r` is a nonzero rational, and `r != -q^n` for every `n >= 1`, the sum is irrational and is not a Liouville number.
2. **q-logarithm/Stieltjes function (equations (1)–(4), PDF pp. 2–3; printed pp. 254–255).** It defines `L^q(x) = sum_{n>=1} 1/(q^n - x)` together with its convergent geometric-series form, records the domain restrictions, and gives the functional relation used for the Padé analysis. The paper explains that `L^q` is a q-analogue of the logarithm.
3. **Padé denominator and numerator (Theorem 1, PDF pp. 3–4; printed pp. 255–256).** The main-diagonal Padé approximant `P_n(x)/Q_n(x)` is constructed explicitly. The source states that `Q_n` has degree `n` in `x` and degree `n^2` in `q` with integer coefficients, and that the normalized numerator has the corresponding polynomial and integrality properties.
4. **Three-term recurrence (Theorem 2, PDF p. 4; printed p. 256).** The denominator polynomials satisfy an explicit three-term recurrence with coefficients displayed in the source. This recurrence belongs to Borwein’s Padé family; the source does not identify it with the Amdeberhan–Zeilberger q-WZ operator.
5. **Approximation estimate (Theorem 3, PDF p. 5; printed p. 257).** For the stated real range of `x`, the source bounds the nonzero Padé error by a quantity that decays rapidly with the diagonal index. It attributes the theorem to Borwein’s earlier Padé analysis and uses it as the approximation input to Theorem 4.
6. **Arithmetic conversion and non-Liouville conclusion (proof of Theorem 4, PDF pp. 5–6; printed pp. 257–258).** The proof shifts the q-logarithm argument, clears the finite denominators using products of `q^n - r` and the q-factorial factors, and obtains integer polynomials in the rational offset. After substituting `r = A/l`, the resulting integer linear forms tend to zero too rapidly for rationality. The closing paragraph derives a uniform lower bound of order `1 / |q|^(constant * s)` for rational approximants and concludes that the value is not Liouville.
7. **Historical boundary (Introduction, PDF p. 1; printed p. 253).** The paper notes that the case `q = 2, r = -1` is the Lambert series proved irrational by Erdős, and that the then-unresolved-looking `sum_{n>=1} 1/(2^n - 3)` is a special case of the new theorem.

## Relation to the release

- This is a distinct fixed-base rational-offset antecedent adjacent to Borwein’s 1992 Lambert-series paper. It supports the full series with denominator `q^n + r`, not an arbitrary infinite support subseries.
- The integer-base hypothesis is essential to the theorem as stated. It does not establish the release’s rational noninteger-base claim at `3/2`, and it does not settle universal Erdős Problem #257.
- The source’s Padé denominator recurrence is not the q-WZ scalar recurrence compared in the local #1049 work. No recurrence transport, endpoint, lattice, valuation, denominator gain, Lean theorem, Comparator result, or Palomar qualification follows from the shared Lambert-series setting.

## Non-support and attribution ceiling

- The paper does **not** state Erdős Problems #249 or #257, the release’s totient-kernel rank, Lean declarations, Comparator, or Palomar.
- Its conclusion is for the full sequence of indices with an integer base and rational offset; it does not cover arbitrary sparse supports, prime supports, squarefree supports, or the release’s local geometry.
- The attribution ceiling is Borwein’s Padé/Stieltjes construction, the displayed polynomial recurrence, the approximation estimate, and Theorem 4 under its exact integer-base and rational-offset hypotheses. No novelty or priority claim is made for the release’s separate formal results.

## Redistribution disposition

The publisher record identifies a copyrighted Elsevier/Academic Press article, and the inspected author reprint itself states that all rights are reserved. Neither route provides an explicit redistribution grant for this acquisition copy. The artifact is therefore `working_tree_only`, `link_and_digest_only`, `public_candidate_inclusion: false`, with `permission_evidence_status: not_verified`; the public candidate must use the official retrieval routes rather than ship the binary.

## Direct consumers

- `docs/PRIOR_ART.md`
- `docs/primary-sources/redistribution-dispositions.json`
- `docs/THIRD_PARTY_NOTICES.md`
