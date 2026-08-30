# Primary-source closure: Van Assche (2001)

## Identity and retrieval

- **Author:** Walter Van Assche.
- **Title:** “Little q-Legendre Polynomials and Irrationality of Certain Lambert Series.”
- **Publication:** *The Ramanujan Journal* 5 (2001), pp. 295–310; the publisher record gives September 2001 as the issue date.
- **Persistent identifiers:** [arXiv:math/0101187](https://arxiv.org/abs/math/0101187); DOI [10.1023/A:1012930828917](https://doi.org/10.1023/A:1012930828917).
- **Authoritative retrieval routes:** <https://arxiv.org/abs/math/0101187>; <https://arxiv.org/pdf/math/0101187>; [publisher record](https://link.springer.com/article/10.1023/A:1012930828917).
- **Acquisition digest:** the locally inspected 15-page arXiv PDF at `docs/primary-sources/reciprocal-tail/van-assche-2001-little-q-legendre.pdf` has SHA-256 `ce878d4a92a709e77723bb398c131e5391cb8bea8c82eeeccd92e6f26fece34d` and size 166,628 bytes.
- **Reading status:** the complete source was read from its text layer and page renders. The arXiv front matter is PDF page 1; the body’s printed pages are PDF pages 1–15.

## Exact support

1. **Lambert values (Introduction, equations (1)–(2), PDF pp. 1–2).** For `p = 1/q > 1`, the paper defines `h_p(1) = sum_{k>=1} 1/(p^k - 1) = sum_{k>=1} q^k/(1 - q^k)` and `ln_p(2) = sum_{k>=1} (-1)^k/(p^k - 1) = sum_{k>=1} (-q)^k/(1 - q^k)`. It places these values against the earlier Erdős, Borwein, Bundschuh–Väänänen, and Matala-aho–Väänänen results.
2. **Little q-Legendre kernel (Section 2, equations (3)–(16), PDF pp. 3–4).** The source defines `P_n(x | q)` as a basic hypergeometric polynomial, records orthogonality on `{q^k : k >= 0}`, gives its `p`-binomial expansion, and gives a Rodrigues formula and the `(qx;q)_k`-basis expansion.
3. **Stieltjes/Padé approximation route (Section 3, equations (17)–(22), PDF pp. 5–6).** The paper defines the Stieltjes function for the discrete measure on `{q^k}`, identifies `f(p^n)` with `h_p(1)` up to a finite rational prefix, and applies the orthogonal-polynomial identity to construct rational approximants.
4. **Integer approximants and error identity (Section 3, equations (23)–(35), PDF pp. 6–9).** Equations (23)–(26) and (31)–(33) give the evaluated polynomial, cyclotomic denominator factor `d_n(p)`, integer sequences `a_n,b_n`, and the error sum. Equation (34) rewrites the error as a positive square-norm sum, and (35) bounds it.
5. **q-harmonic theorem (Theorem 1, PDF p. 10; publication p. 304).** The source states that for every integer `p > 1`, the constructed `a_n,b_n` give `h_p(1)` irrational and records the bound `r(h_p(1)) <= 2 pi^2/(pi^2 - 2) = 2.50828...`.
6. **q-logarithm theorem (Section 4, equations (38)–(44), Theorem 2, PDF pp. 11–13; publication pp. 305–307).** The analogous evaluation at `-p^n` gives integer approximants for `ln_p(2)`. Theorem 2 states irrationality for every integer `p > 1` and records `r(ln_p(2)) <= 2 pi^2/(pi^2 - 4) = 3.36295...`.
7. **Rational-parameter extension (Section 5, equations (45)–(46), Theorem 3, PDF pp. 13–14; publication pp. 307–308).** For rational `c = a/b` with `c p^k != 1`, the paper extends the construction to `L = sum_{k>=1} 1/(c p^k - 1)`, proves irrationality, and records the bound `r(L) <= 3 pi^2/(pi^2 - 3) = 4.310119...`.

## Relation to the #1049 comparison

- The source’s equation (23) explicitly says that `P_n(p^n | q)` is nearly the `b_n` from Amdeberhan–Zeilberger (1998, p. 277), whose `b_n` uses the neighbouring evaluation `P_n(p^(n+1) | q)`. It also notes that Borwein’s construction uses `P_(n-1)(c p^n | q)`. These are the exact source-level moving-diagonal anchors for the local recurrence comparison.
- The source supplies a Padé/little-q-Legendre construction and its own irrationality theorems. The local residual at `n = 0` for the Van Assche diagonal, and the resulting non-transfer statement for the Amdeberhan–Zeilberger scalar recurrence, are separately computed and Lean-checked; they are not claims stated by Van Assche.
- The source does not establish the release’s rational noninteger-base claim at `3/2`, the Bundschuh–Väänänen height route at `7/2`, or any local endpoint or valuation conclusion.

## Non-support and attribution ceiling

- The paper does **not** state Erdős Problems #249 or #257, the release’s totient-kernel rank, Lean declarations, Comparator, or Palomar.
- The shared little-q-Legendre kernel and neighbouring evaluations do not authorize transporting a recurrence, endpoint, lattice, valuation, denominator, or irrationality conclusion to a different diagonal.
- The attribution ceiling is Van Assche’s Padé construction, the stated little-q-Legendre identities, and Theorems 1–3 with their hypotheses and reported irrationality-measure bounds. No novelty or priority claim is made for the local residual or its formal proof.

## Redistribution disposition

The publisher record identifies the article as subscription content, while the arXiv preprint is available for retrieval. Neither route provides an explicit redistribution grant for this acquisition copy. The artifact is `working_tree_only`, `link_and_digest_only`, `public_candidate_inclusion: false`, with `permission_evidence_status: not_verified`; the public candidate must use the official retrieval routes rather than ship the binary.

## Direct consumers

- `docs/PRIOR_ART.md`
- `docs/primary-sources/redistribution-dispositions.json`
- `docs/THIRD_PARTY_NOTICES.md`
