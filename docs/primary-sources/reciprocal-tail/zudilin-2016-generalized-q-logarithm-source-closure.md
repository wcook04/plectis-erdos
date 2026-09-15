# Primary-source closure: Zudilin (2016)

## Identity and retrieval

- **Author:** Wadim Zudilin.
- **Title:** “On the irrationality of generalized q-logarithm.”
- **Publication:** *Research in Number Theory* 2 (2016), Article 15; arXiv version 2 is dated 24 January 2016.
- **Persistent identifiers:** [arXiv:1601.02688](https://arxiv.org/abs/1601.02688); DOI [10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x).
- **Authoritative retrieval routes:** <https://arxiv.org/abs/1601.02688>; <https://arxiv.org/pdf/1601.02688v2>; [publisher record](https://link.springer.com/article/10.1007/s40993-016-0042-x).
- **Acquisition digest:** the locally inspected 12-page arXiv v2 PDF at `docs/primary-sources/reciprocal-tail/zudilin-2016-generalized-q-logarithm.pdf` has SHA-256 `53947bb2fc82e853c12ccfdb293a526229f6fe2ac99d9c991d2170ae6e1266e3` and size 198,114 bytes.
- **Reading status:** the complete arXiv v2 source was read from its rendered pages on 15 September 2026. Its printed pages 1–12 are PDF pages 1–12, and every page reference below is to that version.

## Exact support

1. **Historical notes (Section 1, pp. 1–3).** The q-harmonic series; Erdős's 1948 irrationality proof for `q = 1/p` with integer `p > 1`; the analytic methods of Bézivin and P. Borwein and the later Padé-approximation literature; and the generalized q-logarithm `l_p(x, z) = x sum_{n>=1} z^n/(p^n - x)` of (3), which is the q-harmonic series at `x = z = 1`.
2. **Theorem 1 (p. 3).** For integer `p` with `|p| > 1` and nonzero rational `x, z` with `x` outside `{p, p^2, p^3, ...}` and `|z| < |p|`, the value `l_p(x, z)` is irrational.
3. **Theorem 2 and the rational-base remark (Section 2, pp. 3–4).** The identity (5) for the q-hypergeometric function (4). The paragraph beginning “Finally, we remark” on p. 4, which precedes the q-notation conventions closing Section 2, remarks that the results can be given for non-integer `p = r/s` with `|p| > 1` under an assumption `log|r| > c log|s|` for some computable constant `c > 0`, and that irrationality measures showing the values are not Liouville numbers can be produced. These quantitative questions are not pursued there beyond a comment at the end of Section 4.
4. **Padé approximations (Section 3, p. 5).** The approximations `I_n(q, x, z)` of the joint work with Bundschuh, the coefficients `A_n`, `B_n`, `C_n`, the denominator `D_n`, and the linear form `v_n(mu)` with coefficients in `Z[p, x, z]`.
5. **Hankel determinants (Section 4, (6)–(8), Lemma 1, pp. 6–8).** `V_n(mu) = det_{0<=j,l<=n-1}(v_{j+l}(mu))`; the normalized moments `v_n^*` of (6); the operator `D_l = (N; q)_l` of (7) built from the backward shift `N`; Lemma 1 on the starting order of `D_l w_n`; the row transformation giving `ord_q V_n^* >= n(n-1)(2n-1)/6` on p. 7; the estimate (8); and the proof of Theorem 1 through Kronecker's criterion on pp. 7–8.
6. **Hypergeometric identity and related questions (Sections 5–6, pp. 8–10).** The proof of Theorem 2 and further generalizations of `l_p(x, z)`.

## Relation to the #1049 notes

- The #1049 notes take the normalized Hankel determinant `V_N^*` of Section 4 at `x = z = 1` and cite the inequality `ord_q V_N^* >= N(N-1)(2N-1)/6` of p. 7 as the antecedent. The equality and the leading coefficient `(N!)^2 (N+1)!/2^N` are argued in the notes; they are not statements of this source.
- The notes cite that paragraph of Section 2, on p. 4, as the published rational-base remark with an unspecified computable constant. The explicit constant `c = mu = 2.4649786835...` used in the notes comes from the 2004 paper together with the notes' own rational specialisation.

## Non-support and attribution ceiling

- The source computes no value of `c` in its rational-base remark and states no explicit rational-base region. It does not state Erdős Problem #1049.
- The attribution ceiling is Theorems 1 and 2 with their hypotheses, the Padé and Hankel constructions, Lemma 1 with the q-order inequality, and the rational-base remark as stated.

## Redistribution disposition

The arXiv preprint and the publisher record are reachable through the official routes, and no explicit redistribution grant was verified for this acquisition copy. The artifact is `working_tree_only`, `link_and_digest_only`, `public_candidate_inclusion: false`, with `permission_evidence_status: not_verified`; the public candidate uses the official retrieval routes rather than shipping the binary.

## Direct consumers

- `docs/PRIOR_ART.md`
- `docs/primary-sources/redistribution-dispositions.json`
- `docs/THIRD_PARTY_NOTICES.md`
