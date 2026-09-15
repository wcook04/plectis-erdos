# Primary-source closure: Zudilin (2004)

## Identity and retrieval

- **Author:** Wadim Zudilin.
- **Title:** “Heine's basic transform and a permutation group for q-harmonic series.”
- **Publication:** *Acta Arithmetica* 111 (2004), no. 2, pp. 153–164. The article records receipt on 13 May 2002 and a revised form on 10 April 2003.
- **Persistent identifier:** DOI [10.4064/aa111-2-4](https://doi.org/10.4064/aa111-2-4).
- **Authoritative retrieval routes:** <https://doi.org/10.4064/aa111-2-4>; [Geodesic record](https://geodesic.mathdoc.fr/articles/10.4064/aa111-2-4/).
- **Acquisition digest:** the locally inspected 12-page publisher PDF at `docs/primary-sources/reciprocal-tail/zudilin-2004-heine-permutation-group.pdf` has SHA-256 `0948a67eda0310b1fc354f417007317898b3c7582f992260763e85a4e138700e` and size 151,336 bytes.
- **Reading status:** the complete source was read from its rendered pages on 15 September 2026. Printed pages 153–164 are PDF pages 1–12, and every page reference below is to the printed pagination.

## Exact support

1. **Problem and earlier bounds (Section 1, displays (1)–(3), pp. 153–154).** For `p = 1/q` in `Z \ {0, ±1}` the paper studies `h_p(1) = sum_{n>=1} 1/(p^n - 1)`. It records Erdős's irrationality proof for `h_2(1)` and his question for every integer `p`, the solutions of Bézivin and P. Borwein, and the Bundschuh–Väänänen bound `mu(h_p(1)) <= 2 pi^2/(pi^2 - 2) = 2.50828476...` in (3).
2. **Theorem 1 (p. 154).** `mu(h_p(1)) <= 2.46497868...`. Following the referee, the paper remarks that the estimate is uniform in `p`.
3. **Cyclotomic bookkeeping (Section 2, (4)–(5), Lemmas 1–2, pp. 154–155).** `Phi_l(p)` are the cyclotomic polynomials, `ord_{Phi_l(p)} [n]_p! = floor(n/l)` for `l >= 2`, and `D_n(p) = prod_{l<=n} Phi_l(p)` is the least common multiple of the `p^k - 1` with `k <= n`. Lemma 1, credited to Bundschuh–Väänänen (Section 2) and Van Assche (Lemma 2), gives `log|D_n(p)|/(n^2 log|p|) -> 3/pi^2`. Lemma 2, credited to the author's 2002 paper (Lemma 1), gives the limit `(3/pi^2)(psi'(u) - psi'(v))` for the cyclotomic mass over a rational demi-interval `[u, v)`.
4. **Linear forms (Section 3, (6)–(11), pp. 155–157).** Positive integers `a_0, a_1, a_2, b` with `a_1 + a_2 <= b`; the rational function `R(T)` and its gamma form (7); the residues `A_k` in (8); the series `F(a;b) = sum_{t>=0} R(q^t) = A(p) h_p(1) - B_1(p) - B_2(p)` in (9), with `A(p)` and `B_1(p)` in (10) and `B_2(p)` in (11).
5. **Lemma 3 and the Heine form, (12)–(13), p. 157.** A first denominator inclusion in `Z[p] h_p(1) + Z[p]`, and the identification (13) of `F(a;b)` with a q-gamma multiple of the basic hypergeometric series `2phi1(q^{a_1}, q^{a_2}; q^b | q, q^{a_0})`, whose lower parameter is `q^b`.
6. **Lemma 4, (14)–(17), pp. 157–159.** Under `a_1 <= a_2` and `a_1 + a_2 <= b <= a_0 + a_2`, the inclusion (15) holds with the exponent `M(a;b) = a_1(a_1 - 1)/2 + a_0 a_1 + (b - a_2)(a_2 - a_1)` of (16), and (17) gives the size estimates. The Remark on p. 159 corrects an exponent in the author's 2002 paper.
7. **The permutation group (Section 4, (20)–(22), Lemmas 5–6, pp. 159–161).** Heine's transform (1) gives the stability of (20) under the parameter map `tau`; `tau` and the exchange `sigma` of `a_1` and `a_2` generate a group of order 12. Lemma 5 states the stability of `H(c)/Pi_q(c)` under that group. Display (21) restates Lemmas 3 and 4, and (22) defines the exponents `nu_l` and `Omega(p) = prod_l Phi_l(p)^{nu_l}` in `Z[p]`.
8. **Lemma 7, display (23), p. 161.** `p^{-M(c)} D_{m(c)}(p) Omega(p)^{-1} H(c)` lies in `Z[p] h_p(1) + Z[p]`, provided `s(c) > 0`. The proof combines (21) with Lemma 5 and uses that the cyclotomic polynomials are coprime to `p` in `Z[p]`.
9. **The q-conclusion (Section 5, (24)–(26), pp. 161–162).** For directions with `alpha_1 <= alpha_2` and `alpha_1 + alpha_2 < beta <= alpha_0 + alpha_2`, the parameters are `a_j = alpha_j n + 1` and `b = beta n + 2`. Display (24) evaluates (23) at the integer `p`; (25) bounds `|A_n|` through `C_1`; `nu_l = omega(n/l)` for an explicit 1-periodic integer-valued function `omega`; and (26) defines `C_0`. The standard argument gives `mu(h_p(1)) <= C_1/C_0` when `C_0 > 0`. At `(alpha_0, alpha_1, alpha_2; beta) = (14, 12, 14; 27)` the paper prints `c = (13, 14, 12, 14, 15, 13)`, `C_1 = 545.5`, `C_0 = 221.30008816...`, the bound `2.46497868...`, and the thirteen demi-intervals on which `omega = 1`, from `[1/14, 1/12)` to `[13/14, 14/15)`.

## Relation to the #1049 notes

- The rational-base theorem of the #1049 short note and long record uses the polynomial conclusion of Lemma 7, display (23), before the integer evaluation (24), at the parameter vector `n(13, 14, 12, 14, 15, 13)`, together with the inputs of that lemma's proof. The direction, the thirteen intervals and the constants `C_1` and `C_0` are those printed on p. 162.
- The rational specialisation, the exact degree computation, the positivity of the remainder, the limit passage and the homogenisation at a rational base are carried out in the notes. They are not statements of this source.
- The short note records that the unnumbered display of `R(T)` on p. 156 prints its second denominator with length `b - a_2 - 1`, while the gamma form (7), the partial-fraction range `k <= b - 1` displayed before (8), and the binomial coefficient in (8) correspond to length `b - a_2`. Both notes use length `b - a_2`.

## Non-support and attribution ceiling

- The source works with `p = 1/q` in `Z \ {0, ±1}` throughout (p. 154) and states no result at a rational non-integer base. It does not state Erdős Problem #1049.
- The attribution ceiling is the construction, Lemmas 1–7 with their hypotheses, the printed constants and Theorem 1. The explicit rational-base region of the #1049 notes is argued in the notes, and no priority claim is attached to it.

## Redistribution disposition

No redistribution grant was verified for this acquisition copy. The artifact is `working_tree_only`, `link_and_digest_only`, `public_candidate_inclusion: false`, with `permission_evidence_status: not_verified`; the public candidate uses the official retrieval routes rather than shipping the binary.

## Direct consumers

- `docs/PRIOR_ART.md`
- `docs/primary-sources/redistribution-dispositions.json`
- `docs/THIRD_PARTY_NOTICES.md`
