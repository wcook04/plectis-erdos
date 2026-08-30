# Primary-source closure: Bundschuh–Väänänen (1994)

## Identity and retrieval

- **Authors:** Peter Bundschuh and Keijo Väänänen.
- **Title:** “Arithmetical investigations of a certain infinite product.”
- **Publication:** *Compositio Mathematica* 91 (1994), no. 2, pp. 175–199; received 1992-10-06 and accepted in final form 1993-04-05.
- **Persistent archive record:** [Numdam CM_1994__91_2_175_0](https://numdam.org/item/CM_1994__91_2_175_0/).
- **Authoritative PDF route:** <https://numdam.org/item/CM_1994__91_2_175_0.pdf>.
- **Acquisition digest:** the locally inspected 26-page PDF at `docs/primary-sources/totient-kernel/bundschuh-vaanenen-1994-infinite-product.pdf` has SHA-256 `e4937a5bbf141c01dc60c6bdb91e0f8a8ad399d69e8e3156b4b27881631913cc` and size 1,274,780 bytes.
- **Reading status:** the complete source was read from its text layer and the rendered pages. The Numdam front matter is PDF page 1; printed pp. 175–199 are PDF pp. 2–26.

## Exact support

1. **The infinite product and its series (printed pp. 175–176; PDF pp. 2–3).** For an algebraic number field \(K\), a place \(v\), and an element \(q\) with \(|q|_v>1\) and \(|q|_w\ne1\) at every other infinite place, the paper defines
   \[
   E_q(z)=\prod_{j\ge1}(1+zq^{-j})
   \]
   and records its Taylor expansion
   \[
   E_q(z)=\sum_{n\ge0}z^n\prod_{\nu=1}^n(q^\nu-1)^{-1}.
   \]
2. **Qualitative linear-independence theorem (Theorem 1, printed p. 176; PDF p. 3).** With \(\lambda=(d\log h(q))/(d_v\log|q|_v)\), \(\alpha\ne-q^j\) for every positive integer \(j\), and \(k\ge3\), the dimension over \(K\) of the span of \(E_q(\alpha),E'_q(\alpha),\ldots,E_q^{(k-1)}(\alpha)\) is at least
   \[
   \frac{k(k-1)}{\lambda\bigl(k+6\pi^{-2}(k-1)\bigr)}.
   \]
   In the special case \(K=\mathbb Q\), the archimedean place, integral \(q\notin\{0,\pm1\}\), and \(\alpha=-1\), the paper gives the improved bound \(k(k+1)/(k+1+6\pi^{-2}(k-1))\); it also records a rational-\(\alpha\) variant.
3. **Lambert-type logarithmic derivative (printed p. 177; PDF p. 4).** Logarithmic differentiation gives
   \[
   L_q(z):=E'_q(z)/E_q(z)=\sum_{j\ge1}(q^j+z)^{-1},
   \]
   and the paper states that linear independence of \(E_q(\alpha)\) and \(E'_q(\alpha)\) over \(\mathbb Q\) is equivalent to irrationality of \(L_q(\alpha)\). It identifies this equivalence with the earlier result of Borwein.
4. **Quantitative theorem (Theorem 2, printed p. 177; PDF p. 4; proof printed pp. 189–193 / PDF pp. 16–19).** Under the stated hypotheses and \(\lambda<3/(2+3\pi^{-2})\), the paper gives an effectively computable lower bound for nonzero linear forms \(a_0E_q(\alpha)+a_1E'_q(\alpha)\), with the improved \(\alpha=-1\) threshold \(\lambda<(1/2+\pi^{-2})^{-1}\). The bound is an irrationality-measure estimate, not a formalized theorem in this release.
5. **The #1049 cited route at \(q=7/2\) (Theorem 2, printed p. 177; PDF p. 4).** For \(K=\mathbb Q\), \(q=7/2\), and \(\alpha=-1\), the absolute-height parameter is \(\lambda=\log 7/\log(7/2)\). The source’s improved threshold is equivalent to
   \[
   \frac{\log 2}{\log 7}<\frac12-\frac1{\pi^2},
   \]
   the elementary inequality checked by the release. This is the exact literature bridge behind the release’s cited irrationality route at base \(7/2\); the local proof checks the numerical hypothesis only.

## Proof route and ceiling

- Section 1, printed pp. 179–181 (PDF pp. 5–7), constructs small linear forms using complex or Schnirelman integrals; Lemma 1 gives their asymptotic size.
- Section 2, printed pp. 182–188 (PDF pp. 8–14), clears denominators, controls polynomial degrees and valuations, and obtains Lemmas 2–3. Lemma 4 on printed p. 188 (PDF p. 14) is the Nesterenko-style dimension criterion used for Theorem 1.
- Section 3, printed pp. 189–193 (PDF pp. 16–19), proves the lower bound for two-term linear forms and hence Theorem 2.
- Section 4, printed pp. 193–198 (PDF pp. 20–25), constructs additional linear forms and completes the proof of Theorem 1 on printed pp. 197–198 (PDF pp. 24–25).
- The source is the authority for this analytic theorem and its stated hypotheses. No priority or novelty claim is made for the release’s elementary height inequality or for its separately formalized Lean statement.

## Non-support

- The paper does **not** state Erdős Problem #249 or #257, the coefficient-weighted totient constant, the release’s Lean declarations, Comparator, Palomar, or the release’s finite-rank claims.
- Its \(E_q\)/\(L_q\) notation is not itself the release’s notation. Any identification with a local Lambert row is a separately checked bridge and must preserve the source’s hypotheses.
- The proof uses external analytic machinery (integral constructions, valuation estimates, and a Nesterenko-style criterion); none of that proof is formalized by the local numerical certificate.

## Redistribution disposition

The Numdam PDF carries the notice “© 1994 Kluwer Academic Publishers” and “tous droits réservés,” and the archive conditions warn against commercial or systematic use. Archive availability and a precise digest establish retrieval and citation identity, not permission to redistribute. The artifact is therefore `working_tree_only`, `link_and_digest_only`, `public_candidate_inclusion: false`, with `permission_evidence_status: not_verified`; the public candidate must use the official retrieval route rather than ship the binary.

## Direct consumers

- `docs/PRIOR_ART.md`
- `docs/COMPARATOR_1049_NUMERICAL_HEIGHT.md`
- `docs/primary-sources/redistribution-dispositions.json`
- `docs/THIRD_PARTY_NOTICES.md`
