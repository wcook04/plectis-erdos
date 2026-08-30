# Primary-source closure: Kakeya (1914)

## Identity and retrieval

- **Author:** S. Kakeya.
- **Title:** “On the Set of Partial Sums of an Infinite Series.”
- **Publication:** *Tokyo Sugaku-Buturigakkwai Kizi Dai 2 Ki*, volume 7, issue 14 (1913–1914), printed pages 250–251; J-STAGE records publication on 1914-05-03.
- **Persistent identifier:** DOI [10.11429/ptmps1907.7.14_250](https://doi.org/10.11429/ptmps1907.7.14_250).
- **Authoritative archive record:** <https://www.jstage.jst.go.jp/article/ptmps1907/7/14/7_14_250/_article/-char/en/>.
- **Authoritative PDF route:** <https://www.jstage.jst.go.jp/article/ptmps1907/7/14/7_14_250/_pdf/-char/ja>.
- **Acquisition digest:** the locally inspected two-page PDF at `docs/primary-sources/reciprocal-tail/kakeya-1914-partial-sums.pdf` has SHA-256 `fd07aaea155e1a726b1705137d70c3e7bf9d435dbd12dd155cced4db42400dfe` and size 162,733 bytes.
- **Reading status:** the complete two-page source was read from both the text layer and page renders. The PDF has printed pages 250–251 as PDF pages 1–2.

## Exact support

The source supports the following historical subsum-set statements.

1. **Definition and scope (printed p. 250; PDF p. 1).** Starting with an infinite series \(\sum_{n=1}^{\infty}a_n\), Kakeya considers finite or infinite series formed from some of its terms, written with selected indices, and calls the resulting objects “partial sums” of the given series.
2. **Perfectness (printed p. 251; PDF p. 2).** Kakeya states that the set of partial sums of any absolutely convergent infinite series, real or complex, is perfect.
3. **Real-series interval enclosure (printed p. 251; PDF p. 2).** For real terms, the set lies in the interval \((u,v)\), where \(u\) and \(v\) are the sums of all negative and all positive terms, respectively.
4. **Interval-filling criterion (printed p. 251; PDF p. 2).** Kakeya states that the real partial-sum set fills the interval exactly when
   \[
   |a_n| \le |a_{n+1}|+|a_{n+2}|+|a_{n+3}|+\cdots
   \]
   for every \(n\).
5. **Nowhere-density assertion and open qualification (printed p. 251; PDF p. 2).** Kakeya states that if the displayed relation does not hold for all \(n\), the set is nowhere dense. He then says that failure at only infinitely many indices seems necessary and sufficient for nowhere density, but explicitly records that he has no proof of this latter claim.

## Non-support and attribution ceiling

- The paper does **not** mention Lambert series, Mersenne denominators, Euler’s totient, Erdős Problems #249 or #257, denominator bounds, Lean declarations, Comparator, or Palomar.
- It does not provide an arithmetic proof for any release theorem. Its result is a classical topological statement about sets of partial sums; any local strict-tail, Cantor-set, or executable certificate is a separately authored/formalised bridge.
- The final “necessary and sufficient” nowhere-density sentence is explicitly conjectural in this source and must not be cited as a proved theorem.
- No novelty or priority claim is made for the release’s formal geometry or its arithmetic applications.

## Redistribution disposition

The PDF is retained only as a working-tree acquisition copy for source reading and digest verification. J-STAGE availability and the DOI establish retrieval and citation identity, not a redistribution grant. The artifact is therefore `working_tree_only`, `link_and_digest_only`, `public_candidate_inclusion: false`, with `permission_evidence_status: not_verified`; the public candidate must retrieve it from the official route rather than ship the binary.

## Direct consumers

- `docs/PRIOR_ART.md`
- `docs/primary-sources/redistribution-dispositions.json`
- `docs/THIRD_PARTY_NOTICES.md`
