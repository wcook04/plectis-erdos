# Primary-source closure: Amdeberhan–Zeilberger (1998)

## Identity and retrieval

- **Authors:** Tewodros Amdeberhan and Doron Zeilberger.
- **Title:** “q-Apéry Irrationality Proofs by q-WZ Pairs.”
- **Publication:** *Advances in Applied Mathematics* 20 (1998), no. 2, pp. 275–283; the inspected preprint is arXiv:math/9804122v1, dated 1998-04-24.
- **Persistent identifiers:** [arXiv:math/9804122](https://arxiv.org/abs/math/9804122); DOI [10.1006/aama.1997.0565](https://doi.org/10.1006/aama.1997.0565).
- **Authoritative preprint PDF route:** <https://arxiv.org/pdf/math/9804122>.
- **Acquisition digest:** the locally inspected seven-page PDF at `docs/primary-sources/reciprocal-tail/amdeberhan-zeilberger-1998-q-apery.pdf` has SHA-256 `0aa934e636ccb32d2abe5ede3209849f1f673e2fbd6217d0f23d6107c3e60a28` and size 106,398 bytes.
- **Reading status:** the complete seven-page source was read from its text layer and page renders. Printed page numbers 1–7 match PDF pages 1–7.

## Exact support

1. **Target q-series (Introduction, printed p. 1; PDF p. 1).** The paper defines
   \[
   h_q(1)=\sum_{k\ge1}\frac1{q^k-1}\quad(|q|>1),
   \qquad
   \mathrm{Ln}_q(2)=\sum_{n\ge1}\frac{(-1)^n}{q^n-1}\quad(|q|\ne0,1).
   \]
   It identifies these as q-analogues of the harmonic series and \(\ln(2)\), and places its method against the earlier Erdős and Borwein results.
2. **q-WZ setup and explicit scalar operator (Sections 1.1–1.5, printed pp. 2–3; PDF pp. 2–3).** The source defines q-WZ pairs and the associated q-WZ 1-form, then gives explicit potential and mollifier functions, sequences \(a(n),b(n)\), and an order-two operator
   \[
   L=y_2(n)N^2+y_1(n)N+y_0(n).
   \]
   Its displayed telescoping identities show that both constructed sequences solve \(Lu(n)=0\). The coefficient formulas \(y_0,y_1,y_2\) are printed in Sections 1.5 and 2.5.
3. **q-harmonic approximation and theorem (Sections 1.6–1.7, printed pp. 3–4; PDF pp. 3–4).** Equations (1.6.1)–(1.6.4) give the growth and rational approximation estimates; Lemmas 1–2 clear denominators and state the error exponent. Theorem 1 on printed p. 4 states: if \(|q|>1\) is an integer, then \(h_q(1)\) is irrational with irrationality measure 4.80.
4. **Alternating q-analogue (Sections 2.1–2.7, printed pp. 5–6; PDF pp. 5–6).** The paper supplies the analogous explicit q-WZ form, operator, telescoping identities, approximation estimates, and denominator-clearing Lemmas 3–4 for \(\mathrm{Ln}_q(2)\). Theorem 2 on printed p. 6 states: if \(|q|\ne0,1\) is an integer, then \(\mathrm{Ln}_q(2)\) is irrational with irrationality measure 4.80.
5. **Computer-assisted construction disclosure (printed pp. 2 and 5; PDF pp. 2 and 5).** The authors state that the claims in Sections 1.1–1.5 and 2.1–2.5 were found using the Maple package qEKHAD and that a script substantiating them is available on the paper’s web pages. The printed telescoping identities and subsequent estimates are the source’s mathematical record; this disclosure is not a Lean verification.

## Relation to the #1049 comparison

- The source’s operator is the external q-Apéry recurrence whose coefficient transport is tested by the local #1049 diagonal comparison.
- The local residual at \(n=0\) for Van Assche’s different moving diagonal is **not** a theorem stated in this paper. It is a separately computed and Lean-checked non-transfer statement; the source supplies only the original operator and its own sequences.
- The source proves integer-\(q\) irrationality statements. It does not itself establish the rational noninteger-base claim at \(3/2\), nor does it supply the release’s separate Bundschuh–Väänänen height route at \(7/2\).

## Non-support and attribution ceiling

- The paper does **not** state Erdős Problems #249 or #257, the totient-kernel rank, the release’s Mersenne subseries, Lean declarations, Comparator, or Palomar.
- No recurrence, endpoint, lattice, valuation, denominator, or irrationality conclusion for Van Assche’s diagonal may be transferred merely because the bivariate kernel resembles the source’s construction; the local release records the contrary finite residual.
- The attribution ceiling is the authors’ q-WZ/Apéry construction and the two stated integer-parameter irrationality theorems with their reported irrationality measure. No novelty or priority claim is made for the local residual or its formal proof.

## Redistribution disposition

The arXiv preprint and author-hosted availability establish retrieval and citation identity, not an explicit redistribution grant for this acquisition copy. The artifact is therefore `working_tree_only`, `link_and_digest_only`, `public_candidate_inclusion: false`, with `permission_evidence_status: not_verified`; the public candidate must use the official retrieval route rather than ship the binary.

## Direct consumers

- `docs/PRIOR_ART.md`
- `docs/primary-sources/redistribution-dispositions.json`
- `docs/THIRD_PARTY_NOTICES.md`
