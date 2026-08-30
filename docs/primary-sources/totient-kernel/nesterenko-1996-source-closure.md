# Nesterenko (1996) source closure: the divisor-sum transcendence rung

This source-evidence record binds Yu. V. Nesterenko's 1996 paper to the
release's cited-only divisor-sum ladder rung.  It records the exact modular
form statement from which the release's
`sum sigma(n)/2^n` consequence follows by an elementary affine rewrite; it
does not turn the paper's analytic proof into a Lean dependency.

## Stable identity and read-through artifact

- **Author and title:** Yu. V. Nesterenko, *Modular functions and
  transcendence questions*.
- **Publication identity:** *Sbornik: Mathematics* **187**, no. 9 (1996),
  1319--1348; translated from *Matematicheskii Sbornik* **187**, no. 9,
  65--96.  DOI:
  [10.1070/SM1996v187n09ABEH000158](https://doi.org/10.1070/SM1996v187n09ABEH000158).
- **Authoritative routes:** the [Math-Net article record](https://www.mathnet.ru/eng/sm158),
  its [English full-text PDF](https://www.mathnet.ru/php/getFT.phtml?jrnid=sm&option_lang=eng&paperid=158&what=fullteng),
  and the DOI above.  Math-Net identifies the author, journal, volume,
  issue, pages, translation status, and DOI on the article record.
- **Read-through translation:** the 30-page English PDF was retrieved from
  the Math-Net full-text route and read directly.  SHA-256 is
  `71c7a1f91a66e28d32edc8107a0c1fbc1c36d260575d86e3d50539f30ad20507`;
  the file is 1,244,818 bytes and contains 30 PDF pages.  The PDF header
  states `©1996 RAS(DoM) and LMS`; no explicit redistribution grant was
  verified.  The binary is not retained under `docs/primary-sources/` in
  this pass, so this record is link-and-digest-only evidence rather than a
  redistribution permission claim.

## Read state and exact locators

The complete text layer was extracted and read for the paper's definitions,
theorems, proof route, historical attribution, and limitations.  The opening
statement pages were also visually checked against the PDF scan because the
text layer has occasional OCR and symbol-conversion errors.

- **Ramanujan functions and coefficient identity (printed p. 1319, PDF p. 1):**
  the paper defines
  \[
  P(z)=1-24\sum_{n\ge1}\sigma_1(n)z^n,\qquad
  Q(z)=1+240\sum_{n\ge1}\sigma_3(n)z^n,\qquad
  R(z)=1-504\sum_{n\ge1}\sigma_5(n)z^n,
  \]
  with `sigma_k(n) = sum_{d|n} d^k`, and records Ramanujan's differential
  equations for these functions.  This is the source-level bridge to the
  divisor-sum series; the release's notation `L(Id)` is its own notation.
- **Main algebraic-independence theorem (printed p. 1320, PDF p. 2,
  Theorem 1):** for every complex `q` with `0 < |q| < 1`, at least three of
  `q`, `P(q)`, `Q(q)`, and `R(q)` are algebraically independent over `Q`.
- **Algebraic-point specialization (printed p. 1320, PDF p. 2,
  Corollary 2):** if `q` is algebraic and `0 < |q| < 1`, then each of the
  triples `(P(q), Q(q), R(q))` and `(J(q), theta J(q), theta^2 J(q))` is
  algebraically independent over `Q`; in particular, every displayed value
  in those triples is transcendental.
- **Release consequence (elementary rewrite, not a separately named source
  theorem):** take `q=1/2` in Corollary 2.  Since
  `P(1/2) = 1 - 24 * sum_{n>=1} sigma_1(n)/2^n`, the value
  `sum_{n>=1} sigma(n)/2^n` is transcendental.  The affine rearrangement is
  elementary; the transcendence input is Nesterenko's Corollary 2.
- **Proof route (printed pp. 1322--1329, PDF pp. 4--10):** Theorem 3 gives
  the multiplicity bound for nonzero polynomial relations among `P`, `Q`,
  and `R`; Section 2 reduces Theorems 1 and 2 to that bound through
  Lemmas 2.1--2.5.  The proof uses integer-coefficient auxiliary
  polynomials, Siegel's lemma, differential-operator identities, and a
  Philippon algebraic-independence criterion.  This is the paper's hard
  analytic/algebraic step and is not claimed as formalized in the release.
- **Historical qualifications (printed pp. 1321--1322, PDF pp. 3--4):** the
  paper distinguishes the prior work of Mahler, Chudnovskii, and Bertrand
  from Nesterenko's theorem and records that the modular-function and
  algebraic-independence results build on those antecedents.  The citation
  therefore credits Nesterenko for the theorem used here, while not
  attributing the underlying Ramanujan definitions or all historical
  consequences to him.

## Attribution and claim ceiling

### Supports

- Attribution to Nesterenko of algebraic independence of the Ramanujan
  values at algebraic `q` in Corollary 2, hence transcendence of
  `P(1/2)` and of the affine divisor-sum value
  `sum sigma_1(n)/2^n`.
- Attribution to Nesterenko of the general Theorem 1 and the auxiliary
  zero-order estimate and proof architecture on printed pp. 1320--1329.
- The publication identity, official Math-Net retrieval route, exact
  read-through digest, and the distinction between the source theorem and
  the release's elementary specialization.

### Does not support

- A proof of any release Lean declaration, Comparator verdict, Palomar
  assurance, replay receipt, or formal kernel result.  The release cites the
  transcendence input; it does not claim to formalize Nesterenko's proof.
- A theorem about the Möbius row, the Euler-totient coefficient row, the
  finite totient-kernel rank or basis, or Erdős Problem #249.  The paper's
  `sigma_1` coefficient series is a different ladder component.
- A new priority or novelty claim for the divisor-sum identity or its
  affine rewrite.  The definitions are presented as Ramanujan's, and the
  local release makes no priority claim for the cited theorem or its use.
- Any conclusion about universal Erdős #257, Mersenne-support subseries,
  geometry, reproducibility, or release acceptance.

## Negative checks

The full 30-page text was checked for the release's Lean declaration names,
Comparator family names, Palomar verdicts, `L(Id)` notation, Euler-totient
coefficient claims, Problem #249, and Mersenne-support assertions.  None is
present.  The directly relevant source statement is the algebraic-point
transcendence of `P(q)` in Corollary 2, with the divisor-sum consequence
obtained by the explicit affine rewrite above.

## Redistribution disposition

Math-Net provides public retrieval and the article record identifies the
translation and copyright holders, but the PDF itself is marked
copyright-protected and no explicit redistribution grant was verified.  No
binary is therefore added to the public source inventory in this pass.  The
closure is link-and-digest-only evidence and does not assert permission to
redistribute the translation.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the cited-only attribution and
  claim-ceiling row for `L(Id)`.
- [`docs/claims.json`](../../claims.json), whose `sigma_transcendence` record
  identifies the result as cited-only and not formalized here.

The allowed outward statement is therefore: Nesterenko's Corollary 2 makes
the Ramanujan value `P(1/2)` transcendental, and its displayed definition
implies the transcendence of `sum sigma(n)/2^n`; this is an external analytic
input for the release, not a Lean-checked theorem or a claim about the
totient-kernel rows.
