# Chowla (1947) source closure: Lambert-type series and the sine-twisted case

This source-evidence record binds S. Chowla's 1947 paper to the historical
Lambert-series entry in the release's prior-art map.  It separates Chowla's
conjecture about the ordinary Lambert series from the specific irrationality
theorem he proves for the sine-twisted series; it is attribution and
claim-boundary evidence, not proof authority for this release.

## Stable identity and read-through artifact

- **Author and title:** S. Chowla, *On Series of the Lambert Type which
  assume Irrational Values for Rational Values of the Argument*.
- **Publication identity:** *Proceedings of the National Institute of
  Sciences of India* **13**, no. 4 (1947), 171--173.  The current Indian
  National Science Academy archive labels the journal *Proceedings of the
  Indian National Science Academy*, volume 13, issue 4, and exposes the
  historical scan as article 05.
- **Authoritative routes:** [INSA 1947 volume archive](https://insa.nic.in/UI/Archivesection.aspx?JID=MA%3D%3D&JYrs=MTk0Nw%3D%3D) and the
  [article PDF](https://insa.nic.in/writereaddata/UpLoadedFiles/PINSA/Vol13_1947_4_Art05.pdf).
- **Read-through scan:** the three-page PDF was retrieved from the INSA
  article route and read directly.  SHA-256 is
  `6697e1d19adbe7066252d28886bc3ad7feca751fec1c265979e76d3cefdd3208`;
  the file is 40,532 bytes and contains three PDF pages.  The scan was not
  retained under `docs/primary-sources/`: the archive's site is marked
  copyright-protected and no explicit redistribution grant was verified.
  The digest and official route are retained here for source identity and
  reproducibility, not as permission to redistribute the scan.

## Read state and exact locators

The PDF has no usable text layer.  All three page images were visually read;
the printed page numbers are 171--173.  The following locators preserve the
source's actual support and its negative boundary.

- **Definitions and conjectural boundary (printed p. 171):** Chowla defines
  \[
  f(x)=\sum_{n\ge1}\frac{x^n}{1-x^n},\qquad
  g(x)=\sum_{n\ge1}\frac{x^n}{1-x^n}\sin\frac{n\pi}{2},
  \]
  for `|x|<1`.  He says that it is not unlikely that both are irrational
  for nonzero rational `x`, explicitly says that he is unable to prove
  anything about `f(x)`, and then states that he can prove `g(1/t)` is
  irrational for a positive integer `t >= 5`.
- **Sum-of-two-squares identity (printed p. 171, Lemma 1):** with `r(n)` the
  number of representations of `n` as a sum of two squares, the paper states
  `1 + 4 g(x) = sum_{n>=0} r(n) x^n`.
- **Long zero blocks (printed pp. 171--172, Lemma 2 and proof):** for every
  positive `epsilon` and sufficiently large positive `m`, Chowla constructs
  an integer `x` with `r(x+t)=0` for `1 <= t <= m` and
  `m > (1/2 - epsilon) log(x)/log log(x)`.  The proof chooses consecutive
  primes congruent to `3 (mod 4)` and uses the simultaneous congruences
  `x+t ≡ q_t (mod q_t^2)`; the resulting exact prime valuations prevent the
  relevant integers from being sums of two squares.
- **Coefficient bound (printed p. 172, Lemma 3):** for every positive
  `epsilon` and all sufficiently large `n`, the paper uses
  `r(n) < 2(1+epsilon) log(n)/log log(n)`.
- **Digit-isolation conclusion (printed pp. 172--173):** Chowla writes
  `S = sum_{n>=1} r(n)/t^n` in base `t`, splits it at the constructed zero
  block, and bounds the post-block tail using Lemma 3.  For integer `t >= 5`,
  the zero block is long enough that the intervening base-`t` digits cannot
  be altered by the later tail.  Since there are infinitely many nonzero
  digits, `S` is irrational, and Lemma 1 transfers this to `g(1/t)`.

## Attribution and claim ceiling

### Supports

- Attribution to Chowla of the historical conjecture that the ordinary
  Lambert series `f(x)` and the sine-twisted series `g(x)` should be
  irrational at nonzero rational arguments, printed p. 171.
- Attribution to Chowla of the proved result that `g(1/t)` is irrational for
  positive integers `t >= 5`, with the proof's sum-of-two-squares gap and
  base-`t` digit argument on printed pp. 171--173.
- Attribution to Chowla of the identity connecting `g` to the representation
  function `r(n)`, Lemma 1 on printed p. 171, and of the two quantitative
  lemmas used in the proof.

### Does not support

- Irrationality of the ordinary Lambert series `f(1/t)`; the author expressly
  says on printed p. 171 that he cannot prove anything about `f(x)`.  The
  full-support divisor-weighted result is therefore correctly attributed to
  Erdős (1948), not silently back-projected to Chowla.
- Irrationality of `g(x)` for arbitrary rational `x`, of either series at all
  rational arguments, or of arbitrary support subseries.
- Any universal solution of Erdős #257, the release's #249 result, the
  Mersenne-support Comparator families, Lean declarations, Palomar assurance,
  replay receipts, geometry refinements, novelty, priority, significance,
  acceptance, or peer review.

## Negative checks

All three printed pages were checked for the release's Lean declaration names,
Comparator family names, Palomar verdicts, totient-kernel rank/basis claims,
and arbitrary-support Mersenne assertions.  None occurs.  The directly
relevant ordinary Lambert statement is explicitly left unproved by Chowla;
the proved statement is the sine-twisted `g(1/t)` result under the stated
integer-base restriction.

## Redistribution disposition

The INSA archive supplies public retrieval and identifies the historical
article, but its page carries a copyright notice and no explicit reuse or
redistribution grant was verified for this scan.  No binary is therefore
added to the public source inventory.  This closure is a link-and-digest-only
source record; it does not assert permission to redistribute the PDF.

## Direct consumers

- [`docs/PRIOR_ART.md`](../../PRIOR_ART.md), the historical Lambert-series
  attribution map and the explicit Chowla/Erdős claim ceiling.
- The source-disposition policy and notices, if a later release pass elects
  to retain a local copy; the present pass retains no binary requiring a
  manifest entry.

The allowed outward statement is therefore: Chowla conjectured irrationality
for the ordinary and sine-twisted Lambert series at nonzero rational
arguments, but his 1947 paper proves only the sine-twisted `g(1/t)` case for
integer `t >= 5`; it expressly does not prove the ordinary `f(x)` case.
