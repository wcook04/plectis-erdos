<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Factorial derivative interpolation: proof and contribution review

Theorem `capacity:thm:jets` in the existing synthesis manuscript proves
`dim_H J_(d,c) = min(c,d)` and the exact interior threshold `c > d` for
factorial generating functions with nonnegative integer coefficients at most
`n^c` eventually and divisible eventually by every fixed integer. In the
critical case `c=d` the image is full-dimensional, null and meagre.
Theorem `capacity:thm:rational-jets` proves the matching arithmetic threshold:
nonpolynomial members with rational vectors of these derivatives exist exactly
when `c>d`. Its obstruction holds even for signed integer coefficients
of size `O(n^d)` under the same eventual divisibilities.

Starting public revision: `50a1dcfe9ffd3ad8d142d9a35ab2540ffb39ae29`.
This is a revision of the existing capacity paper, not a new paper assembled
around a misunderstanding of an original problem. Its ordinary proof was
developed in the operator-directed synthesis investigation on 20 September
2026. No independent referee or historical-priority verdict is recorded.

## Why this route was selected

The corpus-wide question was whether comparing the existing constructions
could yield a stronger theorem, rather than a new organizational surface.
Three materially different attacks were considered. The scalar dimension
problem offered a classical restricted-digit calculation, useful but limited.
The returned Gaussian-Hankel argument offered an analytic advance at the
existing #1049 owner; it was not adopted as a theorem of this synthesis or
silently treated as verified. Simultaneous interpolation offered a new
obligation: construct several independent weighted sums of one sequence.

The useful transfer was between factorial carries (#68) and congruence
feedback (#251). Counting independent coefficients alone does not prove
surjectivity or dimension: their images can cancel. Multiplication by
`(z-1)^k` produces a triangular derivative map, while an integer polynomial
annihilating the first `d-1` tail terms supplies the exact obstruction.
The decisive test was whether these constructions met at the same exponent;
both give `c=d`. A final proof pass replaced the annihilator argument with
a simpler, stronger counting proof: eventual evenness alone forces nullity
at `c=d`. The annihilator remains an exact checked exploratory calculation.
Its complementary-tail form subsequently supplied the rational-derivative
rigidity theorem: division by `(z-1)^d` turns the critical polynomial
growth bound into bounded integer coefficients and preserves eventual
divisibility. Those coefficients must vanish. For dimension, dividing
by `z^n` at the first differing
index changes growing binomial coefficients into coefficients depending on
the distance to that index. This gives a uniform separation estimate.

No premise from #243, #249, #257, #269, #1041 or #1049 is needed in the final
theorem. Their comparison helped select the question, but counting eight
inputs is not evidence of eight mathematical dependencies. No Erdős endpoint
is asserted or promoted. In particular, factorial denominators here are
not the denominators `n!-1` of #68.

## Proof audit

- **Arithmetic obstruction:** eventual evenness gives at most
  `(3/4) n^c` digit choices at every sufficiently late index. Prefix count
  is at most `C (3/4)^N (N!)^c`; the derivative-tail radius is polynomial
  in `N` divided by `(N+1)!`. For `c<=d` the total covering volume tends
  to zero. Compactness and a countable union over prefixes give meagreness.
- **Interior:** prove the signed statement for every allowance constant and
  every initial cutoff. Induct with `A+(z-1)B`. Choose `B` first, then put
  `A` sufficiently far out that all its higher derivatives are uniformly
  smaller than the available cube. This avoids assuming a continuous scalar
  digit selector. A fixed slowly divisible baseline restores positivity.
- **Dimension upper bound:** prefix count has logarithm
  `c log(N!)+O(N)` and derivative tails have radius `polynomial(N)/(N+1)!`.
  Finite exceptions are handled by a countable union, not ignored.
- **Dimension lower bound:** independent digits in the `k`th channel have
  exponent `min(1,c-k)`. Their sum is `min(c,d)`. In moving Taylor coordinates
  the future error is at most `2 exp(2) epsilon < 18 epsilon < 1/2` times
  `1/n!`, while the first differing integer has magnitude at least `1/n!`.
  The coordinate change costs only a polynomial in `n`. Uniform cylinder
  measure therefore obeys every Frostman exponent below `min(c,d)`.
- **Rationality threshold:** remove the rational Taylor polynomial at 1
  and clear denominators. Division by `(z-1)^d` has an integer prefix
  formula at 0, which also preserves each eventual divisibility. Vanishing
  derivatives give a complementary tail starting at `n+d`, whose ratio
  bound makes the quotient coefficients bounded for growth `O(n^d)`.
  Boundedness and divisibility force eventual zero. Above the threshold,
  the open set has eventually positive coefficient representatives and
  therefore supplies nonpolynomial representatives of rational vectors.
  A finite correction of `(z-1)^d exp(z)` shows that the growth hypothesis
  without the congruences would be insufficient.
- **Boundary cases:** `d=1` is covered by the same counting argument;
  integer `c` has exactly `min(c,d)` active channels; unused channels are zero;
  all constructions start beyond index zero, so multiplying by `(z-1)^k`
  introduces no constant term. Nonnegative coefficients prevent global
  surjectivity onto all of real `d`-space, so only an open set is asserted.
- **Congruences:** the common modulus is the largest factorial below
  `log(n+3)`; it is nested, eventually contains every fixed divisor, and
  has negligible logarithmic entropy cost. Finitely many shifted integer
  combinations preserve the property. Cumulative congruences are asserted
  for the earlier scalar theorem, not added without proof to the jet theorem.

The proof was reread after the finite checks, specifically at the shared-cube
induction step and the cylinder separation step. The complete proof is
ordinary mathematics; the finite tests do not stand in for either argument.

## Literature comparison

- [Wegmann (1968), Satz 4, p.625](https://dml.cz/bitstream/handle/10338.dmlcz/100861/CzechMathJ_18-1968-4_7.pdf)
  gives the scalar restricted-digit dimension formula, credited there to
  Šalát. The entropy/mass-distribution method is established prior art.
  The additional obligation here is separation of the joint derivative
  image after several polynomial carry channels have been added.
- [Airey–Mance–Vandehey (2015), Section 6](https://nyjm.albany.edu/j/2015/21-60v.pdf)
  already combine eventual divisibility of digits with asymptotically full
  digit entropy in Cantor-series constructions. That device is not new.
- [Waldschmidt's survey, Sections 2–3](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/SurveyIntegerValuedEntireFunctions.pdf)
  situates integer Taylor coefficients and prescribed derivatives in the
  classical Hurwitz-function literature. The survey's growth and multipoint
  integrality results are not a stated source for the precise finite-vector
  dimension/interior theorem here. A bounded search did not establish
  priority for this theorem; absence from those sources is not a novelty proof.

This is a concrete method transfer with a sharp general theorem. Neither
field-wide importance nor a general advantage of an AI discovery procedure
has been demonstrated.

## Verification and publication boundary

`jets.py` checks factorial carry powers through degree seven, derivative
orders through eight, integer annihilator expansions through dimension eight,
the moving Taylor formula, and an exact rational infinite-tail majorant.
It also checks the finite carry endpoint terms, whose omission would be false.
Both quotient formulas are checked on every polynomial basis vector in the
tested range, including beyond its support; fractional and saturated
entropy allocations are checked separately.
The saved validation record binds those checks to source hashes.

`FactorialJet.lean` proves `carry_scaled`, `sum_carry`,
`sum_weighted_carry`, and `dvd_carry`. The full dimension and interior theorem
and the rational-derivative rigidity theorem have not been formalised.
The existing feedback module supplies the scalar
formal ingredient; its full capacity proof is also ordinary mathematics.

The existing manuscript, companion research record and paper metadata are
updated. The eight problem registries, Comparator roster and Palomar state
remain unchanged: no new reviewed claim and no new pending submission are
justified by these local checks. Nothing is submitted or pushed.

The reusable mathematical lesson is recorded in the proof itself: use a
vanishing polynomial to expose a free higher-order observable, and use
coordinates centred at the first differing index to prove that multiple
channels remain independent. No new process framework is needed.
