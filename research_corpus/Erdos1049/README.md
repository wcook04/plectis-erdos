<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# Erdős 1049 research corpus

The weighted Lambert-tail Hankel determinant is positive, has the exact real
asymptotic `K(q) N! N^L q^(N(N+1)(2N+1)/6) P^(2N)`, and as a rational function
has every `Phi_d` with `N <= d <= 2N-1` as a pole of exact order `2N-d`, for
**every** rational parameter `mu >= 1/2` rather than a generic one. The
primitive rows of the actual reduced tails span exactly `Z x bZ`, with Smith
invariants `(1,b)` and window minor valuation `b^(s+1)`. Both are proved here.

What is missing is a bound on the specialisation gcd, so neither result gives
an integer-height conclusion, and `F(3/2)` stays open. The manuscripts in
`paper/1049/` and `paper/reasoning-parts/erdos1049/` remain the only
claim-bearing surfaces for this problem; the files below are working notes and
candidate formal sources.

## What landed here, and what it is worth

| File | Content | Evidence class |
|---|---|---|
| `WeightedTailRoutes.md` | The weighted residual determinant, its exact real asymptotic, its high cyclotomic poles at every rational parameter `mu >= 1/2`, the exact primitive prefix lattice of the tails, and the finite Rogers–Szegő route with its recurrence | Ordinary proofs. None compiled in Lean. The pole theorem is a statement over `Q(q)`, not a height bound after integer specialisation |
| `SunCatalanAudit.md` | Reconstruction and audit of Zhi-Wei Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1 | A falsifier for the displayed aggregation used in that preprint's Proposition 9.5, with original TeX and printed-page locators. It does not decide the irrationality of Catalan's constant |
| `WeightedTailFinite.lean` | Eleven finite supporting lemmas for the two notes above | **UNRUN.** Not imported by any registered module and not part of any checked build. No `sorry` and no new `axiom` is a lexical observation, not a kernel-acceptance claim |

## Boundary

The infinite statements in these notes are ordinary mathematics. The finite
computations named inside them corroborate the statements and do not prove
them. Sun's endpoint theorem is an unverified preprint claim and is not a
manuscript input anywhere in this repository.

The parts of this work that carry proofs strong enough for the record were
moved into the long reasoning record as
`long1049:thm:geometric-universality`, `long1049:prop:rogers-factorisation`,
`long1049:thm:sharp-fixed-base` and `long1049:res:tail-lattice`. What stayed
here is what still lacks either a complete argument or a consumer.

## The remaining step

An approximation family whose **primitive** coefficient height and local
denominator cost are proved smaller than its real decay, with nonvanishing
retained. Rationally reweighting the tails does not produce one:
`long1049:res:tail-lattice` shows that the primitive rows and the endpoint
valuations are unchanged by that operation. The polynomial pole degree of the
weighted determinant already exceeds its real decay coefficient, at
`4/pi^2 - 1/3 = 0.0719...`, but no bound on the specialisation gcd has been
proved, so no integer-height conclusion follows from that degree alone.

## Provenance

Type B research return `erdos1049_sun_return`, 20 September 2026, assimilated
against the canonical manuscripts. The return was produced against a snapshot
171 commits behind `origin/main`; its manuscript patches were not applied, and
the mathematics was ported onto the current sources by hand.
