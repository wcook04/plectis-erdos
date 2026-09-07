# Erdős #249: carry-rank frontier

This six-endpoint package exposes the full rationality-to-carry anti-
compression chain already explained in the #249 paper:

- non-irrationality of a linearly bounded binary coefficient series is
  equivalent to existence of a positive-multiplier tempered integral carry;
- adjacent carry sections recover each positive-residue totient channel;
- a separated canonical minor transports to a `2^e - 1` carry-rank lower
  bound;
- hypothetical non-irrationality supplies one carry with that lower bound at
  every level;
- carry displacement divisibility is exactly tail-difference integrality; and
- the same rationality-supplied carry is uniformly eventually periodic modulo
  its multiplier while retaining unbounded rational dyadic-section rank.

This is the exact compression boundary, not an irrationality proof. Modular
periodicity is quotient compression; no theorem turns it into a finite
torsion-free `ℚ`-rank upper bound.

Its **Plectis Signal is 91/100**: theorem closure 23/25, parent-problem
proximity 21/25, mechanism depth 19/20, hypothesis sharpness 15/15, and
consequence reach 13/15.  That is a portfolio-relative editorial judgment,
not proof authority, a novelty claim, a Palomar verdict, mechanical readiness,
or permission to submit.

## Paper correspondence

Every selected Comparator endpoint has a manuscript-owned route in
`formalization.yaml`.  The LaTeX label is the stable locator; the pinned source
link is a human convenience, not a substitute for that label.

| Comparator endpoint | Reader treatment | Exact boundary |
|---|---|---|
| `not_irrational_totientSeries_implies_mod_period_and_unbounded_rank` | [`res:carryrank`](https://github.com/wcook04/plectis-lean-erdos249-257/blob/19cb0aa21c1769828c4f70b22a4298dd52811e33/paper/erdos-249-binary-totient-series.tex#L361-L387) | [`prob:carryrank`](https://github.com/wcook04/plectis-lean-erdos249-257/blob/19cb0aa21c1769828c4f70b22a4298dd52811e33/paper/erdos-249-binary-totient-series.tex#L1601-L1615) |
| `not_irrational_totientSeries_implies_unbounded_carryRank_unconditional` | [`res:carryrank`](https://github.com/wcook04/plectis-lean-erdos249-257/blob/19cb0aa21c1769828c4f70b22a4298dd52811e33/paper/erdos-249-binary-totient-series.tex#L361-L375) | [`prob:carryrank`](https://github.com/wcook04/plectis-lean-erdos249-257/blob/19cb0aa21c1769828c4f70b22a4298dd52811e33/paper/erdos-249-binary-totient-series.tex#L1601-L1615) |
| `finrank_canonicalCarryKernel_ge_of_certificate` | [`res:carryrank`](https://github.com/wcook04/plectis-lean-erdos249-257/blob/19cb0aa21c1769828c4f70b22a4298dd52811e33/paper/erdos-249-binary-totient-series.tex#L361-L375) | [`prob:carryrank`](https://github.com/wcook04/plectis-lean-erdos249-257/blob/19cb0aa21c1769828c4f70b22a4298dd52811e33/paper/erdos-249-binary-totient-series.tex#L1601-L1615) |
| `totient_carryKernel_diff` | [`res:carryrank`](https://github.com/wcook04/plectis-lean-erdos249-257/blob/19cb0aa21c1769828c4f70b22a4298dd52811e33/paper/erdos-249-binary-totient-series.tex#L361-L375) | [`sec:carry-rank`](https://github.com/wcook04/plectis-lean-erdos249-257/blob/19cb0aa21c1769828c4f70b22a4298dd52811e33/paper/erdos-249-binary-totient-series.tex#L949-L962) |
| `carryShift_dvd_iff_tailDiff_mem_int` | [`prop:CP-01-inv`](https://github.com/wcook04/plectis-lean-erdos249-257/blob/19cb0aa21c1769828c4f70b22a4298dd52811e33/paper/erdos249-totient-reasoning-surface.tex#L2410-L2421) | same proposition, including its positive-multiplier hypothesis |
| `not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit` | [`sec:carry-rank`](https://github.com/wcook04/plectis-lean-erdos249-257/blob/19cb0aa21c1769828c4f70b22a4298dd52811e33/paper/erdos-249-binary-totient-series.tex#L949-L962) | same section, including the linear-growth hypothesis |

`Challenge.lean` imports only Mathlib. `Solution.lean` transports the exact
source theorems. `AxiomAudit.lean` prints all six axiom rosters. The deliberate
negative module gives the summit declaration the wrong type and omits the
other required endpoints.
