# Why the minimum moment needs index eight

This checks the finite-support claims in the #68 short paper, lines 430–438
of public edition `551bae6d`. Coefficients are arbitrary signed integers.
For a vector supported at indices 2 through 7, write its factorial moment as
M and its divisor-channel numerators as V₂ and V₄.

The exact six basis rows give

    11M − 46V₂ + 12V₄ = 4140(c₆ + 7c₇).

Checking each basis row proves the identity for every choice of integer
coefficients by linearity. It is not a search over bounded coefficients.
When both channels vanish, the explicit identity
`3011 × 11 − 8 × 4140 = 1` yields

    M = 4140[3011(c₆ + 7c₇) − 8M].

Thus every such moment is divisible by 4,140. If support is at most five,
the first identity forces M = 0. The vector

    246e₂ − 112e₃ + 180e₄ − 66e₅ + 11e₆

has moment 4,140 and cancels all three channels V₂, V₃ and V₄. Scaling it
shows that the moment ideal is exactly 4140ℤ for support at most six or seven,
even with the third channel required. This also gives the positive minimum.

Since 4,140 does not divide 1,380, no vector with maximum index below eight
can attain moment 1,380 under V₂ = V₄ = 0. The paper's vector
`1482e₂ − 784e₃ − 136e₅ + 83e₆ − e₈` attains 1,380 and cancels all three
channels, so eight is the exact smallest possible maximum index.

Run `python3 lean/ErdosProblems/Erdos68/scripts/check_depth_four_short_support.py`. The retained certificate has
identical output under ordinary and optimized Python. Three corrupted dual
coefficient sets are rejected; explicit examples show that either vanishing
premise alone is insufficient, and that cancelling V₃ restricts vectors even
when the attainable moments are unchanged.

This is an exact integer certificate with a linear proof of the finite-support
claim. It supplies neither a Lean proof nor a proof of the unrestricted
moment ideal or irrationality of the infinite series. Those have separate
source and validation owners.

## Source and downstream disposition

This note makes the existing paper assertion independently checkable. It does
not claim novelty for the assertion. The original proof and checker are held
in batch `erdos68_short_support_20260927`; the checker here is byte-identical
to its committed audit source.

Paper route: `paper/68/erdos-68-factorial-denominator-irrationality.tex` at
public commit `551bae6dc6e732cf85172d66323c8d2bc77ba962`, in the paragraph following `eq:depth-four-short-vector`, using the identity
`eq:depth-four-dual`.
The exact general low-channel ideal remains a separate Lean theorem in
`PaperCompleteMomentIdeal.lean`; the numerical all-support depth-four replay
remains a separate check. Neither is inferred from this restricted-support
certificate.

Comparator disposition: ordinary-proof paper support; no dedicated Comparator
family or acceptance is claimed. A formalization of the universal basis
identity and its finite-support consequences is required before an exact
Challenge/Solution pair can be selected.

Palomar disposition: no separate entry. Keep this finite-support explanation
under the existing #68 paper family; it supplies no Lean-kernel or NanoDa
receipt and does not change the frozen submitted/prepared entry identity.
Revisit this disposition only if an independently useful checked interface is
landed or the existing family is deliberately expanded.
