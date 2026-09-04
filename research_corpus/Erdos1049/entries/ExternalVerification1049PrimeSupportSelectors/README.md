# Erdős #1049: prime-supported rational gaps and two-selector escape

Plectis Signal: **96/100**

Components: theorem closure 25, parent-problem proximity 23, mechanism depth
19, hypothesis sharpness 15, consequence reach 14.

This Comparator package exposes one six-endpoint hierarchy from the
source-current q-Apéry and two-selector development. The mathematical order is
deliberately unequal:

1. the sharp two-row 1/q gap forced by a common denominator prime and the
   first-power exterior-determinant boundary;
2. the impossibility of simultaneous decay to zero through non-collinear
   integral rows at a rational target;
3. the sharp one-row prime and prime-power 1/q gaps;
4. the determinant–height–decay cost of real unit-determinant recombination,
   including integer-unimodular changes of basis; and
5. the reduced N < 2^k collision threshold after all denominator coordinates
   vanish modulo N.

The first two are the principal review endpoints. The final two are supporting
mechanisms, not coequal headline results.

## Exact paper routes

The active reader-facing paper is:

- source: paper/erdos-1049-rational-base-lambert.tex
- repository: <https://github.com/wcook04/plectis-lean-erdos249-257>
- pinned public base:
  <https://github.com/wcook04/plectis-lean-erdos249-257/blob/78d1faeb2bf79fa3ddc3291b63c73f19dfe48b94/paper/erdos-1049-rational-base-lambert.tex>
- staged revision:
  ErdosProblems/papers/erdos-1049-prime-support-selectors.patch
- staged target: public commit
  78d1faeb2bf79fa3ddc3291b63c73f19dfe48b94
- target file SHA-256:
  012dab93eebf3478bd31ab41faf4d55ff5f8538e1eb982c20183bd116ba44e77

| Comparator declaration | Exact paper location |
|---|---|
| primeSupportedTwoSelector_rationalGap | Theorem res:prime-supported-two-selector-gap |
| rationalTwoSelector_notBothTendstoZero | Corollary res:rational-two-selector-no-double-decay |
| primeSupportedOneRow_rationalGap | Proposition res:prime-supported-one-row-gap |
| primePowerSupportedOneRow_rationalGap | Corollary res:prime-power-supported-one-row-gap |
| twoSelector_unimodularHeightDecay_tradeoff | Proposition res:unit-determinant-height-decay |
| zeroDenominatorCoordinates_binaryCollision | Proposition res:zero-denominator-selector-collision |

The shared limitation is bdry:prime-support-remaining-hypotheses. The patch is
the application-ready local paper authority until an explicitly authorized
public promotion lands it; the pinned public base does **not** yet contain
these anchors. The patch dry-applies, compiles to a 27-page PDF, and has been
visually inspected.

## Exact boundary

The package does not prove that actual q-Apéry rows provide suitable primes
cofinally, does not prove that the determinant has exactly one copy of the
selected prime cofinally, does not supply the analytic remainder estimates,
and does not prove irrationality at 3/2.

The prime-power endpoint retains its stronger denominator-data hypothesis
without inflating the conclusion: one prime copy already yields the same sharp
1/q gap.

The height–decay endpoint is slightly stronger than the shorthand
“unimodular”: its transformation coefficients are real and the absolute
determinant is one. Integer-unimodular matrices form a special case.

## Assurance state

An independent static audit found exact parity among the six source
declarations, Challenge statements, Solution transports, theorem-name lists,
and AxiomAudit declarations. Challenge imports Mathlib only, the permitted
axiom budget is exactly `propext`, `Quot.sound`, and `Classical.choice`,
and NanoDa is enabled. The focused validation future
`cf_929375a15f54470ebf1e` exhausted five low-disk defer retries and
terminated in `deferred_capacity` with exit 75, without a Lean diagnostic.
Focused Lean replay, the axiom audit, and terminal positive and
deliberate-negative Comparator receipts therefore remain pending until disk
capacity materially changes.

The deliberate negative exposes only the weakest finite collision interface.
Comparator must therefore reject the missing principal interfaces, beginning
with the two-row gap.
