# Erdős #1041: checked kernels for three solved polynomial families

This Comparator package exposes one strong checked endpoint from each of three
source-current families for which Erdős #1041 is proved by an ordinary
mathematical assembly. The sharp collinear family is an all-degree theorem with a best
constant and equality configurations; the primitive quintic and translated
cubic fibres are substantial solved companions.

The theorem list is deliberately ordered by mathematical signal:

- `SharpCollinear.existsPeakLeComparisonBound` is the sharp Chebyshev endpoint
  in the collinear argument. The ordinary affine normalization, gap-maximizer
  selection, transport back to the root line, and equality construction give
  the sharp collinear root-diameter theorem.
- `primitiveQuintic_twoStrictTailEnergies` is the finite real-moment selector
  for the closed-disc primitive sparse quintic. It selects two distinct
  indices, not automatically two distinct complex values. The ordinary
  rotation, Newton-moment derivation, Abel summation, and zero-occurrence path
  convention give the solved open-disc family without erasing that boundary.
- `cubic_safeRootSpoke` selects a complete safe spoke for one root of any
  monic cubic with its three listed roots in the open unit disc. The ordinary
  companion pulls that spoke through `z ↦ (z-h)^q`, `q ≥ 2`, to prove the
  translated cubic quotient-fibre family.

The boundary is deliberate.  Lean checks exactly the three displayed
endpoint declarations; it does not check the ordinary fibre pullback, Abel
path construction, affine transport, or the unrestricted Erdős problem.
Erdős #1041 remains open for arbitrary monic polynomials with roots in the
open unit disc.

## Exact paper routes

The active public paper does not yet contain these results. The routes below
target the application-ready staged revision
`ErdosProblems/papers/erdos-1041-critical-value-separation.patch`, which
dry-applies to public paper base
`fe5d678bec0111c52059d04e77dfc20130c6176c` with source-file SHA-256
`d1135882e5f39869396018a0a770a2d23f4211de80d4048cdc0a7381448cd1a4`.
They become live public routes only after authorized promotion.

| Comparator declaration | Exact checked-kernel label | Ordinary theorem supported | Exact boundary |
|---|---|---|---|
| `SharpCollinear.existsPeakLeComparisonBound` | `prop:sharp-collinear-chebyshev-comparator` | `thm:sharp-collinear-diameter`; target corollary `cor:collinear-erdos-1041` | `rem:sharp-collinear-formal-boundary` |
| `primitiveQuintic_twoStrictTailEnergies` | `prop:primitive-quintic-two-tail-energy-selector` | `thm:primitive-quintic-two-tail` | `rem:primitive-quintic-formal-boundary` |
| `cubic_safeRootSpoke` | `lem:cubic-safe-root-spoke` | `thm:translated-cubic-quotient-fibres` | `rem:cubic-quotient-formal-boundary` |

The shared package seam is `bdry:solved-polynomial-families`.

`Challenge.lean` imports only Mathlib and reproduces the two definitions used
by the sharp collinear theorem. `Solution.lean` wraps the exact source
declarations. The deliberate negative omits the sharp collinear endpoint, so
Comparator must reject it as incomplete.

Static package, source-alignment, JSON, and metadata checks pass. A focused
build exposed and prompted repair of a missing `open Polynomial` in the
challenge and solution. After repair, the Challenge, Solution, deliberate
negative, and AxiomAudit passed focused Lean replay; all three selected
endpoints reported exactly `propext`, `Quot.sound`, and `Classical.choice`.
The supported Comparator runner now includes this positive/deliberate-negative
pair. Terminal Comparator/NanoDa replay on Linux behind the required systemd
boundary, authorized paper promotion, and a pinned public source identity
remain Palomar gates. This package records a high-interest candidate without
claiming an external validation or submission receipt it does not have.
