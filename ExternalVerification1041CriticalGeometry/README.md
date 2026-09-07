# Erdős #1041: critical geometry and exact straight-line obstructions

This Comparator entry packages six source-current endpoints from the geometry
of polynomial lemniscates: two complementary all-degree critical metric
theorems, a positive cubic selector, and two exact boundaries on straight-line
containment arguments.

The all-degree theorem starts at any non-root critical point. If `r` is the
geometric mean of all root distances from that point, two distinct root
occurrences have total distance at most `2r`. This is the strongest currently
checked scale-sensitive metric selector for the unrestricted problem.

The complementary global disk theorem is the exact algebraic core behind the
paper's stronger unit-disk conclusion.  Given the two nearest distances
`δ ≤ e`, the unit-disk diameter bounds, reciprocal balance
`e ≤ (N-1)δ`, and the disk inverse-square estimate, it proves `δ+e ≤ 2` at
every critical point.  A strict diameter margin gives `δ+e < 2`.  Lean checks
these two complete implication interfaces; deriving their geometric
hypotheses for a polynomial is the ordinary proof, and neither theorem supplies
lemniscate containment.

The second theorem is the safe-spoke fan-in for a monic cubic: among three
roots in the open unit disc, at least one complete radial root spoke stays in
the closed unit lemniscate. It is the load-bearing checked kernel in the
complete ordinary theorem for translated quotient fibres
`P((z-h)^q)`, `q >= 2`.

The quintic arithmetic theorem verifies that one tenth of the unique nearest
root spoke escapes. Its reciprocal-balance and unique-nearest-root properties
are separately Lean-checked in the source, so this compared declaration is the
exact escape endpoint rather than the entire bundled certificate.

The final theorem gives an explicit monic cubic of radius `99/100` for which
the midpoint of every distinct root pair lies outside the unit lemniscate.
The source definitions for this configuration are private; Challenge and
Solution therefore reproduce those constants literally and transport the
source proof. This is exact explicit-definition transport, not a direct wrapper
around a public source type.

Together these statements preserve the real boundary. Both critical proximity
theorems stop at Euclidean distance and do not prove containment; radial spokes
can fail even for the unique nearest root,
and no universal straight root-pair segment argument is possible. The safe
cubic spoke theorem does not extend the quotient-fibre assembly or solve the
unrestricted problem.

`Challenge.lean` imports only Mathlib. The deliberate negative omits both disk
inverse-balance theorems, the cubic selector, and both obstruction declarations,
so Comparator must reject it as an incomplete package.
