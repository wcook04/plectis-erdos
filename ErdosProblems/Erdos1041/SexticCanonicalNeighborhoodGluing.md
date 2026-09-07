# The canonical sextic charts already overlap exactly

Two earlier results were designed around the same normalized transverse
coordinates ((p,q,r)) and null-branch parameter (eta), but their constants
had not been explicitly glued.

The tetrahedral transverse selector closes the outer region

\[
p^2+q^2+r^2\ge6075\beta^4.                         \tag{1}
\]

The complete finite null-box atlas closes the inner coordinate box

\[
|p|,|q|,|r|\le78\beta^2.                            \tag{2}
\]

There is no intermediate region.  Indeed, if (1) fails, then for each
(x\in\{p,q,r\}),

\[
x^2<6075\beta^4<78^2\beta^4=6084\beta^4,
\]

so (|x|<78\beta^2).  Lean proves this dichotomy and an abstract fan-in
theorem: any conclusion established on (1) and (2) holds on the entire
canonical transverse chart.

The normalization agrees with the existing null-box formulas.  At the
canonical contact (a=r_0h), the physical transverse contact coordinates are
(a a_1), (2a^2\theta), and (-a(b_1+2a^2c)).  Dividing the normalized
chord by (r_0^2/2) turns the (eta^2)-coefficients in
`SexticNullBranchFiniteTransfer` exactly into its (P,Q,U) coordinates.
Thus the number 78 is the coordinatewise envelope of the radius
(\sqrt{6075}<78), not an unrelated numerical choice.

Consequently the canonical homogeneous neighborhood has no missing overlap
between the first-order outer selector and the finite null-box atlas.  The
remaining sextic task is no longer to invent a third canonical transition
chart.  It is to glue this now-complete canonical neighborhood to the strict
noncanonical phase collars and the (4/5) first-mode overlap, and then absorb
the actual-polynomial remainder.

This theorem is an exact atlas-gluing result, not yet the nonlinear transfer
and not unrestricted Erdős #1041.
