# FAILED DRAFT — Erdős 1041 weighted-cusp transport toward `u=10^-2`

**Status: not a theorem; do not cite or land.**  The exact checker proves the
carrier geometry on 37 adaptive cells but fails its final sign-payment gate:
the worst two-sided selected upper bound is `+0.04284646`.  The fully proved
connected collar still stops at `u=10^-3`.

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_quintic_weighted_cusp_transport_to_one_hundredth.py`.
Consumes the connected five-sheet theorem `QuinticWeightedCuspTransportToOneThousandth.md`.

## 1. Result

> **Attempted statement WCT-2 (not proved).** For
>
> ```text
> kappa=u^3,       0 <= u <= 1/100,                 (W2.1)
> ```
>
> every upper-half-plane sheet of the regular double-tight carrier has
> strictly negative paired inverse-arm excess.

The earlier exact theorem supplies the connected collar through `u=1/1000`.
The new checker begins at that exact endpoint and covers every rational cell
through `u=1/100`; hence no continuity-only interval is inserted.

## 2. Recentered cusp payment

The three sheets limiting to `mu=-10` are the tight part of the estimate.
Instead of carrying the deliberately coarse absolute gradient budget from the
microscopic cusp, the checker recomputes the full exact wall excess at

```text
u = 1/1000, 1/250, 7/1000, 1/100.                 (W2.2)
```

All twelve sheet-anchor excesses are strictly negative.  Between consecutive
anchors it partitions geometrically by `u -> min(11u/10,u_right)`.  Parametric
Krawczyk isolates the carrier root `z(u)` on every cell and exact implicit
differentiation gives

```text
z'=-H_u/H_z,
mu'=z+uz',
phi'=-Im[(P_u+P_z z')/P].                          (W2.3)
```

The exact wall engine certifies `G_mu<2`, `G_phi<8` on the complete wall tube,
so a cell payment is

```text
Delta E <= (G_mu |mu'|+G_phi |phi'|) Delta u.      (W2.4)
```

For each cell the replay separately accumulates (W2.4) from its segment's
left and right exact anchors, then selects the smaller outward upper bound.
Thus the old global-payment loss is discarded at every anchor; this is an
exact two-sided cover, not a sampled sign claim.

## 3. The two `mu_*` germs

The other two upper sheets stay in the regular `(t,a,mu)` chart with
`kappa=t/(1+t^2)`.  The checker keeps the germs separate, proves each
two-complex-variable parametric Krawczyk self-map, differentiates the exact
carrier equations, fixes the chamber by the exact sign of the cross
derivative, and transports the preceding exact endpoint bounds in `t`.  Their
unit-scale negative margins dominate the new payment without recentering.

## 4. Exactness and boundary

All anchor excesses, carrier inclusions, chamber signs, inverse-arm tubes,
wall gradients, implicit derivatives, and transport payments use outward
rational complex-ball arithmetic.  `mpmath` supplies only provisional Newton
centres, each accepted only after an exact Krawczyk inclusion.

This attempted statement is explicitly the positive side `kappa=u^3>=0`.  It does not
certify the negative-`kappa` cusp, and it does not cover

```text
1/100 < u <= 1/10.
```

Those are separate surviving obligations; no complete double-tight or
unrestricted Erdős 1041 conclusion is asserted here.
