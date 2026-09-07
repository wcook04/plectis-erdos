# Erdős 1041: the full weighted-cusp collar reaches `u=10^-3`

Date: 2026-08-30. Exact replay:
`scripts/check_erdos1041_quintic_weighted_cusp_transport_to_one_thousandth.py`.
Consumes `QuinticWeightedCuspBridgeCell.md` and the exact wall engine.

## 1. Result

> **Theorem WCT (five-sheet gradient transport).** For
>
> ```text
> kappa=u^3,       0 <= u <= 1/1000,                 (WCT1)
> ```
>
> every upper-half-plane sheet of the regular double-tight carrier has
> strictly negative paired inverse-arm excess.

The proof is connected.  The limiting fibre and the microscopic interval
are supplied by the earlier cusp certificates.  The new transport begins at

```text
u_0=10005/10^8,
```

which overlaps the first full bridge cell by exactly `1/20000000`, and ends
at `u=1/1000`.  Thus there is no continuity-only gap between the exact limit
and the new outer face.

## 2. Exact transport cells

Starting at `u_0`, define rational endpoints

```text
u_{j+1}=min(11u_j/10,1/1000).                       (WCT2)
```

There are 25 cells.  On each of the three `mu=-10` sheets the checker
isolates the weighted carrier root `z(u)` by parametric Krawczyk and computes

```text
z'=-H_u/H_z,
mu'=z+uz',
phi'=-Im[(P_u+P_z z')/P].                           (WCT3)
```

The exact wall engine runs in gradient-only mode on the whole `(mu,d)` tube.
It proves `G_mu<2`, `G_phi<8` cell by cell.  Consequently

```text
|d mathcal E/du| <= G_mu |mu'|+G_phi |phi'|.        (WCT4)
```

Every quantity on the right is an outward rational bound.  Summing the 25
payments from the exact bridge-cell upper endpoint leaves all three sheets
strictly negative at `u=1/1000`.

For the two `mu_*` germs the checker uses the regular carrier variables
`(t,a,mu)`, with `kappa=t/(1+t^2)`.  It encloses each cell's exact preimage by

```text
u_min^3 <= t <= u_max^3+4u_max^9,                   (WCT5)
```

performs a two-complex-variable parametric Krawczyk self-map, differentiates
the exact two-equation carrier, and applies the same gradient transport in
`t`.  The two germs are therefore never mixed with the cubic `mu=-10`
coordinate.

## 3. Exactness and boundary

The anchor, every carrier inclusion, chamber sign, inverse-arm tube,
gradient integral, derivative bound, and accumulated transport payment are
replayed with rational outward complex-ball arithmetic.  `mpmath` supplies
only Newton centres, each of which is subsequently enclosed by an exact
Krawczyk test.  Process parallelism changes runtime only; each returned row
is an independent exact certificate.

This theorem fills the former gap from the microscopic cusp collar through
`|kappa|=10^-9` on the positive side.  It does not certify

```text
10^-3 < u <= 10^-1
```

or the negative-`kappa` side of the regular double-tight atlas.  Therefore
the complete double-tight sign theorem and its downstream consequences
remain open.
