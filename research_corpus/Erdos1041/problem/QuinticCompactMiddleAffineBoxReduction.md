# Erdős 1041: an explicit six-real-dimensional compact middle for degree five

Date: 2026-08-30.  Exact arithmetic replay:
`scripts/check_erdos1041_quintic_compact_middle_affine_box.py`.

This note turns the part of the degree-five problem outside the sharp
low-critical spoke theorem into one explicit compact coefficient box.  It is
a reduction and certificate specification, not the missing certificate and
not a proof of degree five.

## 1. Normalization at the least critical-value hub

Let `f` be a monic quintic, let `c` minimize `|f|` on the critical points,
write `mu=|f(c)|>0`, choose `lambda^5=f(c)`, and set

```text
P(u)=f(c+lambda u)/f(c)
    =u^5+a_4u^4+a_3u^3+a_2u^2+1.                 (CM1)
```

This is Theorem N of `AffineNormalisedModuli.md`: `P(0)=1`, `P'(0)=0`,
the minimum critical-value modulus of `P` is one, and lengths and minimum
enclosing radii are divided by `|lambda|`.  Let `R=R_MEC(P)`.

The Fekete--Hadamard critical-product inequality gives

```text
1=mu_P <= R^5,                                      (CM2)
```

so `R>=1`.  Conversely, if a critical point `kappa` of `P` satisfies

```text
|P(kappa)|<=R^5,          L_P(kappa)<2R,             (CM3)
```

then its corresponding hub for `f` is admissible and has length `<2R_f`.
Indeed `|f(c+lambda kappa)|<=mu R^5=R_f^5<1` when the original roots lie
in an open disk of radius `R_f<1`, while lengths scale by `|lambda|`.
Thus (CM3), at any one of the four hubs, is a parent-valid certificate.

## 2. The sharp spoke cutoff makes the residual bounded

Let

```text
t_* = 5/16+3sqrt(105)/80,
M_5=(1-t_*)(1+t_*)^3 sqrt(16t_*^2-4t_*+1),           (CM4)
```

the exact degree-five constant of Lemma S5 in
`Degree5AssemblyAndSharpenedCuts.md`.  Apply that theorem after translating
the MEC centre to zero and dividing spatial coordinates by `R`.  The
normalized critical value at the image of `u=0` is `1/R^5`.  Therefore

```text
R^5>=M_5  ==>  two contained straight spokes of total length <=2R. (CM5)
```

So every counterexample not already closed by S5 obeys

```text
1<=R<M_5^(1/5)<13/10.                               (CM6)
```

The last inequality is exact.  Squaring (CM4) gives

```text
M_5^2 = 2963137215087/419430400000
      +(49597072497/83886080000)sqrt(105),           (CM7)
```

and `sqrt(105)<41/4`; direct rational comparison then proves
`M_5^2<(13/10)^10`.

## 3. One explicit coefficient box

Let `m` be the centre of the MEC of the roots of `P`.  Since `0` is a
critical point, Gauss--Lucas puts `0` in their convex hull.  The closed disk
`D(m,R)` contains that convex hull, hence `|m|<=R`, and every root `u_j`
satisfies

```text
|u_j|<=|u_j-m|+|m|<=2R<13/5.                         (CM8)
```

Vieta and (CM8) now give the rational bounds

```text
|a_4| < 13,
|a_3| < 68,
|a_2| < 176.                                         (CM9)
```

Consequently every unresolved normalized quintic lies in the fixed
six-real-dimensional box

```text
B=[-176,176]^2 x [-68,68]^2 x [-13,13]^2,            (CM10)
```

where each square records real and imaginary parts of `a_2,a_3,a_4`.
Inside `B` the relevant semialgebraic/analytic subdomain is cut out by

```text
P has five roots in an MEC of radius R in [1,13/10],
|P(kappa)|>=1 for every root kappa of
  5u^3+4a_4u^2+3a_3u+2a_2,
```

with ties and collisions retained by closure.  This subdomain is compact:
it is the continuous image/limit of bounded root tuples satisfying closed
critical-value and MEC inequalities.

The regular pentagon is exactly the single coefficient point
`(a_2,a_3,a_4)=(0,0,0)`.  Once `(EX-U+)` is supplied, the
trace-min qualitative transfer closes a relative open neighbourhood of this
point.  Removing any such neighbourhood leaves a genuine compact annulus in
the explicit box (CM10); there is no remaining cusp at infinity and no root
shell whose scale must be guessed.

There is a substantially tighter coordinate cube.  Write the three nonzero
critical points of `P`, with multiplicity, as `kappa_1,kappa_2,kappa_3`.
Then

```text
P'(u)=5u product_(j=1)^3(u-kappa_j),
a_4=-(5/4)e_1(kappa),
a_3= (5/3)e_2(kappa),
a_2=-(5/2)e_3(kappa).                                  (CM11)
```

Gauss--Lucas puts every `kappa_j` in the MEC disk of the roots.  As that disk
also contains zero, the same argument as (CM8) gives
`|kappa_j|<=2R<13/5`.  Hence the whole residual can instead be covered in
the unordered critical-coordinate cube

```text
(kappa_1,kappa_2,kappa_3) in D(0,13/5)^3,               (CM12)
P(u)=1+integral_0^u 5s product_j(s-kappa_j) ds,
```

and (CM11) improves (CM9) to

```text
|a_4|<10,              |a_3|<34,              |a_2|<44. (CM13)
```

This is the preferred atlas coordinate: it removes polynomial root-finding
for `P'`, makes the trace-min inequalities simply `|P(kappa_j)|>=1`, and
quotients the only remaining label symmetry by permutations of three points.

## 4. Fail-closed finite certificate

The shortest source-current compact-middle computation is therefore a
six-variable critical-point atlas, not a ten-variable root atlas.

For each rational complex box in (CM12):

1. reconstruct `P` from (CM11) and isolate its five roots by complex interval
   Krawczyk tests (all four critical hubs are already exact box variables or
   zero);
2. bound the MEC by the finite pair/triple support enumeration for five
   planar points, rejecting boxes outside `1<=R<13/10`;
3. reject boxes on which some nonzero critical value is provably below one,
   because those do not belong to the chart where zero is trace-minimal;
4. for every eligible hub use the resolved equation
   `P(Z(u))=P(kappa)(1-u^2)`, `0<=u<=1`, and exact Taylor-model interval
   integration of `Z'=-2uP(kappa)/P'(Z)` to upper-bound both stable arms;
5. accept as soon as one hub has the strict rational gates
   `|P(kappa)|_upper<R_lower^5` and `L_upper<2R_lower`.

Saddle connections are not guessed through: retain every stable limiting
sheet and subdivide, exactly as required by
`QuinticTraceMinQualitativeTransfer.md`.  Root or critical collisions route
to the already-landed lower-degree/generic-closure strata.  A box is never
accepted from a floating branch label.

This atlas has an important stopping theorem.  On every compact subset on
which a fixed eligible stable sheet satisfies (CM3) strictly, interval
Krawczyk plus Taylor integration accepts all sufficiently small boxes.
Hence, after the origin neighbourhood is removed, failure of adaptive
subdivision to terminate can only accumulate on an exact equality,
admissibility wall, saddle connection, or collision.  Those are the four
explicit residual strata; ordinary bulk points are not a fifth obstruction.

A targeted unit-circle falsifier (1,200 configurations, source-current
descending-arm engine) found, in angular-gap distance from the regular
pentagon,

```text
distance >= .02: max admissible-product 0.82916, max min_hub L 1.691;
distance >= .10: max admissible-product 0.68458, max min_hub L 1.522.
```

These values are only computational sizing evidence.  They indicate that the
compact middle has a fat sign margin once the local gon theorem is removed;
they are not certificate cells and are not used in (CM1)--(CM10).

## Claim boundary

Proved here: the affine normalization consumer (CM3), the sharp-cutoff
compactness (CM6), the exact rational outer radius `13/10`, the explicit
coefficient box (CM10), and the tighter critical-coordinate cube
(CM11)--(CM13).  Imported: Theorem N, Fekete--Hadamard, Lemma S5,
Gauss--Lucas, and the trace-min qualitative transfer.  Computed only: the
two sizing rows above.

Open: `(EX-U+)`; the interval atlas over the compact annulus; equality/wall
strata not already consumed by existing certificates; degree five; and
unrestricted Erdős 1041.
