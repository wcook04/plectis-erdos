# Component passports and the critical-hub rescue on a tied Newton face

## 1. Component degree and end count

Let

```text
Q(z)=-z^n+sum_{m<n} A_m z^m,       H=Re Q,
Omega_-={H<0},
```

and let `U` be a connected component of `Omega_-`.  Label the negative ends
by `omega_j=exp(2 pi i j/n)` and let `E(U)` be the labels whose sufficiently
long radial tails lie in `U`.  If `ram(c)=ord_c Q'`, then

```text
|E(U)| = 1 + sum_{c in U, Q'(c)=0} ram(c).                  (1)
```

More precisely, `U` is unbounded and simply connected, and

```text
Q|_U : U -> {Re w<0}
```

is a proper surjective holomorphic map of degree `|E(U)|`.  The end sets of
the different negative components form a noncrossing partition of the cyclic
labels.  In particular, every negative component containing a critical point
has at least two ends.

### Proof

A bounded negative component is impossible: its boundary lies in `{H=0}`, so
the minimum principle applied to harmonic `H` contradicts `H<0` inside.  If a
Jordan curve lies in `U`, compactness gives `H<=-eta<0` on it; the maximum
principle gives the same bound throughout its interior.  The interior thus
lies in `U`.  The planar Jordan-curve criterion makes `U` simply connected.

For compact `K` in the left half-plane, `Q^{-1}(K)` is compact and its
intersection with `U` is closed: components are relatively closed in
`Q^{-1}({Re w<0})`.  Hence the restriction is proper.  Its image is open by
the open mapping theorem and closed by properness, so connectedness of the
half-plane makes it surjective.

For large `T`, the `n` solutions of `Q(z)=-T` are uniquely located near
`T^(1/n) omega_j`.  The sheets belonging to `U` are exactly `E(U)`, proving
that the mapping degree is `|E(U)|`.  Riemann maps conjugate the restriction
to a finite Blaschke product of that degree.  Riemann--Hurwitz gives total
interior ramification `degree-1`, which proves (1).  Finally, alternating end
labels for two disjoint components would give disjoint plane continua with
alternating endpoints on a sufficiently large circle, contradicting the
crosscut separation lemma.  Thus the partition is noncrossing.

Resolving critical points makes the monodromy on `E(U)` a noncrossing tree:
there are `|E(U)|-1` elementary branch edges and connected monodromy.  A
critical point of ramification `r` contributes `r` edges.

The Riemann-map, finite-Blaschke, Riemann--Hurwitz, and planar crosscut steps
remain ordinary mathematics.  The Lean module checks their finite arithmetic
fan-in, not a weakened claim that those analytic adapters have been formalized.

## 2. Exact passport for the calibration quintic

For

```text
Q(z)=-(379/256)z+3z^2-z^5,       c0=1/4,
```

let `U` contain `c0`.  The exact result is

```text
E(U)={1,2,3,4},      degree(Q|_U)=4,      total ramification in U=3. (2)
```

The remaining component has the single end `{0}` and degree one.

The critical connector below proves `1,4 in E(U)`.  The earlier rational-hub
rescue joins sectors 1 and 2, so its component is `U`; conjugation adds sector
3.  Thus `|E(U)|>=4`.  The derivative has total ramification four, while the
unique real cubic-factor critical point in `(24/25,1)` has positive critical
value and is outside `U`.  Formula (1) therefore gives `|E(U)|<=4`, proving
(2).

This corrects the earlier interpretation.  The adjacent angular pairs
bracketing `arg c0=0` are `{4,0}` and `{0,1}`; each mixes ends from different
components.  The hub `c0` is usable, but those angularly selected pairs are
not.

## 3. A strict connector through the original critical point

Let `s=sqrt(5)`,

```text
omega=(s-1)/4 + i sqrt(10+2s)/4,       R=1/2.
```

On the arm from `c0` to `R omega`, the degree-five Bernstein controls of
`Re Q` are

```text
-47/256, -47/256,
-(849+182s)/5120,
-(1319+1117s)/10240,
-(369+1162s)/5120,
-(69+763s)/2048.                                         (3)
```

They are strictly negative; conjugation gives the other arm.  On both tails,

```text
Re Q(r omega)
=-r^5-3(1+s)r^2/4-379(s-1)r/1024 < 0                    (4)
```

for `r>0`.  Finally,

```text
|R omega-c0|^2=(6-s)/16 < R^2,
2|R omega-c0|=(1/2)sqrt(6-s) < 1=2R.                      (5)
```

Thus the very critical point that fails both adjacent bracketing pairs gives
a strict connector for its actual component pair `{1,4}`.  The exact symbolic
checker reconstructs (3)--(5); Lean checks their radical, Bernstein, tail,
and metric kernels.

## 4. The honest all-degree metric residual

For two ends `j,k in E(U)`, define

```text
F_U^{j,k}(R)=d_U(R omega_j,R omega_k)-2R.
```

Radial extension makes this nonincreasing.  Every joining path must enter a
fixed disk, so it is bounded below and has a finite limit `beta_U(j,k)`.

There is a crucial quantifier guard:

```text
beta_U(j,k) < 0       => a finite R with F_U^{j,k}(R)<0,
beta_U(j,k) = 0       does not imply a finite R with F_U^{j,k}(R)<=0. (6)
```

A monotone function may approach zero from above.  Therefore the tied-face
producer must prove a strict negative limiting defect, a finite-radius
inequality directly, or an equality-rigidity theorem.  Merely proving
`min beta<=0` is insufficient.

For a simple negative critical point whose leftward critical-value ray avoids
the other critical values, lift

```text
Q(gamma_+(t))=Q(gamma_-(t))=Q(c)-t.
```

Containment in `U` is automatic.  The convergent horizontal-fibre defect is

```text
delta_Q(c)=integral_0^infinity [
  1/|Q'(gamma_+(t))| + 1/|Q'(gamma_-(t))|
  -(2/n)t^(1/n-1)] dt.                                    (7)
```

Near a ramification-`r` point the singularity is
`O(t^{-r/(r+1)})`, hence integrable.  If the maximal low degree is `M<n/2`,
the inverse expansion at infinity leaves error
`O(t^((M-2n+1)/n))`, also integrable.  Closing the two lifted endpoints to
their asymptotic rays gives

```text
beta_U(j(c),k(c)) <= delta_Q(c).                            (8)
```

Consequently the sufficient strict producer is

```text
min_{negative critical c} delta_Q(c) < 0,                  (HF-strict)
```

or the non-strict version plus an equality-rigidity argument.  This is better
posed than angular adjacency: the component and ends are selected by the
branched covering, containment is built in, and only reciprocal-derivative
length remains.

The unrestricted Erdős problem is still open.  After paired trace, the live
near-Fekete residual is `HF-strict` (or a direct finite connector), followed
by strict finite-face transfer.  Compact-away-from-Fekete consumers remain
separate and indispensable.
