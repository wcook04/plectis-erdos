# Erdős 1041: exact negative curved excess at both endpoints of the `mu=-10` phase arc

Date: 2026-08-30. Exact checker:
`scripts/check_erdos1041_quintic_minus_ten_endpoint_excess.py`. Lean algebra:
`QuinticMinusTenEndpointExcessCertificate.lean`.

## 1. Result

For

```text
F(x)=F_{-10}(x)=x^3(x^2+5x+10),
q_0=1/(2sqrt(2)),
phi_0=arctan(q_0),
```

the two nonzero critical gaps are `12+-24 i sqrt(2)`. Consequently the
allowed phase slice on this repeated-critical stratum is

```text
|tan(phi)| <= q_0.
```

At each of its two endpoints, the canonical pair of curved inverse-ray arms
born at the triple hub has strictly negative excess:

```text
mathcal E(-10,+-phi_0) < -1/80 < 0.                   (E0)
```

This is an ordinary exact statement about the actual limiting curved pair,
not a substitute connector and not a numerical sign. Together with
`QuinticMinusTenCentralExcessCertificate.md`, it closes the centre and both
endpoints of the phase arc.  The later uniform theorem
`QuinticMinusTenFullArcExcessCertificate.md` closes the intervals between
them; the endpoint bound here remains sharper at `+-phi_0`.

## 2. Both arms are quadratic algebraic curves

Put `q=tan(phi)` and write an upper-half-plane arm as

```text
x=b(t+i),  b>0.
```

The ray equation `F(x)=e^{-i phi}s`, `s>=0`, implies
`Im F+q Re F=0`. After division by `b^3` this is

```text
Q_q(t,b)=A_q(t)b^2+B_q(t)b+C_q(t)=0,                 (E1)
A_q(t)=q(t^5-10t^3+5t)+5t^4-10t^2+1,
B_q(t)=5qt^4-30qt^2+5q+20t^3-20t,
C_q(t)=10qt^3-30qt+30t^2-10.
```

The cubic start direction is the selected zero of `C_q`. The checker proves
the tighter exact isolations

```text
q=-q_0:  -740/1000 < t_start < -7395/10000,
q=+q_0:  -4351/10000 < t_start < -4350/10000.        (E2)
```

At infinity, `t` tends to the selected positive zero `k_q` of `A_q`. Since
`8q^2=1`, eliminating `q` gives

```text
k^10-220k^8+910k^6-980k^4+185k^2-8=0,               (E3)
```

and exact Sturm isolation selects

```text
q=-q_0:  251289438338469/10^15 < k_- < 251289438338470/10^15,
q=+q_0:  401880733924049/10^15 < k_+ < 401880733924050/10^15.   (E4)
```

For phase `+phi_0`, the upper arm is the `q=+q_0` curve and the lower arm is
the conjugate of the `q=-q_0` upper curve. At phase `-phi_0` the roles are
reversed. Thus one exact estimate for these two signed upper arms proves both
endpoint statements.

## 3. A nonsingular transverse coordinate

Set

```text
w=b(k_q-t).
```

Writing

```text
D_q(k,t)=(A_q(t)-A_q(k))/(t-k),
S_q(k,t,w)=-D_q(k,t)w^2+B_q(t)w+C_q(t)(k-t),          (E5)
```

the terminal equation `A_q(k)=0` gives the exact factorization

```text
S_q(k,t,b(k-t))=(k-t)Q_q(t,b).                        (E6)
```

Moreover `B_q(k)=A_q'(k)`, so `S_q(k,k,1)=0`; the selected branch therefore
has `w -> 1`. Its terminal direction is

```text
u_q=(k_q+i)/sqrt(1+k_q^2).
```

If `p=da/db` is the physical tangent slope, implicit differentiation of
`S_q=0` gives the stable formula

```text
p=t + w(k-t)S_w/(wS_w-(k-t)S_t).                     (E7)
```

The half-angle from the terminal direction is consequently

```text
tan(|theta|/2)
 = |k-p|/(sqrt(1+p^2)sqrt(1+k^2)+1+pk).              (E8)
```

Finally the transverse coordinate of the translated branch `1+x` is

```text
Im(conj(u_q)(1+x))=(w-1)/sqrt(1+k_q^2).               (E9)
```

## 4. Exact finite support--oscillation certificates

The whole selected branches are contained in the following slightly
extended rational intervals:

```text
q=-q_0:  -741/1000 <= t <= 252/1000,
q=+q_0:  -436/1000 <= t <= 403/1000.                 (E10)
```

The checker divides each interval into 640 rational cells. Floating point is
used only to propose root boxes. Acceptance requires, on every entire cell,
exact rational endpoint signs isolating one root of `S_q=0`; both adjacent
node boxes must lie inside that cell box. Thus the local isolations glue to
one branch. The first cell contains the isolated start with `w=0`, and the
last contains the isolated terminal point with `w=1`. The exact signs
`S_w>0` and `wS_w-(k-t)S_t>0` also prove

```text
db/dt=(wS_w-(k-t)S_t)/(S_w(k-t)^2)>0,
```

so increasing `t` follows the positive physical ray. Since the start lies in
`-1<t<0`, `Re(10(t+i)^3)=10(t^3-3t)>0`; and the only nonzero zero of `F`
in the upper half-plane has `t=-sqrt(5/3)<-1`. Hence this glued branch has
positive ray scalar at its start and never returns to scalar zero.  Moreover

```text
F'(x)=5x^2(x^2+4x+6),
```

whose nonzero upper critical point has `t=-sqrt(2)<-1`.  On the certified
domain `F'` is therefore nonzero; and `db/dt>0` makes `dx/dt` nonzero.  Thus
the ray scalar cannot turn, so its initial positive sign identifies the glued
curve with the outward inverse-ray lift throughout.  The checker then
evaluates an outward rational interval for (E8).

Cells with a fixed exact sign of `w'=-S_t/S_w` contribute their endpoint
variation. On the few unresolved clusters, eliminate `b`, then eliminate the
endpoint algebraic numbers `q,k`. The checker deliberately retains the full
square-free degree-120 polynomial in `t`, including its degree-ten terminal
factor. This avoids erasing a possible finite turn at a terminal root of a
foreign algebraic branch; the retained factor can only overcount turns.
Exact Sturm counts give

```text
q=-q_0 unresolved clusters: root bounds 1,1,
q=+q_0 unresolved cluster:  root bound 4.             (E11)
```

If a cluster contains at most `r` turns, its total variation is at most
`(r+1)` times its certified `w`-range. Summing the cell and cluster bounds
with exact rational arithmetic proves

```text
J_- := integral tan(|theta_-|/2)|dw_-| < 7/20,
J_+ := integral tan(|theta_+|/2)|dw_+| < 11/40.        (E12)
```

The displayed decimal diagnostics (`0.348870...` and `0.270305...`) are only
readable projections of those strict rational comparisons.

## 5. Negative endpoint fan-in

Projection on `u_q`, the identity
`1-cos(theta)=|sin(theta)|tan(|theta|/2)`, and (E9) give each arm

```text
e_q <= (J_q-k_q)/sqrt(1+k_q^2).                      (E13)
```

For the `q=-q_0` arm, (E4) and (E12), together with the trivial cosine bound
`1/sqrt(1+k_-^2)<1`, give

```text
e_- < 7/20-1/4 = 1/10.
```

For the `q=+q_0` arm, the checker proves

```text
k_+>2/5,  1/sqrt(1+k_+^2)>9/10,
```

and hence

```text
e_+ < (9/10)(11/40-2/5) = -9/80.
```

Therefore

```text
E_pair=e_-+e_+ < 1/10-9/80=-1/80,
```

which proves (E0) at both endpoint phases.

## 6. Selected full-arc continuation (subsequently closed)

The endpoint computation also identified the uniform route later completed in
`QuinticMinusTenFullArcExcessCertificate.md`.  For `0<=q<=q_0`, let `r(q)` be
the selected zero of `C_q`, let `k(q)` be the selected zero of `A_q`, and
normalize

```text
t=r(q)+(k(q)-r(q))y,   w=b(k(q)-t),   0<=y<=1.
```

On the glued branch `S_q(k,t,w)=0`, the oscillation term becomes

```text
J(q)=integral_0^1 h(q,y)|-(k-r)S_t/S_w| dy,
```

There is a second exact stabilization.  With

```text
Y=wS_w-(k-t)S_t,
X=tY+w(k-t)S_w,
```

the physical tangent is `p=X/Y`, but no interval division by `Y` is needed:

```text
kY-X=-(k-t)^2S_t,
h=|kY-X|/(sqrt(X^2+Y^2)sqrt(1+k^2)+Y+kX).
```

Thus the half-angle inherits a double terminal factor directly.  Direct
natural-interval quadrature of `|w_y|` was dependency-limited and was retired
as the practical certificate route.  The completed proof multiplies the
quotient-free half-angle by `|w_y|` and obtains the exact smooth identity

```text
h|w_y|=(k-r)^3(1-y)^2 S_t^2/(S_w Delta),
Delta=sqrt(X^2+Y^2)sqrt(1+k^2)+Y+kX.
```

It combines exact node variation on sign-fixed cells with direct integration
of this nonnegative square on sign-uncertain cells.  Exact first-order interval
jets then pay the phase width once per slab through the mean-value theorem.
The earlier 17-point signed-phase turn probe selected the successful boxes but
is no longer proof authority.  The exact factorizations

```text
k-t=(k-r)(1-y),
C_q(t)=(t-r)10(q(r^2+rt+t^2-3)+3(r+t))
```

are the dependency-reducing forms used by the completed exact checker.  Its
64 phase anchors, 640 point cells per signed arm, and 128 derivative cells per
signed arm prove the uniform paired support bound
`B(q)=e(q)+e(-q)<-1/100` on `[0,q_0]`.

## Claim boundary

The Python checker is the authority for the exact rational interval,
resultant, and Sturm certificate. The Lean companion checks the endpoint
level-curve algebra, terminal polynomial, transverse factorization, and
final rational fan-in.

This note closes exactly the canonical pair at the two endpoint points of the
universal chamber.  The later full-arc certificate closes the rest of
canonical (EX-10).  The weighted wall-sheet maximum principle reduces regular
(EX-W) to one-dimensional double-tight branches and puncture limits, but
direction-dependent simple-hub resolutions at the triple hub can select a
different pair of the three limiting arms.  Those side-pair limits, the other
(EX-W) branches, actual-polynomial real-scale transfer, degree five, and
unrestricted Erdős 1041 remain open.
