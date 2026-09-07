# Erdős 1041: qualitative model-to-real transfer by the actual trace-min hub

Date: 2026-08-30.  Checker:
`scripts/check_erdos1041_quintic_trace_min_qualitative_transfer.py`.

## 1. Point of the reduction

The finite real polynomial should not be forced to use the hub selected by
the leading model.  That selection is false at visible finite scale
(`QuinticModelRealTransferLaw.md`).  The correct selector is already present
in the finite polynomial: among its four critical points choose one at which
`|f(c)|` is least.  This hub is automatically admissible, and after blow-up
every subsequential limit of such hubs is trace-maximal for the limiting
two-mode model.  Consequently a strict **all-sheet** form of `(EX-U)` transfers
qualitatively to an actual near-pentagon neighbourhood without any explicit
remainder constant.

This is a reduction, not a proof of `(EX-U)`.  Its useful content is that the
finite-scale hub-selection anomaly creates no additional theorem after the
compact double-tight atlas is closed.

## 2. Exact finite identities

Let a centred/gauged near-pentagon quintic be written, without translating the
physical `z`-plane, as

```text
f_r(rw)=q_r+r^5 P_r(w),
P_r(w)=w^5+d_{4,r}w^4+d_{3,r}w^3+b_{2,r}w^2+b_{1,r}w.       (T1)
```

Here `r>0`, `q_r=f_r(0)`, and in the transverse near-Fekete chart

```text
d_{4,r}->0,  d_{3,r}->0,
(b_{1,r},b_{2,r})->(b_1,b_2),  max(|b_1|,|b_2|)=1.          (T2)
```

The estimates in `QuinticTransverseFiniteTransfer.md` §2 (Fourier pairing,
`eta <= (24/5)r^3`, and the paired cubic) give exactly (T1)--(T2), after
passing to a subsequence and the usual domain/range gauges.  Put

```text
H(w)=w^5+b_2w^2+b_1w,
qhat_r=q_r/|q_r|,
M_r(w)=-conj(qhat_r)P_r(w),  M=-conj(qhat)H.                (T3)
```

For two critical points `rw_i,rw_j`, the following ordering identity is
exact:

```text
|f_r(rw_i)|^2-|f_r(rw_j)|^2
 = -2 r^5 |q_r| Re(M_r(w_i)-M_r(w_j))
   +r^10(|P_r(w_i)|^2-|P_r(w_j)|^2).                      (T4)
```

Thus a minimizer of the finite critical-value modulus can only limit to a
maximizer of `Re M` on the limiting critical fibre.

The finite descending value segment has an equally exact normalized form.
Writing

```text
f_r(rw)=t f_r(rw_c),  0<=t<=1,
s=(1-t)|q_r|/r^5,
```

gives

```text
M_r(w)=M_r(w_c)+s(1-(r^5/|q_r|)M_r(w_c)).                 (T5)
```

Hence its two inverse lifts converge to the rightward inverse-ray lifts from
the limiting trace-maximal hub.  The direction error in (T5) is `O(r^5)`;
the finite ray has terminal parameter `|q_r|/r^5 -> infinity`.

Finally, if the two finite lifts land at roots `a_i=rw_i`, `a_j=rw_j`, their
excess scales with no error at all:

```text
L_r(c)-(|a_i|+|a_j|)
 =r [ length(w_c to w_i)+length(w_c to w_j)-|w_i|-|w_j| ]. (T6)
```

The checker symbolically replays (T4)--(T6), as well as the critical-product
identity used below.

## 3. The all-sheet transfer theorem

Let `C_5` be the compact trace-max chamber of
`QuinticTraceMaxUniversalChamber.md`.  At repeated critical values, interpret
the rightward pair excess on the stable all-sheet compactification: every
pair obtained as a limit of simple ray-separated quintics is retained.  This
is precisely the boundary object certified by the double-tight carrier and
its exceptional fibres, not a choice of one favoured branch.

> **Theorem (trace-min qualitative transfer).**  Assume the strict all-sheet
> universal excess theorem:
>
> ```text
> (EX-U+)  every compactified rightward pair at every trace-maximal hub
>          of every non-pure H=w^5+b_2w^2+b_1w has pair excess <0.       (T7)
> ```
>
> Then there is `r_0>0` such that every ray-separated monic quintic in the
> transverse near-pentagon chart with `0<r<r_0` has an admissible critical
> point `c` whose two descending arms have total length `<2`.
>
> Consequently, by the radial branch and the already proved generic-density /
> lower-semicontinuity bridge, `(EX-U+)` closes an (ineffective but genuine)
> actual quintic neighbourhood of the regular pentagon.  No separate
> model-hub remainder theorem is required.

### Proof

Suppose otherwise and take a counterexample sequence `f_r`, `r->0`.  Choose
`c_r` among the four critical points so that `|f_r(c_r)|` is minimal.
The critical-product identity is

```text
5^5 product_{f_r'(c)=0}|f_r(c)|=|disc(f_r)|<=5^5,          (T8)
```

where the last inequality is the sharp Fekete bound for five points in the
closed unit disk.  Hence `|f_r(c_r)|<=1`: the chosen hub is admissible.

After taking subsequences, (T2) gives a limiting core model and the normalized
critical point `c_r/r` converges to a critical point `w_*` (multiplicity is
allowed).  Identity (T4) shows that `w_*` maximizes `Re M` among all limiting
critical points.  Indeed, a strict gap from some other critical point would,
for small `r`, dominate the `r^10` term in (T4), contradicting the choice of
`c_r`.  This argument automatically handles the tangent orbit: there all
four leading critical levels tie, so the finite selector is free to choose
whichever sheet its next-order term prefers, and every such limit remains in
the all-sheet trace-max fibre.

The normalized arms satisfy (T5).  On each compact part of the open ray,
inverse branches converge by the implicit-function theorem; at the initial
critical point the holomorphic normal form gives an integrable
`s^{1/(m+1)-1}` majorant.  Uniformly on the compact coefficient core, the
large-`s` inverse branches have

```text
w(s)=u s^(1/5)+O(1),       w'(s)=(u/5)s^(-4/5)+O(s^(-1)),
```

and their support-defect integrand is `O(s^(-6/5))`.  Thus the omitted tail
is `O(S^(-1/5))`, uniformly.  Repeated starting values are dealt with by
taking the finite collection of local branches in the stable all-sheet
compactification.  It follows from (T5) that, after another subsequence, the
bracket in (T6) converges to one of the compactified rightward pair excesses
at `w_*`.

By (T7) that limit is strictly negative.  Therefore the bracket in (T6) is
negative for all sufficiently large indices.  Since the two terminal roots
lie in the closed unit disk,

```text
L_r(c_r)<|a_i|+|a_j|<=2,
```

contradicting the counterexample assumption.  QED

## 4. Why strict pointwise `(EX-U+)` is enough

No numerical global margin is an extra hypothesis.  The chamber and its
stable all-sheet fibre are compact, and the excess is upper-semicontinuous by
the same compact/tail argument in the proof.  Therefore strict negativity at
every sheet implies a uniform margin `-delta<0`.  The current double-tight
program is exactly the missing verification of those sheets; once its
regular truncations are certified, the exceptional `mu=-10`, `mu_*`, event,
and tangent certificates already supply the boundary.

This also explains the finite-scale anomaly in
`QuinticModelRealTransferLaw.md`: the model-selected and finite trace-min hubs
may differ at a visible `r`, but (T4) forces every limit of the latter into the
trace-max model fibre.  The anomaly affects an effective value of `r_0`; it
does not create a new qualitative obstruction.

## 5. Exact open boundary

This theorem does **not** prove `(EX-U+)`; it removes only the downstream
model-to-real selection/remainder gap.  It also does not cover the compact
middle of degree five or any higher degree.  For use in the parent chain the
double-tight atlas must certify every stable limiting pair, not merely one
arbitrarily labelled branch at a repeated value.  If a future atlas omits a
stable sheet, the argument above correctly stops at that omission.

Evidence class: ordinary complex-analysis reduction; exact algebra is replayed
by the checker.  No novelty or external-review claim.
