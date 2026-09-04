# Erdős 1041: the degree-three theorem

## Result

Let

\[
  f(z)=\prod_{j=1}^3(z-z_j),\qquad |z_j|<1,
\]

with the roots listed with multiplicity.  Then two listed roots can be joined
inside `|f|<1` by a polygonal path of length strictly below `2`.  If the cubic
is squarefree, the two roots are distinct.

This proves the cubic case of Erdős #1041.  It does **not** prove the
unrestricted problem.  The point of the argument is structural: among the two
critical points, the one with smaller critical-value modulus supplies both the
metric scale and straight-spoke containment.  The quintic counterexample to a
prescribed critical point therefore does not occur in degree three.

## 1. The normalized zero-count lemma

For `b` in `C`, put

\[
  P_b(w)=w^3-\frac32bw^2+1.
\]

**Lemma.**  If

\[
  \left|1-\frac{b^3}{2}\right|\ge 1,
\]

then `P_b` has at least two zeros, counted with multiplicity, in the closed
unit disc.

First assume that the displayed inequality is strict.  A zero `w` of `P_b`
on the unit circle would give

\[
  b=\frac23(w+w^{-2}).
\]

Writing `w^3=e^{2iu}` and `c=cos u`, direct calculation gives

\[
 \left|1-\frac{b^3}{2}\right|^2
 =1+\frac{64}{729}c^4(16c^2-27)\le1.
\]

The inequality is strict unless `c=0`; in that exceptional case `b=0` and
the left side equals one.  Thus no `P_b` in the strict region has a unit-circle
zero.

The radial deformation `b -> s b`, `s>=1`, remains in the strict region:
if `z=b^3/2`, then

\[
 |1-z|^2>1 \quad\Longleftrightarrow\quad |z|^2>2\Re z,
\]

and hence

\[
 |1-s^3z|^2-1
 =s^3\bigl(s^3|z|^2-2\Re z\bigr)>0.
\]

For sufficiently large `s`, Rouché's theorem on `|w|=1` compares `P_{sb}`
with `-(3/2)sbw^2`, because the latter has modulus `(3/2)s|b|>2` while
`|w^3+1|<=2`.  Therefore `P_{sb}` has exactly two zeros in the open unit
disc.  The zero count cannot change along the deformation because no zero
crosses the unit circle.  This proves the strict case.

For equality, scale by `s>1` and let `s` decrease to one.  Continuity of the
multiset of polynomial roots leaves at least two zeros in the closed unit
disc.  If `b=0`, all three zeros of `w^3+1` already lie on the unit circle.

## 2. Why a small normalized zero gives a safe spoke

If `P_b(w)=0`, then for `0<=t<=1`

\[
  P_b(tw)=1-t^2-t^2(1-t)w^3.
\]

Consequently, when `|w|<=1`,

\[
 |P_b(tw)|
 \le (1-t^2)+t^2(1-t)|w|^3
 \le 1-t^3\le1.

Thus the whole straight segment from `0` to `w` is safe.  The identity and
norm estimate are Lean-checked in `CubicCriticalHub.lean`.

## 3. Reduction of a cubic to the lemma

Multiple roots settle the statement by a constant path, so suppose `f` is
squarefree.  A standard component/critical-point count for polynomial
lemniscates says that a component containing two roots contains a critical
point.  The Erdős--Herzog--Piranian component lemma therefore gives a critical
point with critical-value modulus below one.

First suppose `f'` has two distinct zeros.  Choose a critical point `c` for
which `|f(c)|` is minimal, write the other one as `c+delta`, and put `v=f(c)`.
The derivative and monicity give the exact Taylor expansion

\[
  f(c+d)=d^3-\frac32\delta d^2+v.

\]

Here `0<|v|<1`; the zero case would make `f` nonsquarefree.  Choose `alpha`
with `alpha^3=v`, and set `b=delta/alpha`.  Dividing the preceding display by
`v` gives

\[
  \frac{f(c+\alpha w)}{v}=P_b(w).

\]

At the other critical point,

\[
  f(c+\delta)=v-\frac{\delta^3}{2}
             =v\left(1-\frac{b^3}{2}\right).

\]

Minimality of `|v|` is exactly the hypothesis of the normalized zero-count
lemma.  Select two normalized roots `w_1,w_2` with `|w_i|<=1`.  Section 2
shows that the two segments from `c` to `c+alpha*w_i` lie in `|f|<=|v|<1`.
Their combined length is at most

\[
  2|\alpha|=2|v|^{1/3}<2.

\]

The two selected zeros are distinct in the squarefree case.

If `f'` has a double zero `c`, then `f(c+d)=d^3+v`.  Its three roots are
`c+alpha`, `c+alpha*omega`, `c+alpha*omega^2`.  Since all three lie in the open
unit disc, averaging their squared moduli gives

\[
 |c|^2+|\alpha|^2<1,

\]

so `|alpha|<1`.  Any two radial spokes have total length `2|alpha|<2`, and
along either spoke the polynomial value has modulus `|v|(1-t^3)<1` away from
the root endpoint (and is zero there).

This completes the cubic theorem.

## Claim boundary and next analytic target

The unrestricted Erdős problem remains open.  What survives from this proof
in higher degree is the selection principle: use a critical point of minimal
critical-value modulus, normalize that value to one, and seek at least two
small root sheets whose descending paths have a length budget below two.  The
cubic succeeds because the entire normalized polynomial has the sparse form
`w^3-(3/2)bw^2+1`, so a small root controls the complete straight spoke.  A
higher-degree proof needs a replacement for that sparsity, not another scan of
critical hubs.
