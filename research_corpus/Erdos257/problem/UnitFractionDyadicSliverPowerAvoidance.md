# Unit-fraction power avoidance at the dyadic sliver

## Status

This note records an exact integer form of the skipped-rank dyadic
undershoot, together with a stronger unit-fraction conjecture suggested by
exhaustive exact searches.  The conjecture is **not proved**.  If true, it
would prove the required undershoot for `1/465` (indeed for every odd unit
fraction), so the finite searches below are discovery evidence only.

Put

\[
 w_d=\frac1{2^d-1},\qquad
 \sigma_F=\sum_{d\in F}w_d,
 \]

where \(F\subset\{1,\ldots,m-1\}\) is finite.  Let the target be the odd
unit fraction \(x=1/D\), and assume the residual

\[
 r=\frac1D-\sigma_F
\]

is positive and rank \(m\) is skipped, so \(r<w_m\).

## 1. Reciprocal powers are the exact obstruction

Write \(r=a/b\) in lowest terms.  Every denominator in the construction is
odd, hence \(b\) is odd and equality \(r=2^{-m}\) is impossible.  Therefore

\[
 2^{-m}\le r<w_m
 \quad\Longleftrightarrow\quad
 (2^m-1)a<b<2^ma
 \quad\Longleftrightarrow\quad
 \boxed{\left\lceil\frac ba\right\rceil=2^m}.       \tag{1}
\]

Thus the desired theorem says that the reciprocal ceiling of a residual is
never an exact power of two at a skipped rank.  Between two selected ranks
the residual is fixed, so (1) says more operationally that the reciprocal
ceiling created by the preceding take must avoid powers of two.

If \(z=1/r\) and rank \(n\) is taken, the exact reciprocal update is

\[
 \boxed{
 z\longmapsto \frac{(2^n-1)z}{2^n-1-z}.}             \tag{2}
\]

The live problem can consequently be viewed as power avoidance for the
source-coupled orbit of the Mobius maps (2).  This is not true for arbitrary
starting rationals: for example \(x=7/15\) takes rank \(2\), leaves
\(r=2/15\), and then skips rank \(3\) with
\(\lceil1/r\rceil=8\).  The unit numerator in \(1/D\), not merely an odd
denominator or a shift-minimal binary word, is essential to the conjecture.

## 2. The exact denominator interval

Use the unreduced common denominator

\[
 P=\prod_{d\in F}(2^d-1),\qquad
 S=\sum_{d\in F}\frac{P}{2^d-1},
 \]

so \(\sigma_F=S/P\).  A dangerous skipped residual is equivalent to

\[
 \sigma_F+2^{-m}\le\frac1D
 <\sigma_F+\frac1{2^m-1}.
\]

After inversion this becomes the exact interval

\[
 \boxed{
 \frac{(2^m-1)P}{P+(2^m-1)S}
 <D\le
 \frac{2^mP}{P+2^mS}.}                            \tag{3}
\]

For nonempty \(F\), its width is exactly

\[
 \boxed{
 \frac{P^2}
 {(P+(2^m-1)S)(P+2^mS)}<1.}                       \tag{4}
\]

Hence each Boolean prefix has at most one dangerous unit-fraction target.
This is a min-entropy statement in the target denominator: the whole dyadic
sliver can contain at most one integer, rather than merely having small real
measure.

If an integer \(D\) did lie in (3), put

\[
 R=P-DS,qquad
 u=2^mR-DP,qquad v=R-u.
\]

Then the corridor is exactly

\[
 \boxed{R>0,\qquad 0\le u<R,\qquad u+v=R,}         \tag{5}
\]

with the left equality \(u=0\) excluded when \(D\) is odd.  Thus
\(u,v>0\), and \(u\) is odd.  Equations (3)--(5) expose the remaining
arithmetic question sharply: prove that the special Mersenne product/sum
pair \((P,S)\), with every exponent below \(m\), cannot split its residual
numerator in this way for an odd integer \(D\).

## 3. Stronger conjecture and exact evidence

The computation suggests the following statement, which does not use
greedy reachability.

> **Unit-fraction sliver conjecture.**  For every nonempty finite
> \(F\subset\{2,\ldots,m-1\}\), the interval (3) contains no integer.

The companion exact-rational audit exhausts all
\(2^{m-2}-1\) nonempty subsets for each \(m\le22\); it finds no integer in
(3).  It also
runs the actual Mersenne-greedy algorithm for every odd \(D<20000\) through
rank \(200\), again finding no power ceiling at a skip.  Independent random
tests of 200 odd denominators below \(10^{30}\) through rank \(350\) also
found none.  These are finite observations and do not establish the
conjecture.

The absence persists well beyond product targets in the computation, while
the numerator-\(7\) example above fails immediately.  This separates the
new candidate law from period 20, anchor 25, divisor density, and the
affine-cylinder language: it is a source-numerator/Farey separation law for
Boolean Mersenne prefixes.  Proving (or finding a counterexample to) that
law is the substantive next step; merely extending the search depth is not
a proof.

## 4. Source-coupling the affine `1^19 0` counterfamily

`AnchorFourFiveAffineCylinderMinEntropyNoGo.md` constructs dangerous
period-20 cylinders from

\[
 \rho_{m,k}=\frac{k}{k2^m-1},\qquad
 X_{m,k}=\rho_{m,k}+\sum_{d=m-19}^{m-1}w_d.
\]

That construction starts from a freely chosen rational.  Requiring it to
come from a unit fraction imposes a rigid divisor congruence.  Write

\[
 P=\prod_{d=m-19}^{m-1}(2^d-1),\qquad
 T=\sum_{d=m-19}^{m-1}\frac{P}{2^d-1},\qquad
 A=P+2^mT,\qquad h=kA-T.
\]

Then

\[
 \frac1{X_{m,k}}=\frac{P(k2^m-1)}h,                    \tag{6}
\]

and direct elimination gives

\[
 \boxed{A\,P(k2^m-1)-P2^m h=-P^2.}                   \tag{7}
\]

Consequently, if the freely constructed cylinder starts at a unit fraction,
then necessarily

\[
 \boxed{h\mid P^2,\qquad h\equiv-T\pmod A.}           \tag{8}
\]

Moreover, an odd unit denominator forces \(k\) even: the numerator in (6)
is odd, while \(h=kA-T\) is odd exactly when \(k\) is even.  Thus the affine
counterfamily reaches the unit-fraction source only if a divisor of the full
Mersenne product square hits one specified residue class.  This is a concrete
primitive-factor/LCM target for (rather than a refutation of) the conjectural
source law.
