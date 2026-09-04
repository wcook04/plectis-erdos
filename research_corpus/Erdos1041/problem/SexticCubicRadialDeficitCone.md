# A quantitative radial-deficit staple at the sextic cubic face

## The theorem

Consider the complete finite sextic Fourier model

\[
 G(z)=-\Delta+\operatorname{Re}
 \left(E_1z+E_2z^2+E_3z^3+E_4z^4+E_5z^5-z^6\right).
\]

Assume

\[
 0<\Delta\le1,qquad |E_3|\le1,qquad
 |E_1|+|E_2|+|E_4|+|E_5|\le\Delta. \tag{1}
\]

Put \(s=\Delta/4\), and let \(\omega=e^{\pi i/3}\).  There is a parity
\(\varepsilon\in\{1,-1\}\) such that all three sixth-root directions with
\(\omega^{3j}=\varepsilon\) have nonpositive cubic projection.  Every one of
those three radial arms from \(s\omega^j\) to \(\omega^j\) is contained in
\(\{G<0\}\), while the entire disk \(|z|\le s\) satisfies the stronger bound

\[
 G(z)\le-\Delta/2. \tag{2}
\]

Consequently any two directions in the selected parity class give a complete
three-segment staple inside \(\{G<0\}\).  Their angular separation is
\(2\pi/3\), so the length is

\[
 2(1-s)+\sqrt3,s=2-(2-\sqrt3)s<2. \tag{3}
\]

This is an explicit full-dimensional cubic-face stability cone.  It repairs
the singularity exposed by `SexticCubicFaceConnectorNoGo.md`: a monolithic
positive-radius homogeneous atlas is false when the constant deficit is
discarded, but the disk-root geometry supplies precisely such a negative
deficit, and it buys an inner safe disk.

## Proof

Choose \(\varepsilon=-1\) when \(\operatorname{Re}E_3\ge0\), and
\(\varepsilon=1\) otherwise.  On a sixth-root ray \(z=t\omega^j\) with
\(\omega^{3j}=\varepsilon\),

\[
 \operatorname{Re}(E_3z^3)
 =t^3\varepsilon\operatorname{Re}E_3\le0.
\]

For \(0<t\le1\), every other power is at most one in modulus, and (1) gives

\[
 G(t\omega^j)
 \le-\Delta+\Delta t-t^6<0. \tag{4}
\]

For \(|z|=u\le s\), the four nuisance modes contribute at most
\(\Delta u\), the cubic contributes at most \(u^3\), and the absolute value
of the sextic term is at most \(u^6\).  Since \(u\le\Delta/4\) and
\(\Delta\le1\),

\[
 \Delta u\le{\Delta\over4},\qquad
 u^3\le{\Delta\over64},\qquad
 u^6\le u^3\le{\Delta\over64}.
\]

Therefore

\[
 G(z)\le-\Delta+{9\Delta\over32}
 <-{\Delta\over2},
\]

which proves (2).  Convexity of the disk contains the inner chord, and (3)
proves the strict metric budget.

## Why the deficit is not optional

The first secondary blow-up around the pure cubic face is

\[
 \operatorname{Re}(Pz+Qz^2+z^3).
\]

A bounded adversarial scout found phase choices for which every odd
root-direction ray has a positive excursion; the best truncated score tends
to zero only as the radius tends to zero.  This is consistent with the exact
positive-radius no-go theorem and shows that a coefficient-norm neighborhood
without \(-\Delta\) is not the correct stability statement.

For actual perturbed roots, however,

\[
 \Delta=-\operatorname{Re}E_0
 \ge {1\over2}\sum_k|e_k|^2.
\]

At a cubic/Nyquist scale, \(|E_3|\) is first order in the perturbation and
the sextic scale is \(|E_3|^2\), exactly the scale of \(\Delta\).  The theorem
above is therefore the natural radial-deficit chart, not an artificial extra
hypothesis inserted after the computation.

## Boundary and handoff

Closed here: the complete model cone (1), including all five Fourier modes,
with explicit value margin, truncation radius, three-ray supply, and strict
length slack.  Lean checks all scalar inequalities and the parity selector;
the exact checker independently replays the constants and sixth-root geometry.

Still open: prove that every actual sextic perturbation sufficiently near the
cubic face either enters (1) after its natural normalization or falls into a
complementary transverse chart; then absorb the origin-anchored logarithmic
remainder.  The next owner should use Parseval, tangent pairing, and the
already-proved radial-energy inequality to classify that complement.  This
theorem does not by itself settle all sextics or unrestricted Erdős #1041.
