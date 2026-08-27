# Erdős 1041: a critical Blaschke two-root bound

## Result

Let \(\Omega\) be a simply connected component of \(\{|f|<t\}\) containing
\(k\ge2\) roots and a non-root critical point \(c\).  Choose a Riemann map
\(\phi:\mathbb D\to\Omega\) with \(\phi(0)=c\), and set

\[
B=\frac{f\circ\phi}{t}.
\]

Up to a unimodular constant, \(B\) is a finite Blaschke product of degree
\(k\), \(B'(0)=0\), and its zeros \(\alpha_j\) have radii
\(r_j=|\alpha_j|=\rho_\Omega(c,a_j)\).  Order them as
\(r_1\le r_2\le\cdots\le r_k\), and put

\[
P=|B(0)|=\prod_jr_j=\frac{|f(c)|}{t},
\qquad q(r)=\frac{1-r^2}{r}.
\]

Then

\[
\boxed{q(r_1)\le(k-1)q(r_2)},
\qquad
\boxed{r_2^k\le(k-1)P}.
\]

This is genuine second-root information.  A bare product bound controls only
\(r_1\).

## Proof

For \(b_\alpha(z)=(z-\alpha)/(1-\bar\alpha z)\),

\[
\frac{b_\alpha'(0)}{b_\alpha(0)}
=-\frac{1-|\alpha|^2}{\alpha}.
\]

Logarithmic differentiation of \(B\) at zero and \(B'(0)=0\) give

\[
\sum_{j=1}^k\frac{1-r_j^2}{\alpha_j}=0.
\]

These are the sides of a closed polygon, with lengths \(q(r_j)\).  Since
\(q\) is decreasing,

\[
q(r_1)\le\sum_{j=2}^kq(r_j)\le(k-1)q(r_2).
\]

Moreover

\[
\frac{q(r_1)}{q(r_2)}
=\frac{r_2}{r_1}\frac{1-r_1^2}{1-r_2^2}
\ge\frac{r_2}{r_1},
\]

so \(r_2\le(k-1)r_1\).  Since every later radius is at least \(r_2\),

\[
P\ge r_1r_2^{k-1}\ge\frac{r_2^k}{k-1}.
\]

For the sharp implicit form, let \(x_k(r)\in(0,r]\) solve
\(q(x_k(r))=(k-1)q(r)\).  Then

\[
\boxed{P\ge x_k(r_2)r_2^{k-1}.}
\]

## Target-deciding Bergman corollary

The two selected zeros lie in the pseudohyperbolic disk of radius \(r_2\)
about zero, hence

\[
\rho_\Omega(a_1,a_2)\le\frac{2r_2}{1+r_2^2}.
\]

`BergmanGeodesicInvariance.md` proves that their hyperbolic geodesic in
\(\Omega\) has Euclidean length \(L\) satisfying

\[
L^2\le\frac{\operatorname{Area}(\Omega)}\pi
\log\frac1{1-\rho_\Omega(a_1,a_2)^2}
\le\frac{2\operatorname{Area}(\Omega)}\pi
\log\frac{1+r_*^2}{1-r_*^2},
\]

where \(r_*\) is either the sharp implicit upper bound or
\(\min(1,((k-1)P)^{1/k})\).  Thus a root path of length at most two is proved
whenever

\[
\boxed{\frac{\operatorname{Area}(\Omega)}\pi
\log\frac{1+r_*^2}{1-r_*^2}\le2.}
\]

Using Pólya's \(\operatorname{Area}\{|f|\le t\}\le\pi t^{2/n}\), a simple
level-one sufficient condition is

\[
((k-1)|f(c)|)^{2/k}\le\tanh(1).
\]

The exact area and the implicit radius make the criterion strictly stronger.

## Higher critical multiplicity

If \(c\) has critical multiplicity \(m\), then
\(B(z)=B(0)+O(z^{m+1})\).  Expanding the logarithm of each Blaschke factor gives
the exact cancellations

\[
\boxed{\sum_j\left(\alpha_j^{-q}-\bar\alpha_j^{,q}\right)=0,
\qquad 1\le q\le m.}
\]

These moments explain why the simple first-moment estimate degenerates near
the regular-polygon equality family: the coalesced critical point carries a
whole block of cancellations.  A full proof still needs a clustered trace or
connector theorem that spends those higher moments rather than discarding
them.

## Verification and claim boundary

`CriticalBlaschkePairBound.lean` checks the scalar implication from polygon and
product bounds to \(r_2^k\le(k-1)P\).  The executable checker verifies the
implicit inversion, explicit domination, equality calibration, and Bergman
threshold on adversarial parameter grids.

This closes a new all-degree sufficient region and supplies a sharper analytic
interface to the global problem.  It does not settle the pinched regime
\(P\to1\), and therefore does not by itself solve unrestricted Erdős 1041.
