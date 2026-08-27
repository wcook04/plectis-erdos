# A certified open mixed sextic connector cell

This note thickens the explicit genuinely mixed fixture from
`SexticMixedOriginSpokeNoGo.md`.  It is the first literal open coefficient cell
in the residual moderate mixed band.

Write

\[
H_{A,B}(z)=\Re\!\left(Az+Bz^2-\overline Bz^4-\overline Az^5-z^6\right).
\]

At the exact endpoint, the coefficients are

\[
A_0=-{\sqrt3\over8}+{i\over8},\qquad
B_0=-{\sqrt6+\sqrt2\over4}
       +i\,{\sqrt2-\sqrt6\over4}.
\]

Let \(\omega=e^{\pi i/3}\), use the two ray tails
\(t\) and \(t\omega\) for \(2/3\le t\le1\), and join their initial points by

\[
z(u)={2\over3}((1-u)+u\omega),\qquad 0\le u\le1.
\]

The previous exact Bernstein calculation gives

\[
H_{A_0,B_0}(z(u))\le -10^{-3}.                    \tag{1}
\]

If \(A=A_0+\Delta A\), \(B=B_0+\Delta B\), then on \(|z|\le1\)

\[
|H_{A,B}(z)-H_{A_0,B_0}(z)|
 \le |\Delta A|(|z|+|z|^5)+|\Delta B|(|z|^2+|z|^4)
 \le 2|\Delta A|+2|\Delta B|.                    \tag{2}
\]

Thus \(|\Delta A|,|\Delta B|\le10^{-4}\) costs at most
\(4\times10^{-4}\), and (1) leaves the whole joining chord below
\(-6\times10^{-4}\).

The direction-one endpoint tail has the stronger exact bound

\[
H_{A_0,B_0}(t\omega)\le-{41\over2916},            \tag{3}
\]

obtained from

\[
Q(t)\ge {41\over81},\qquad
Q(t)=24t^5-5t^4+18t^3-18t+5,
\]

and the comparison \(H(t\omega)\le-tQ(t)/24\).  The perturbation budget in
(2) is therefore harmless on that tail.  On the direction-zero tail, the
two low-mode projections remain negative throughout the coefficient ball;
the factorization into \((t-t^5)\), \((t^2-t^4)\), and \(-t^6\) makes the
sign immediate.

Consequently the same adjacent pair and the same rational radius work for
the entire product ball

\[
|A-A_0|\le10^{-4},\qquad |B-B_0|\le10^{-4}.        \tag{4}
\]

Lean checks the exact complex-to-real chord identity, the unit-disk norm
bounds, the perturbation estimate, (3), both ray tails, and the combined
coefficient-ball theorem `coefficient_ball_connector`.

This is not yet the finite atlas and does not solve Erdős #1041.  It converts
one computationally discovered point into a rigorous open set with explicit
radius and slack.  The next atlas step is to enlarge or symmetry-transport
this cell and locate the next uncovered boundary fixture.
