# Merge-node separation and the one-root Bergman consumer

This ordinary proof assimilates the September 4 merge-tree return. The
unrestricted parent remains open. The regular-polygon no-go was already in
the corpus; its uniform open-neighbourhood extension and its positive
monodromy companion are the useful additions.

For f(z)=z^n-r^n, 0<r<1, the critical level is r^n. Below it every component
has one root. Above it the sublevel is connected. Put
E={|z^n-r^n|<=r^n}. Polar integration gives

    Area(E)=(r^2/2) integral_{-pi/2}^{pi/2}(2cos theta)^{2/n} dtheta
             >= pi r^2/2.

The inequality is Jensen, using integral log(2cos theta)=0. For any regular
r^n<t<=1, x=r^2/t^{2/n} and q=r^n/t, hence

    Area({|f|<t})/(pi t^{2/n}) log((1+q^{2/n})/(1-q^{2/n}))
      >= x artanh(x) >= r^2 artanh(r^2).

At r=99/100 the last quantity exceeds 2541/1250>2: the logarithm's ratio
19801/199 exceeds 64 and log 2>56/81 follows from the first two terms of
2 sum_{k>=0}(1/3)^{2k+1}/(2k+1). Thus no multi-root node satisfies the
existing scalar certificate.

Fix n and r with this strict inequality. The same positive margin holds
uniformly on a sufficiently small coefficient neighbourhood, across every
regular t<=1 and every multi-root component. Otherwise take a convergent
sequence of counterexamples and levels t_m->t. If t<r^n there are eventually
no critical points below the level and no multi-root components. If t=r^n,
each multi-root component contains a critical point whose normalized value
tends to one; it also contains fixed small neighbourhoods of two limiting
simple roots, so its area stays positive and the logarithm diverges. If
t>r^n, all critical points are below the level, the sublevel is connected,
and area and critical-value convergence give the strict limiting margin.
The critical levels cannot tend to zero. These cases prove uniformity.

Nevertheless this entire neighbourhood satisfies the parent. Choose s>0 with
s^n<min(r^n,1-r^n) and 2(r-s)+2pi s/n<2. Such s exists since r<1.
The value lollipop from zero to -r^n+s^n, around -r^n once on radius s^n,
and back has a lift between adjacent roots of length exactly
2(r-s)+2pi s/n. It stays over |value|<1 and avoids the critical value.
Its full-cycle monodromy and lifted lengths persist under sufficiently small
coefficient perturbations, with strict length and value clearance preserved.

## One-root distance and strict COVER

Let C be a regular degree-k polynomial sublevel component of {|f|<t}, and
h in C. A Riemann map identifies f/t with a finite Blaschke product B of
degree k, with zero preimages b_j. If h corresponds to zeta, then
product_j rho(zeta,b_j)=|f(h)|/t. Some b_j has
rho(zeta,b_j)<= (|f(h)|/t)^{1/k}. Compose the Riemann map with a disc
automorphism taking b_j to zero. The radial segment to zeta has length at most

    sqrt(Area(C)/pi * log(1/(1-(|f(h)|/t)^{2/k}))).          (1)

To see the constant directly, expand the resulting univalent map
phi(z)=sum a_l z^l. Cauchy--Schwarz on the radial length, or the Bergman
restriction operator, gives squared length <= (sum l|a_l|^2)
sum_{l>=1}rho^{2l}/l = Area(C)/pi log(1/(1-rho^2)).
This is the source [BergmanGeodesicInvariance.md](BergmanGeodesicInvariance.md)
with one endpoint moved to zero.

If a connected compact set Gamma in C contains two distinct roots and
|f|<=s on Gamma, and the right squared bound in (1) is strictly below one,
then some two distinct roots have an intrinsic connector of length <2.
Indeed, choose L<1 uniformly above all these distances. The sets of points
of Gamma having distance <L to each root are relatively open and cover
Gamma. If two sets meet, concatenate the two short paths. If none meet,
connectedness forces only one nonempty set; the other root in Gamma then
has distance <L to that root, which already proves the assertion. This
strict formulation avoids a compactness assertion about minimizing geodesics.

Apply this to a descending pair from a least-critical point, with critical
modulus mu, in a regular ancestor component C_t. The sufficient condition is

    Area(C_t)/pi * log(1/(1-(mu/t)^{2/k})) < 1.

Polya's global area estimate and t sufficiently close to one give the
explicit sufficient regime mu<(1-exp(-1))^{n/2}. For a proper component
with k<n roots, use the existing exterior-fibre capacity bound
Area(C_1)/pi <= (k/(2n-k))^{2/n}, or its regular t<1 version, to obtain

    mu < (1-exp(-((2n-k)/k)^{2/n}))^{k/2}.

These are sufficient strict regimes. This note does not infer a sharp
threshold, a universal node crossing, or a global metric theorem from a
critical-value power mean. The regular-polygon failure shows exactly why
weighted averages of strictly failing copies of the same scalar cannot repair it.
