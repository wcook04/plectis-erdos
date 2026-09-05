<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: Apache-2.0 -->

# A pointwise bound for critical values in a disk

Let \(f\in\mathbb C[z]\) be monic of degree \(n\ge2\), with every root
in the closed unit disk. List the roots of its derivative, with their
algebraic multiplicities, as \(c_1,\ldots,c_{n-1}\). Then
\[
 |f(c_j)|\le\prod_{k=1}^{n-1}|1-\overline{c_j}c_k|
 \qquad(1\le j\le n-1).                                      \tag{1}
\]
This ordinary proof bounds each critical value using the actual critical
points. It therefore gives the free-point-to-critical-value implication
without moving the roots to the unit circle or using plurisubharmonicity.
No Lean verification or novelty claim is made for this note.

## The reflected derivative

First suppose all roots \(a_1,\ldots,a_n\) satisfy \(|a_i|<1\).
Gauss–Lucas places every \(c_k\) in the open unit disk. Define
\[
 N(z)=nf(z)-zf'(z),\qquad
 G(z)=n\prod_{k=1}^{n-1}(1-\overline{c_k}z).
\]
The monicity convention gives \(f'(z)=n\prod_k(z-c_k)\). Thus \(G\)
is the reflected derivative:
\[
 G(z)=z^{n-1}\overline{f'(1/\bar z)}\quad(z\ne0).
\]
The product defines it at zero as well, where \(G(0)=n\). If
\(f'(z)=\sum_{\ell=0}^{n-1}b_\ell z^\ell\), its coefficient definition
is \(G(z)=\sum_{\ell=0}^{n-1}\overline{b_\ell}z^{n-1-\ell}\).
In particular, critical points equal to zero cause no difficulty.
For \(|z|\le1\), every factor of \(G(z)\) is nonzero, since
\(|\overline{c_k}z|<1\).

On \(|\zeta|=1\), the logarithmic derivative satisfies
\[
 w=\frac{\zeta f'(\zeta)}{f(\zeta)}
   =\sum_{i=1}^n\frac1{1-a_i\bar\zeta},\qquad
 \operatorname{Re}\frac1{1-a_i\bar\zeta}
 =\frac12+\frac{1-|a_i|^2}{2|1-a_i\bar\zeta|^2}>\frac12.
\]
Consequently
\[
 |n-w|^2-|w|^2=n^2-2n\operatorname{Re}w<0,
 \qquad |N(\zeta)|<|f'(\zeta)|=|G(\zeta)|.      \tag{2}
\]
The quotient \(N/G\) is holomorphic on a neighborhood of the closed disk.
The maximum-modulus principle and (2) give \(|N(z)|<|G(z)|\) throughout
that disk: the continuous boundary quotient attains a maximum strictly less
than one. At \(z=c_j\), \(N(c_j)=nf(c_j)\), so dividing by \(n\)
gives (1), strictly in this open-root case. Finally
\(|1-\overline{c_k}c_j|=|1-\overline{c_j}c_k|\) by conjugation.

For roots in the closed disk, take \(0<r<1\) and set
\[
 f_r(z)=r^n f(z/r)=\prod_{i=1}^n(z-ra_i).
\]
This polynomial is monic, and
\(f_r'(z)=r^{n-1}f'(z/r)\). Its critical points are exactly
\(rc_1,\ldots,rc_{n-1}\), with the same multiplicities. The open-root
case yields
\[
 r^n|f(c_j)|\le\prod_{k=1}^{n-1}
      |1-r^2\overline{c_j}c_k|.
\]
Letting \(r\uparrow1\) proves (1) by continuity of a finite product.
This also handles repeated critical points, boundary critical points, and
critical points that are roots of \(f\); no simple-root assumption or
choice of varying root branches occurs.

The same limiting argument proves the stronger polynomial comparison
\[
 |nf(z)-zf'(z)|\le n\prod_k|1-\overline{c_k}z|,
 \qquad |z|\le1:                                            \tag{3}
\]
apply the open-root comparison to \(f_r\) at \(rz\), then let
\(r\uparrow1\). The useful numerator is \(nf-zf'\), whose value at a
critical point is \(nf\); estimating \(f\) on the circle alone loses
the factor needed in (1).

When every \(|a_i|=1\), put \(\alpha=(-1)^n\prod_i a_i\).
Then \(|\alpha|=1\) and the self-inversive identity
\(f(z)=\alpha z^n\overline{f(1/\bar z)}\) gives, by comparing
coefficients, \(N=\alpha G\). Thus (1) is an equality at every critical
point in this case, including repeated and boundary critical points.

The boundary reflection comparison is a classical polynomial-inequality
ingredient; see the proof of Lemma 5 in Singh, Shah and Liman,
[A generalized inequality for the polar derivative of a polynomial](https://link.springer.com/article/10.1186/1029-242X-2013-183)
(2013). The argument above supplies the particular interior and critical-value
consequences directly; it does not assert their priority.

## The finite-point consumer

For \(m\ge1\), let \(\mathrm{FP}_m\) denote the statement that arbitrary
\(u_1,\ldots,u_m\) in the closed unit disk satisfy
\[
 \sum_{j=1}^m\left(\prod_{k=1}^m
       |1-\overline{u_j}u_k|\right)^{1/m}\le m.
\]
Set \(m=n-1\). Gauss–Lucas and (1) show that \(\mathrm{FP}_m\) gives
\(\sum_j y_j\le m\), where \(y_j=|f(c_j)|^{1/m}\). The scalar inequality
\[
 y^{m/(m+1)}\le\frac{my+1}{m+1}\qquad(y\ge0)
\]
then yields
\[
 \sum_{j=1}^{n-1}|f(c_j)|^{1/n}\le n-1.                     \tag{4}
\]
If the roots of a monic polynomial \(f\) lie in a disk centered at
\(h\) of radius \(R>0\), apply (4) to
\(F(w)=R^{-n}f(h+Rw)\). Its critical points are \((c_j-h)/R\),
and its critical values are \(R^{-n}f(c_j)\). Hence
\[
 \sum_{j=1}^{n-1}|f(c_j)|^{1/n}\le(n-1)R.
\]
For \(R=0\), \(f(z)=(z-h)^n\) and every critical value vanishes.
The disk need not be a minimum enclosing disk. The constant is attained by
\(f(z)=(z-h)^n-\lambda\) with \(R=|\lambda|^{1/n}\).

The established finite-point cases \(m\le4\) therefore give the budget in
degrees two through five. For higher degrees this implication still requires
\(\mathrm{FP}_{n-1}\). In every degree a value budget alone supplies no
inverse-ray length bound or path selector; that metric step remains separate.
