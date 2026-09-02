# The complete finite null-box atlas

## The theorem

Put

\[
s=\sqrt3,\quad q_0={7+4s\over27},\quad
a_0={3\over2}q_0(s-1),\quad
k_*={21+11s\over54},\quad
\beta_*={106+25s\over1221}.
\]

Use the exact homogeneous sextic family and normalized coordinates
\((P,Q,U)\) from SexticNullBranchFiniteTransfer.md, with
\(|P|,|Q|,|U|\le78\). For every \(0<\beta\le\beta_*\), one of the four
adjacent pairs \(j=0,2,3,5\), equipped with

\[
\rho_+^4=q_0+k_*\beta\quad(j=0,2),\qquad
\rho_-^4=q_0-k_*\beta\quad(j=3,5),
\]

gives a complete truncated connector in \(\{H\le0\}\). Its two radial tails
and its joining chord are nonpositive, and its length is \(2-\rho<2\).

Thus the earlier \(10^{-9}\) transfer was not a tiny-parameter accident:
the entire normalized second-order box survives throughout the full
canonical null-branch interval.

## The selector cells are finite polytopes

The four limiting optimized profiles are

\[
\begin{array}{ll}
\Phi_0=o_++P+Q+U,&\Phi_2=o_+-P-Q+U,\\
\Phi_3=o_--P+Q-U,&\Phi_5=o_-+P-Q-U,
\end{array}
\]

where

\[
o_+=-117+{135\over2}s,\qquad o_-=-9+{9\over2}s.
\]

Their common average is

\[
\bar\Phi=-63+36s<-{3\over5}.
\]

Select a smallest profile. Intersecting each selector cone with the cube
\([-78,78]^3\) gives a bounded polytope. Reflection identifies the
\(\Phi_2\)- and \(\Phi_5\)-cells with the \(\Phi_0\)- and \(\Phi_3\)-cells,
so only 17 vertices remain: seven in the first cell and ten in the third.

Let

\[
a=-54+{63\over2}s,\qquad d=78-a.
\]

The seven vertices of the \(\Phi_0\)-cell are

\[
\begin{gathered}
(-78,-78,-78),\ (-78,-78,d),\ (-78,d,-78),\\
(d,-78,-78),\ (d,-d,-78),\ (-d,d,-78),\ (0,0,-a).
\end{gathered}
\]

The ten vertices of the \(\Phi_3\)-cell are

\[
\begin{gathered}
(78,78,78),\ (78,78,d),\ (78,-78,78),\ (78,-78,-78),\\
(78,-d,-78),\ (-78,-78,78),\ (-78,-78,d),\\
(d,-78,-78),\ (d,-d,-78),\ (0,0,-a).
\end{gathered}
\]

Every noncentral vertex has selected profile at most \(-78\). The sole
central equalizer \((0,0,-a)\) has all relevant profiles equal to
\(\bar\Phi\). For fixed \(\beta,t\), the normalized chord is affine in
\((P,Q,U)\); consequently a certificate at these vertices propagates to
the whole selector cell by convexity.

## The two parameter regimes

Write the normalized chord as

\[
N=N_0+\beta N_1+\beta^2N_2+\mathcal R.
\]

For \(0<\beta\le10^{-6}\), the earlier contact calculation can be sharpened
at the central vertex:

\[
|N_1'|<5,\quad |N_1''|<33,\quad |N_2|<1,\quad |N_2'|<4.
\]

Outside \(|t-t_j|<11\beta\), the exact canonical quadratic floor dominates.
Inside that interval, Taylor expansion and completion of the square give

\[
N\le\beta^2(\bar\Phi+56000\beta)
<-\frac12\beta^2.
\]

At every noncentral vertex the coarser all-box estimate suffices:

\[
N\le\beta^2(\Phi_j+40{,}500{,}000\beta)\le0.
\]

For \(10^{-6}\le\beta\le\beta_*\), Taylor's theorem in \(\beta\) gives

\[
N\le N_0+\beta N_1+\beta^2N_2+K\beta^3. \tag{1}
\]

One may take \(K=300\) throughout the full box. Indeed, after writing

\[
A={a_0\over q_0}={3\over2}(s-1),\qquad
B_\pm=\pm{k_*\over q_0},
\]

we have \(0<A<6/5\), \(|B_\pm|<3/2\), and \(\beta_*<1/8\).
Every nonpolynomial factor in the third derivative of \(N\) is a product
of \((1+A\beta)^{\pm1/4}\) and
\((1+B_\pm\beta)^{\pm1/4}\). Their arguments are at least \(13/16\).
Direct differentiation bounds the first three derivatives of either
factor by \(1/2,6/5,7\) in the only large reciprocal term; the two ratio
terms contribute less than 24 in total, and the \((P,U)\)-term contributes
less than 209. The remaining terms have zero third derivative. Hence
\(|\partial_\beta^3N|/6<233<300\).

The central vertex needs the sharper \(K=1/2\). This is proved without
sampling. Expand the three factors

\[
(1+A\beta)^{1/4}(1+B\beta)^{-1/4},\quad
(1+B\beta)^{1/4}(1+A\beta)^{-1/4},\quad
(1+B\beta)^{-1/4}
\]

through degree 20. Since
\(|\binom{\pm1/4}{m}|\le1\), the differentiated discarded tails are
bounded by the geometric majorants with ratios \(27/80\) and \(3/16\).
Their total contribution is less than \(10^{-3}\). Exact
\(\mathbb Q(\sqrt3)\) Bernstein subdivision of the remaining
degree-\((18,3)\) polynomial in \((\beta,t)\) proves

\[
{\partial_\beta^3N\over6}\le\frac12
\qquad(0\le\beta\le\beta_*,\ 0\le t\le1). \tag{2}
\]

Finally, exact bivariate Bernstein certificates show that the right side
of (1) is nonpositive at all 17 vertices: \(K=300\) at the noncentral
vertices and \(K=1/2\) at the equalizer. Reflection and convexity complete
all four cells.

## The radial tails

For a selected sixth-root direction write \(z=\rho y\omega^j\), \(y\ge1\),
and normalize by \(2/\rho^2\). Its radial derivative has the form

\[
A_5(\beta)y^5+B_1(\beta)y+C_0(\beta),
\qquad A_5=-12\rho^4<0. \tag{3}
\]

For \(y\ge1\), the four inequalities

\[
A_5\le0,\quad A_5+B_1\le0,\quad
A_5+C_0\le0,\quad A_5+B_1+C_0\le0 \tag{4}
\]

imply that (3) is nonpositive, regardless of the signs of \(B_1,C_0\).
The same degree-20 binomial expansion gives an absolute tail below
\(10^{-8}\), and exact univariate \(\mathbb Q(\sqrt3)\) Bernstein
certificates verify (4) for both rays at every selector vertex throughout
\([0,\beta_*]\). The chord endpoint is already nonpositive, so each
outward ray remains nonpositive. Since \(0<\rho<1\), the connector length
is \(2-\rho<2\).

## Verification and boundary

The checker reconstructs the selector vertices, the exact chord two-jets,
the differentiated binomial-tail bounds, 17 bivariate chord certificates,
the central cubic certificate, and every radial monotonicity certificate.
Lean formalizes the small-parameter absorption, Taylor handoff,
convex-vertex propagation, and four-way selector.

This closes the full finite homogeneous null-box atlas. It does not yet
classify the other compact sextic coefficient faces, transfer the
homogeneous atlas to every nearby actual polynomial, or settle unrestricted
Erdős #1041. Those are the next proof obligations.
