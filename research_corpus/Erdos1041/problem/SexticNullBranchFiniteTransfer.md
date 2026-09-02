# The sextic second-order atlas survives at finite parameter

## The exact family

Put

\[
s=\sqrt3,\quad q_0={7+4s\over27},\quad
a_0={3\over2}q_0(s-1),\quad
k_*={21+11s\over54},\quad h={3-s\over2},\quad r_0=q_0^{1/4}.
\]

For \(0<\beta\le10^{-9}\) and \(|P|,|Q|,|U|\le78\), define

\[
R^4=q_0+a_0\beta,\qquad
a_1={Pr_0\over2h},\qquad b_1=-{Ur_0\over2h},\qquad
\theta={Q\over4h^2},
\]

and the exact homogeneous sextic model

\[
\begin{aligned}
H(z)=\Re\big(&[-3i\beta R(2-s)+\beta^2(a_1+ib_1)]z\\
&+[-1-i\beta^2\theta]z^2+{i\beta\over R}z^3-z^6\big).
\end{aligned} \tag{1}
\]

For the adjacent pairs \(j=0,2\), use truncation radius
\(\rho_+^4=q_0+k_*\beta\). For \(j=3,5\), use
\(\rho_-^4=q_0-k_*\beta\). Then at least one of these four truncated
connectors lies in \(\{H\le0\}\), and its chord has the stronger normalized
bound

\[
{2\over\rho^2}H(\rho w_j(t))\le-{\beta^2\over2}
\qquad(0\le t\le1). \tag{2}
\]

Its two radial tails are also nonpositive, and its length is
\(2-\rho<2\). This is an actual finite-parameter theorem for the complete
bounded second-order box, not only a limiting blow-up.

## The normalized chord and its exact two-jet

With \(w_j(t)=\omega^j((1-t)+t\omega)\), direct normalization of (1) gives

\[
\begin{aligned}
N_j={}&-2\Re(w_j^2)-2\rho^4\Re(w_j^6)
 +6\beta {R\over\rho}(2-s)\Re(-iw_j)\\
&+2\beta {\rho\over R}\Re(iw_j^3)
 +{2\beta^2\over\rho}\Re((a_1+ib_1)w_j)
 +2\beta^2\theta\Re(-iw_j^2). \tag{3}
\end{aligned}
\]

Let \(t_j=s-1,2-s,s-1,2-s\), respectively, and put \(x=t-t_j\).
At \(\beta=0\), all four chords have the same double-contact geometry:

\[
N_{j,0}(t_j)=N'_{j,0}(t_j)=0,\qquad N''_{j,0}(t_j)=-8. \tag{4}
\]

Writing \(N_j=N_0+\beta N_1+\beta^2N_2+E\), exact differentiation
of (3) gives

\[
N_1(t_j)=0,\qquad
N_2(t_j)+{N_1'(t_j)^2\over16}=\Phi_j(P,Q,U), \tag{5}
\]

where the four \(\Phi_j\) are exactly the profiles in
SexticNullBranchSecondOrderAtlas. Thus their average remains
\(-63+36\sqrt3<-3/5\).

## Uniform estimates

The following deliberately coarse bounds hold on \(0\le t\le1\),
\(0\le\beta\le10^{-9}\), and the stated coefficient box:

\[
\begin{array}{rcl}
N_0(t)&\le&-{2\over5}x^2,\\
|N_0'''(t)|&\le&240,\\
|N_1'(t)|&\le&24,\qquad |N_1''(t)|\le72,\\
|N_2(t)|&\le&1000,\qquad |N_2'(t)|\le1200,\\
|E(t)|&\le&1000\beta^3. \tag{6}
\end{array}
\]

The first inequality is an exact square-factor certificate: after dividing
by \(x^2\), subtracting \(2/5\), and converting to Bernstein form, all
coefficients are positive. The derivative bounds use
\(|w_j|,|w_j'|\le1\). Every fourth-root argument in (3) lies in
\([2/5,1]\). On that interval the first three derivatives of \(x^{1/4}\)
are bounded by \(1,2,6\), and those of \(x^{-1/4}\) by \(2,5,28\).
Product differentiation bounds both ratios \(R/\rho\) and \(\rho/R\)
through third order by \(3,5,14,70\). Taylor's theorem then gives the last
line of (6), including the \(\beta^2/\rho\) perturbation.

If \(|x|\ge100\beta\), (6) yields

\[
N_j\le-{2\over5}x^2+24\beta|x|+1000\beta^2+1000\beta^3
\le-{\beta^2\over2}. \tag{7}
\]

If \(|x|\le100\beta\), Taylor expansion at the contact and completion of
the square give

\[
N_j\le\beta^2\Phi_j+
(40\cdot100^3+36\cdot100^2+1200\cdot100+1000)\beta^3.
\]

The coefficient is \(40{,}481{,}000<40{,}500{,}000\). Since
\(40{,}500{,}000\beta\le0.0405<1/20\), any profile below \(-3/5\)
gives (2). The four-profile average supplies such a profile independently
of \(P,Q,U\).

## Rays and metric budget

The weakest canonical selected ray is \(x^2(1/2-x^4)\). Exactly,

\[
q_0-\frac12>\frac1{64},\qquad
\rho^2>\frac7{10},\qquad
\rho^4-\frac12>\frac1{64}-10^{-9}>\frac1{70}.
\]

Thus its canonical contribution is at most \(-1/100\). The two first-order
low modes contribute in absolute value less than \(5\beta\), while the
transverse first and second modes contribute less than \(234\beta^2\):
here \(R,\rho>4/5\), \(h>1/2\), and the coordinate box was used directly.
At \(\beta\le10^{-9}\) their sum is below \(1/200\), so both selected tails
remain negative. Adjacent sixth-root directions have unit chord length;
hence the two tails plus chord have length \(2-\rho<2\).

## Boundary

This closes the finite-parameter core of the canonical bounded second-order
null tube. It does not cover every other sextic coefficient face, prove the
full finite atlas around all positive branch parameters, transfer the
homogeneous model to arbitrary actual polynomials, or settle unrestricted
Erdős #1041. The next target is to overlap this explicit core with the
positive-branch stability tubes and the first-order outer selector, then
classify the remaining compact sextic faces.
