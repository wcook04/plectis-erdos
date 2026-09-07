# Exterior fibre-defect stability for the full critical numerator

## 1. Purpose and evidence boundary

This note gives a quantitative version of the saturation rigidity in
`ExteriorRadialWaterFillingAndSaturationRigidity.md`.  It uses the complete
antipodal fibre, rather than only the product of the zeros or the Boolean
inequality `max |B'| < n`, and therefore retains angular information that is
lost by the `(p,r)` water-filling reduction.

The result is an ordinary exact argument.  The accompanying checker replays
the algebraic identities and the scalar inequalities in a concrete rational
instance; it is not a formalization of the complex-analytic proof.

The conclusion first bounds every exterior critical value of the quotient
`W(z)=z^n/B(z)`.  Controlling the entire exterior critical set, rather than
only its least value, then supplies the missing topology: every excluded-zero
component must eventually attach to the boundary component, and its first
attachment level is an exterior critical value.  Thus the same estimate is an
actual attachment-compatible next-merge ceiling.

## 2. Setup

Let

\[
 B(z)=\frac{P(z)}{Q(z)},\qquad
 P(z)=u\prod_{\nu=1}^m(z-a_\nu),\qquad
 Q(z)=\prod_{\nu=1}^m(1-\overline {a_\nu}z),
 \qquad |u|=1,
\]

be a finite Blaschke product of degree `m`, with

\[
 0<p:=\prod_{\nu=1}^m|a_\nu|<1.
\]

After multiplying `B` by a unimodular constant, assume `B(0)=-p`.  Put

\[
 n=m+d>m,qquad
 g(\zeta)=\frac{\zeta B'(\zeta)}{B(\zeta)}=|B'(\zeta)|
 \quad(|\zeta|=1),
\]

and assume the strict speed condition

\[
 0<g(\zeta)<n\qquad(|\zeta|=1).                         \tag{1}
\]

Let `\zeta_1,\ldots,\zeta_m` be the roots of `B(\zeta)=1`, in circular
order, and set

\[
 h_j=n-g(\zeta_j),\qquad
 \Delta=\frac{1-p}{1+p}-\frac mn.                     \tag{2}
\]

The Clark fibre identity gives

\[
 \sum_{j=1}^m\frac1{g(\zeta_j)}=\frac{1-p}{1+p},
\]

so

\[
 \boxed{\displaystyle
 \Delta=\sum_{j=1}^m\frac{h_j}{n(n-h_j)}.}             \tag{3}
\]

In particular `\Delta>0` under (1).  If

\[
 p_0=\frac{n-m}{n+m}=\frac d{n+m},
\]

then the exact capacity translation is

\[
 \Delta
 =\frac{(n+m)(p_0-p)}{n(1+p)}
 =\frac{2(p_0-p)}{(1+p)(1+p_0)}.                       \tag{4}
\]

## 3. The complete-fibre interpolation norm

Define the full critical numerator

\[
 C(z)=nP(z)Q(z)-z\bigl(P'(z)Q(z)-P(z)Q'(z)\bigr).      \tag{5}
\]

On the circle,

\[
 \frac{C}{PQ}=n-\frac{zB'}B=n-g>0.                    \tag{6}
\]

Consequently `C` has no unit-circle zero and admits the spectral
factorization

\[
 h(e^{i\theta})
 =K\left|\frac{A(e^{i\theta})}{P(e^{i\theta})}\right|^2,
 \qquad
 A(z)=\prod_{k=1}^m(z-\alpha_k),                       \tag{7}
\]

where the `\alpha_k` are the `m` roots of `C` in the open disk, counted with
multiplicity, and `A` is monic.  Since `|C(0)|=np`, comparison of the constant
terms in the self-inversive factorization gives

\[
 K=\frac{np}{\prod_k|\alpha_k|}\ge np.                \tag{8}
\]

Let `F=P-Q`.  Its roots are exactly the `\zeta_j`.  If `L` is its leading
coefficient, then its constant term has modulus `1+p`; because every root of
`F` is unimodular,

\[
 |L|=1+p.                                               \tag{9}
\]

Thus `f=F/L=\prod_j(z-\zeta_j)` is monic.  At a fibre point,

\[
 g(\zeta_j)=\frac{|F'(\zeta_j)|}{|P(\zeta_j)|}.
\]

Equations (7)--(9) therefore give the exact sample identity

\[
 \boxed{\displaystyle
 \left|\frac{A(\zeta_j)}{f'(\zeta_j)}\right|^2
 =\frac{(1+p)^2h_j}{K g(\zeta_j)^2}.}                  \tag{10}
\]

Two sharp one-dimensional estimates now compose.  First, Jensen's inequality
applied to `x\mapsto x/[n(n-x)]` in (3) yields

\[
 \sum_jh_j\le
 \frac{n^2\Delta}{1+n\Delta/m}.                       \tag{11}
\]

Second, the Kovalev--Yang boundary-derivative inequality gives

\[
 \min_{|\zeta|=1}g(\zeta)>\frac{m}{d+1}               \tag{12}
\]

under the strict hypothesis `\max g<n`.  Combining (8), (10), (11), and
(12), define

\[
 \varepsilon^2=
 \sum_{j=1}^m\left|\frac{A(\zeta_j)}{f'(\zeta_j)}\right|^2
\]

and obtain

\[
 \boxed{\displaystyle
 \varepsilon^2<E^2:=
 \frac{n(1+p)^2(d+1)^2\Delta}
 {p m^2(1+n\Delta/m)}.}                                \tag{13}
\]

This is the retained angular datum: it is a complete set of weighted fibre
samples of the full critical numerator, not merely a radial moment.

## 4. Quantitative critical-root localization

The phase of `B` increases at speed at most `n`.  Consecutive roots of
`B=1` therefore have angular separation at least `2\pi/n`, hence chordal
separation at least

\[
 \sigma=2\sin\frac\pi n.                               \tag{14}
\]

Because `A` and `f` are monic, `R=A-f` has degree below `m`.  Lagrange
interpolation at the complete fibre gives the exact rational identity

\[
 \frac{R(z)}{f(z)}
 =\sum_{j=1}^m
 \frac{A(\zeta_j)}{f'(\zeta_j)(z-\zeta_j)}.            \tag{15}
\]

On `|z-\zeta_k|=\rho<\sigma/2`, Cauchy--Schwarz implies

\[
 \left|\frac{R(z)}{f(z)}\right|
 \le \varepsilon
 \sqrt{\rho^{-2}+(m-1)(\sigma-\rho)^{-2}}.             \tag{16}
\]

Set `\rho=2E`.  If

\[
 \boxed{\displaystyle
 E<\min\left\{
 \frac1{2(n+2)},
 \frac{\sigma}{2(1+\sqrt{m-1})}
 \right\},}                                            \tag{17}
\]

then (13) and (16) make the right side strictly below `1`: the distinguished
term contributes less than `1/2`, and the Euclidean norm of all remaining
terms contributes less than `1/2`.  Rouche's theorem, on the disjoint circles
`|z-\zeta_j|=\rho`, gives exactly one zero `\alpha_j` of `A` in each disk.
Thus, after relabelling,

\[
 |\alpha_j-\zeta_j|<\rho.                              \tag{18}
\]

The reciprocal roots

\[
 \beta_j=\frac1{\overline{\alpha_j}}
\]

are precisely the exterior roots of `C`, counted with multiplicity.  From
(18),

\[
 |\beta_j-\zeta_j|
 <R_0:=\frac{\rho}{1-\rho}<\frac1{n+1}.                \tag{19}
\]

## 5. Explicit exterior critical-value bound

Let

\[
 W(z)=\frac{z^n}{B(z)}=z^n\frac{Q(z)}{P(z)}.
\]

The numerator in `zW'/W` is exactly `C`.  Hence the `\beta_j` are the
exterior critical points of `W`, counted with multiplicity (a multiple zero
has critical value zero and only strengthens the conclusion).

Condition (1), evaluated in the radial direction of each Blaschke zero,
implies

\[
 |a_\nu|<\frac{n-1}{n+1}.                              \tag{20}
\]

The straight segment from `\zeta_j` to `\beta_j` lies in the `R_0`-disk
about `\zeta_j`.  Put

\[
 D_0=\frac2{n+1}-R_0>0,
 \qquad
 \Gamma_0=\frac n{(1-R_0)^2}+\frac{2m}{D_0^2}.         \tag{21}
\]

Throughout that segment, (20) gives

\[
 |z|\ge1-R_0,
 \quad |z-a_\nu|\ge D_0,
 \quad |1-\overline{a_\nu}z|\ge D_0.
\]

Write `\mathcal L=W'/W`.  Direct differentiation of

\[
 \mathcal L(z)=\frac nz+\frac{Q'(z)}{Q(z)}-
 \frac{P'(z)}{P(z)}
\]

and the preceding denominator bounds give

\[
 |\mathcal L'(z)|\le\Gamma_0.                          \tag{22}
\]

The important extra datum is `\mathcal L(\beta_j)=0`: the endpoint is a
critical point, not merely an arbitrary point in the collar.  Hence, at
arclength `s` from `\zeta_j` along a segment of length `\ell_j`,

\[
 |\mathcal L(z(s))|\le\Gamma_0(\ell_j-s).
\]

Therefore

\[
\boxed{\displaystyle
 |W(\beta_j)|<\exp\left(\frac{\Gamma_0R_0^2}{2}\right)
 \quad(j=1,\ldots,m).}                                 \tag{23}
\]

In particular the least exterior critical value obeys the same explicit
bound.  By (4), (13), and (19), its logarithm is `O(p_0-p)` as
`p\uparrow p_0`; this quadratic collar estimate uses criticality at the
endpoint.  At exact saturation `p=p_0`, the earlier rigidity theorem
recovers the regular `m`-fold model; (23) is its quantitative, non-symmetric
stability precursor.

## 6. From all critical values to an actual next merge

Let

\[
 X=\{z:|z|\ge1\},
 \qquad
 K_b=\{z\in X:|W(z)|\le b\}\quad(b\ge1),
\]

and let `K_b^\partial` denote the component of `K_b` containing the unit
circle.  The excluded roots are the zeros

\[
 \xi_\nu=1/\overline{a_\nu}\in X
\]

of `W`.  In the original polynomial coordinate, joining an excluded root to
`K_b^\partial` is exactly joining the distinguished component to that root at
relative level `b`.

> **Attachment lemma.**  For each excluded zero `\xi_\nu`, the least `b>1`
> at which `\xi_\nu\in K_b^\partial` is the modulus of an exterior critical
> value of `W`.  Consequently
> \[
>  \frac{b_{\rm next}}t
>  \le \max_{W'(\beta)=0,\ |\beta|>1}|W(\beta)|.        \tag{24}
> \]

*Proof.*  The rational function `W` has no pole on `X`, satisfies
`|W|=1` on `\partial X`, and tends to infinity at infinity.  Every excluded
zero can be joined to `\partial X` by a compact path in `X`; the maximum of
`|W|` on that path is finite.  Thus its zero component joins the boundary
component at some finite least level.

That least level is above `1`, because (1) says that the outward normal
derivative of `\log|W|` on `\partial X` is `n-g>0`, producing a positive
barrier collar.  If the joining level were regular, the implicit-function
theorem and the normalized gradient flow of `\log|W|` would identify the
nearby sublevel sets, preserving their components across the level.  This
contradicts its definition as the first joining level.  Hence the joining
occurs at an exterior critical point.  Taking the first excluded zero to join
proves (24).  Multiplicities cause no problem: a multiple excluded zero is
itself a critical point at value zero, but its boundary-attachment barrier is
still attained at a nonzero exterior saddle.  \(\square\)

Combining (23) and (24) gives the promised metric-topological theorem:

\[
 \boxed{\displaystyle
 \frac{b_{\rm next}}t
 <\exp\left(\frac{\Gamma_0R_0^2}{2}\right).}           \tag{25}
\]

This keeps the actual distinguished component and an actual excluded root;
it does not replace attachment by an unclassified least saddle.

## 7. Exact open boundary

The theorem closes a previously missing local implication:

\[
 \text{small complete-fibre saturation defect}
 \Longrightarrow
 \text{an attachment-compatible next merge lies close to level }1.
\]

Its remaining limitation is quantitative, not topological: the explicit
smallness condition (17) only applies in a near-saturation neighborhood of
`p_0`.  It does not prove the conjectural symmetric envelope throughout
`0<p<p_0`, and it does not by itself dispose of the low-capacity part of the
`d=2,3` terminal blocks.  Also, the proof needs the maximum of the complete
exterior critical set; replacing it by the least exterior critical value
would still be unsupported.
