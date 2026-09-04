# Erdős 1041: smooth unique-active contacts are impossible in every finite arity

## Strengthening after assimilation

On the stated fixed-product smooth cell, **no positive-valued unique-active
stationary point exists at any level**, not only at level one. Indeed, the
angular and radial stationarity calculation below forces all labelled zeros
to coincide. Their attached rays and their full radial optimization domains
then coincide as well, so all V_j are equal. This contradicts uniqueness of
the active index when m>=2. No comparison with the regular polygon, no level
normalization and no local-maximum assumption is needed for this stronger
stationarity exclusion. All inequality constraints must still be strict, all
spectator angular/radial directions available, and the active radial optimum
unique, nondegenerate and interior. Nonsmooth switches are not excluded.

The returned polarisation inequality is independently correct and retained
below as a reusable strict comparison. The stronger argument ends already
after equation (9). Evidence: ordinary calculus proof; the replay checks
algebra, not a formalization of the envelope theorem.

## Statement

Let \(m\ge 2\), let
\[
   a_k=r_k e^{i\alpha_k}\in\mathbb D\setminus\{0\},\qquad
   \prod_{k=1}^m r_k=p,
\]
and put
\[
   \rho(z,a)=\left|\frac{z-a}{1-\overline a z}\right|.
\]
For the ray attached to \(a_j\), write \(u_j=a_j/r_j\) and
\[
   V_j(C)=\max_{r_j\le q\le 1}
       q^{-\nu}\prod_{k=1}^m \rho(q u_j,a_k),
   \qquad
   H(C)=\frac{\min_j V_j(C)}{R_m(p)}.                 \tag{1}
\]
Here \(\nu\) is fixed, and \(R_m(p)\) is the maximum of the same
normalised profile for the regular \(m\)-gon of exterior zeros with product
\(p\).  Thus, if \(r=p^{1/m}\), its pointwise exterior factor is
\[
   G_m(q,r)=\frac{q^m-r^m}{1-r^m q^m}.                \tag{2}
\]

Work in an interior smooth configuration cell: all inequality constraints are
strict, the active ray is unique, and its radial maximiser \(q\) is unique,
nondegenerate and interior.  The usual fixed-product tangent directions are
therefore available and the envelope theorem applies.

> **All-arity unique-active exclusion.**  A nonregular local maximum of
> \(H\) at level \(H=1\) cannot have a unique active ray.

Consequently, in any finite arity, a surviving nonregular smooth first contact
must lie on a selector switch with at least two active attached rays.  The
statement does not remove optimiser-switch cells, closed constraint
boundaries, or multi-active selector switches.

## Proof

Assume that ray \(j\) is uniquely active.  It remains active nearby, so on the
fixed-product slice a local maximum of \(H\) is a local maximum of \(V_j\),
because \(R_m(p)\) is constant.  Rotate so that \(u_j=1\) and
\(\alpha_j=0\).  The contact value is positive, hence the interior maximiser
satisfies \(q>r_j\).

For a spectator zero \(a_k=r_k e^{i\alpha_k}\), set
\[
\begin{aligned}
  N_k&=q^2+r_k^2-2q r_k\cos\alpha_k,\\
  D_k&=1+q^2r_k^2-2q r_k\cos\alpha_k.
\end{aligned}                                                   \tag{3}
\]
Direct differentiation gives
\[
 \frac{\partial}{\partial\alpha_k}\log\rho(q,a_k)
 =\frac{q r_k(1-q^2)(1-r_k^2)\sin\alpha_k}{N_kD_k}.              \tag{4}
\]
Every factor outside the sine is strictly positive.  The spectator angles are
independent tangent coordinates after common rotation has been quotiented
out.  Stationarity therefore forces
\[
        \alpha_k\in\{0,\pi\}\qquad(k\ne j).                     \tag{5}
\]

Now use logarithmic radii \(t_k=\log r_k\).  Along the fixed-product slice,
\(\sum_k t_k=\log p\), stationarity is equivalent to equality of all
single-zero scale derivatives.  On the two collinear directions those
derivatives are
\[
\begin{aligned}
 S_+(r)&=-\frac{r(1-q^2)}{(1-qr)(q-r)},                            \tag{6}\\
 S_-(r)&= \frac{r(1-q^2)}{(1+qr)(q+r)}.                            \tag{7}
\end{aligned}
\]
The active zero contributes \(S_+(r_j)<0\).  An opposite spectator has
\(S_-(r_k)>0\), and a same-ray spectator with \(r_k>q\) also has
\(S_+(r_k)>0\).  A spectator at \(r_k=q\) would make the contact product zero.
Hence every zero lies on the selected ray and satisfies \(0<r_k<q\).

For fixed \(q\),
\[
 F_q(r)=\frac{r}{(1-qr)(q-r)}
\]
is strictly increasing on \((0,q)\), since
\[
 \frac{d}{dr}\log F_q(r)
   =\frac1r+\frac{q}{1-qr}+\frac1{q-r}>0.                         \tag{8}
\]
Thus \(S_+(r)=-(1-q^2)F_q(r)\) is injective.  Equality of the scale
derivatives forces
\[
             r_1=\cdots=r_m=:r.                                  \tag{9}
\]
The only putative unique-active stationary object is therefore the \(m\)-fold
coincident zero on one ray.

It remains to compare that object with the regular \(m\)-gon.  Put
\[
       \delta=\frac{q-r}{1-qr}\in(0,1).
\]
Factor the regular profile as
\[
 \frac{q^m-r^m}{1-(qr)^m}
 =\delta\,
   \frac{A_m(q,r)}{D_m(q,r)},                                    \tag{10}
\]
where
\[
 A_m(q,r)=\sum_{i=0}^{m-1}q^{m-1-i}r^i,
 \qquad
 D_m(q,r)=\sum_{i=0}^{m-1}(qr)^i.                                \tag{11}
\]
There are two strict elementary inequalities.  First,
\[
 q-\delta=\frac{r(1-q^2)}{1-qr}>0.                               \tag{12}
\]
Second,
\[
 A_m-q^{m-1}D_m
 =\sum_{i=1}^{m-1}q^{m-1-i}r^i(1-q^{2i})>0.                      \tag{13}
\]
Equations (10)--(13) give
\[
 \frac{q^m-r^m}{1-(qr)^m}
   >\delta q^{m-1}
   >\delta^m.                                                     \tag{14}
\]
Thus the pointwise exterior factor of the coincident configuration is
strictly below that of the regular \(m\)-gon:
\[
 \left(\frac{q-r}{1-rq}\right)^m
 <\frac{q^m-r^m}{1-r^m q^m}.                                    \tag{15}
\]
The common factor \(q^{-\nu}\) does not alter the comparison.  Evaluating
(15) at the assumed contact optimiser yields
\[
       V_j(C)<G_m^{\mathrm{normalised}}(q,r)\le R_m(r^m),         \tag{16}
\]
contradicting \(V_j(C)=R_m(p)\) and \(p=r^m\).  The unique-active smooth
contact cannot exist.  ∎

## What genuinely generalises, and what does not

The angular envelope identity, the fixed-product scale identity and the
strict coincident-versus-regular polarisation gap are all arity-free.  No
regular-triangle algebra is used in the argument above.  What remains
arity-sensitive is the nonsmooth minimax geometry when two or more rays are
active.  An aggregate Poisson or model-space identity cannot, by itself,
select one fixed ray over a whole scale interval; the supplied five-ray exact
falsifier blocks precisely that inference.

## Exact frontier effect

This result removes every smooth one-active-ray stratum from the finite
contact atlas, for every \(m\ge2\).  The remaining live strata are:

1. multi-active selector switches;
2. radial optimiser switches;
3. the closed speed boundary and other constraint boundaries;
4. the regular equality orbit.

No unrestricted resolution of Erdős 1041 is claimed.

## Verification

Run

```sh
python3 formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_unique_active_all_arity.py
```

The checker verifies the differential identities, the scale signs and
monotonicity identity, the arbitrary-arity finite-sum factorisation, and exact
rational samples of the strict polarisation inequality.

```text
tao_pipeline_receipt:
  input_stage: nonsmoothed finite-selector first-contact system
  output_stage: all-arity exclusion of the smooth unique-active stratum
  human_understanding_delta: unique-ray stationarity collapses every arity to a coincident radial cluster, while a two-line finite-sum inequality strictly favours the regular polygon
  verification_state: ordinary exact proof plus symbolic and exact-rational replay
  publication_or_review_state: research return; not independently reviewed
  canonicalization_state: proposed arity-free strengthening of the three-exterior unique-active contact theorem
  unresolved_downstream_bottleneck: multi-active selector switches and constraint-boundary contacts
  next_stage_owner: switch-surface elimination or certified compact atlas
```
