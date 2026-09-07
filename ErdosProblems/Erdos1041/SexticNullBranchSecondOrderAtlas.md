# The sextic null branch has a uniform second-order connector atlas

## Result

The first-order selector reduces the canonical sextic transition to
perturbations lying \(O(\beta^2)\) from the exact null branch.  In that tube,
write the three normalized second-order transverse contact coordinates as
\(p,q,r\).  There are four relevant adjacent connectors, corresponding to
the contacts \(a(\pm1\pm i)\).

After optimizing the first-order slope \(k\) of the fourth power of each
truncation radius, their limiting normalized maxima are

\[
\begin{array}{ll}
\Phi_{++}=o_++(p+q+r),&
\Phi_{-+}=o_++(-p-q+r),\\
\Phi_{--}=o_-+(-p+q-r),&
\Phi_{+-}=o_-+(p-q-r),
\end{array} \tag{1}
\]

where

\[
o_+=-117+\frac{135}{2}\sqrt3,\qquad
o_-=-9+\frac92\sqrt3. \tag{2}
\]

For every \(p,q,r\in\mathbb R\),

\[
\min(\Phi_{++},\Phi_{-+},\Phi_{--},\Phi_{+-})<-\frac35. \tag{3}
\]

Thus the complete bounded second-order model has a uniform four-connector
atlas.  No transition regime survives at the homogeneous limiting level:
first-order transverse perturbations are handled by the sharp tetrahedral
selector, the exact null branch by its strict companion, and all
\(O(\beta^2)\) transverse perturbations by (3).

This is a limiting-model theorem.  The remaining step is a uniform
finite-\(\beta\) Taylor remainder estimate that transfers its fixed
\(3/5\) margin to the actual coefficient family.

## Deriving the local profiles

Let \(\omega=e^{\pi i/3}\) and parameterize adjacent chord \(j\) by

\[
w_j(t)=(1-t)\omega^j+t\omega^{j+1}.
\]

Normalize the actual model by the positive factor \(\rho^2/2\), and write

\[
\rho^4=q_0+k\beta,\qquad
q_0=\frac{7+4\sqrt3}{27}.
\]

At \(\beta=0\), each of the four relevant chord functions has a double zero
at its square contact.  If \(x\) is the contact-scale displacement, its
quadratic term is exactly

\[
-4x^2. \tag{4}
\]

The first-order tilt is \(d(k-k_0)x\), with

\[
d=648-378\sqrt3,\qquad
k_0=\frac32q_0(\sqrt3-1)
\]

for the two upper contacts; the lower pair has center \(-k_0\) with the
corresponding reflected sign.  Therefore

\[
-4x^2+\lambda x+C\le C+\frac{\lambda^2}{16}. \tag{5}
\]

The remaining second-order radius-ratio term is linear in \(k\).  For the
upper pair its complete raw profile is

\[
P_+(k)=b(k-k_0)+\frac{d^2(k-k_0)^2}{16},
\quad b=-\frac{9963}{2}+\frac{5751}{2}\sqrt3.
\]

For the lower pair,

\[
P_-(k)=-b(k-k_0)+\frac{d^2(k+k_0)^2}{16}.
\]

Both complete squares with the same positive coefficient:

\[
\begin{aligned}
P_+(k)&=o_++D(k-k_*)^2,\\
P_-(k)&=o_-+D(k+k_*)^2,
\end{aligned} \tag{6}
\]

where

\[
k_*=\frac{21+11\sqrt3}{54},\qquad
D=\frac{2187}{4}(97-56\sqrt3)>0. \tag{7}
\]

The positivity follows from \(\sqrt3<97/56\).  Hence the optimized radius
slopes are exactly \(\pm k_*\), and the optimized offsets are (2).

## Why four connectors cover every perturbation

The four transverse terms in (1) sum to zero.  Consequently

\[
\frac{\Phi_{++}+\Phi_{-+}+\Phi_{--}+\Phi_{+-}}4
=\frac{o_++o_-}{2}
=-63+36\sqrt3<-\frac35, \tag{8}
\]

where the last inequality follows already from \(\sqrt3<26/15\).  At least
one of four numbers is no larger than their average, proving (3).

This averaging is the mechanism the numerical search was pointing at.  The
search was not finding an isolated favorable phase: it was seeing a
tetrahedral cancellation with two radius-optimized offsets.

## Formal and computational status

SexticNullBranchSecondOrderAtlas.lean checks both radius-slope
complete-square identities, positivity of their common coefficient, the
local concave-quadratic maximum, the exact profile sum, and the uniform
four-connector cover.  The exact symbolic checker independently reconstructs
all four chord curvatures and first-order slopes from sixth roots of unity,
verifies the optimized offsets, and stress-tests 100,000 exact rational
transverse triples.

## Boundary and downstream handoff

The theorem closes the entire second-order homogeneous blow-up at the
canonical sextic null branch.  It does not yet prove a uniform finite-\(\beta\)
neighborhood, the remaining sextic coefficient faces, finite
actual-polynomial transfer, or unrestricted Erdős #1041.

The exact next obligation is now a standard quantitative transfer: bound the
third-order Taylor remainder of the four actual chord functions uniformly on
a compact transverse box, use the fixed \(3/5\) normalized margin to absorb
it, and overlap that core with the already-proved positive-branch tube and
the first-order outer selector.
