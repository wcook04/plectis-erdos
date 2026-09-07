# Concave critical thresholds close the canonical sextic phase

Status: ordinary analytic homogeneous-model theorem with an exact symbolic
certificate, 2026-09-05. This covers arbitrary first and tangent-cubic
coefficients at the canonical second-mode phase. It is not an
actual-polynomial transfer, a full mixed-phase theorem, or a solution of
unrestricted Erdős #1041. No Lean check or independent review is claimed.

## The theorem and the idea

For every \(A\in\mathbb C\) and \(C\in\mathbb R\), put
\[
 H_{A,C}(z)=\operatorname{Re}(Az-z^2+iCz^3-z^6),\qquad
 \omega=e^{\pi i/3}.
\]
**Theorem.** There are adjacent sixth roots \(\omega^j,\omega^{j+1}\)
and a radius \(0<r<1\) such that the two radial tails from radius \(r\)
to these roots and their joining chord all lie in \(\{H_{A,C}\le0\}\).
The total length is \(2-r<2\).

Sixth-root rotation gives the same theorem for
\(\operatorname{Re}(Az+Bz^2+iCz^3-z^6)\) whenever
\(B\in\{-1,-\omega^2,-\omega^4\}\). The first coefficient and cubic
are unrestricted; this is the complete canonical phase orbit, rather than
one small tube around a selected coefficient curve.

The proof replaces many local coefficient boxes by a critical-value curve.
For the symmetric first coefficient \(A=-iu\), optimized chord contacts
suggest solving
\[
                  H_{-iu,C}(z)=0,\qquad F'_{u,C}(z)=0,
 \quad F_{u,C}(z)=-iuz-z^2+iCz^3-z^6.                    \tag{1}
\]
These equations admit an explicit one-parameter family. Its cubic value,
written \(C=\gamma(u)\), is strictly concave. Since
\(\gamma(0)=0\), opposite chords have overlapping cubic ranges:
\[
                      \gamma(u)+\gamma(-u)<0\quad(u>0). \tag{2}
\]
In fact the tangent line at zero gives the simple selector
\(C\ge\sqrt3u\) versus \(C\le\sqrt3u\). The radius varies with \(u\);
the selector does not require solving a minimax problem in \(C\).

## 1. An algebraic family of zero critical contacts

Let \(1\le h\le19/10\), and define
\[
\begin{gathered}
 k=h^2/3,\qquad D=5+25k-13k^2-k^3,\qquad
 Y=\frac{3k+1}{3D},\qquad y=Y^{1/4},\\
 U=\frac{2(k-1)(k+1)(-k^2+8k+1)}{D},\qquad
 V=\frac{2(k-1)(-k^2+20k+5)}{3D},\\
 u=yU,\qquad \gamma=V/y,\qquad
 r=\frac{y(h+1)}{\sqrt3},\qquad z_*=y(\sqrt k+i).
\end{gathered}                                                     \tag{3}
\]
All fourth roots here are positive. Direct substitution gives (1), with
\(C=\gamma\). The point \(z_*\) lies on the radius-\(r\) chord from
\(1\) to \(\omega\), at parameter
\[
                              t_*=2/(h+1).                \tag{4}
\]
These are full complex critical equations, not just a stationary point of
the restriction to one chord. They explain why optimizing both radius and
chord parameter led to this family.

For reference, eliminate \(u,C\) from (1) with \(z=x+iy\), \(x,y>0\).
The remaining equation is
\[
 3x^6+39x^4y^2-75x^2y^4+3x^2-15y^6+y^2=0.
\]
Setting \(k=x^2/y^2\) gives exactly \(y^4=Y\), and the two critical
partials then give \(U,V\) in (3).

## 2. Every chord in the family is safe

Write
\[
 Z(t)=\frac{h+1}{2\sqrt3}(2-t+i\sqrt3t),\qquad z(t)=yZ(t).
\]
Put \(T=h^6+39h^4-225h^2-135=-27D<0\). Exact expansion gives
\[
 \frac{H_{-iu,\gamma}(z(t))}{y^2}
   =\frac{(h+1)((h+1)t-2)^2}{6T}\,Q(h,t).                \tag{5}
\]
The polynomial \(Q\) is positive on \([1,2]\times[0,1]\). To make
(5) an inspectable finite certificate, the following matrix specifies its
Bernstein coefficients of bidegree \((6,4)\) in \(h-1,t\):
\[
\begin{pmatrix}
352&352&296&176&16\\
1336/3&1378/3&394&710/3&20\\
2792/5&598&7874/15&958/3&388/15\\
3449/5&3871/5&13967/20&4313/10&343/10\\
2504/3&995&4637/5&8759/15&146/3\\
2953/3&3809/3&14777/12&4775/6&469/6\\
1128&1613&3281/2&1098&143
\end{pmatrix}.                                           \tag{6}
\]
Thus \(Q\ge16\). The checker reconstructs \(Q\) from the original
polynomial, verifies the exact division in (5), and computes (6).
Likewise \(-T>0\) on \([1,2]\) has an exact univariate Bernstein
certificate. The prefactor in (5) is nonpositive, proving containment of
the entire chord, with its prescribed square contact.

The radius lies below one throughout \(1\le h\le19/10\):
\[
 r^4=\frac{(h^2+1)(h+1)^4}{-T}<1.                         \tag{7}
\]
Indeed the numerator of \(1-r^4\), namely
\(-T-(h^2+1)(h+1)^4\), has all positive Bernstein coefficients on that
interval; their minimum is \(32947839/500000\).

The real ray is always safe because its value is \(-t^2-t^6\). On the
other ray the cubic vanishes and the value is
\[
 t\left(\frac{\sqrt3}{2}u+\frac12t-t^5\right).
\]
The chord endpoint already makes this nonpositive at \(t=r\). Moreover
\[
 r^4-\frac1{10}
 =-\frac{(h-1)(11h^5+51h^4+160h^3+240h^2+85h+125)}{10T}\ge0. \tag{8}
\]
Thus \(\tfrac12t-t^5\) is nonincreasing for every \(t\ge r\), and
the whole outward ray remains nonpositive. This proves a complete
connector for every parameter in (3), not just a chord certificate.

## 3. The critical threshold is strictly concave

Define
\[
 u_* = \frac4{5\sqrt3\,10^{1/4}}.
\]
At \(h=1\), (3) gives \(u=-u_*\). At \(h=\sqrt3\), it gives
\(u=\gamma=0\). At \(h=19/10\), its positive \(u\) is larger than
\(u_*\), as checked exactly by fourth powers. Hence the family includes
both parameters \(u\) and \(-u\) for \(0\le u\le u_*\).

It defines a single-valued function \(\gamma(u)\). To see this, let
\[
 R(k)=k^6+54k^5-265k^4+564k^3+495k^2+150k+25.
\]
Differentiating (3) gives
\[
 \frac1y\frac{du}{dk}
 =\frac{(3k-1)R(k)}{(3k+1)D^2}>0\qquad(k>1/3).           \tag{9}
\]
Here \(R>0\) on \([1/3,4/3]\); the checker gives a positive Bernstein
certificate. Elementary bounds also suffice, since
\(265k^4\le(1060/3)k^3<564k^3\) on this interval. At the left
endpoint the derivative is zero, but strict monotonicity follows on the
whole interval by continuity and positivity in its interior.

Differentiate the zero critical value in (1). The derivatives in \(z_*\)
drop out because \(F'(z_*)=0\), leaving
\[
 \gamma'(u)=\frac1{y^2(3k-1)}>0.                           \tag{10}
\]
Its logarithmic derivative with respect to \(k\) is
\[
 \frac{d}{dk}\log\gamma'(u)
 =\frac{4(15k^3-51k^2-23k-5)}{(3k-1)(3k+1)D}<0.          \tag{11}
\]
For \(1/3<k\le4/3\), the numerator is negative because
\(15k^3\le20k^2\). Equations (9)–(11) prove
\(\gamma''(u)<0\) in the interior. Concavity extends continuously to
\(u=-u_*\).

At zero,
\[
 \gamma(0)=0,\qquad \gamma'(0)=\sqrt3,\qquad
 \gamma''(0)=-\sqrt2\,3^{3/4}.                            \tag{12}
\]
Consequently
\[
 \gamma(u)\le\sqrt3u,\qquad
 \gamma(-u)\le-\sqrt3u,                                  \tag{13}
\]
with strict inequalities for \(u>0\). The threshold overlap near zero
has the exact expansion
\[
 -\gamma(u)-\gamma(-u)
          =\sqrt2\,3^{3/4}u^2+O(u^4).                    \tag{14}
\]
The quadratic constant observed in the radius optimization was therefore
\(\sqrt2\,3^{3/4}=3.223709\ldots\), not an unexplained numerical fit.

## 4. Two cubic ranges cover the symmetric first mode

Fix \(0\le u\le u_*\). On the chord for parameter \(u\), the cubic
shape is nonnegative:
\(\operatorname{Im}z(t)^3\ge0\). Increasing \(C\) decreases \(H\),
and it does not change either ray. Thus that connector works for
\(C\ge\gamma(u)\), in particular for \(C\ge\sqrt3u\).

The antipodal connector for parameter \(-u\) works for
\(C\le-\gamma(-u)\), because
\[
                         H_{-iu,C}(-z)=H_{iu,-C}(z).
\]
By (13) it works whenever \(C\le\sqrt3u\). These two ranges cover all
real cubics. For \(u>0\) they overlap strictly by (2).

For \(u\ge u_*\), a simpler construction takes over. The rays in
directions \(-1,-\omega\) are nonpositive for all \(t\ge0\), since
\[
 \max_{t\ge0}(t/2-t^5)=\frac2{5\,10^{1/4}}
                       =\frac{\sqrt3}{2}u_*.
\]
Choose
\[
 0<r\le\min\left\{\frac14,\frac{u}{16},
                       \sqrt{\frac{u}{24(1+|C|)}}\right\}.
\]
Along their radius-\(r\) chord, the first-mode derivative is
\(-\sqrt3ur/2\). The remaining derivatives have modulus at most
\(2r^2+3|C|r^3+6r^6\), which is smaller than \(4ur/5<\sqrt3ur/2\).
The value starts at \(-r^2-r^6<0\) and decreases, so this small chord is
strictly negative. The complete connector has length \(2-r<2\).
This covers every \(u\ge0\) and every real \(C\).

## 5. Reflection removes the real first coefficient

Write \(A=a-iu\). Conjugating the variable, when necessary, replaces
\((A,C)\) by \((\overline A,-C)\), so we may arrange \(u\ge0\).
The pure-imaginary model is invariant under reflection across the imaginary
axis, \(z\mapsto-\overline z\). Each constructed connector lies wholly
in one closed half-plane \(\operatorname{Re}z\ge0\) or
\(\operatorname{Re}z\le0\). Choose it or its reflected copy so that
\(a\operatorname{Re}z\le0\) everywhere. Adding that real first-mode
term only decreases the value. Reflections preserve the sixth roots,
adjacency, radii and length. This proves the theorem for arbitrary complex
\(A\). Sixth-root rotation proves the stated orbit of \(B\).

## Replay and frontier consequence

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_canonical_critical_threshold.py --stress 72
```

The exact checks cover the critical equations, square factorization,
Bernstein positivity, radius and ray bounds, parameter monotonicity,
concavity, range endpoints, and the small-chord regime. The optional
90-digit experiment exercises the assembled construction, including
reflections, the three second-mode phases, both cubic signs, and both sides
of \(u_*\). Its finite samples are regression evidence, not the proof of
the quantified theorem.

This result contains the older canonical mixed slice, null branch and
companion as special coefficient configurations; their separate exact
certificates remain valid. It also covers canonical-phase coefficients
outside the old local null boxes. It does not subsume the boxes' nonreal
second-mode perturbations. The full intermediate mixed region still allows
a continuous second-mode phase; transferring this new family to actual
polynomials also requires strictness and perturbation budgets. The previous
actual first-mode cone and paired-quartic zero-first-mode lift remain
separate source-specific results.

`tao_pipeline_receipt`: input: numerical parity-threshold optimization and
local canonical contact certificates; output: an exact algebraic contact
family and ordinary analytic theorem for the complete canonical phase;
artifact: this note/checker; understanding delta: critical-value concavity,
rather than a list of coefficient boxes, forces the opposite cubic ranges
to overlap; verification: exact symbolic identities and Bernstein/rational
bounds, plus a separately labelled finite construction audit;
publication/review: internal, not independently reviewed; canonicalization:
one global canonical-phase model theorem contains several earlier slices;
unresolved downstream bottleneck: continuous second-mode phases and the
actual-polynomial transfer of this family; next owner: #1041 proof lane.

`tao_writing_review`: the theorem states the model, coefficient phase,
quantifiers and full path geometry. The saddle equations motivate the
parameterization; a displayed certificate makes the whole chord sign
inspectable. Concavity is proved through two derivative factorizations, and
its role in the exhaustive cubic selector is explicit. The original root
problem and finite-polynomial claims are kept distinct from this model
result. Computation supplied the contact geometry and exact identities; the
proof of coverage is analytic.
