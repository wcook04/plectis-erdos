# The sextic null branch is the only first-order transition

## Result

At the canonical sextic model

\[
H_0(z)=\operatorname{Re}(-z^2-z^6),
\]

the four equality connectors touch the boundary at

\[
z=a(\pm1\pm i),\qquad
a={r_0(3-\sqrt3)\over2},\qquad
r_0^4={7+4\sqrt3\over27}.
\]

Write a gauge-fixed tangent perturbation as

\[
\delta H(z)=\operatorname{Re}\big((a_1+i b_1)z-i\theta z^2+i c z^3\big).
\]

Put

\[
p=aa_1,\qquad q=2a^2\theta,\qquad
r=-a(b_1+2a^2c).
\]

The four contact variations are exactly

\[
p+q+r,\quad p-q-r,\quad -p-q+r,\quad -p+q-r. \tag{1}
\]

If \(m\) is their minimum, then

\[
m\le0,\qquad p^2+q^2+r^2\le3m^2. \tag{2}
\]

The constant \(3\) is sharp: at \(p=q=r=1\), the four values are
\(3,-1,-1,-1\).

Consequently every perturbation transverse to

\[
a_1=\theta=0,\qquad b_1=-2a^2c \tag{3}
\]

makes at least one of the four square contacts strictly negative, with a
quantitative margin equal to at least
\(\sqrt{(p^2+q^2+r^2)/3}\).  Equation (3) is therefore not merely a null
direction found by a search: it is the complete common kernel of all four
first variations.

This closes the first-order part of the \(\beta\to0\) transition.  Together
with SexticNullBranchUniformMargin, it reduces the remaining homogeneous
sextic problem to a genuinely second-order tube around one explicit algebraic
branch.

## Contact calculation

Let \(x,y\in\{\pm1\}\) and \(z=a(x+iy)\).  Since

\[
z^2=2ia^2xy,\qquad z^3=-2a^3x+2ia^3y,
\]

direct substitution gives

\[
\delta H(a(x+iy))
=a a_1x+2a^2\theta xy-a(b_1+2a^2c)y. \tag{4}
\]

The four sign pairs \((x,y)\) give (1).

## Tetrahedral proof

Call the four values \(v_1,\ldots,v_4\).  They obey the exact Hadamard
identities

\[
\sum_i v_i=0,\qquad \sum_i v_i^2=4(p^2+q^2+r^2). \tag{5}
\]

Let \(m=\min_i v_i\), and put \(u_i=v_i-m\ge0\).  Then
\(\sum_i u_i=-4m\).  Positivity of the pairwise products gives

\[
\sum_i u_i^2\le\left(\sum_i u_i\right)^2=16m^2.
\]

Using \(v_i=m+u_i\) and \(\sum_i v_i=0\),

\[
\sum_i v_i^2=-4m^2+\sum_i u_i^2\le12m^2.
\]

Combine this with (5) to obtain (2).  Equality occurs at the sharp fixture
above, so no stronger Euclidean constant is possible.

## From one contact to its whole chord

The canonical square-times-Bernstein factorization supplies the local bound

\[
H_0\le-{(t-t_0)^2\over20}.
\]

If a coefficient perturbation has contact value at most \(-\mu\) and varies
away from that contact by at most \(3\delta|t-t_0|\), then

\[
\begin{aligned}
H_0+\delta H
&\le-\frac{x^2}{20}-\mu+3\delta|x|\\
&=45\delta^2-\mu-\frac{(|x|-30\delta)^2}{20}.
\end{aligned}
\]

Thus the full local chord is nonpositive whenever
\(\mu\ge45\delta^2\).  In particular, outside the explicit quadratic tube

\[
p^2+q^2+r^2<6075\,\delta^4, \tag{6}
\]

the tetrahedral selector supplies such a contact.  This is the promised
two-scale reduction: all transverse directions close linearly, and only an
\(O(\delta^2)\) neighborhood of the exact null branch reaches the secondary
model.

The two selected radial tails have fixed negative slack at the canonical
point, so sufficiently small coefficient perturbations preserve them.  The
new theorem isolates the chord contact, which was the singular part.

## Formal and computational status

SexticNullBranchTransverseSelector.lean verifies both Hadamard identities,
the sharp tetrahedral inradius estimate, the exact null-line
characterization, the completing-square absorption lemma, and the explicit
quadratic-tube consequence.  The companion checker replays the identities
symbolically and stress-tests 100,000 exact rational triples.

## Boundary and next handoff

This theorem does not prove the entire sextic atlas, finite actual-polynomial
transfer, or unrestricted Erdős #1041.  Its exact downstream obligation is
smaller: classify the bounded second-order model obtained by writing the
transverse coordinates as \(O(\beta^2)\).  The four-connector numerical probe
currently gives a strictly negative best margin throughout its tested box;
that evidence must be converted into a finite analytic atlas before it can
change the claim ceiling.
