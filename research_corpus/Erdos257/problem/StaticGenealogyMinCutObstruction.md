# A finite cut obstruction for the static cylinder genealogy

Write
\[
 w_n=\frac1{2^n-1},\qquad M(a,b)=w_aw_b,
 \qquad \tau_n=M(n-1,n)=w_{n-1}-2w_n.
\]
This note formulates the exact cut condition obtained when the atoms of a
fixed positive cylinder genealogy are treated as demands and its unexpanded
boundary cylinders are treated as supplies.  The condition is lossless for
one pooled recut.  It fails on an explicit finite prefix of the genealogy
rooted at \(M(2,3)\).

The failure is forced by the same contraction that makes the boundary value
tend to zero.  Once two nodes of a fixed genealogy emit the same rank, their
carry tax remains positive at every later prefix, whereas the boundary supply
tends to zero.  Thus an ordinary static flow network cannot encode the global
ownership problem.  A valid construction must allow a recut to remove or
replace future atom demands.

## 1. The exact cut inequality

Consider the positive binary splitting tree
\[
 M(a,b)=w_{a+b}+M(a,a+b)+M(b,a+b),                 \tag{1}
\]
where \(2\leq a\leq b\).  Let \(U\) be a finite ancestor-closed set of
opened nodes.  Write \(\partial U\) for its unexpanded boundary, and put
\[
 A(U)=\sum_{u\in U}w_{r(u)},\qquad
 S(U)=\sum_{v\in\partial U}M(a_v,b_v),             \tag{2}
\]
where \(r(u)=a_u+b_u\).  Telescoping (1) gives the exact conservation law
\[
 M(2,3)=A(U)+S(U).                                 \tag{3}
\]

Normalize the finite multiset of ranks \(r(u)\) by binary carries.  If
\(B(U)\) is the value of the resulting Boolean multiset, its complete carry
tax is
\[
 T(U)=B(U)-A(U).                                   \tag{4}
\]
Every elementary carry increases the atom value by \(\tau_n>0\), so
\(T(U)\geq0\).

The boundary cylinders can pay these taxes by a nonnegative pooled recut if and
only if
\[
 \boxed{S(U)\geq T(U).}                            \tag{5}
\]
Necessity is scalar.  For sufficiency, refine all boundary cylinders and all
adjacent tax cylinders to common first and second coordinates.  A nonnegative
scalar difference is then a nonnegative integer multiple of the common
cylinder.  Equivalently, (3)--(4) turn (5) into
\[
 B(U)\leq M(2,3).                                  \tag{6}
\]

Thus (5) is the total-source cut in the completely pooled max-flow model.
If endpoint or ancestry restrictions delete source-to-demand edges, the
other Hall inequalities become stronger, but no such restriction can repair
a failure of (5).

The sets \(U\) are the lossless finite cuts of a *fixed* genealogy: an atom
can be exposed only after its ancestors have been opened.  They are not a
lossless model of a dynamic recut, because spending a boundary cylinder may
replace its entire descendant genealogy.

## 2. Contraction makes every repeated rank obstruct a later cut

The preceding observation has a general consequence.  Suppose a locally
finite positive genealogy has boundary value \(S_d\to0\) along its complete
depth prefixes.  If two distinct nodes emit the same atom \(w_r\), then every
sufficiently deep prefix contains both emissions.  Its binary normalization
performs at least one carry at rank \(r\), and hence
\[
 T(U_d)\geq\tau_r.                                 \tag{7}
\]
For all sufficiently large \(d\), one has \(S_d<\tau_r\), contradicting
(5).  We obtain:

> A fixed contractive positive genealogy whose whole boundary is expanded
> cannot have both vanishing residual value and a repeated emitted rank.

This statement does not exclude a Boolean construction by nonlocal recuts.
It shows that the demands in such a construction are endogenous: a cylinder
used to pay a tax cannot also be required to emit every atom in its original
descendant tree.

## 3. An explicit root cut

For a node \((a,b)\), give its cylinder the anchored load
\[
 \ell(a,b)=2^{-b}.
\]
The two children in (1) have total load
\[
 2\,2^{-(a+b)}=2^{1-a}\ell(a,b)
 \leq\frac12\ell(a,b)<\frac{31}{60}\ell(a,b).     \tag{8}
\]
Thus the complete depth-\(d\) boundary of the root has total load
\[
 L_d<\frac18\left(\frac{31}{60}\right)^d.         \tag{9}
\]
Since \(a,b\geq2\),
\[
 M(a,b)\leq\frac49,2^{-b},
\]
and therefore its total scalar supply satisfies
\[
 S_d<\frac1{18}\left(\frac{31}{60}\right)^d.      \tag{10}
\]

Two distinct root descendants emit rank 11:
\[
 (2,3)\longrightarrow(3,5)\longrightarrow(3,8),
 \qquad 3+8=11,                                    \tag{11}
\]
and
\[
 (2,3)\longrightarrow(2,5)\longrightarrow(2,7)
 \longrightarrow(2,9),
 \qquad 2+9=11.                                    \tag{12}
\]
Both nodes belong to every complete depth prefix with \(d\geq4\).  Hence
\[
 T(U_d)\geq\tau_{11}=M(10,11)=\frac1{2094081}.     \tag{13}
\]

At depth 18, exact integer comparison gives
\[
 \frac1{18}\left(\frac{31}{60}\right)^{18}
 <\frac1{2094081}.                                 \tag{14}
\]
Combining (10), (13), and (14),
\[
 \boxed{S(U_{18})<T(U_{18}).}                     \tag{15}
\]
The complete depth-18 prefix is therefore an exact finite, root-reachable
min-cut obstruction.  No enumeration of its \(2^{18}\) boundary cylinders
is used; (15) follows from the uniform contraction and the two displayed
paths.

The sharper factor \(1/2\) in (8) already gives the same conclusion at
depth 17.  The depth-18 statement uses only the previously established
\(31/60\) bound.

## 4. Relation with the reserve tax bound

The reserve tax theorem remains valid.  A dormant rank-\(r\) component can
pay the aggregate carry tax of its formal sibling tree because its value is
not expanded into mandatory descendant atoms during that epoch.  The cut
\(U_{18}\) expands every boundary cohort.  It therefore removes the dormant
reserve while retaining the repeated rank-11 demands.

Consequently the reserve theorem is an epoch statement, not a static-flow
certificate for the complete genealogy.  A max-flow formulation becomes
lossless only after adding the exclusive operation
\[
 \text{use a cylinder as tax supply}
 \quad\text{or}\quad
 \text{expand it into atom and child demands},     \tag{16}
\]
with the first choice deleting the second branch of (16).  This is a
disjunctive recut problem rather than an ordinary max-flow problem.  The
remaining mathematical question is whether those recuts can be chosen
cofinally while each rank stabilizes.

## 5. Exact receipt

The companion script checks (1), the paths (11)--(12), and all rational
comparisons in (8)--(15):

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/static_genealogy_mincut_obstruction.py
