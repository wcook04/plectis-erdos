# Every positive cylinder genealogy has an unavoidable first collision

Write

\[
 w_n=\frac1{2^n-1},\qquad M(a,b)=w_aw_b,
\]

and let (a,b\geq2).  Put

\[
 g=\gcd(a,b),\qquad A=\frac ag,\qquad B=\frac bg,
\]

so that (gcd(A,B)=1).  The ordinary positive cylinder expansion is

\[
 M(a,b)=\sum_{n\geq1}c_{a,b}(n)w_n,
 \qquad
 c_{a,b}(n)=\#\{(p,q)\in\mathbb N_{>0}^2:
     \gcd(p,q)=1, ap+bq=n\}.                     \tag{1}
\]

The expansion (1) is obtained by iterating

\[
 M(x,y)=w_{x+y}+M(x,x+y)+M(y,x+y).                \tag{2}
\]

The preceding notes found the first duplicate (c_{2,3}(11)=2) and used
it to exhibit a finite cut obstruction for the fixed genealogy rooted at
(M(2,3)).  The same obstruction occurs for every positive cylinder.  Its
location is determined exactly by the least common multiple of the two root
coordinates.

## 1. Exact first-collision rank

Define

\[
 n_*(a,b)=g(AB+A+B)=a+b+\operatorname{lcm}(a,b).  \tag{3}
\]

Then

\[
 \boxed{
 c_{a,b}(n)\leq1\quad(n<n_*),\qquad
 c_{a,b}(n_*)=2.
 }                                                  \tag{4}
\]

To prove (4), suppose that two distinct positive solutions of
(ap+bq=n) exist.  After interchanging them, there is an integer (k\geq1)
such that

\[
 p=p'+kB,\qquad q'=q+kA.                           \tag{5}
\]

Indeed, (5) follows from (A(p-p')=-B(q-q')) and
(gcd(A,B)=1).  Hence

\[
 \frac ng=A p'+Bq+kAB\geq A+B+AB.                 \tag{6}
\]

This proves that no rank below (n_*) can be repeated.  Equality in (6)
forces (p'=q=k=1), and the two solutions are

\[
 (p,q)=(B+1,1),\qquad (p',q')=(1,A+1).             \tag{7}
\]

Both pairs are primitive.  They are the only positive solutions at
(n_*), which proves (4).

In the labelled binary tree (2), the two nodes in (7) occur on the two
outer branches, at depths (B) and (A), respectively.  Thus the first
duplicate belongs to every complete depth-(d) prefix with

\[
 d\geq\max(A,B).                                   \tag{8}
\]

Formula (3) is the cross-anchor invariant.  Replacing (M(2,3)) by a
different positive cylinder does not remove the first collision.  It moves
the collision from the first emission rank (a+b) by exactly
(operatorname{lcm}(a,b)).

## 2. A universal finite cut obstruction

Orient every node (M(x,y)) so that (2\leq x\leq y), and give it load

\[
 \ell(x,y)=2^{-y}.
\]

The two children in (2) have total load

\[
 2\,2^{-(x+y)}=2^{1-x}\ell(x,y)leq\frac12\ell(x,y). \tag{9}
\]

Let (U_d) be the complete depth-(d) prefix of the labelled genealogy
rooted at (M(a,b)), and let (S_d) be the total value of its unexpanded
boundary cylinders.  Since

\[
 M(x,y)\leq\frac49,2^{-y},                        \tag{10}
\]

equation (9) gives

\[
 S_d\leq\frac49,2^{-\max(a,b)-d}.                 \tag{11}
\]

Normalize the finite multiset of atoms emitted by (U_d) using binary
carries.  Write (T_d\) for the increase in atom value.  Every elementary
carry at rank (r) costs

\[
 \tau_r=w_{r-1}-2w_r=M(r-1,r)>0.                  \tag{12}
\]

For (d\geq\max(A,B)), the two emissions in (7) force at least one carry
at rank (n_*).  Therefore

\[
 T_d\geq\tau_{n_*}.                                \tag{13}
\]

At the explicit depth (d=2n_*), equations (11)--(13) yield

\[
 S_{2n_*}
 \leq\frac49,2^{-\max(a,b)-2n_*}
 <2^{1-2n_*}
 <M(n_*-1,n_*)
 \leq T_{2n_*}.                                    \tag{14}
\]

The first strict inequality uses (a,b\geq2); the second uses
(w_m>2^{-m}).  The pooled cut condition for paying all atom carries from
the unexpanded cylinder boundary is (S_d\geq T_d).  Equation (14) proves
the opposite inequality.  We have therefore shown:

> For every (a,b\geq2), the complete ordinary cylinder genealogy rooted
> at (M(a,b)) has a finite prefix whose boundary value cannot pay the
> carry tax of its emitted atoms.  Depth (2n_*(a,b)) always suffices.

This statement is independent of endpoint restrictions or a particular
matching rule.  It already fails the total-source cut in which all boundary
cylinders may be pooled without ancestry restrictions.

## 3. Finite recutting cannot end in an ordinary forest

The same argument applies to any nonempty finite forest of positive
cylinders.  Expand every root by (2).  The total boundary value tends to
zero by (9), while any one root contributes a repeated atom at its rank
(n_*).  Consequently the complete depth prefixes eventually violate the
pooled cut condition.

It follows that a Booleanisation procedure cannot perform finitely many
nonlocal recuts and then finish by ordinarily expanding the remaining finite
cylinder forest.  Any successful procedure must continue to make nonlocal
recut decisions at unbounded depths.  Such a recut must delete or replace
some future atom demands; merely assigning the complete ordinary descendant
forest to every residual cylinder recreates the fixed tax in (13) after its
boundary supply has contracted away.

This rules out the proposed way of finding an easier rational cylinder
anchor.  The theorem does not prove that (M(a,b)) has no Boolean
representation, and it does not exclude an infinite dynamic recut.  It shows
that no choice of (a,b\geq2) makes terminal approximation accessible by a
static ordinary genealogy, or by a construction whose nonlocal recutting
stops after finitely many stages.  The obstruction is the joint law

\[
 \text{first duplicate delay}=\operatorname{lcm}(a,b),qquad
 \text{boundary supply}\longrightarrow0,
\]

with a positive carry tax that remains fixed once the duplicate has been
emitted.

## 4. Exact audit

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/universal_cylinder_first_collision_nogo.py
```

The script enumerates the primitive coefficients on a bounded grid to check
the exact first-collision formula and verifies the rational inequalities in
(9)--(14).  The proof above is algebraic and does not depend on the finite
range of the audit.
