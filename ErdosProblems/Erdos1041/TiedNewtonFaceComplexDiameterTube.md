# An all-degree complex rotated-diameter tube

## Theorem

Let `N=2m` be even and positive.  Fix `u in C` with `|u|=1` and `u^N=1`.
For a finite set `J subset {0,...,N-1}`, consider

~~~text
Q(z)=-z^N+b+sum_{j in J} c_j z^j,                         (1)
~~~

with arbitrary complex coefficients.  Choose real majorants `d_j>=|c_j|`, a
cutoff `R>=1`, and put

~~~text
A_R=sum d_j R^j,                 B_R=sum d_j/R^(N-j).     (2)
~~~

If

~~~text
Re b+A_R<0,                     B_R<=1,                   (3)
~~~

then the complete rotated real line `u R` lies in `{Re Q<0}`.  In fact

~~~text
Re Q(tu) <= Re b+A_R<0                 for every t in R.   (4)
~~~

Thus, for every `R>0`, the segment from `-Ru` to `Ru` and both outward tails
form a contained opposite-end carrier.  After composition with the moving-root
staple identity of `ReciprocalNewtonExpansion` R4, the corresponding actual
root path has length strictly below two; finite transfer needs only preserve
containment.

For fixed `u,R,b`, the certified coefficient region is convex: both `A_R` and
`B_R` are weighted complex `ell^1` norms, so their sublevel sets are convex,
and `Re b+A_R<0` is an open convex inequality.  Thus each rotated diameter is
an exact full-dimensional convex chart cell with two explicit weighted-norm
facets.  Chart-cover computations should test overlap of these cells directly,
not sample coefficient points.

## Proof

Because `N` is even and `u^N=1`,

~~~text
Re[-(tu)^N]=-t^N=-|t|^N.
~~~

Also

~~~text
Re[c_j(tu)^j] <= |c_j| |t|^j <= d_j |t|^j.               (5)
~~~

For `|t|<=R`, (5) sums to at most `A_R`, proving (4).  For `|t|>=R`,

~~~text
sum d_j |t|^j <= |t|^N sum d_j/R^(N-j)=B_R|t|^N<=|t|^N.
~~~

The lower modes cancel at most the negative leading term, leaving
`Re Q(tu)<=Re b<=Re b+A_R`.  This proves the global uniform margin.

## Exact genuinely complex witness

Take `N=4`, `u=i`, `R=2`, `b=-1`, and

~~~text
Q(z)=-z^4-1+((1+i)/100)z+((1+i)/100)z^3.                 (6)
~~~

Since `|(1+i)/100|<1/50`, use `d_1=d_3=1/50`.  Then

~~~text
A_2=(2+8)/50=1/5,
B_2=(1/8+1/2)/50=1/80.
~~~

Hence `Re Q(it)<=-4/5` for all real `t`.  This witness is not a real
coefficient polynomial and uses the non-real diameter `i R`, so the theorem is
strictly broader than `TiedNewtonFaceAsymmetricDiameterTube`.

## Consequence for the programme

Every even-degree tied face satisfying the finite norm budgets (3), after any
allowed leading-coefficient rotation, is removed from the joint-selector
search.  This is a full complex-coefficient open convex tube.  Its actual-polynomial
consumer is the strict compactified-containment transfer: finite-chord control
from the reciprocal `C^0` expansion, mesoscopic tail control from leading-term
domination, and outer-arm control near the two actual roots.  No metric contact
remains.

The unrestricted problem remains open because a general tied face need not
admit any direction and cutoff satisfying (3), and the just-described
all-degree containment transfer is not yet proved.

## Formal boundary

Lean proves the complex real-part-to-norm domination for every rotated monomial
and reuses the exact two-region uniform-margin kernel.  The finite-sum split,
asymptotic-end interpretation, and actual-polynomial containment transfer remain
ordinary mathematics.  The exact checker uses Gaussian-rational arithmetic to
replay (6), its norm majorants, both budgets, and rational line samples.
