# An all-degree asymmetric diameter tube

## Theorem

Fix `m>=1`.  Let `S` and `J` be finite sets of nonnegative integers, with
every `j in J` satisfying `j<2m`, and put

~~~text
P(z)=-z^(2m)+sum_{k in S} a_k z^(2k)+b+sum_{j in J} c_j z^j.       (1)
~~~

Assume `a_k<=0`, `b<0`, and choose a real cutoff `R>=1`.  Define

~~~text
A_R=sum_{j in J} |c_j| R^j,
B_R=sum_{j in J} |c_j| / R^(2m-j).
~~~

If

~~~text
A_R < -b,                 B_R <= 1,                              (2)
~~~

then, more sharply,

~~~text
P(x) <= b+A_R < 0                 for every real x.        (3)
~~~

Hence the complete real axis lies in one
component of `{Re P<0}`; `[-R,R]` joins its two opposite ends with length
exactly `2R`, and both outward tails are contained.

This is a genuine asymmetric, all-degree open tube around the
coefficientwise nonpositive even cone.  The perturbation may contain any
finite mixture of real odd and positive even lower modes; it is not required
to preserve reflection symmetry of the polynomial.

## Proof

Write `r(x)=sum c_j x^j`.  The nonpositive even terms can only help.

If `|x|<=R`, then `|x|^j<=R^j`, so

~~~text
P(x) <= b+|r(x)| <= b+A_R < 0.
~~~

If `|x|>=R`, then, because `j<2m`,

~~~text
|x|^j <= |x|^(2m)/R^(2m-j).
~~~

Consequently `|r(x)|<=B_R |x|^(2m)<=|x|^(2m)=x^(2m)`, and therefore

~~~text
P(x) <= -x^(2m)+|r(x)|+b <= b < 0.
~~~

Since `A_R>=0`, the outer bound `P(x)<=b` also implies `P(x)<=b+A_R`.
This proves the uniform margin (3).  The two cases include the boundary
`|x|=R`; the geometric conclusion follows
from the same real-axis carrier as in `TiedNewtonFaceEvenSymmetricDiameter`.

## Exact asymmetric witness

Take

~~~text
P(z)=-z^6-1+(z+z^3+z^5)/100,       R=2.
~~~

Then

~~~text
A_2=(2+8+32)/100=21/50<1=-b,
B_2=(1/32+1/8+1/2)/100=21/3200<1.
~~~

Thus the theorem certifies the entire real axis for a polynomial with three
nonzero odd modes.  This proves that the equality-diameter mechanism is not a
thin symmetry locus.

## The metric transfer is already free

The model diameter has length exactly `2R`, but this does **not** create a
metric-contact problem for actual roots.  The staple identity in
`ReciprocalNewtonExpansion`, Theorem R4, says that for actual roots `a_i,a_j`
and any admissible common cutoff `s`, the two root arms plus the chord between
`s a_i/|a_i|` and `s a_j/|a_j|` have length

~~~text
|a_i|+|a_j|-s(2-|a_i/|a_i|-a_j/|a_j||) <= |a_i|+|a_j| < 2.   (4)
~~~

Moving root directions therefore cost no length margin.  After composing
(3) with R4, finite near-Fekete transfer on this tube has only a containment
obligation: prove that the moved finite chord and reciprocal tails inherit the
uniform strict model margin.  It is not a zero-metric-contact problem.

## Programme consequence

The all-degree tied-face selector may remove every coefficient region
admitting (2) from its asymmetric search.  The resolved-transfer desk receives
a strict compactified-containment regression: combine the global margin (3),
the reciprocal `C^0` tail estimate, root-direction tracking, and the metric-free
staple identity (4) to obtain an actual-polynomial neighbourhood theorem.

The unrestricted Erdős #1041 statement remains open.  Conditions (2) are a
sufficient lopsided-coefficient test, not a cover of all tied Newton faces,
The unrestricted statement remains open because this compactified containment
transfer has not yet been proved and conditions (2) do not cover every tied
face.  Exact model metric equality is no longer listed as a separate residual.

## Formal boundary

The companion Lean file proves the two-region domination kernel, its uniform
upper margin, and the exact diameter algebra.  The
finite-sum power comparison and the interpretation in terms of asymptotic
ends remain in the ordinary proof above.  The exact checker independently
replays the rational witness and both coefficient budgets.
