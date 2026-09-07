# Reciprocal power cells and the exact fatal boundary at (1/465)

## Status

This note records an exact reciprocal-coordinate calculation for the
real-greedy route from (1/465).  It identifies the full-tail fatal boundary
inside a power-of-two ceiling cell, proves that the boundary is conjugated by
the same Möbius map as the residual, and gives a source-charge-preserving
family of fatal first-hit cylinders.  The family is not on the actual orbit:
its predecessor reciprocal is not (465).  Consequently the calculation is
a no-go for parity, denominator, and (465)-divisibility arguments, not a
proof or counterexample for Erdős Problem 257.

Write

\[
 M_n=2^n-1,qquad w_n=M_n^{-1},qquad
 T_m=\sum_{n>m}w_n.
\]

For a positive residual (r), put (z=1/r).  The next selected rank is the
least unused (n) for which (M_n\geq z), and selection at (n) sends

\[
 \boxed{z\longmapsto {zM_n\over M_n-z}.}                 \tag{1}
\]

## 1. Power cells and fatality

Suppose rank (m) is skipped and put (P=2^m).  Dyadic unsafety is exactly

\[
 M_m<z<P.
\]

Thus there is a unique (0<\delta<1) with

\[
 z=P-\delta.                                            \tag{2}
\]

If (z=C/a) is reduced, then

\[
 \delta={g\over a},\qquad C=aP-g,qquad 0<g<a,qquad
 \gcd(a,g)=1.                                           \tag{3}
\]

Define the exact tail threshold

\[
 \lambda_m=P-{1\over T_m}.                              \tag{4}
\]

Since (r=1/(P-\delta)), the skipped state lies above the complete remaining
tail precisely when

\[
 \boxed{r>T_m\iff\delta>\lambda_m.}                     \tag{5}
\]

The threshold is uniformly trapped in a much narrower interval than the
whole power cell:

\[
 \boxed{{1\over3}<\lambda_m<{3\over8}\qquad(m\geq1).}   \tag{6}
\]

Indeed, expanding every summand geometrically and then summing first over
the rank offset gives

\[
 T_m=\sum_{s\geq1}{1\over P^s(2^s-1)}.                 \tag{7}
\]

The first three terms in (7) give

\[
 T_m>{1\over P}+{1\over3P^2}+{1\over7P^3}
      >{1\over P-1/3}.
\]

For the other direction, for every (j\geq1),

\[
 {1\over P2^j-1}
 ={1\over P2^j}+{1\over P2^j(P2^j-1)}
 \leq {1\over P2^j}
      +{1\over P(P-1/2)4^j}.
\]

The inequality is strict after summation, and hence

\[
 T_m<{1\over P}+{1\over3P(P-1/2)}
     <{1\over P-3/8}.
\]

These two comparisons are equivalent to (6).

## 2. The fatal boundary is a Möbius orbit

After the forced selection at rank (m+1), formula (1) with
(M_{m+1}=2P-1) gives

\[
 z'=2P-F_P(\delta),
 \qquad
 F_P(u)={(4P-1)u-P\over P-1+u}.                         \tag{8}
\]

The tail recurrence (T_m=w_{m+1}+T_{m+1}) implies the exact conjugacy

\[
 \boxed{\lambda_{m+1}=F_P(\lambda_m).}                  \tag{9}
\]

Moreover, direct subtraction gives

\[
 \boxed{
 F_P(u)-F_P(v)
 ={(2P-1)^2(u-v)\over(P-1+u)(P-1+v)}.}                 \tag{10}
\]

Thus the fatal side of the boundary is preserved by the forced take, and
its signed separation from the boundary is expanded by the positive factor
in (10).  This is an exact identity.  It does not exclude the fatal side;
it explains why replacing the tail boundary by the coarse cut (1/3) loses
the only state-dependent quantity.

## 3. Exact source-charge-preserving fatal cylinders

The remaining question is whether the actual start (z_0=465) can ever
reach the fatal side.  The following family shows that the obvious static
arithmetic inherited from that start does not decide it.

Let

\[
 m=20k+10\quad(k\geq1),\qquad P=2^m,qquad
 a=472,qquad g=193,qquad C=aP-g.                      \tag{11}
\]

Since (2^{20}\equiv1\pmod{465}), (2^{10}\equiv94\pmod{465}), and

\[
 472\cdot94\equiv193\pmod{465},
\]

we have (465\mid C).  Also (C) is odd and

\[
 \gcd(C,a)=\gcd(g,a)=1,qquad
 {3\over8}<{193\over472}<{1\over2}.                    \tag{12}
\]

Consequently the reduced state

\[
 z={C\over a}=P-{193\over472}                           \tag{13}
\]

has all of the following properties:

* its numerator is odd and divisible by (465);
* its reciprocal residual (a/C) has odd denominator;
* rank (m) is skipped and is dyadically unsafe;
* by (6) and (12), the state is already fatal: (a/C>T_m).

There is also an exact safe predecessor through the genuine Mersenne take at
rank (9).  Put (B=M_9=511) and

\[
 x={Bz\over B+z}={BC\over Ba+C}.                         \tag{14}
\]

Then (T_B(x)=z), where (T_B) denotes the map (1).  For (m\geq30),

\[
 2^8<x<B.                                               \tag{15}
\]

Thus the predecessor skips rank (8) dyadically safely, takes rank (9),
then skips every rank (10,\ldots,m); the first dyadically unsafe skip in
this block is the fatal rank (m).  Reduction of (14) cannot cancel a factor
of (465), because

\[
 \gcd(Ba+C,465)=\gcd(Ba,465)=1.
\]

Hence the reduced numerator of (x) is again divisible by (465), while
its reduced denominator is odd.

Finally, with (D=C/465), the residual in (13) has the target-compatible
common-height form

\[
 {a\over C}={472\over465D}<{1\over465}qquad(m\geq30).  \tag{16}
\]

What (16) does **not** say is that
(1/465-472/(465D)) is a Boolean Mersenne prefix.  That missing signed
prefix identity is precisely the actual-history information discarded by
the reciprocal state and by static source-charge divisibility.

## 4. Boundary

Equations (5), (9), and (10) give the exact fatal-coordinate dynamics.  The
family (11)--(16) proves that odd denominators, reduced parity, a surviving
(465) factor, one genuine Mersenne predecessor, local greedy admissibility,
and even a first unsafe event do not force the safe side of the full-tail
boundary.  A proof for the actual (1/465) orbit must retain an identity
linking the whole selected prefix to (1/465), not merely the divisibility
that such an identity implies.

The companion script checks the finite algebra and the family for several
period-(20) instances in exact rational arithmetic.  It does not certify
the infinite Lambert-series inequalities; those are proved above.
