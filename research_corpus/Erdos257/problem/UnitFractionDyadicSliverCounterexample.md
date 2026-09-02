# A sparse counterexample to unrestricted unit-fraction sliver avoidance

## Result

The unit-fraction sliver conjecture in
`UnitFractionDyadicSliverPowerAvoidance.md` is false, including when the
unit-fraction denominator is odd.

Let

\[
 m=81803,
 \qquad
 C=\{1,3,4,7,8,13,15,16\},
 \qquad
 F=\{m-c:c\in C\}.
\]

Put

\[
 N=106907,
 \qquad k=50847,
 \qquad
 D=\frac{2^m-k}{N}.
\]

The following three small-integer identities hold:

\[
 1+\sum_{c\in C}2^c=N,
 \qquad
 1+\sum_{c\in C}4^c=Nk,
 \qquad
 2^m\equiv k\pmod N.
\]

Consequently, (D) is a positive odd integer.  Exact cleared-integer
arithmetic gives

\[
 \boxed{
  2^{-m}
  < \frac1D-\sum_{d\in F}\frac1{2^d-1}
  < \frac1{2^m-1}.}
\]

Thus (D) lies in the integer interval asserted to be empty in equation
(3) of the earlier note.

## Exact certificate

Let

\[
 P=\prod_{d\in F}(2^d-1),
 \qquad
 S=\sum_{d\in F}\frac{P}{2^d-1},
 \qquad
 R=P-DS.
\]

The displayed strict inequalities are exactly the integer assertions

\[
 R>0,
 \qquad
 2^mR-DP>0,
 \qquad
 DP-(2^m-1)R>0.
\]

The companion script constructs these integers directly and checks all
three signs.  It also verifies the three small identities above.  No
floating-point or interval arithmetic is used.

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/unit_fraction_dyadic_sliver_counterexample.py
```

## Why this family is visible

For ranks $d=m-c$, put $x=2^{-m}$.  The scaled prefix has the exact
convergent expansion

\[
 2^m\sum_{c\in C}\frac1{2^{m-c}-1}
 =\sum_{j\ge0}\left(\sum_{c\in C}2^{(j+1)c}\right)x^j.
\]

Meanwhile $2^m/D=N/(1-kx)$.  The first identity above matches the
constant term needed for a residual of size $2^{-m}$, and the second
identity makes the coefficient of $x$ differ by exactly one.  The
congruence makes $D$ integral.  The exact certificate determines the
signs of the remaining terms.

## Boundary

This prefix is also greedily reachable from $1/D$.  Since

\[
 D>2^{m-17}-1,
\]

every rank through $m-17$ is skipped.  Exact cleared-denominator replay
from rank $m-16$ through rank $m$ takes precisely

\[
 m-16,m-15,m-13,m-8,m-7,m-4,m-3,m-1
\]

and skips rank $m$.  The residual at that skip is the one in the boxed
sliver above.  The script checks every one of these decisions.

In fact the skip is fatal, not merely dyadically dangerous.  For every
$n>m$,

\[
 \frac1{2^n-1}-2^{-n}
 =\frac1{2^n(2^n-1)}<2^{1-2n}.
\]

Consequently the full remaining tail satisfies

\[
 T_m=\sum_{n>m}\frac1{2^n-1}
 <2^{-m}+\frac{2}{3}\,4^{-m}.
\]

The same exact certificate checks the stronger lower bound

\[
 \frac1D-\sum_{d\in F}\frac1{2^d-1}
 >2^{-m}+\frac{2}{3}\,4^{-m}>T_m.
\]

Thus this odd unit fraction is not a Boolean Mersenne subsum.

## Infinite progression

The same construction gives infinitely many counterexamples.  Keep

\[
 C=\{1,3,4,7,8,13,15,16\},\qquad N=106907,\qquad k=50847
\]

fixed, and take

\[
 m=81803+106906t,\qquad t\in\mathbb Z_{\ge0}.
\]

The exact modular identities

\[
 2^{81803}\equiv k\pmod N,
 \qquad
 2^{106906}\equiv1\pmod N
\]

make $D_m=(2^m-k)/N$ a positive odd integer throughout this progression.
To control the signs uniformly, write $y_c=2^c$ and $x=2^{-m}$.  If
$\rho_m$ denotes the residual multiplied by $2^m$, then

\[
 \rho_m
 =\frac{N}{1-kx}-\sum_{c\in C}\frac{y_c}{1-y_cx}
 =1+x-\sum_{j\ge2}a_jx^j,
\]

where

\[
 a_j=\sum_{c\in C}y_c^{j+1}-Nk^j>0\qquad(j\ge2).
\]

Indeed $2^{16}>k$ and $(2^{16})^3>Nk^2$, so the last inequality follows
from its case $j=2$ by multiplication by $2^{16}/k>1$.  Put
$E=\sum_{c\in C}y_c^3=317209123492360$.  Then

\[
 0<\sum_{j\ge2}a_jx^j
 <\frac{x^2E}{1-2^{16}x}<\frac{x}{3};
\]

the final inequality already holds for $m\ge50$.  Therefore

\[
 1+\frac23x<\rho_m<1+x<\frac1{1-x}.
\]

After division by $2^m$, this proves both the dyadic-sliver inequalities
and the fatal-tail lower bound uniformly.

It remains to check that the same prefix is greedy.  At $x=0$, each
decision from offset $16$ down to offset $1$ is ordinary binary subtraction
from

\[
 N=1+\sum_{c\in C}2^c;
\]

the comparison has an integer margin of at least one.  For $m\ge50$, the
total perturbation of any such comparison is at most

\[
 \frac{x\left(Nk+\sum_{c\in C}y_c^2\right)}{1-2^{16}x}<1.
\]

Hence no decision changes: the greedy prefix takes exactly the ranks
$m-c$ for $c\in C$ and then makes the fatal skip at $m$.  Moreover,
$N<2^{17}$ gives

\[
 D_m-(2^{m-17}-1)
 =\frac{(2^{17}-N)2^{m-17}+N-k}{N}>0,
\]

so every earlier rank is skipped as well.  This proves an infinite family,
not merely a single computed example.

Therefore the counterexample refutes dyadic undershoot, and even achievement
set membership, for arbitrary actual greedy orbits starting from odd unit
fractions.  It does not refute a target-specific theorem for the orbit from
$1/465$.  Any successful proof for that target must use arithmetic special
to $465$, or another constraint stronger than unit numerator and greedy
reachability.

## Bounded offset-resonance audit

The fixed-offset mechanism above has a useful finite classification.  For a
nonempty set $A\subset\{1,\ldots,26\}$, put

\[
 q=1+\sum_{a\in A}2^a,\qquad B=\sum_{a\in A}4^a.
\]

If $2^m=qD+s$ and the associated residual is eventually to enter the
dyadic sliver, comparison of the first two coefficients forces

\[
 qs-B\in\{0,1\}.                                  \tag{8}
\]

The companion script contains an optional Gray-code audit of all
$2^{26}-1$ offset sets and all ranks

\[
 \max A<m<81803.
\]

Among the sets satisfying (8), only one also has
$2^m\equiv s\pmod q$ in this range:

\[
 A=\{1,2,4\},\qquad q=23,\qquad m=10,
 \qquad s=12.
\]

Here $qs-B=0$, but the next coefficient is

\[
 qs^2-\sum_{a\in A}8^a=-856.
\]

The exact residual for $D=(2^{10}-12)/23=44$ is positive but less than
$2^{-10}$, so this candidate falls below the sliver.  Thus the rank-$81803$
family is the first viable **second-order fixed-offset resonance** within
this bounded offset search.  This is not a minimality theorem over arbitrary
supports.

The optional audit is run by

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/unit_fraction_dyadic_sliver_counterexample.py --audit-smaller-offset-resonances
```
