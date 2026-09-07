# Primitive primes exclude the coefficient-six corridor at divisor heights

Put
\[
 w_n=\frac1{2^n-1},\qquad M(2,H)=\frac1{3(2^H-1)},
\]
and, for \(n\mid H\), write
\[
 L_n(H)=\frac{2^H-1}{2^n-1}.
\]
The first root residual is \(1510M(2,15)\).  At a common height \(H\)
divisible by 15, its coefficient is \(1510L_{15}(H)\), while subtraction of
an atom \(w_n\), with \(n\mid H\), subtracts \(3L_n(H)\).

## 1. The divisor-height lattice theorem

Let \(H\) be divisible by 15, and let \(F\) be a finite Boolean set of
divisors of \(H\).  Suppose the residual coefficient
\[
 K=1510L_{15}(H)-3\sum_{n\in F}L_n(H)             \tag{1}
\]
is nonnegative.  Then
\[
 \boxed{K\ne6.}                                    \tag{2}
\]

To prove this, choose a primitive prime divisor \(p\) of \(2^H-1\).  The
Bang--Zsigmondy theorem supplies such a prime for every \(H\) divisible by
15; the exceptional exponent 6 does not occur.  Thus
\[
 \operatorname{ord}_p(2)=H,
\]
so \(p>3\).  If \(n\) is a proper divisor of \(H\), then
\(p\nmid2^n-1\), and hence
\[
 L_n(H)\equiv0\pmod p.                             \tag{3}
\]

For \(H>15\), equation (3) also applies to \(n=15\), so the incoming root
coefficient is zero modulo \(p\).  At \(H=15\), take \(p=151\); the same
conclusion holds because
\[
 1510=10\cdot151.                                  \tag{4}
\]
Every proper-divisor atom therefore disappears modulo \(p\).  The only
remaining possibility is the atom at rank \(H\) itself.  Since \(F\) is
Boolean, (1) gives
\[
 K\equiv0\quad\text{or}\quad K\equiv-3\pmod p.    \tag{5}
\]
Neither residue can equal 6 modulo a prime greater than 3.  This proves
(2).

## 2. This excludes the complete fatal interval at the anchor rank

For an integral coefficient \(K\),
\[
 2w_H\le KM(2,H)<w_{H-1}                           \tag{6}
\]
is equivalent to
\[
 6\le K<\frac{3(2^H-1)}{2^{H-1}-1}
       =6+\frac3{2^{H-1}-1}.                       \tag{7}
\]
Since \(H\ge15\), the only integer in (7) is \(K=6\).  Equations (2) and
(7) therefore show that no residual of the form (1) can enter the
coefficient-six fatal corridor at rank \(H\).

This is stronger than the earlier modulo-six pattern.  It applies at every
height divisible by 15, with no bound on \(H\), and to every Boolean choice
of divisor-rank atoms.  It is also schedule-independent: once all emitted
ranks divide the common height, scalar conservation forces (1), irrespective
of how the packet rewrites were ordered.

The restriction to divisor ranks is essential.  If an emitted rank does not
divide \(H\), its atom coefficient is not \(3L_n(H)\); after enlarging the
common height it may introduce a new pulse not annihilated by the primitive
prime used above.  Likewise, a fatal pair at a rank \(r<H\) occupies the
larger coefficient corridor between \(6L_r(H)\) and \(3L_{r-1}(H)\), not the
single coefficient 6.  The present theorem closes the anchor-rank seam and
identifies nondivisor pulse arrival as the only way around this lattice
obstruction.

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/primitive_prime_divisor_height_exclusion.py

for exact factor and residue receipts at the first eight heights divisible by
15.  The unbounded existence statement is the specialized Bang--Zsigmondy
argument above; the finite calculation is only a regression audit.
