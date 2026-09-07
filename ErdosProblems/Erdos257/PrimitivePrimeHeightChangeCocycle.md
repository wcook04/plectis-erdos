# Primitive-prime charges under an LCM height change

For \(n\mid H\), put
\[
 L_n(H)=\frac{2^H-1}{2^n-1}.
\]
Let \(p_d\) be a primitive prime divisor of \(2^d-1\), so that
\(\operatorname{ord}_{p_d}(2)=d\).  The preceding divisor-height exclusion
uses the charge obtained by reducing anchored coefficients modulo \(p_H\).
This note determines exactly how that charge changes when a new rank enlarges
the common height.

## 1. Projection of a divisor pulse

Let \(H=md\), and let \(n\mid H\).  Then
\[
 \boxed{
 L_n(H)\equiv
 \begin{cases}
 0,&d\nmid n,\\[1mm]
 m/q,&n=qd,
 \end{cases}
 \pmod {p_d}.}                                    \tag{1}
\]
If \(d\nmid n\), the numerator is zero modulo \(p_d\) and the denominator
is nonzero.  If \(n=qd\), then \(q\mid m\) and
\[
 L_n(H)=1+2^n+\cdots+2^{(m/q-1)n}equiv m/q\pmod {p_d}.
\]

Thus a primitive charge at period \(d\) sees only ranks which are vertical
multiples of \(d\).  Every rank transverse to that period is annihilated.

## 2. The height-change cocycle

Suppose a state of coefficient \(C\) at height \(d\) is lifted to height
\(H=md\), and a Boolean set \(F\) of divisor-rank atoms is subtracted.  Its
new coefficient is
\[
 K=C L_d(H)-3\sum_{n\in F}L_n(H).
\]
Equation (1) gives the exact cocycle
\[
 \boxed{
 K\equiv mC
 -3\sum_{\substack{q\mid m\\qd\in F}}\frac mq
 \pmod {p_d}.}                                    \tag{2}
\]
In particular, introducing a rank \(n\) with \(d\nmid n\) and replacing the
height by \(\operatorname{lcm}(d,n)\) does not itself alter the old primitive
charge.  Only later atoms at ranks divisible by \(d\) can change it.

The new height also creates a fresh charge.  Let \(p_H\) be primitive for
\(2^H-1\).  The lifted old state and every atom of proper divisor rank have
coefficient zero modulo \(p_H\).  Hence
\[
 K\equiv0\pmod {p_H}                               \tag{3}
\]
until rank \(H\) itself is used.  LCM growth therefore accumulates primitive
coordinates; it does not erase the previous one and replace it by an
unrelated residue.

## 3. Adjacent divisor clocks cannot pulse together

Assume now that \(r\mid H\) and \(r-1\mid H\).  The coefficient endpoints
of the rank-\(r\) fatal corridor are
\[
 6L_r(H),\qquad 3L_{r-1}(H).                       \tag{4}
\]
Project (4) to the period-\(d\) charge, where \(d\mid H\).  By (1), the
lower endpoint is nonzero only if \(d\mid r\), and the upper endpoint is
nonzero only if \(d\mid r-1\).  Since consecutive integers cannot both be
divisible by \(d>1\),
\[
 \boxed{\text{the two endpoint clocks never pulse simultaneously in one
 primitive coordinate}.}                          \tag{5}
\]

More explicitly, writing \(H=md\),
\[
 6L_r(H)\equiv
 \begin{cases}
 6m/(r/d),&d\mid r,\\
 0,&d\nmid r,
 \end{cases}
\]
and the analogous upper residue is \(3m/((r-1)/d)\) when \(d\mid r-1\),
and zero otherwise.

Equation (5) is the exact nonalignment law between LCM growth and the two
adjacent Mersenne pulse trains.  It does not by itself exclude the complete
moving corridor: when both endpoints vanish in one coordinate, the interval
may contain many coefficients of that residue.  It does show that a proof
cannot treat height changes as arbitrary phase resets.  A dangerous state
must satisfy the nested cocycles (2) simultaneously for every inherited
primitive period, while its two boundary clocks alternate rather than align
inside each coordinate.

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/primitive_prime_height_change_cocycle.py

for exact checks of (1)--(5) across several rooted height changes.  The
unbounded statements follow directly from multiplicative order and the
geometric quotient formula.
