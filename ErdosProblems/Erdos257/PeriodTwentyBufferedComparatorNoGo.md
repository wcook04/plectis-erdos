# A period-twenty countermodel to the buffered quotient strategy

Status: exact theorem-level cross-target falsifier, 2026-08-21.  This note
does not falsify the conjectured quotient bound for \(1/465\).  It proves
that the period length, the seven source bits per period, the factorisation
\(465=(2^4-1)(2^5-1)\), and a square-root buffer do not suffice to prove
that bound.

Put

\[
 w_d=\frac1{2^d-1},\qquad x=\frac{64}{465},
\]

and, for a horizon \(N\), define

\[
 H_N=\lfloor 2^Nx\rfloor,\qquad
 S_N=2\lfloor\sqrt N\rfloor+5,\qquad
 C_N=H_N-S_N,
\]

\[
 q_{N,d}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor.
\]

Run decreasing-weight Boolean greedy on
\(q_{N,1},\ldots,q_{N,N}\), and denote its terminal remainder by \(r_N\).

## 1. The source has exactly the same period statistics

The denominator is reduced, because \(\gcd(64,465)=1\), and

\[
 \operatorname{ord}_{465}(2)
 =\operatorname{lcm}(2,4,5)=20.
\]

Thus the binary expansion of \(x\) has exact period twenty.  Its period is

\[
 00100011001111000000,
\]

which has seven ones.  This is the six-place dyadic phase shift of the
period for \(1/465\),

\[
 00000000100011001111.
\]

Consequently the two targets have the same reduced denominator, exact
period, period Hamming weight, and Mersenne-product denominator.  They
differ only in source phase and numerator.

## 2. The real greedy orbit is rigorously fatal

The first three weights exceed the target.  For the last of them,

\[
 w_3-x=\frac17-\frac{64}{465}=\frac{17}{3255}>0.
\]

On the other hand, the complete tail after rank three satisfies

\[
 \sum_{d\ge4}w_d
 <\sum_{d\ge4}\left(2^{-d}+2^{1-2d}\right)
 =\frac18+\frac1{96}=\frac{13}{96}.
\]

The target lies strictly above this tail:

\[
 x-\frac{13}{96}=\frac{11}{4960}>0.                 \tag{1}
\]

Therefore real greedy skips ranks \(1,2,3\) and takes every rank from
\(4\) onward.  Indeed, before any rank \(d\ge4\), its residual is larger
than the complete remaining tail and hence larger than \(w_d\).  The word
is exactly

\[
 000111111\ldots .                                  \tag{2}
\]

This is the permanent all-selected obstruction in its simplest form, not a
finite numerical imitation of it.

## 3. The buffered quotient remainder is exponential

For \(N\ge8\), the rank-three quotient already exceeds the shifted target.
Indeed,

\[
 q_{N,3}\ge 2^Nw_3-1,
 \qquad C_N\le H_N\le2^Nx,
\]

and

\[
 2^N(w_3-x)-1
 =2^N\frac{17}{3255}-1>0.
\]

Hence quotient greedy skips ranks \(1,2,3\).  Even if it were allowed to
take every later quotient, its terminal remainder would obey

\[
\begin{aligned}
 r_N
 &\ge H_N-S_N-\sum_{d=4}^{N}q_{N,d}\\
 &\ge 2^N\left(x-\sum_{d\ge4}w_d\right)-S_N-1\\
 &>\boxed{\frac{11}{4960}\,2^N-S_N-1}.             \tag{3}
\end{aligned}
\]

In particular, \(r_N\) is exponential.  No estimate of the form

\[
 r_N+U_N\le T_x(N)+O(\sqrt N)
\]

can hold for this target, since \(U_N\le N\) and the source popcount
\(T_x(N)\) is linear.

## 4. Exact scope of the no-go theorem

The target \(64/465=2^6M(4,5)\) preserves every coarse datum used by a
period-block argument: denominator factorisation, order twenty, seven
source bits per period, quotient divisor pulses, and the universal
square-root phase estimate.  Nevertheless it sits in a literal final-zero
cylinder and violates the buffered remainder conclusion exponentially.

Therefore a proof for \(1/465\) cannot follow from those data alone.  It
must use information destroyed by dyadic phase shift: the precise
numerator-one source phase, the anchor-four/five ownership geometry, or an
equivalent target-specific invariant.  This is a no-go theorem for the
coarse period-twenty strategy, not evidence against the still-live
numerator-one bound.

## 5. Exact audit

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/period_twenty_buffered_comparator_nogo.py
```

The script checks the two period words, their Hamming weights, all rational
inequalities above, the exact real-greedy fatal word through a finite audit
window, and the quotient lower bound at every tested horizon.
