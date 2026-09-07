# A variational principle for the delayed-density reservoir

Status: exact deductions, 2026-08-20.  The quotient dominance inequality used
below is proved in Lean as
`localMersenneQuotient_dominanceGap` in
`BooleanMobiusGreedyReduction.lean`.  The reservoir identities are ordinary
deductions from the definitions in `DelayedDoublingDensityAttack.md`.  The
result does not prove that the reservoir is nonnegative.

## 1. The insertion coefficients

Fix a horizon `N`, and set

\[
 q_{d,N}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor,
 \qquad
 c_{d,N}=q_{d,N}+\mathbf 1_{2d\le N}-1
 \quad (2\le d\le N).
 \tag{1}
\]

For a Boolean support `A`, insertion of a previously absent rank `d` changes
the reservoir by exactly `c_(d,N)`.  Thus

\[
 R_{A\cup\{d\}}(N)-R_A(N)=c_{d,N}.
 \tag{2}
\]

In particular, `c_(N,N)=0`.  The terminal decision is invisible to the
reservoir at its own horizon.

The remaining coefficients are strictly superincreasing:

\[
 \boxed{
 c_{d,N}>\sum_{e=d+1}^{N}c_{e,N}
 }
 \qquad (2\le d<N).
 \tag{3}
\]

To prove (3), first suppose `2d<=N`.  Then `c_(d,N)=q_(d,N)`, while
`c_(e,N)<=q_(e,N)` for every later rank.  The Lean-checked quotient
dominance theorem, applied with `M=R=N`, gives

\[
 1+\sum_{e=d+1}^{N}q_{e,N}\le q_{d,N},
\]

and (3) follows.

It remains to consider `N<2d`.  Put `k=N-d`, so `1<=k<d`.  Division of

\[
 2^N=2^k(2^d-1)+2^k
\]

shows that `q_(d,N)=2^k`, because `2^k<2^d-1`.  Every later rank is in the
same upper half, and hence

\[
 c_{d,N}=2^k-1,
 \qquad
 \sum_{e=d+1}^{N}c_{e,N}
 =\sum_{j=0}^{k-1}(2^j-1)
 =2^k-1-k.
\]

Their difference is `k>0`, proving (3).  This also proves the insertion
monotonicity without computation.

## 2. Exact use of real greedy complementarity

Let

\[
 x=\frac1{21},\qquad w_d=\frac1{2^d-1},
\]

and let `G_N` be the actual real-greedy support through rank `N`.  If
`D` is any support contained in `{2,...,N}` such that

\[
 \sum_{d\in D}w_d\le x,
 \tag{4}
\]

then `G_N` is lexicographically at least `D`, with smaller ranks compared
first.  Indeed, at the first differing rank `d`, it is impossible to have
`d in D` and `d notin G_N`: the earlier partial sums agree, and the greedy
rejection of `d` says that adjoining `w_d` already exceeds `x`, contradicting
(4).  Therefore the first difference belongs to `G_N`.

Combining this fact with (3) gives

\[
 \sum_{d\in D}c_{d,N}
 \le
 \sum_{d\in G_N}c_{d,N}.
 \tag{5}
\]

The possible first difference at `d=N` causes equality because
`c_(N,N)=0`; otherwise (5) is strict.

This ordering is exactly an ordering of reservoirs.  Let

\[
 T_N=\left\lfloor\frac{2^N}{21}\right\rfloor,
 \qquad
 \tau(N)=\#\{n\le N:n\equiv0,5\pmod 6\},
\]

and, for a support `D` satisfying (4), write

\[
 Q_D(N)=T_N-\sum_{d\in D}q_{d,N},
 \qquad
 U_D(N)=\#\{d\in D:2d>N\}.
\]

Real feasibility implies `Q_D(N)>=0`.  Moreover,

\[
 R_D(N)
 =\tau(N)+3-Q_D(N)-U_D(N)
 =\tau(N)+3-T_N+\sum_{d\in D}c_{d,N}.
 \tag{6}
\]

Equations (5) and (6) prove the finite variational principle

\[
 \boxed{
 R_D(N)\le R_{G_N}(N)
 }
 \tag{7}
\]

for every real-feasible Boolean support `D` at the same horizon.  Equivalently,
the actual greedy prefix minimizes

\[
 Q_D(N)+U_D(N)
 \tag{8}
\]

among all real-feasible finite supports.  Thus real greedy complementarity
does control the joint quotient-defect/upper-half-count quantity; no further
exchange estimate is needed for that purpose.

## 3. The remaining sign problem

The variational principle does not determine the sign of the maximum.  It
would prove `R_(G_N)(N)>=0` if one could exhibit, for every `N`, a support
`D_N` satisfying

\[
 \sum_{d\in D_N}w_d\le\frac1{21},
 \qquad
 Q_{D_N}(N)+U_{D_N}(N)\le\tau(N)+3.
 \tag{9}
\]

But the existence of such a comparator is equivalent to the desired sign:
the forward implication follows from (7), while the reverse implication
allows `D_N=G_N`.  Consequently (9) must not be presented as a reduction.
The content of (7) is instead that the exchange part of the argument is
complete: the only remaining issue is an absolute source-sensitive upper
bound for the minimum in (8).

The adjustment by `U_D(N)` is essential.  The unadjusted quotient weights
are already known to be gap-dominating, but quotient admissibility alone
allows the positive-flux cofinite supports in `SourceClockBorrowNoGo.md`.
Formula (8) identifies the additional price imposed by the delayed binary
channel: every selected rank above `N/2` costs one unit, while the quotient
defect pays for unused binary capacity.  The period-six target supplies only
`tau(N)+3` units in the conjectured inequality.
