# The doubling-block word and the odd quotient suffix

Status: exact deductions and exact finite computation, 2026-08-20.  The
all-depth density inequality in `DelayedDoublingDensityAttack.md` remains
unproved.  This note distinguishes the actual greedy block from the bounded
quotient suffix and records the resulting escape and carry cocycles.

## 1. The actual word differs from the quotient suffix

Let `A` be the actual greedy support for `1/21`, write `b_d=1_A(d)`, and let

\[
 B(N)=\sum_{d\leq N}b_d.
\]

For `K>=2`, define the actual upper-block numeral

\[
 W_K=\sum_{K+2\leq d\leq2K+1}b_d2^{2K+1-d}.
 \tag{1}
\]

Thus `W_K` is the binary word on the ranks `K+2,...,2K+1`, and
`s_2(W_K)=B(2K+1)-B(K+1)`.  Define the actual-prefix odd quotient reservoir

\[
 R_K=\left\lfloor\frac{2^{2K+1}}{21}\right\rfloor
 -\sum_{\substack{d\leq K+1\\b_d=1}}
  \left\lfloor\frac{2^{2K+1}}{2^d-1}\right\rfloor.
 \tag{2}
\]

Let `Q_N` denote `twentyOneGreedyDefect N`.  Expanding the coefficient
numerator through depth `2K+1` gives the exact identity

\[
 \boxed{R_K=W_K+Q_{2K+1}.}
 \tag{3}
\]

Indeed a selected divisor `d<=K+1` contributes its complete truncated
geometric string to the quotient sum in (2).  A selected divisor
`K+2<=d<=2K+1` can contribute only at its own index, and those contributions
form (1).  Subtracting the complete coefficient numerator from the target
quotient leaves `Q_(2K+1)`.

Equation (3) is the odd-depth counterpart of
`S_R=H_R+Q_(2R)` in `ActualPrefixBoundaryInvariant.md`.  It also shows why
the odd quotient suffix is not the actual greedy word.  Even when the lower
support in (2) agrees with the quotient recurrence, its bounded suffix is
the low binary part of `W_K+Q_(2K+1)`, rather than `W_K`.

The first explicit discrepancy occurs at `K=6`.  The actual support on ranks
`8,...,13` is

```text
111101_2 = 61.
```

Here `Q_13=1`, so (3) gives

```text
R_6 = 61+1 = 62 = 111110_2.
```

Thus the two words already differ at this depth.  Their Hamming weights both
happen to equal five, so a popcount-only comparison does not detect this
first seam.

## 2. The exact escape-height cocycle

Write the Euclidean decomposition

\[
 R_K=z_K2^K+h_K,\qquad 0\leq h_K<2^K.                  \tag{4}
\]

The integer `h_K` is the low quotient suffix.  The integer `z_K` records the
part discarded when the quotient row is treated as a `K`-bit suffix.

Let `D_K=A intersect {2,...,K+1}` and put

\[
 u_K=2a_{2K+2}+a_{2K+3},
\]

where `a_n` is the `n`-th binary digit of `1/21`, and

\[
 L_K=2\,\operatorname{supportCoeff}(D_K,2K+2)
       +\operatorname{supportCoeff}(D_K,2K+3).
\]

The two-step quotient identity and the new endpoint quotient

\[
 \left\lfloor\frac{2^{2K+3}}{2^{K+2}-1}\right\rfloor=2^{K+1}
\]

give

\[
 R_{K+1}=4R_K+u_K-L_K-b_{K+2}2^{K+1}.                 \tag{5}
\]

Take the Euclidean quotient and remainder of

\[
 A_K=4h_K+u_K-L_K
\]

by `2^(K+1)`:

\[
 A_K=c_K2^{K+1}+h_{K+1},\qquad0\leq h_{K+1}<2^{K+1}.
\]

Substitution in (5) yields the exact cocycle

\[
 \boxed{z_{K+1}=2z_K+c_K-b_{K+2}.}                    \tag{6}
\]

When `z_K=0`, `c_K` and `b_(K+2)` are Boolean, and the quotient comparison is
one-sided, nonnegativity of `z_(K+1)` gives `c_K>=b_(K+2)`.  Agreement keeps
the height zero.  A quotient-only take, `c_K=1` and `b_(K+2)=0`, injects one
unit into (6); every later agreement doubles it.  Thus the fatal homogeneous
mode is exactly the high quotient of the same odd suffix whose low part is
used in the density computation.

The recurrence for `h_K` alone deletes `z_K`.  Consequently no potential on
the bounded suffix can distinguish zero flux from a positive escape height
unless it also controls the discrepancy `c_K-b_(K+2)`.

## 3. The binary carry term missing from the suffix audit

Let

\[
 q_K=Q_{2K+1}\bmod2^K,
 \qquad
 \epsilon_K=\left\lfloor\frac{W_K+q_K}{2^K}\right\rfloor.
\]

Then (3)-(4) imply

\[
 h_K=(W_K+q_K)\bmod2^K.                                \tag{7}
\]

Let `Carr_K(W_K,q_K)` be the total number of binary carry operations in the
addition of the two `K`-bit integers.  The standard digit-sum identity for
addition gives

\[
 \boxed{
 s_2(W_K)=s_2(h_K)-s_2(q_K)
          +\operatorname{Carr}_K(W_K,q_K)+\epsilon_K.}
 \tag{8}
\]

This is the exact binary-borrow debt.  One seam may propagate through an
arbitrarily long string, so the number of changed digits is not bounded by
the number of seams.  Exact computation through actual greedy rank `20000`
finds

```text
K = 8600,
Q_(2K+1) = q_K = 5,
s_2(W_K) = 4252,
s_2(h_K) = 4240,
Carr_K(W_K,q_K) = 14,
epsilon_K = 0.
```

Here `R_K=W_K+5<2^K`, so `z_K=0` and `h_K=R_K`; the reservoir has bit length
`8600`.  The raw period-six source has `2867` ones in the block.  The tested
quotient-suffix bound permits

```text
floor((2K+5)/3) = 5735
```

ones, leaving quotient-word slack `5735-4240=1495`.  Since `b_(K+1)=0`, the
odd delayed-doubling bound (12) has the same allowance and leaves actual-word
slack `5735-4252=1483`.  The twelve-unit difference between these two slacks
is exactly the carry term in (8).

Thus `s_2(W_K)-s_2(h_K)=12`.  This falsifies any transfer from the quotient
suffix to the actual block with a borrow allowance of two, or with any
smaller constant.  The calculation does not prove that the discrepancy is
unbounded.

In particular, the finite inequality

\[
 3s_2(h_K)-2K\leq5
\]

reported for the quotient suffix is not the corresponding finite check of
the delayed-doubling inequality.  The latter concerns `s_2(W_K)` and requires
the carry term in (8).

## 4. The block discrepancy and the self-double charge

For the even doubling block put

\[
 V_K=B(2K)-B(K).
\]

The proposed density inequality at `N=2K` is exactly

\[
 V_K\leq\left\lfloor\frac{2K}{3}\right\rfloor+2.       \tag{9}
\]

The block endpoints give the unconditional recurrence

\[
 V_{K+1}-V_K=-b_{K+1}+b_{2K+1}+b_{2K+2}.               \tag{10}
\]

Hence the raw debt

\[
 \mathcal D_K=2K+6-3V_K
\]

satisfies

\[
 \mathcal D_{K+1}-\mathcal D_K
 =2+3b_{K+1}-3b_{2K+1}-3b_{2K+2}.                     \tag{11}
\]

The rank `K+1` divides `2K+2`.  If it is selected, its guaranteed divisor
contribution pays three units of the four-unit loss caused by a newly
selected pair at `2K+1,2K+2`; the remaining change in (11) is `-1`.  If the
ancestor is skipped and both endpoints are selected, the change is `-4`.
All eight triples

\[
 (b_{K+1},b_{2K+1},b_{2K+2})\in\{0,1\}^3
\]

occur in the exact replay through rank `20000`.  Thus neither the
self-double contribution nor any sign rule on one such triple proves (9).
An amortised proof must transport unpaid carry debt to later multiples.

For odd depths, (1) gives the exact form

\[
 B(2K+1)-B(K)=b_{K+1}+s_2(W_K).
\]

Therefore the proposed inequality at `N=2K+1` is equivalent to

\[
 b_{K+1}+s_2(W_K)
 \leq\left\lfloor\frac{2K+1}{3}\right\rfloor+2.        \tag{12}
\]

Equations (8), (11), and (12) are the exact connection between the actual
doubling blocks, the quotient suffix, and the divisor feedback at a double.

## 5. A countermodel to weakened amortisation hypotheses

The fixed period-six source, Booleanity, nonnegative quotient defect, and
exact divisor feedback do not imply (9).  Take

\[
 A_7=\{d:d\geq7\}.
\]

Since

\[
 \sum_{d\geq7}\frac1{2^d-1}
 <\sum_{d\geq7}2^{1-d}=\frac1{32}<\frac1{21},
\]

every truncated binary coefficient numerator for `A_7` lies below the
corresponding denominator-`21` target quotient.  Thus the exact defect

\[
 Q_N=\left\lfloor\frac{2^N}{21}\right\rfloor
     -\sum_{n\leq N}\operatorname{supportCoeff}(A_7,n)2^{N-n}
\]

is nonnegative at every depth.  The support is Boolean, and every selected
`d` contributes to the divisor load at `2d`.  Nevertheless

\[
 B(18)-\left\lfloor\frac{18}{3}\right\rfloor-B(9)
 =12-6-3=3,
\]

so the proposed bound with constant two fails.

This countermodel is not the greedy support for `1/21`.  Its purpose is to
isolate the missing hypothesis: a valid potential must use the exact greedy
take/skip inequalities at every scale.  The period-six source, a nonnegative
carry, and the self-double pulse do not suffice, even when they are retained
together.

More generally, after any finite actual greedy prefix ending immediately
before a selected rank `m`, one may skip `m` and select every sufficiently
late rank while remaining below `1/21`, because
`mersenneTail_lt_weight` gives

\[
 \sum_{d>m}\frac1{2^d-1}<\frac1{2^m-1}.
\]

Such supports can agree with the actual orbit through an arbitrarily long
finite prefix and then violate every fixed doubling-density bound.  No
finite-prefix or eventual divisor-feedback argument can replace the global
greedy complementarity condition.

## 6. Finite status of the density candidate

`delayed_doubling_borrow_cocycle_audit.py` checks the actual greedy word by
a dyadic integer enclosure.  Through rank `20000`,

\[
 B(N)-\lfloor N/3\rfloor-B(\lfloor N/2\rfloor)\leq2.
\]

The maximum is first attained at `N=11`, not `N=13`.  This is a finite
calculation.  The exact cocycles above neither prove nor falsify the
all-depth inequality.

## 7. Claim corrections for the delayed-density note

Three statements in `DelayedDoublingDensityAttack.md` require the following
qualifications.

First, the estimate

\[
 \sum_{n>K}e_n<\frac23 4^{-K}
\]

places the unresolved correction inside one depth-`2K` cell, but it does not
determine the actual doubling-block word.  Crossing that cell boundary may
start one carry chain, and a single chain may change an arbitrarily long
binary suffix.  The statement that ranks above `K` cannot modify the word
must therefore be replaced by the exact congruence (7).

Second, the quotient-suffix computation is not an analogous computation of
the actual block density.  The two words differ at `K=6`, and (8) is the
exact transfer law.  A valid amortised statement need not bound the carry
loss by an absolute constant.  It must bound that loss by the unused density
allowance of the quotient word, with the later divisor loads paying any debt
which persists across scales.  At `K=8600` the quotient slack is `1495`, the
carry loss is `12`, and the actual slack is `1483`.

Third, the adversarial boundary requires all of the following information at
once: the period-six source, the divisor incidences of the same Boolean word,
and exact greedy complementarity.  The support `A_7` proves that the first
two, even with nonnegative quotient defect, do not imply the density bound.

## 8. A stronger endpoint-compensated reservoir

Let `t_n` be the period-six source bit, let

\[
 h(n)=\sum_{d\mid n}b_d-b_n,
 \qquad
 s_n={\bf1}_{2\mid n}b_{n/2},
\]

and retain the exact defect recurrence

\[
 Q_n=2Q_{n-1}+t_n-b_n-h(n).                           \tag{13}
\]

Put

\[
 P_N=T(N)+B(\lfloor N/2\rfloor)-B(N),
 \qquad R_N=P_N+3-Q_N,
\]

and consider the sharper candidate

\[
 F_N=P_N+4-2Q_N=R_N-Q_N+1.                            \tag{14}
\]

This is not a renaming of the reservoir inequality.  It charges the current
endpoint defect one additional time.  Indeed

\[
 P_N-P_{N-1}=t_N-b_N+s_N,
\]

so (13) gives both exact forms of its increment:

\[
 \begin{aligned}
 F_N-F_{N-1}
   &=b_N-t_N+s_N+2h(N)-2Q_{N-1}\\
   &=h(N)+s_N-Q_N.                                    \tag{15}
 \end{aligned}
\]

There is also an exact borrow-area interpretation.  Set

\[
 A_N=\sum_{n<N}Q_n,
 \qquad
 D_N=\sum_{\substack{d\leq N/2\\b_d=1}}
          \left\lfloor\frac Nd\right\rfloor.
\]

Summing the defect recurrence and exchanging the divisor sums gives

\[
 P_N=D_N-A_N+Q_N.
\]

Consequently

\[
 R_N=D_N-A_N+3,
 \qquad
 F_N=D_N-A_N-Q_N+4.                                  \tag{16}
\]

Thus `F_N >= 0` is precisely the endpoint-compensated borrow-area bound

\[
 A_N+Q_N\leq D_N+4.                                  \tag{17}
\]

It is strictly stronger as an algebraic inequality than `R_N >= 0` whenever
the endpoint defect is large.  No equivalence of the two inequalities on the
actual greedy orbit is known.

### 8.1 Why the sharper law would force the reservoir law

There is nevertheless an exact finite-prefix implication which makes (17) a
decisive sufficient theorem rather than an unrelated socket.

**Lemma.**  If `F_n >= 0` for every `n <= N`, then `R_n >= 0` for every
`n <= N`.

**Proof.**  From (14) and `Q_n >= 0`, one first has `R_n >= -1`.  Suppose
`n <= N` is the first rank with `R_n=-1`.  Then (14) forces `Q_n=0`, while
`R_{n-1}>=0`.  The exact reservoir increment is

\[
 R_n-R_{n-1}=h(n)+s_n-Q_{n-1}.
\]

It follows that

\[
 Q_{n-1}=R_{n-1}+h(n)+s_n+1\geq h(n)+s_n+1.
\]

But (13), Booleanity of `b_n,t_n`, and nonnegativity of `h(n)` then give

\[
 Q_n
 =2Q_{n-1}+t_n-b_n-h(n)
 \geq h(n)+2s_n+1>0,
\]

contradicting `Q_n=0`.  Since `R_0=3`, no negative reservoir rank exists.
\(\square\)

Therefore an all-depth proof of `P_N+4 >= 2Q_N` would imply `R_N>=0`, hence
the delayed-doubling inequality with constant three established by the
reservoir reduction.  It does not by itself improve that constant to two.

### 8.2 Necessary shape of a first failure

If `N` were the first rank with `F_N<0`, (15) would force the exact integer
inequality

\[
 Q_N\geq F_{N-1}+h(N)+s_N+1.                          \tag{18}
\]

Equivalently,

\[
 2Q_{N-1}\geq
 F_{N-1}+b_N-t_N+s_N+2h(N)+1.                         \tag{19}
\]

Applying the preceding lemma only through rank `N-1` also shows that such a
first failure must have `Q_{N-1}>=1`.  For if `Q_{N-1}=0`, the first line of
(15) can decrease `F` by at most one.  A failure would require
`F_{N-1}=0`, `t_N=1`, and `b_N=s_N=h(N)=0`; but then
`R_{N-1}=F_{N-1}+Q_{N-1}-1=-1`, contradicting the finite-prefix lemma.

These conditions identify the remaining obstruction sharply: a failure
requires a positive inherited defect followed by a current defect larger
than all current proper-divisor and self-double feedback plus the entire
available `F` margin.  Equation (18) is only a necessary first-failure
condition, not a proof that the event cannot occur.

The cofinite support `A_7` from Section 5 adversarially falsifies any attempt
to derive (17) from the defect recurrence, nonnegative defect, Booleanity,
and eventual self-double feedback alone.  Its first failure is already

\[
 N=7,\qquad Q_7=5,\qquad P_7=1,\qquad F_7=-5.
\]

Thus the missing all-depth argument must still use actual greedy
complementarity; (15) does not make that dependence disappear.

### 8.3 The canonical comparator is an equivalent socket

At a fixed horizon put

\[
 a_{N,d}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor,
 \qquad
 g_{N,d}=2a_{N,d}-{\bf1}_{2d>N}.
\]

For an arbitrary Boolean word `x`, (14) has the finite linear expansion

\[
 F_N(x)=T(N)+4-2\left\lfloor\frac{2^N}{21}\right\rfloor
        +\sum_{d\leq N}g_{N,d}x_d.                   \tag{20}
\]

The coefficients `g_(N,d)` are strictly superincreasing in decreasing rank.
For `d>N/2`,

\[
 g_{N,d}=2^{N-d+1}-1,
 \qquad
 g_{N,d}-\sum_{e>d}g_{N,e}=N-d+1.
\]

For `d<=N/2`, the usual quotient dominance gap gives

\[
 a_{N,d}\geq 2^{N-\lfloor N/2\rfloor}
              +\sum_{d<e\leq N/2}a_{N,e},
\]

while the sum of all upper-half `g` coefficients is strictly less than twice
the displayed power of two.  Since `g_(N,d)=2a_(N,d)` in the lower half,
strict superincrease follows there as well.

Let `z^(N)` be the lexicographically least word crossing the threshold

\[
 \sum_{d\leq N}g_{N,d}z^{(N)}_d
 \geq
 2\left\lfloor\frac{2^N}{21}\right\rfloor-T(N)-4.   \tag{21}
\]

It is tempting to regard real-Mersenne feasibility of `z^(N)` as a new route
to (17).  In fact it is exactly equivalent to (17) on the actual greedy word.
If `z^(N)` is feasible, greedy lexicographic maximality and superincrease of
the `g` coefficients imply `F_N(b)>=0`.  Conversely, if `F_N(b)>=0`, then
the threshold definition gives `z^(N)<=b` in lexicographic order.  The real
Mersenne weights are themselves strictly superincreasing, by

\[
 \sum_{e>d}\frac1{2^e-1}<\frac1{2^d-1}.
\]

Hence `z^(N)` has real sum no larger than the feasible actual prefix `b`, so
`z^(N)` is feasible.  The comparator is therefore a dual certificate for the
same invariant, not an independent reduction.

This equivalence also corrects a misleading apparent failure at `N=63`.
For that comparator, `Q=2`, the threshold overshoot is `2`, and the sum of
fractional quotient remainders is approximately `2.313459`.  The feasibility
criterion is not that this last number be at most `Q`; it is

\[
 \Phi_N\leq Q_N+\left\{\frac{2^N}{21}\right\}.
\]

Here the omitted target fraction is `8/21`, so the right side is about
`2.380952`.  The comparator is feasible, with

\[
 2^{63}(1/21-S)\approx0.0674931>0.
\]

Directed integer rounding certifies the positive sign.

### 8.4 Exact finite audit

The accompanying script checks (13)--(16) on the actual greedy orbit.  Through
rank `100000`,

\[
 \min_{N\leq100000}F_N=0,
\]

with equality only at `N=9,13`.  Among ranks with `Q_N=0`, the minimum
reservoir is `1`, first at `N=10`.  The maximum one-step withdrawal
`Q_N-h(N)-s_N` is already `33`, first at `N=95759`, where `F_N=7839`;
thus a pointwise bound on the withdrawal is neither true nor the observed
mechanism.  The computation is exact but finite.  The all-depth inequality
(17) remains unproved.

The canonical comparator from (21) was separately certified real-feasible
through horizon `2000`.  Its smallest directed fractional margin in that
range occurs at `N=63`.  By the equivalence just proved, this is another
finite certificate of the same `F_N>=0` data, not additional evidence toward
an all-depth argument.
