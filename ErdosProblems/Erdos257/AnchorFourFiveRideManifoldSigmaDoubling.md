# Sigma-doubling is the dyadic residual in cylinder coordinates

## Status

This note gives an exact identity and a conditional all-depth reduction for
the compressed source corridor of

\[
 x=\frac1{465}=w_4w_5,
 \qquad w_d=\frac1{2^d-1}.
\]

It does not solve Erdős #257.  The deviation which doubles during a
non-extraction ride is exactly a finite-prefix real residual measured from a
dyadic half-tail.  The doubling law is useful, but it is not an independent
arithmetic invariant.  The remaining task is a target-specific separation
theorem for the prefixes which are actually reachable by the corridor.

The companion program verifies the online truncated identity and the corridor
invariants with exact integer arithmetic through a chosen finite horizon.  No
finite audit is promoted to an all-depth statement.

## 1. The corrected echo identity

Fix a selected prefix $P\subseteq\{1,\ldots,p\}$ and put

\[
 R_P=x-\sum_{d\in P}w_d,
 \qquad
 Q_m(P)=\left\lfloor2^mx\right\rfloor
  -\sum_{d\in P}\left\lfloor\frac{2^m}{2^d-1}\right\rfloor.
\]

Let $t_j$ be the binary digits of $x$, let

\[
 g_P(j)=\#\{d\in P:d\mid j\},
 \qquad \rho_j=g_P(j)-t_j,
\]

and define the forward echo

\[
 \sigma_m^P=\sum_{k\geq1}2^{-k}\rho_{m+k}.
\]

Swapping the absolutely convergent sums gives

\[
 \boxed{
 \sigma_m^P
 =\sum_{d\in P}\left\{\frac{2^m}{2^d-1}\right\}
   -\left\{2^mx\right\}
 =Q_m(P)-2^mR_P.}                                  \tag{1}
\]

The target fractional part in (1) is essential.  A support-only formula is
not the echo of $g_P-t$.  Nor does the oddness of the individual denominators
imply that $\sigma_m^P$ is nonintegral; rational fractional terms can cancel.

## 2. Exact doubling and what it means

Suppose the source corridor is normalized at rank $m=p+L$, with fixed prefix
$P$, suffix endpoint

\[
 A_m=2^{L-1}+\delta_m,
\]

and quotient coordinate $Q_m(P)=A_m$.  Combining this normalization with
(1) yields

\[
 \boxed{
 e_m:=\delta_m-\sigma_m^P
 =2^m\left(R_P-2^{-p-1}\right).}                   \tag{2}
\]

During a non-extraction run, $P$ and $p$ remain fixed while $m$ increases by
one.  Hence (2) immediately gives

\[
 \boxed{e_{m+h}=2^h e_m}                            \tag{3}
\]

for every rank in that run.  Equivalently,
$\sigma_{j+1}^P=2\sigma_j^P-\rho_{j+1}$ and the cylinder displacement obeys
the same affine recurrence.

This has two rigorous consequences.

First, since $0\leq\delta_j<K_j$ and
$|\sigma_j^P|<|P|+1$, a ride which continues for $h$ steps satisfies

\[
 2^h|e_m|\leq K_{m+h}+p+1.                          \tag{4}
\]

Thus a ride much longer than $\log_2 K$ requires the reachable residual
$R_P$ to shadow $2^{-p-1}$ exponentially closely.

Second, a permanent bounded ride would force $e_m=0$, hence
$R_P=2^{-p-1}$.  This is impossible: $R_P$ is rational with odd reduced
denominator, whereas $2^{-p-1}$ is a nonintegral dyadic rational.  This
excludes a permanent ride for a fixed finite prefix, but it gives no uniform
bound on long finite rides.

## 3. Extraction resets and the half-rank gate

The reset estimate needs both orientations.  Before an extraction, write the
old upper endpoint as $2^{L-1}+\delta$ and put

\[
 u=2\delta+t_m-g_P(m).
\]

The enlarged interval is

\[
 \bigl[2^L+u-K_m,\ 2^L+u\bigr].                   \tag{5}
\]

If $0\leq u<K_m$, (5) crosses the half boundary and no leading bit is common.
An extraction can therefore occur only in one of the following two cases.

* If $u\geq K_m$, both endpoints lie above the boundary.  After stripping
  the common leading $1$, the suffix interval is $[u-K_m,u]$.  Since
  $\delta<K_{m-1}$ and $t_m-g_P(m)\leq1$, its width uses $O(\log m)$ bits.
* If $u<0$, both endpoints lie below the boundary.  Put $h=-u$.  They lie in
  the last block of $K_m+h$ integers below $2^L$, so their varying suffix has
  at most $\lceil\log_2(K_m+h)\rceil$ bits.  Moreover
  $h\leq g_P(m)\leq\tau(m)-1$, again giving $O(\log m)$ bits.

Consequently every genuine extraction resets the suffix width to $O(\log m)$.
If all subsequent non-extraction runs have length at most $B(m)=o(m)$, then

\[
 L_m=O(\log m)+B(m)=o(m).
\]

After a finite audited base this gives $p_m=m-L_m\geq m/2$, so every proper
divisor needed by the next transition remains source-locked.  The nested
cylinders then continue at all depths, and their $O(m2^{-m})$ real defects
converge to zero.  This is the valid conditional consumer of a sublinear ride
bound.

## 4. The exact remaining socket

By (2), an echo-gap theorem is exactly the assertion that actual reachable
prefixes do not shadow their dyadic half-tail too well:

\[
 \boxed{
 2^m\left|R_P-2^{-p-1}\right|\geq2^{-f(m)},
 \qquad f(m)=o(m).}                                 \tag{6}
\]

A trivial denominator bound is far too small because the least common
multiple of the selected Mersenne denominators can grow superexponentially in
the prefix length.  A proof of (6) must use the actual ancestry of the
reachable prefix, not just periodicity, parity, or a bounded forcing window.
The known CRT countermodels explain why those local hypotheses are
insufficient.

There is also a useful compactness consumer for failures of the gate.  If a
ride with prefix length $p$ reaches a rank $r\geq2p+1$, (4) and (2) give

\[
 \left|R_P-2^{-p-1}\right|
 \leq (K_r+p+1)2^{-r}.                              \tag{7}
\]

Since

\[
 0<w_{p+1}-2^{-p-1}
 =\frac1{2^{p+1}(2^{p+1}-1)},
\]

adding rank $p+1$ to $P$ produces a finite Boolean sum within
$O(p4^{-p})$ of $x$: for $r\geq2p+1$, the function
$(K_r+p+1)2^{-r}$ is bounded by a constant multiple of
$p2^{-2p}$.  Therefore gate-threatening rides at unbounded
prefix lengths already imply achievement-set membership by closedness.  A
single finite gate loss supplies only one approximant, so the finite-loss
branch remains open.

## 5. Finite verification receipt

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_ride_manifold_sigma_doubling.py --horizon 200000
```

The program maintains the prefix online.  For every recorded ride it evaluates
the truncated echo using exactly the prefix frozen on that ride, includes the
terminal boundary term, and checks

\[
 e^{(J)}_{j+1}=2e^{(J)}_j-2^{-J}\rho_{j+J+1}
\]

with integers scaled by $2^J$.  It also checks full endpoint coverage,
uniqueness, and the half-rank ancestry gate through the requested horizon.
