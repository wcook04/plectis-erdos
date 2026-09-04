# The first-failure greedy bridge and the phase seam

Status: exact deductions and one exact finite counterexample, 2026-08-20.
This note does not prove the endpoint-compensated invariant.  It identifies
the missing real-greedy datum exactly and proves that the period-six digit
source, the integer defect recurrence, divisor incidence, and even genuine
real-greedy complementarity inside the same binary cylinder do not by
themselves exclude a first failure.

## 1. The decision before the Boolean digit is chosen

Let `b_d` be the actual greedy support for `x=1/21`, and write

\[
 H_N=\left\lfloor\frac{2^N}{21}\right\rfloor,
 \qquad
 \alpha_N=\left\{\frac{2^N}{21}\right\},
 \qquad
 q_{N,d}=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor.
\]

Before the decision at rank `N`, put

\[
 C_N=H_N-\sum_{d<N}b_dq_{N,d}
     =2Q_{N-1}+t_N-h(N),                              \tag{1}
\]

and define the fractional divisor-clock phase

\[
 \Phi_N=\sum_{d<N}b_d
   \left\{\frac{2^N}{2^d-1}\right\}
 =\sum_{d<N}b_d\frac{2^{N\bmod d}}{2^d-1}.           \tag{2}
\]

If `r_(N-1)` is the real greedy remainder before rank `N`, splitting every
scaled Mersenne coin into its integer quotient and fractional remainder gives
the exact identity

\[
 \boxed{\quad 2^Nr_{N-1}=C_N+\alpha_N-\Phi_N.\quad}   \tag{3}
\]

Consequently the real greedy decision is

\[
 \boxed{
 b_N=1
 \iff
 C_N+\alpha_N-\Phi_N
 \geq \frac{2^N}{2^N-1}.}                            \tag{4}
\]

After the decision, `Q_N=C_N-b_N`.  If

\[
 \Psi_N=\Phi_N+\frac{b_N}{2^N-1},
\]

then the post-decision remainder is

\[
 2^Nr_N=Q_N+\alpha_N-\Psi_N\geq0.                    \tag{5}
\]

The fractional state has the same divisor pulse as the integer state:

\[
 \Phi_N=2\Psi_{N-1}-h(N).                             \tag{6}
\]

Equations (1), (3), and (6) are the exact joint bridge.  The integer
predefect says which binary cell contains the residual; `alpha_N-Phi_N`
says on which side of the Mersenne threshold it lies.  Dropping the latter
term loses the actual take/skip decision.

## 2. A complete description of a moving seam

More generally, fix a rank `m` and suppose the prefix through `m-1` is held
fixed.  Put

\[
 Y_m=C_m+\alpha_m-\Phi_m=2^mr_{m-1}.
\]

For `k>=1`, the next greedy block is

\[
 b_m b_{m+1}\cdots b_{m+k}=0\,1^k
\]

if and only if

\[
 \boxed{
 2^m\sum_{j=1}^k\frac1{2^{m+j}-1}
 \leq Y_m
 <\frac{2^m}{2^m-1}.}                                \tag{7}
\]

Indeed, the upper inequality is exactly the skip at `m`.  Conditional on
that skip, all of the next `k` coins are taken precisely when the old
remainder pays their total; because their partial sums increase with `k`,
the last partial sum is the only additional inequality needed.

This interval is the moving seam in one scalar coordinate.  Its location is
binary-suffix capacity, while `Phi_m` is the complete divisor/LCM phase.
Thus (7) is an exact alignment law, not an analogy between the two effects.

At the horizon `N=m+k`, replacing the block `1 0^k` by `0 1^k` loses exactly
`k+1` units in the linear functional for

\[
 F_N=P_N+4-2Q_N.
\]

Indeed all these ranks lie above `N/2`, where the coefficient of rank `d`
in `F_N` is

\[
 g_{N,d}=2^{N-d+1}-1.
\]

Therefore

\[
 g_{N,m}-\sum_{j=1}^kg_{N,m+j}=k+1.                  \tag{8}
\]

Equations (7) and (8) isolate the common mechanism behind seam escape and
borrow failure: landing just below the early Mersenne threshold replaces one
early digit by a later run and spends a discrete `k+1` units of the
endpoint-compensated reservoir.

## 3. Same-cylinder real-greedy first failure

The fractional phase in (3) is indispensable.  Set

\[
 x^-=\frac1{21}-\frac1{3\,2^{63}}.
\]

For every `n<=63`,

\[
 \left\lfloor2^nx^-\right\rfloor
 =\left\lfloor\frac{2^n}{21}\right\rfloor.
\]

Thus `x^-` and `1/21` have exactly the same first 63 source bits, including
the same period-six source used by the defect recurrence.  Exact rational
verification of the displayed floor equality is short: for `n<=60` the
scaled perturbation is at most `1/24`, smaller than the least target phase
`1/21`; at ranks `61,62,63` it is respectively `1/12,1/6,1/3`, smaller than
the corresponding phases `2/21,4/21,8/21`.

Exact rational greedy calculation then gives the same support through rank
60:

\[
\begin{split}
\{5,7,8,9,10,11,13,16,18,20,22,24,28,32,34,37,39,
42,45,46,47,49,50,51,53,54,57,58,59,60\}.
\end{split}
\]

The two genuine real-greedy orbits then make the opposite seam exchange

\[
 \begin{array}{c|c}
 \text{target}&(b_{61},b_{62},b_{63})\\ \hline
 1/21&100\\
 x^-&011.
 \end{array}                                         \tag{9}
\]

At rank 61 the common prefix has `C_61=2` and the same `Phi_61`.  The exact
target has `alpha_61=2/21`, whereas `x^-` has
`alpha_61^-=1/84`.  Equivalently their seam coordinates differ by exactly
`1/12`.  Directed rational comparison gives

\[
 2^{61}\left(\frac1{2^{62}-1}+\frac1{2^{63}-1}\right)
 <Y^-_{61}
 <\frac{2^{61}}{2^{61}-1}
 <Y_{61}.                                            \tag{10}
\]

So (7) forces `011` for `x^-`, while (4) forces the protective early take
for `1/21`.

The integer endpoint states are

\[
\begin{array}{c|cc|cc}
 &\multicolumn{2}{c|}{1/21}&\multicolumn{2}{c}{x^-}\\
 n&(Q_n,P_n,F_n)&b_n&(Q_n,P_n,F_n)&b_n\\ \hline
 60&(1,3,5)&1&(1,3,5)&1\\
 61&(1,2,4)&1&(2,3,3)&0\\
 62&(2,2,2)&0&(3,2,0)&1\\
 63&(2,2,2)&0&(3,1,-1)&1.
\end{array}                                         \tag{11}
\]

For `x^-`, rank 63 is the first negative value of `F`.  At that rank
`h(63)=2`, `s_63=0`, and the exact first-failure increment is

\[
 F_{63}-F_{62}=h(63)+s_{63}-Q_{63}=-1.
\]

This is a genuine real-greedy counterexample to every proposed first-failure
argument which uses only the finite source word, Booleanity, divisor
incidences, the nonnegative integer defect recurrence, and take/skip
complementarity abstracted away from the fractional target phase.  All of
those data are present here.  What distinguishes the prescribed target is
the exact rational endpoint `alpha_m`, coupled to the divisor-clock phase
`Phi_m` in (3).

## 4. The remaining law

A first-failure proof for `1/21` must therefore establish a phase-exclusion
statement: whenever a block `0 1^k` would spend more than the available
`F` margin through (8), the exact quantity

\[
 C_m+\alpha_m-\Phi_m
\]

must avoid the interval (7).  This is stronger than a bound on `Phi_m`
alone, and stronger than the period-six digit recurrence alone.  It is the
precise joint suffix-capacity/divisor-pulse assertion which remains
unproved.  The rank-61 calculation shows that the phase allowance can be
narrow: changing the endpoint by `1/12` in scaled seam coordinates changes
the protective block `100` into the fatal block `011` while leaving every
source digit through the failure unchanged.
