# Every positive power replaces the square-root repair deadline

Ordinary proof. Historical novelty unassessed. This refines the already
Lean-checked generic real-target theorem
`mem_iff_greedyBinaryDefect_sqrt_windows` in
[GreedyRepairCriterion.lean](GreedyRepairCriterion.lean). It does not prove
membership of \(1/2\) or \(1/21\).

## Theorem

Fix \(0<\varepsilon<1\). There is a constant \(C_\varepsilon\), independent
of the real target \(x\ge0\), such that for the actual greedy support
\(A_x\), its Lambert prefix numerator \(P_N\), and
\(Q_N=\lfloor 2^N x\rfloor-P_N\), the following are equivalent:

(a) \(x\) belongs to the Mersenne achievement set;

(b) for every \(K\ge0\), some \(N\) with
\(K\le N<K+\lceil C_\varepsilon(K+1)^\varepsilon\rceil\) satisfies
\(Q_{N+1}\le Q_N\).

Moreover non-membership makes \(Q_N\) eventually strictly increasing, so
(b) remains equivalent if required only for arbitrarily late \(K\).

**Proof.** For every \(\delta>0\) there is \(D_\delta\) with
\(\tau(n)\le D_\delta n^\delta\) for all positive integers: for primes
\(p\ge 2^{1/\delta}\) use \(e+1\le 2^e\le p^{\delta e}\); for the finitely
many smaller primes the supremum of \((e+1)p^{-\delta e}\) is finite.

If \(x\) is represented, the exact Lambert-prefix identity gives
\[
0\le Q_N\le\sum_{r\ge1}\tau(N+r)2^{-r}
\le D_\delta(N+1)^\delta\sum_{r\ge1}(r+1)^\delta 2^{-r}
=H_\delta(N+1)^\delta.
\]
Take \(\delta=\varepsilon/2\). Choose \(C>1\) so large that
\(C>H_\delta(C+3)^\delta\), possible because \(\delta<1\), and put
\(T=\lceil C(K+1)^\varepsilon\rceil\). If all \(T\) transitions in the
stated window strictly increase the integer \(Q\), then
\(Q_{K+T}\ge T\ge C(K+1)^\varepsilon\). But
\(K+T+1\le(C+3)(K+1)\) since \(\varepsilon<1\), so the same value is
bounded by \(H_\delta(C+3)^\delta(K+1)^\delta<C(K+1)^\varepsilon\), a
contradiction.

Conversely, a non-member has a fatal greedy rank with a positive excess
\(\gamma\) above all remaining mass. The excess persists, so the actual
greedy residual satisfies \(r_N\ge\gamma\) thereafter. The exact prefix
decomposition gives \(Q_N+1\ge 2^N r_N\), hence \(Q_N\ge 2^N\gamma-1\).
The one-step recurrence is
\(Q_{N+1}=2Q_N+\beta_N-c_{A_x}(N+1)\) with \(\beta_N\in\{0,1\}\). Since
\(c_{A_x}(N+1)\le\tau(N+1)\) grows subpolynomially, eventually
\(Q_{N+1}-Q_N>0\). Thus all sufficiently late windows fail (b). ∎

The square-root exponent in the registered theorem reflects its elementary
divisor-function envelope. It is not an intrinsic dynamical exponent. The
fully explicit square-root bound remains useful for computation. Neither
establishes a repair on either unresolved rational orbit.

The same orbit's exact one-step obligation is
\(Q_{N+1}\le Q_N\) iff \(c_{A_x}(N+1)\ge Q_N+\beta_N\). At \(x=1/2\) one
has \(\beta_N=0\) for \(N\ge1\). Pointwise majorants on synthetic pulses
do not supply these inequalities for the actual greedy selector.
