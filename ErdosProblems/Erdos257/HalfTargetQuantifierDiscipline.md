# Half-target quantifiers restored

Type B's revision packet correctly objected to two claim-language errors in
the *reviewed short note*, not in the live Palomar paper. The live paper
never stated a global doubling shadow for the seam coordinate, and the live
declaration

`Erdos257PeriodNoncollapse.greedyMersenneSecondChannelPhaseRat_succ`

already includes the rank-dependent translations
\(2^{n+1}\) on both branches. This note locks the restored quantifiers so
they cannot be re-strengthened.

## S1 (horizon-dependent shadowing)

A finite-horizon carry-free identity of the shape

\[
\forall k\ \bigl(\text{carry-free}(N,\ldots,N+k-1)
\Longrightarrow
\exists M_k,\delta_k:\ 
y_{N+k}=2^k(y_N-\delta_k)-M_k\bigr)
\]

does not yield a single pair \((M,\delta)\) independent of \(k\). Witnesses
may depend on the horizon. A global shadowing point, a bounded fundamental
domain, equidistribution, or a geometric-gap law is a separate claim and is
not supplied by a finite-horizon locator. Finite trigger histograms through
any bounded rank remain finite arithmetic.

The live tree records finite half-cylinder shadows in
`HalfCylinderFiniteShadow.lean` with the same discipline: finite identities,
no global no-wrap.

## S2 (non-autonomous phase map)

The exact rational second-channel recurrence is

\[
\Phi_{n+1}=
\begin{cases}
4\Phi_n+2^{n+1}, & \Phi_n<\tau_n,\\
4\Phi_n-2^{n+1}-2-2/(2^{n+1}-1), & \Phi_n\ge\tau_n,
\end{cases}
\qquad
\tau_n=2^n/(2^{n+1}-1).
\]

Omitting the translations \(2^{n+1}\) changes the dynamics. The open
interval \((0,1)\) is not forward invariant: \(z=1/4\) skips and lands
beyond \(1\). Its complement is not invariant either. The explicit greedy
state \(x=17/256\) has \(\Phi_2=-15/8\) and \(\Phi_3=1/2\). These witnesses
refute a global trapping-region argument. They do not decide S2 for the
target \(1/2\).

Independent exact check:
`scripts/reconstruct_variable_exponent_dagger.py` (`s2_witness`).
