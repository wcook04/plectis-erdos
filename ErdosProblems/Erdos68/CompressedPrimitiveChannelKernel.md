# Compressed primitive channel kernels and moment absorption

Ordinary proofs for Erdős #68. The residual identity
\(\mathcal R=MS+K\) is already Lean-checked in `PrimeUnitTranslator.lean`
(`exists_channelResidual_eq_moment_mul_factorialGapSeries_add_int` and the
Cramer specialisation). The live Cramer grid uses step \((D!)^2\). This note
records a smaller arithmetic grid, an explicit primitive kernel, and the
consequence that cofinal nonintegrality is equivalent to irrationality on any
unbounded family of these grids. The parent series remains open: no
nonintegrality producer is proved.

`--quick` checkers:

```
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/scripts/check_compressed_primitive_channel_kernel.py --quick
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos68/scripts/check_interval_optimal_cf_extraction.py --quick
```

## Collision with the live corpus

- `cramer_nonzero_moment_channel_kernel_producer` and
  `uniform_factorial_grid_rank_two_reduction` already produce a zero-channel
  vector of nonzero moment on the coarser grid of step \((D!)^2\). The
  construction below is a smaller step and an explicit primitive
  normalisation, not a new residual identity and not a proof that
  \(\det(A)S\) is nonintegral.
- `rank_two_producer_is_a_smoothness_exclusion_not_an_irrationality_route`
  remains correct for *one* kernel: nonintegrality of \(\mathcal R=MS+K\) is
  exactly \(q\nmid M\). Its promotion to a prohibition on every unbounded
  factorial-grid family is false for the grids below.
- `canonical_channel_kernel_D2_D12` is a finite regeneration of a different
  (returned) primitive family, not this closed form.
- `global_complementary_tail_residue_reduction` is already Lean-checked. It is
  not re-announced here.
- The live finite CF lead remains \(q\ge 2^{39990}>10^{12038}\). An
  interval-optimal extraction from the same enclosure is ordinary geometry;
  the numerical floor \(Q_*>10^{12040}\) is not used as the live lead without
  reconstructing the remaining complete-quotient interval. The 80000-bit scan
  is not rerun.

## 1. Closed-form primitive kernel on a compressed grid

Let \(D\ge 2\), \(r\ge 2\), and let \(L\) be a positive multiple of every
integer \(2,\ldots,D\). Put
\[
i_j=r+jL\quad(0\le j<D),\qquad N=r+(D-1)L,
\qquad a_d=(d!)^{L/d}\quad(2\le d\le D).
\]
Define \(H(X)=\prod_{d=2}^D(a_d X-1)=\sum_{j=0}^{D-1}h_j X^j\) and
\(A=\prod_{d=2}^D a_d\). The primitive integer channel-annihilating vector is
\[
\lambda_j^*=\frac{N!\,h_j}{A\,i_j!}\qquad(0\le j<D).
\]
Every coordinate is an integer, \(\lambda^*_{D-1}=1\), and every integer
vector annihilating channels \(2,\ldots,D\) on this grid is an integer
multiple of \(\lambda^*\). Its moment is
\[
M(\lambda^*)=\frac{N!}{A}H(1)=N!\prod_{d=2}^D\Bigl(1-\frac1{a_d}\Bigr)>0.
\]

**Proof.** Associate to an integer vector \(\lambda\) the polynomial
\(F_\lambda(X)=\sum_j\lambda_j i_j! X^j\). Because \(L/d\) is integral, the
\(d\)-channel is a nonzero rational multiple of \(F_\lambda(a_d^{-1})\). The
roots \(a_d\) are distinct: \((d!)^{1/d}\) is strictly increasing, since
\((d+1)^d>d!\), and raising to the common power \(L\) preserves
distinctness. Vanishing channels therefore force \(F_\lambda=cH\) for a
rational scalar \(c\).

The coefficient \(h_j/A\) of \(H/A=\prod(X-a_d^{-1})\) is
\[
(-1)^{D-1-j}\sum_{\substack{B\subseteq\{2,\ldots,D\}\\|B|=D-1-j}}
\frac1{\prod_{d\in B}a_d}.
\]
For one such \(B\), \(N-i_j=|B|L\). Partitioning \(|B|L\) elements into
\(L/d\) blocks of size \(d\) for each \(d\in B\) shows
\(\prod_{d\in B}a_d\mid(|B|L)!\), and \((|B|L)!\mid N!/i_j!\). Every summand
of \(\lambda_j^*\) is therefore integral, including the empty-subset endpoint
\(\lambda^*_{D-1}=1\).

The associated polynomial is \((N!/A)H\), so the channels vanish. A last
coordinate of one makes the vector primitive. Any other integer kernel has
polynomial \(cH\); comparing leading coefficients gives
\(\lambda=\lambda_{D-1}\lambda^*\). The moment is \(F_\lambda(1)\). QED.

The sufficient step is \(L=\operatorname{lcm}(2,\ldots,D)\). At \(D=6\) this
replaces Lean's \(518400=(6!)^2\) by \(60\). For \(D=2\) and \(L=2\) one has
\(\lambda^*=\bigl(-(r+1)(r+2)/2,\,1\bigr)\) and \(M=(r+2)!/2\).

## 2. Factorial divisibility after primitive reduction

Every nonzero integer channel-annihilating vector on the same grid has moment
divisible by
\[
r!\Bigl(\prod_{d=2}^D(L/d)!\Bigr)\Bigl(\prod_{d=2}^D(a_d-1)\Bigr).
\]
In particular \(r!(L/2)!\mid M(\lambda)\). This holds for the primitive
vector, not merely for raw Cramer cofactors.

**Proof.** The leading-coefficient relation \(F_\lambda=cH\) is
\(\lambda_{D-1}N!=cA\). Write \(k_d=L/d\). The block-partition count
\[
\frac{N!}{r!\prod_{d=2}^D(d!)^{k_d}k_d!}
\]
is an integer, so \(r!A\prod k_d!\mid N!\). Thus \(r!\prod k_d!\mid N!/A\mid c\).
Multiply by \(H(1)\). QED.

## 3. Unbounded families absorb every fixed denominator

Take any sequence of such grids with \(N_t\to\infty\) and any nonzero integer
kernel on each. Then \(\lfloor\sqrt{N_t}/2\rfloor!\mid M_t\), so every fixed
positive integer \(q\) divides \(M_t\) for all large \(t\). Combined with the
Lean residual identity \(\mathcal R_t=M_t S+K_t\),
\[
S\notin\mathbb Q
\quad\Longleftrightarrow\quad
\mathcal R_t\notin\mathbb Z\text{ for arbitrarily large }t.
\]
No separate bound below a rational lattice spacing is required for this
family. Nonintegrality of the actual residuals remains open.

**Proof.** Section 2 gives \(r_t!(L_t/2)!\mid M_t\). Put
\(u_t=\max(r_t,L_t/2)\). Then \(D_t\le L_t\le 2u_t\) and
\(N_t=r_t+(D_t-1)L_t<4u_t^2\), so
\(\lfloor\sqrt{N_t}/2\rfloor!\mid u_t!\mid M_t\). If \(S=a/q\) then \(M_t S+K_t\)
is eventually integral. If \(S\) is irrational then each nonzero \(M_t\) makes
the residual irrational. QED.

## 4. Interval-optimal CF extraction (ordinary geometry)

If a closed rational interval \(I\) has \(j\) common continued-fraction
quotients, last common convergent \(p_j/q_j\), predecessor \(p_{j-1}/q_{j-1}\),
and remaining complete-quotient interval \((\alpha,\beta)\) containing an
integer \(k=\lfloor\alpha\rfloor+1\) with \(k<\beta\), then the smallest
denominator of any rational in \(I\) is \(Q_*=k q_j+q_{j-1}\), attained at
the complete quotient \(k\). Unimodularity of the CF matrix keeps the image
reduced. This is not a new enclosure. The live #68 receipt stores the last
common convergent size, not \((\alpha,\beta)\); the 80000-bit scan is not
rerun. The printed lead stays \(q\ge 2^{39990}>10^{12038}\). The two power
comparisons \(2^{39996}\) and \(10^{12040}\) must not be chained:
\(2^{39996}<10^{12040}\).
