# Polynomial-shifted factorial LCMs, excess layer mass, and the 3/2 packaging

Ordinary proofs for Erdős #68. The pre-existing `n!-1` segment bound in
`ChannelIntegralCongruence.lean` is Lean-checked. The general shifted gcd identity is in `PolynomialPerturbationLcm.lean`.
The first focused build failed (`linarith` used without import, so the gcd
theorems depended on `sorryAx`). The parent replaced those tactics by
`ring`/`calc`. A later `lean_fast_build.py` returned 75 and queued
`cf_9f83e6a6e4f64e37b2bf`; there is still no kernel receipt. The parent irrationality of
\(S=\sum_{n\ge2}(n!-1)^{-1}\) remains open.

## Collision with the live corpus

The live packet already contains:

- `factorial_gap_lcm_segment_bound` (Lean): 
  \(\prod_{n=N-k+1}^N(n!-1)\le L_N\, N^{\binom{k+1}{3}}\).
- `factorial_gap_lcm_lower_bound` (ordinary, GLS): \(\log L_N\gg N^{4/3}\log N\).
- Finite square-subsequence radius theorems that *use* the same segment
  inequality, including a Lean-checked \(R+1>(3/2)t^3\) bound at \(t\ge 2^{32}\).
- Affine-defect rigidity and the Kovač–Tao quadratic window, which concern
  sequences *near* \(n!-1\), not \(\operatorname{lcm}(n!+P(n))\).
- The integer-shift family \(S_t=\sum 1/(n!+t)\), which is a rationality
  criterion, not an lcm-growth theorem.

The displayed liminf
\[
\liminf_{N\to\infty}\frac{\log L_N}{N^{3/2}\log N}\ge\frac{2\sqrt2}{3},
\qquad L_N=\operatorname{lcm}_{2\le n\le N}(n!-1),
\]
is therefore **not a new mechanism**. It is Stirling packaging of the
Lean-checked segment bound, and it is strictly stronger than the GLS \(4/3\)
exponent. It is recorded here as an ordinary corollary, not as an independent
discovery. Digit-law, companion-orbit, channel-radius, and carry-characterization
labs do not occupy the polynomial-shift statement.

## 1. The 3/2 packaging of the Lean segment bound

Write \(d_n=n!-1\) and \(L_N=\operatorname{lcm}_{2\le n\le N}d_n\). Lean already
proves that a finite list of positive integers satisfies
\(\prod_i x_i\mid\operatorname{lcm}_i(x_i)\prod_{i<j}\gcd(x_i,x_j)\), and that
\(\gcd(i!-1,j!-1)\) divides \(j!/i!-1<N^{j-i}\) for \(2\le i<j\le N\). On the
terminal block of \(k\) indices the pair-distance sum is \(\binom{k+1}{3}\), so
\[
\log L_N\ge\sum_{n=N-k+1}^N\log(n!-1)-\binom{k+1}{3}\log N.
\]
Take \(k=\lfloor\alpha\sqrt N\rfloor\). Stirling’s bounds
\(n\log n-n-\log 2\le\log(n!-1)\le n\log n\) make the sum
\((\alpha+o(1))N^{3/2}\log N\) and the loss \((\alpha^3/6+o(1))N^{3/2}\log N\).
The resulting coefficient \(\alpha-\alpha^3/6\) is maximised at \(\alpha=\sqrt2\),
with value \(2\sqrt2/3\).

This is an ordinary corollary of a Lean-checked finite inequality. It is not a
lower bound for \(\operatorname{den}(H_N)\), and it does not prove \(S\)
irrational.

## 2. Polynomial perturbation (new, ordinary)

Let \(P\in\mathbb Z[X]\) be a fixed *nonzero* polynomial, choose \(n_0\) so that
\(n!+P(n)>0\) for all \(n\ge n_0\), and set
\[
L_N(P)=\operatorname{lcm}_{n_0\le n\le N}\bigl(n!+P(n)\bigr).
\]
Then
\[
\liminf_{N\to\infty}\frac{\log L_N(P)}{N^{3/2}\log N}\ge\frac{2\sqrt2}{3}.
\]
The constant is independent of \(P\); the threshold from which the estimates
hold may depend on \(P\).

**Proof.** Write \(D=\deg P\). For large \(N\), \(P\) has no roots on
\([N/2,N]\) and there are constants \(c_P,C_P>0\) with
\(c_P N^D\le|P(i)|\le C_P N^D\) on that interval. For \(i<j\) in the interval
put \(Q=j!/i!\) and \(g=\gcd(i!+P(i),j!+P(j))\). Subtracting \(Q\) times the
first argument from the second yields
\[
g\mid P(j)-QP(i).
\]
The integer on the right is nonzero for large \(N\): \(Q\ge i+1\ge N/2\), while
\(|P(j)/P(i)|\) stays bounded. Moreover
\[
\bigl|P(j)-QP(i)\bigr|\le 2C_P N^{D+j-i},
\]
so \(\log g\le(j-i)\log N+D\log N+O_P(1)\). The product-lcm-gcd identity on the
last \(k=\lfloor\alpha\sqrt N\rfloor\) values, whose indices lie in \([N/2,N]\)
for large \(N\), therefore gives
\[
\log L_N(P)\ge
\sum_{n=N-k+1}^N\log\bigl(n!+P(n)\bigr)
-\binom{k+1}{3}\log N-O_P(k^2\log N).
\]
Since \(|P(n)|/n!\to0\) uniformly on the block, eventually
\(n!/2\le n!+P(n)\le 2n!\). The same Stirling estimate as in §1 produces the
gain \(\alpha\) and the cubic loss \(\alpha^3/6\). Take \(\alpha=\sqrt2\). ∎

The kernel-checkable step is the identity
\(\gcd(i!+P(i),j!+P(j))\mid P(j)-(j!/i!)P(i)\), source-landed in
`PolynomialPerturbationLcm.lean` (focused kernel receipt 2026-09-06). The printed
factorial-polynomial congruence
behind the gcd step appears in Lai, arXiv:2103.14894v1, proof of Lemma 2.4,
(2.5); Stewart records the plus-sign case for \(n!+1\). No literature search
here is a priority claim for the lcm conclusion.

**The nonzero hypothesis cannot be dropped.** If \(P=0\), then
\(L_N(0)=N!\) and \(\log L_N(0)/(N^{3/2}\log N)\to0\). The corresponding gcd collapse \(\gcd(i!,j!)=i!\) for \(i\le j\) is
source-landed in the same Lean module. Constant shifts
\(P=t\neq0\) are the immediate specialisation; they are not the same object as
the already-formalised rationality boundary for \(S_t\).

## 3. Excess layer mass, not pairwise gcd mass

For a finite list of positive integers \(d_2,\ldots,d_N\) put
\[
P_N=\sum_n\log d_n,\qquad
E_N=P_N-\log L_N,\qquad
G_N=\sum_{i<j}\log\gcd(d_i,d_j),
\]
and \(h_{r,e}=\#\{n:r^e\mid d_n\}\). Expanding each valuation by occupied
layers gives
\[
\begin{aligned}
P_N&=\sum_{r,e}h_{r,e}\log r,\\
\log L_N&=\sum_{r,e}\mathbf1_{h_{r,e}\ge1}\log r,\\
E_N&=\sum_{r,e}(h_{r,e}-1)_+\log r,\\
G_N&=\sum_{r,e}\binom{h_{r,e}}{2}\log r.
\end{aligned}
\]
A layer of multiplicity \(h\ge2\) contributes \(h-1\) to \(E_N\) and
\(\binom h2\) to \(G_N\), so \(E_N\le G_N\le(N-1)E_N/2\).

For factorial gaps, Stirling summation yields \(P_N=\tfrac12 N^2\log N+O(N^2)\).
Consequently the proposed equivalence “exponent \(3/2\) is sharp if and only
if \(G_N\) has order \(N^{3/2}\log N\)” is false:

- if \(G_N=O(N^{3/2}\log N)\), then \(E_N=o(P_N)\), hence
  \(\log L_N\sim\tfrac12 N^2\log N\);
- if \(\log L_N=O(N^{3/2}\log N)\), then \(E_N\sim P_N\), hence
  \(G_N\ge(\tfrac12+o(1))N^2\log N\).

The quantity that decides whether the elementary exponent can be improved is
the *excess repeated-layer mass* \(E_N\). A bound on total pairwise gcd mass
is sufficient for controlling \(E_N\) but can overcount highly repeated layers.
No proof or counterexample of \(\log L_N\gg N^{2-o(1)}\) is claimed here.

## 4. The constant \(2\sqrt2/3\) is optimal for the coarse terminal-block estimate

Among lower bounds of the shape
\[
\log L_N\ge\sum_a\log(i_a!-1)-\sum_{a<b}(i_b-i_a)\log N
\]
over ordered subsets \(2\le i_1<\cdots<i_k\le N\), the terminal block
\(i_a=N-k+a\) is simultaneously maximal for the first sum (monotonicity of
\(n!-1\)) and minimal for the subtracted distances (\(i_b-i_a\ge b-a\)). At
\(k\sim\alpha\sqrt N\) the leading coefficient is \(\alpha-\alpha^3/6\), whose
positive maximum is \(2\sqrt2/3\). Replacing \((j-i)\log N\) by \(\log(j!/i!)\)
on that block saves only \(O(N)\). This is a barrier for this coarse
optimisation, not a theorem that the actual lcm exponent is \(3/2\).

## 5. Full-lcm clearing cannot make the positive tail small

Let \(T_N=S-H_N\). The 3/2 packaging supplies a fixed \(c>0\) with
\(\log L_N\ge c N^{3/2}\log N\) eventually, while
\(\log((N+1)!)=O(N\log N)\). Hence \(L_N/((N+1)!)^A\to\infty\) for every fixed
\(A>0\). Positivity of the series gives \(T_N>1/((N+1)!-1)\), so
\(L_N T_N\to\infty\). A lower bound for the *common* denominator therefore
pushes the naive “positive integer below one” argument *away* from success.
Useful cancellation must act on a different linear form or a smaller
multiplier. This does not rule out the complementary-residue route.

## 6. Joint budget (algebraic rewriting, not a new estimate)

On a tailored block with \(R_p>1\), write \(\delta_p=\rho_p/R_p\) and
\(\widetilde C_p\) for the normalised collision core. The registered global
sufficient inequality \((2p+1)L_p^{\mathrm{blk}}<K_p\rho_p\) with
\(L_p^{\mathrm{blk}}=F_p\widetilde C_p R_p\) and \(F_p=(p-1)!\) is exactly
\[
\log\widetilde C_p+\log(1/\delta_p)
<\log\frac{K_p}{(2p+1)F_p}=p\log p+(2\log 2-1)p+O(\log p).
\]
Both losses must be controlled on the *same* cofinal family. Coprimality of
the complementary residue and a large private modulus do not by themselves
meet the scale: the model \(\widetilde C=1\), \(T=R-1\), \(\rho=1\) with \(R\)
an arbitrarily large prime has \(\gcd(T,R)=1\) and \(\delta=1/R\), and fails
the inequality once \(R\) is large. That model is not realised by the factorial
recurrence; it only kills the qualitative shortcut.

A deterministic averaging form is available: if, along unbounded \(X\), a
nonempty set of primes in \([X,2X]\) with \(R_p>1\) has mean normalised losses
adding to a constant strictly less than one, then some prime in the set meets
the budget, and the registered complementary-residue criterion yields
irrationality. No such averages are proved for the factorial construction.
The parent problem remains open.
