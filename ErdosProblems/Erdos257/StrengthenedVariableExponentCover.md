# Strengthened variable-exponent covers and a support beyond every old cover

Ordinary proofs. Historical novelty unassessed. These statements do not
replace the Lean-checked reciprocal-summable theorem, which remains the
paper lead and the Palomar flagship.

## Collision with r2

The r2 note
[VariableExponentCoverSeparation.md](VariableExponentCoverSeparation.md)
lands two facts that stay in force:

* \(A^\dagger\), with reserved primes \(q_j\in(2^{6j},2^{6j+1})\), satisfies
  the manuscript (old) variable-exponent criterion
  \(\sum_j C_j 2^{j\alpha_j} 2^{\alpha_j}/(2^{\alpha_j}-1)^2<\infty\), while
  every fixed-\(\alpha\) positive cover and every finite-prime weighted mass
  diverges;
* a pairwise-coprime reciprocal-divergent family defeats every positive
  cover, old or new.

The r3 package is not a restatement of those rows. It enlarges the
sufficient class from the old cost to
\(\sum_j C_j 2^{j\alpha_j}/(2^{\alpha_j}-1)<\infty\), then exhibits a
squarefree support \(A^\star\) which meets the new criterion, fails every
old cover (not merely the displayed one), and still has divergent
reciprocal and finite-\(P\) weighted mass. The cover-independent averaging
lemma already Lean-checked in
[CoverIndependentPeriodicMean.lean](CoverIndependentPeriodicMean.lean)
is reused; it is not re-announced as new kernel work.

The pairwise-coprime obstruction still defeats the new method, so this
improvement does not absorb Tao–Teräväinen on the primes.

## Theorem A.1 (uniform modular estimate)

For real \(B>1\) and positive integers \(L,d,X\),
\[
\frac1X\sum_{m=1}^{X}\frac{B^{Lm\bmod d}}{B^d-1}
\le\frac{B^L}{d\log B}.
\]
The limit as \(X\to\infty\) is \(g/(d(B^g-1))\) with \(g=\gcd(L,d)\), and
this is at most \(1/[d(B-1)]\).

**Proof.** Write \(h(t)=B^{t-d\lfloor t/d\rfloor}/(B^d-1)\) for \(t\ge0\).
On each interval \([L(m-1),Lm]\) the exponent in \(h(Lm)/h(t)\) is
\[
Lm-t-d\bigl(\lfloor Lm/d\rfloor-\lfloor t/d\rfloor\bigr)\le L,
\]
hence \(h(Lm)\le B^L h(t)\). Summing therefore gives
\[
\frac1X\sum_{m=1}^X h(Lm)
\le\frac{B^L}{LX}\int_0^{LX}h(t)\,dt.
\]
If \(Y=kd+r\) with \(0\le r<d\), then
\[
\int_0^Y h(t)\,dt
=\frac{k+(B^r-1)/(B^d-1)}{\log B}.
\]
Convexity of \(r\mapsto B^r\) yields \((B^r-1)/(B^d-1)\le r/d\), so the
integral is at most \(Y/(d\log B)\). This is (A1). The residues of \(Lm\)
modulo \(d\) are \(0,g,\ldots,d-g\), each once per period \(d/g\); their
geometric mean is the stated limit. Finally \(B^g-1\ge g(B-1)\). ∎

For \(1<B\le2\) one has \(B^L/\log B\le 2^{L+1}/(B-1)\). The large factor
depends on the already fixed \(L\), which is harmless for dominated
convergence. No uniformity in unbounded \(L\) is claimed.

The reconstruction script checks (A1) on small \((B,L,d,X)\). It does not
replace the ordinary proof.

## Theorem A.2 (strengthened positive-cover criterion)

Let \((F_j)_{j\ge1}\) be finite subsets of the positive integers. Suppose
\(0<\alpha_j\le1\), \(c_{j,d}\ge0\),
\[
f_{F_j}(n)^{\alpha_j}\le\sum_{d\mid n}c_{j,d},
\qquad
C_j=\sum_{d\ge1}\frac{c_{j,d}}d.
\]
Let \(\eta_j>0\) with \(\sum_j\eta_j=1\). If
\[
\sum_{j\ge1}\frac{C_j\eta_j^{-\alpha_j}}{2^{\alpha_j}-1}<\infty,
\]
then every infinite \(A\subseteq\bigcup_j F_j\) has irrational
\(X_A(b)=\sum_{a\in A}(b^a-1)^{-1}\) at every integer base \(b\ge2\).
The choice \(\eta_j=2^{-j}\) is the displayed new cost.

**Proof.** Write \(B_j=2^{\alpha_j}\) and
\[
U_F(n)=\sum_{r\ge1}2^{-r}f_F(n+r),\qquad
V_j(n)=\sum_{r\ge1}B_j^{-r}\sum_{d\mid n+r}c_{j,d}.
\]
Subadditivity of \(x\mapsto x^{\alpha_j}\) gives
\(U_{F_j}(n)^{\alpha_j}\le V_j(n)\). Regrouping yields
\[
V_j(n)=\sum_{d\ge1}c_{j,d}\frac{B_j^{n\bmod d}}{B_j^d-1}.
\]
Theorem A.1 supplies, for each fixed \(L\), an integrable dominator over
\(d\), so
\[
\lim_{X\to\infty}\frac1X\sum_{m\le X}V_j(Lm)
=\sum_d\frac{c_{j,d}\gcd(d,L)}{d(B_j^{\gcd(d,L)}-1)}
\le\frac{C_j}{B_j-1},
\]
and every finite average is bounded by \(2^{L+1}C_j/(B_j-1)\).

Fix \(\varepsilon>0\) and put \(t_j=\varepsilon\eta_j\). Because
\(0<\alpha_j\le1\), the factor \(\varepsilon^{-\alpha_j}\) is bounded by
\(\max(1,\varepsilon^{-1})\). Choose \(J\) so that
\(\sum_{j>J}C_j t_j^{-\alpha_j}/(B_j-1)<1\). Only after choosing \(J\),
choose \(L\) divisible by every member of \(\bigcup_{j\le J}F_j\). For this
fixed \(L\), dominated convergence over \(j\) is licensed by A.1 and the
new cost. The Cesàro limit of
\(S(m)=\sum_{j>J}t_j^{-\alpha_j}V_j(Lm)\) is then less than 1, so
arbitrarily large \(m\) have \(S(m)<1\). At every such \(m\),
\(\sum_{j>J}U_{F_j}(Lm)<\varepsilon\).

The first \(J\) covering sets contribute zero binary displacement at
\(N=Lm\). Each remaining selected exponent is covered by some later
\(F_j\). Positivity, even with overlaps, gives
\(0<\Delta_A(Lm)\le\sum_{j>J}U_{F_j}(Lm)<\varepsilon\), the left-hand
strict inequality because an infinite support contains an exponent larger
than \(Lm\). If \(X_A(2)=p/q\), every positive displacement is at least
\(1/q\). The registered factor-two comparison of binary and radix-\(b\)
displacements transfers the same argument to every integer base. ∎

Neither \(\alpha_j\) nor \(B_j-1\) is bounded away from zero. The cover
need not be disjoint. The conclusion includes all infinite thinnings.

## Theorem B.1 (cover-independent logarithmic-square obstruction)

For a finite positive set \(F\) write
\[
\mathbb E_F H(f_F)
=\frac1{\operatorname{lcm}(F)}\sum_{n=1}^{\operatorname{lcm}(F)}H(f_F(n)),
\qquad
\log^+t=\log\max(1,t).
\]
For any positive cover as in A.2, the old cost
\[
K=\sum_{j\ge1}C_j 2^{j\alpha_j}\frac{2^{\alpha_j}}{(2^{\alpha_j}-1)^2}
\]
satisfies \(K\ge\tfrac12\mathbb E_F[(\log^+ f_F)^2]\) for every finite
\(F\subseteq A\). Unbounded finite periodic logarithmic-square moments
therefore exclude every old variable-exponent positive cover.

**Proof.** Put \(k(\alpha)=2^\alpha/(2^\alpha-1)^2\). Convexity of \(2^x\)
on \([0,1]\) gives \(2^\alpha-1\le\alpha\), hence \(k(\alpha)\ge\alpha^{-2}\).
Coverage yields \(\sum_j f_{F_j}(n)\ge f_F(n)\). Since \(\sum_j 2^{-j}=1\),
some \(j\) has \(f_{F_j}(n)\ge 2^{-j}f_F(n)\). Consequently
\[
\sum_j 2^{j\alpha_j}k(\alpha_j)\sum_{d\mid n}c_{j,d}
\ge k(\alpha_j)\,f_F(n)^{\alpha_j}
\ge\frac{e^{\alpha_j\log f_F(n)}}{\alpha_j^2}
\ge\tfrac12(\log f_F(n))^2
\]
whenever \(f_F(n)>0\), using \(e^u\ge u^2/2\) for \(u\ge0\). Averaging over
\(1\le n\le X\), Tonelli and \(\lfloor X/d\rfloor/X\le 1/d\) bound the left
average by \(K\). The right average tends to its periodic mean. The
already-checked Cesàro majorant
`cesaro_le_divisorMajorantCost` is the averaging engine; this argument
adds only the pointwise logarithmic-square comparison and the covering
pigeonhole. ∎

The quantification is over every cover, every overlap, every exponent, and
every enumeration. Failure of a displayed decomposition is not enough.

## Theorem B.2 (a squarefree class beyond every old cover)

There is an infinite set \(A^\star\) of squarefree positive integers such
that:

1. every infinite subset of \(A^\star\) has irrational \(X_A(b)\) at every
   integer base \(b\ge2\);
2. no old variable-exponent positive cover of \(A^\star\) has finite cost;
3. its reciprocal sum diverges, and its finite-prime weighted mass diverges
   for every finite prime set and every integer base.

**Construction.** Choose pairwise distinct primes \(q_j\) with
\(2^{3j}<q_j<2^{3j+1}\) (Bertrand; the intervals are disjoint). Remove
these primes and \(2\) from the primes. The leftover reciprocal sum still
diverges. Choose pairwise disjoint finite blocks \(P_j\) of remaining
primes with \(4^j\le S_j:=\sum_{p\in P_j}1/p\le 4^j+1\). Put
\(M_j=\prod_{p\in P_j}p\), \(F_j=\{q_j d:d\mid M_j\}\),
\(A^\star=\bigcup_j F_j\), and \(\alpha_j=4^{-j}\).

**New cost.** Within a frame,
\(f_{F_j}(n)=\mathbf 1_{q_j\mid n}\,2^{\omega_{P_j}(n)}\), with exact cost
\[
C_j=\frac1{q_j}\prod_{p\in P_j}\Bigl(1+\frac{2^{\alpha_j}-1}{p}\Bigr)
\le\frac{e^{\alpha_j S_j}}{q_j}
\le e^{5/4}2^{-3j}.
\]
Since \(2^{\alpha_j}-1\ge\alpha_j\log 2\) and \(2^{j\alpha_j}\) is bounded,
\[
\sum_j\frac{C_j 2^{j\alpha_j}}{2^{\alpha_j}-1}
\ll\sum_j 2^{-3j}4^j=\sum_j 2^{-j}<\infty.
\]
Theorem A.2 gives assertion 1.

**Old covers.** For a uniform residue modulo \(q_j M_j\), the indicators
\(\mathbf 1_{p\mid n}\) are independent Bernoulli of means \(1/p\),
independent also of \(\mathbf 1_{q_j\mid n}\). Hence
\[
\mathbb E_{F_j}[(\log^+ f_{F_j})^2]
=\frac{(\log 2)^2}{q_j}\mathbb E\Bigl[\Bigl(\sum_{p\in P_j}\mathbf 1_{p\mid n}\Bigr)^2\Bigr]
\ge\frac{(\log 2)^2 S_j^2}{q_j}
>\frac{(\log 2)^2}{2}\,2^j.
\]
Theorem B.1 gives assertion 2 for every old cover, not merely the displayed
frames.

**Weighted mass.** A finite prime set \(P\) meets only finitely many
frames. On later frames \(h_P\equiv 1\), and
\[
\sum_{a\in F_j}\frac{h_P(a)}{a(b^{h_P(a)}-1)}
=\frac1{(b-1)q_j}\prod_{p\in P_j}\bigl(1+1/p\bigr)
\]
tends to infinity because \(\log\prod(1+1/p)\ge S_j-\tfrac12\sum p^{-2}\)
dominates \(\log q_j=O(j)\). Reciprocal divergence is the same calculation
without \(1/(b-1)\). ∎

**Relation to \(A^\dagger\).** The r2 support used the sparser windows
\((2^{6j},2^{6j+1})\) and therefore satisfied the old cost. Changing the
reserved-prime scale to \(2^{3j}\) makes the old cost diverge on the
displayed cover; B.1 upgrades that to every cover. Reconstruction
`reconstruct_variable_exponent_dagger.py --quick` checks the analytic
discriminator (old \(A^\star\) terms grow; old \(A^\dagger\) terms decay)
and Bertrand windows \(q=11,67,521\) for \(j=1,2,3\). It does not
enumerate the \(4^j\) blocks.

## What this does not do

It does not change the paper lead. Reciprocal summability remains the
Lean-checked all-base hereditary theorem, and is the statement Erdős
printed with coprimality and asserted without coprimality. A
reciprocal-divergent pairwise-coprime family still defeats the new
positive-cover method. Universal #257, membership of \(1/2\), and
membership of \(1/21\) remain open.
