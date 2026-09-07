# Cover-independent means and the variable-exponent remainder

Ordinary proofs. Historical novelty unassessed. These statements do not
replace the Lean-checked reciprocal-summable theorem, which remains the
paper lead and the Palomar flagship.

The manuscript already records a variable-exponent positive-cover criterion
and warns that its displayed moving-frame example “does not exclude other
fixed-exponent covers of the same union.” The arguments below close that
gap, then record the complementary obstruction.

## Lemma (cover-independent periodic mean)

Let \(F\) be finite and \(0<\alpha\le 1\). Write
\(f_F(n)=\#\{a\in F:a\mid n\}\) and
\[
\mathcal M_\alpha(F)=\frac1{L_F}\sum_{n=1}^{L_F}f_F(n)^\alpha,
\qquad L_F=\operatorname{lcm}(F).
\]
Suppose \(A\subset\bigcup_i G_i\) is a countable cover by finite sets, each
equipped with a nonnegative divisor majorant of cost \(C_i=\sum_d c_{i,d}/d\)
for the same exponent \(\alpha\). Then for every finite \(F\subset A\),

\[
\mathcal M_\alpha(F)\le\sum_i C_i.
\]

**Proof.** Finitely many of the \(G_i\) cover \(F\). Subadditivity of
\(t\mapsto t^\alpha\) on \([0,\infty)\) for \(0<\alpha\le 1\) gives
\(f_F(n)^\alpha\le\sum_i f_{G_i}(n)^\alpha\le\sum_i\sum_{d\mid n}c_{i,d}\).
Averaging over \(1\le n\le X\) and using \(\lfloor X/d\rfloor/X\le 1/d\)
bounds the Cesàro mean by \(\sum_i C_i\). The periodic mean is the Cesàro
mean at \(X=L_F\). No conditionally convergent sum is interchanged. ∎

The Lean module
[CoverIndependentPeriodicMean.lean](CoverIndependentPeriodicMean.lean)
checks the averaging inequality for an arbitrary nonnegative \(g\) dominated
by a finite divisor majorant. The coprime-union density identity used below
is an ordinary argument in this note.

## Theorem (a support beyond every fixed-\(\alpha\) cover and every finite-\(P\) weight)

Reserve a prime \(q_j\) in \((2^{6j},2^{6j+1})\) by Bertrand. The leftover
odd primes still have divergent reciprocal sum. From them choose pairwise
disjoint finite blocks \(P_j\) with
\[
4^j\le\sum_{p\in P_j}\frac1p\le 4^j+1.
\]
Put \(M_j=\prod_{p\in P_j}p\), \(F_j=\{q_j d:d\mid M_j\}\),
\(A^\dagger=\bigcup_j F_j\), and \(\alpha_j=4^{-j}\). The frames are
disjoint. Every infinite \(B\subset A^\dagger\) has irrational
\(X_B(b)\) at every integer base \(b\ge 2\), by the manuscript's
variable-exponent criterion. Nevertheless:

1. every fixed-\(\alpha\) positive divisor-majorant cover of \(A^\dagger\)
   has infinite total cost;
2. \(W_{b,P}(A^\dagger)=\infty\) for every finite nonempty prime set \(P\)
   and every \(b\ge 2\);
3. the reciprocal sum of \(A^\dagger\) diverges, and the support is
   squarefree and not contained in the prime powers.

**Proof of the variable-exponent bound.** For squarefree \(M\) and
\(F=\{gd:d\mid M\}\) the exact nonnegative expansion is
\[
f_F(n)^\alpha=1_{g\mid n}\prod_{p\mid M}\bigl(1+(2^\alpha-1)1_{p\mid n/g}\bigr),
\]
with cost \(C=g^{-1}\prod_p\bigl(1+(2^\alpha-1)/p\bigr)\). Convexity of
\(2^x\) on \([0,1]\) gives \(2^{\alpha_j}-1\le\alpha_j\). With
\(q_j>2^{6j}\) and \(\alpha_j S_j\le 5/4\) one obtains
\(C_j\le e^{5/4}2^{-6j}\). The manuscript's summability factor
\(2^{j\alpha_j}B_j/(B_j-1)^2\) is then \(O(2^{-2j})\). Heredity is the
manuscript's.

**Proof excluding every fixed exponent.** The exact periodic mean of the
\(j\)th frame is
\[
\mathcal M_\alpha(F_j)=q_j^{-1}\prod_{p\in P_j}(1+(2^\alpha-1)/p).
\]
The estimate \(\log(1+x)\ge x-x^2/2\) together with \(S_j\ge 4^j\) sends
this mean to infinity. The cover-independent lemma forces every fixed-\(\alpha\)
cover to have infinite cost.

**Proof of infinite weighted mass.** A finite prime set \(P\) meets
\(\{q_j\}\cup P_j\) for only finitely many \(j\). On all later frames
\(h_P\equiv 1\), so the weighted mass is a positive multiple of the frame
reciprocal mass, which tends to infinity by the \(\alpha=1\) case. ∎

The reconstruction script
[scripts/reconstruct_variable_exponent_dagger.py](scripts/reconstruct_variable_exponent_dagger.py)
checks the exact frame identities, the elementary inequalities, small-\(j\)
Bertrand windows, and a miniature dagger. It does not enumerate the \(4^j\)
prime-harmonic blocks.

## r3 successor (not a restatement)

The old variable-exponent cost is strictly enlarged in
[StrengthenedVariableExponentCover.md](StrengthenedVariableExponentCover.md).
That note's support \(A^\star\) uses reserved primes in
\((2^{3j},2^{3j+1})\) and lies outside every old cover, including every
regrouping of the present \(A^\dagger\). Reciprocal summability remains the
Lean flagship; the pairwise-coprime obstruction below still defeats the new
method.

## Theorem (pairwise-coprime obstruction)

Suppose \(A\) contains a pairwise-coprime set \(E\subset\{2,3,\dots\}\) with
divergent reciprocal sum. Then every countable cover of \(A\) by finite sets,
with any exponents \(\alpha_i>0\) and any nonnegative divisor majorants,
has infinite total cost. In particular the manuscript's variable-exponent
summability condition fails, as does every finite-\(P\) weighted test.

**Proof.** Write \(E_i=E\cap G_i\) and \(H_i=\sum_{a\in E_i}1/a\). On the
event that some \(a\in E_i\) divides \(n\), one has \(f_{G_i}(n)^{\alpha_i}\ge 1\).
Pairwise coprimality and the Chinese remainder theorem give periodic density
\(1-\prod(1-1/a)\ge 1-e^{-H_i}\) for that event. Averaging the majorant as in
the lemma yields \(C_i\ge 1-e^{-H_i}\). Finite total cost would force
\(H_i=O(C_i)\) for large \(i\), hence \(\sum H_i<\infty\), contradicting
divergence of \(\sum_{a\in E}1/a\). The manuscript's extra factors
\(2^{i\alpha_i}B_i/(B_i-1)^2\) are at least \(2\) for \(0<\alpha_i\le 1\), so
its summability condition already implies \(\sum C_i<\infty\). ∎

The primes themselves are such an \(E\). Their irrationality is Tao–Teräväinen,
not a positive-cover or finite-\(P\) theorem. Failure of those sufficient
methods is not evidence of rationality.

## What this does not do

It does not change the paper lead. Reciprocal summability remains the
Lean-checked all-base hereditary theorem, and is the statement Erdős printed
with coprimality and asserted without coprimality. The weighted and
variable-exponent criteria are strict enlargements of that flagship, not
replacements of it.
