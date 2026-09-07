# Dynamic source ownership: classification and convex no-go

Status: exact theorem and exact counterfamilies, 2026-08-21. This note does
not prove irrationality in the dense-support case. It classifies every
additive source-local cocycle compatible with the binary carry law and shows
that pairwise overlap and convex ownership purity do not supply a
target-payment inequality.

## 1. The lossless source ledger

For \(d\geq1\), put

\[
 h_d(n)=\frac{2^{\,n\bmod d}}{2^d-1}.
\]

This is the contribution of source \(d\) to the shifted binary tail. It
satisfies the source-resolved carry law

\[
 2h_d(n)-h_d(n+1)=\mathbf 1_{d\mid n+1}.                 \tag{1}
\]

Indeed, away from a multiple of \(d\), the residue and the numerator double.
At the wrap from \(d-1\) to \(0\),

\[
 \frac{2^d}{2^d-1}-\frac1{2^d-1}=1.
\]

For a Boolean support \(A\), the vector

\[
 \mathcal H_A(n)=\bigl(\mathbf1_A(d)h_d(n)\bigr)_{d\geq1} \tag{2}
\]

is absolutely summable in the source coordinate at every \(n\). Summing
(1) gives

\[
 2\lVert\mathcal H_A(n)\rVert_1-
 \lVert\mathcal H_A(n+1)\rVert_1
 =f_A(n+1),                                             \tag{3}
\]

where \(f_A(m)=\#\{d\in A:d\mid m\}\). The checked theorem
<code>binaryCoeffTail_supportCoeff_eq_tsum_shiftedSupportAtom</code> identifies the
scalar total in (2) with the exact binary coefficient tail
([ReciprocalSupportIrrationality.lean:820-834](../../Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean#L820)).
The coordinate step is checked as <code>shiftedSupportAtom_step</code>
([lines 773-781](../../Erdos257PeriodNoncollapse/ReciprocalSupportIrrationality.lean#L773)).
Thus (2) describes every actual support orbit; it is not a relaxation.

## 2. Classification of additive local cocycles

The shifted atom is forced by the carry law.

**Theorem (local cocycle classification).** Let \(V\) be a real vector
space, fix \(d\geq1\), and suppose

\[
 c:\mathbb Z/d\mathbb Z\longrightarrow V,
 \qquad \kappa\in V
\]

satisfy

\[
 2c(a)-c(a+1)=0\quad(0\leq a<d-1),
 \qquad 2c(d-1)-c(0)=\kappa.                         \tag{4}
\]

Then

\[
 \boxed{c(a)=\frac{2^a}{2^d-1}\,\kappa.}            \tag{5}
\]

**Proof.** The first \(d-1\) equations give \(c(a)=2^ac(0)\). The wrap
equation gives

\[
 \kappa=(2^d-1)c(0).
\]

Division by the nonzero scalar \(2^d-1\) proves (5). \(\square\)

Consequently every additive source-local scalar ownership law is a weighted
shifted-atom sum

\[
 \Phi(n)=\sum_{d\in A}\lambda_d h_d(n).              \tag{6}
\]

Taking every \(\lambda_d=1\) recovers the ordinary carry tail. Retaining the
whole family of weights is equivalent to retaining the vector (2). A
source-labelled additive ledger can prevent literal reuse of one coordinate,
but every scalarization factors through the shifted atoms already present in
the exact tail theorem.

This classification is local and unconditional. It does not assume a
rational target, tempering, reciprocal summability, or greediness.

## 3. The exact pair-overlap kernel

The first nonlinear statistic is pairwise overlap. Let

\[
 L=[d,e],\qquad g=(d,e).
\]

Then

\[
 \boxed{
 \frac1L\sum_{n=0}^{L-1}h_d(n)h_e(n)
 =\frac{2^g+1}{3L(2^g-1)}.}                         \tag{7}
\]

To prove this, pair residues \(r\pmod d\) and \(s\pmod e\). The Chinese
remainder condition is \(r\equiv s\pmod g\), and every compatible pair occurs
once modulo \(L\). Writing \(r=c+gi\), \(s=c+gj\), the numerator sum is

\[
 \sum_{c=0}^{g-1}4^c
 \left(\sum_i2^{gi}\right)
 \left(\sum_j2^{gj}\right).
\]

The two geometric sums cancel \(2^d-1\) and \(2^e-1\), leaving

\[
 \frac{\sum_{c=0}^{g-1}4^c}{(2^g-1)^2}
 =\frac{2^g+1}{3(2^g-1)}.
\]

Division by \(L\) gives (7). The overlap kernel therefore retains the exact
LCM phase which a linear scalar tail loses.

Equation (7) is not coercive against the known square-root carry strip. Its
diagonal is

\[
 \frac{2^d+1}{3d(2^d-1)}\sim\frac1{3d},             \tag{8}
\]

so divergent reciprocal support makes the averaged diagonal energy diverge
only on the harmonic scale. This is compatible with a carry of size
\(O(\sqrt n)\); (7) supplies neither a sign nor a target-payment inequality.

## 4. A positive pair-energy resolvent

The overlap kernel also has an exact pointwise evolution. Put

\[
 S_n=\sum_{d\in A}h_d(n),\qquad
 P_n=\sum_{d\in A}h_d(n)^2,\qquad
 E_n=S_n^2-P_n.
\]

Thus \(E_n=\sum_{d\ne e}h_d(n)h_e(n)\) is the ordered cross-source overlap.
For \(m=n+1\), let

\[
 D_m=\{d\in A:d\mid m\},\qquad
 f_m=|D_m|,\qquad
 G_n=\sum_{d\in D_m}h_d(n).
\]

Applying (1) coordinatewise gives

\[
 S_{n+1}=2S_n-f_m,\qquad
 P_{n+1}=4P_n-4G_n+f_m.
\]

Consequently

\[
 \boxed{E_{n+1}=4E_n-C_n,}                         \tag{9}
\]

where

\[
 C_n=4(f_mS_n-G_n)-f_m(f_m-1).                    \tag{10}
\]

This charge is nonnegative. If \(f_m\geq2\), then every \(d\in D_m\) has
\[
 h_d(n)=\frac{2^{d-1}}{2^d-1}>\frac12.
\]
The ordered pairs of distinct pulse sources therefore contribute more than
\(f_m(f_m-1)/2\) to \(f_mS_n-G_n\). Hence

\[
 \boxed{C_n\geq f_m(f_m-1).}                       \tag{11}
\]

For \(f_m=0\), both sides vanish. For \(f_m=1\), (10) is four times the
mass of the other sources and is nonnegative.

The checked universal tail bound
([BooleanMobiusCarry.lean:290-305](../../Erdos257PeriodNoncollapse/BooleanMobiusCarry.lean#L290))
gives \(S_N=O(\sqrt N)\) for every Boolean support. Since
\(0\leq E_N\leq S_N^2\), one has \(E_N/4^N\to0\). Telescoping (9) yields
the exact future-collision resolvent

\[
 \boxed{
 E_n=\sum_{r\geq1}4^{-r}C_{n+r-1}
 \geq\sum_{r\geq1}4^{-r}f_{n+r}(f_{n+r}-1).}       \tag{12}
\]

Equation (12) couples the binary source-age vector to all future
divisor/LCM coincidences with no signed cancellation. It also explains why
the coupling is not yet coercive. A collision delayed by \(r\) places only
the factor \(4^{-r}\) on the right. Sending a finite family to its common
multiple can therefore make its collision charge arbitrarily cheap at the
earlier row. This is the same LCM-height distortion as in the linear carry,
now in an exact positive nonlinear identity.

For a finite support, averaging (9) over a common period gives
\[
 \operatorname{mean}(C)=3\operatorname{mean}(E).
\]
Together with (7), this is an identity, not a contradiction. Reciprocal
divergence makes the finite-prefix pair means unbounded: the kernel in (7)
is at least \(1/(3de)\), so the off-diagonal sum is bounded below by one
third of
\[
 \left(\sum_{d\in F}\frac1d\right)^2-\sum_{d\in F}\frac1{d^2}.
\]
This lower bound can remain far below the available \(O(N)\) pointwise bound
for \(E_N\).

## 5. Convex ownership purity is destroyed by legal carries

Consider a physical dyadic packet of value \(x>0\), with nonnegative source
masses \(m_s\) satisfying \(\sum_sm_s=x\). For \(p>1\), define its normalized
convex purity

\[
 \Pi_p(x,m)=x^{1-p}\sum_sm_s^p.                    \tag{13}
\]

A pure packet has purity \(x\). When two packets of the same value \(x\)
carry to one packet of value \(2x\), their ownership vectors add. Convexity
gives

\[
 \boxed{
 \Pi_p(2x,m+n)\leq\Pi_p(x,m)+\Pi_p(x,n).}           \tag{14}
\]

Thus \(\Pi_p\) is a subadditive nonlinear currency that one might try to
spend on endpoint or target pulses.

It cannot pay them. Start with \(k=2^r\) unit packets owned by \(k\) distinct
sources and merge them through a complete binary carry tree. Every source is
used once, all merge inputs are disjoint, and the final packet has value
\(k\) with ownership mass \(1\) in every source. Its purity is

\[
 \Pi_p(k,(1,\ldots,1))=k^{\,2-p},                  \tag{15}
\]

whereas a source-blind binary bit or endpoint demand can consume its full
value \(k\). The purity-to-value ratio is

\[
 k^{1-p}\longrightarrow0.                          \tag{16}
\]

For quadratic purity, \(k\) units of input purity become exactly one unit,
while the output bit has value \(k\). This is an arbitrary-depth exact
counterfamily.

Shannon mixing does not give a universal local target charge either. A
one-source finite support has an exact rational binary orbit with zero
cross-source mixing and infinitely many nonzero divisor pulses. The target
and the divisor word see scalar value, not the purity or entropy of its
ancestry. An entropy charge would require an additional global hypothesis.

## 6. Why the backward-bank family remains legal

The family in <code>BackwardBankDefectTransport.md</code> does not reuse a source. Its
two non-pure providers have distinct ranks, every pure correction rank
\(e_v=R-v\) is distinct, and each correction is inserted once at the exact
current discrepancy valuation. The resulting carry graph is a path. It
transports a forbidden label-three debt to a forbidden label-two debt over an
unbounded valuation interval while satisfying strict one-use ownership at
every node.

Therefore the proposed rule

> retain source labels and forbid spending the same ancestral quantum twice

does not exclude the counterfamily. The universal ledger (2) records the
transport, and the convex costs (13) record the mixing created by the legal
path. Neither makes the transported endpoint value unavailable.

## 7. Boundary for the next invariant

The results above rule out a precise class, not every ownership argument.

* Additive source-local cocycles are exactly weighted shifted atoms.
* Pairwise overlap has the positive kernel (7) and the positive resolvent
  (12), but LCM delay discounts a future collision by \(4^{-r}\).
* Convex purity is subadditive, yet a source-disjoint carry tree makes it an
  arbitrarily small fraction of the spendable scalar output.
* The backward-bank transport obeys strict one-use ownership.

A coercive invariant must impose a nonlocal admissibility rule on which mixed
output may pay which future pulse. It must couple cross-source phase to the
tempered boundary or to a target-specific scheduling law. A conserved source
vector, an overlap average, or a generic convex cost cannot provide that rule.

## 8. Exact receipt

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/dynamic_ownership_cocycle_classification.py

The script checks the local cocycle formula, the pair-overlap identity, the
convex merge inequality, and the complete distinct-source carry tree in exact
rational arithmetic. The displayed arguments, rather than the finite
regression ranges, prove (5), (7), (9)--(12), and (14)--(16).
