# Minimal primitive-channel service height and its Archimedean reversal

Let

\[
M_n=2^n-1.
\]

The shared-descendant construction in
[MersenneCrtSharedDescendantCapacityNoGo.md](MersenneCrtSharedDescendantCapacityNoGo.md)
shows that two common multiples can cancel arbitrarily many primitive channels.  This note determines the exact height cost in the simplest creation and preservation problems.  The height cost is real, but it does not yield an Archimedean contradiction: larger service height makes the selected Mersenne reciprocals smaller.

## 1. One descendant: exact minimum

For \(a\ne6\), let

\[
P(a)=
\prod_{\substack{p\mid M_a\\ \operatorname{ord}_p(2)=a}}
p^{v_p(M_a)}
\]

be the full primitive prime-power part of \(M_a\).  Put \(P=P(a)\).  If \(k\) is a unit modulo \(P\), then

\[
\frac{M_{ak}}{M_a}\equiv k\pmod P.
\tag{1}
\]

Consequently, the complete primitive part belonging to \(a\) cancels from

\[
\frac1{M_a}+\frac1{M_{ak}}
\]

if and only if

\[
1+k^{-1}\equiv0\pmod P.
\tag{2}
\]

### Theorem 1 (least one-descendant multiplier)

The least positive multiplier \(k>1\) satisfying (2) is

\[
k=P-1.
\tag{3}
\]

For every primitive prime \(p\mid M_a\), the two-term sum

\[
\frac1{M_a}+\frac1{M_{a(P-1)}}
\tag{4}
\]

is \(p\)-integral.

### Proof

Equation (2) is equivalent to \(k\equiv-1\pmod P\), whose least positive representative is \(P-1\).  Congruence (1), applied modulo each full prime power \(p^{v_p(M_a)}\), then cancels the normalized residues.  ∎

Thus a fresh primitive denominator demand \(P\) really does force height in the one-descendant problem.  Bang--Zsigmondy gives \(P\ge a+1\), so the service index is at least \(a^2\).

## 2. The real value of the minimal service term

Write \(w_n=1/M_n\).  The minimal service term in Theorem 1 satisfies

\[
\frac{w_{a(P-1)}}{w_a}
=
\frac{2^a-1}{2^{a(P-1)}-1}
<
2^{\,1-a(P-2)}.
\tag{5}
\]

Indeed, \(2^a-1<2^a\) and

\[
2^{a(P-1)}-1\ge2^{a(P-1)-1}.
\]

As \(a\to\infty\), the right side of (5) tends to zero faster than \(2^{-a^2+O(a)}\).  The primitive prime-power cancellation is exact even though the service term has negligible real size relative to the term whose primitive denominator it cancels.

This rules out an argument that assigns a positive real repayment cost to primitive \(p\)-adic cancellation.  The congruence cancellation does not require comparable Archimedean mass.

## 3. Two descendants preserving accumulated cancellations

Let \(B\) be a finite Mersenne support whose primitive channels have already been cancelled.  More precisely, suppose \(C\subseteq B\), put

\[
R=\prod_{a\in C}P(a),
\qquad
L=\operatorname{lcm}(B),
\tag{6}
\]

and assume

\[
\rho_a(B)=0\pmod{P(a)},
\qquad
\gcd(L/a,P(a))=1
\quad(a\in C),
\tag{7}
\]

where

\[
\rho_a(B)=
\sum_{\substack{n\in B\\a\mid n}}
(n/a)^{-1}\pmod{P(a)}.
\]

Add two common descendants \(Lk_1,Lk_2\), with both multipliers coprime to \(R\).  For each \(a\in C\), their new contribution to \(\rho_a\) is

\[
(L/a)^{-1}(k_1^{-1}+k_2^{-1}).
\]

Since the primitive parts \(P(a)\) are pairwise coprime, all old cancellations are preserved exactly if and only if

\[
k_1^{-1}+k_2^{-1}\equiv0\pmod R.
\tag{8}
\]

### Theorem 2 (sharp accumulated preservation height)

Assume \(R\ge5\).  Among distinct integers \(k_1,k_2>1\) which are units modulo \(R\) and satisfy (8),

\[
\min\max(k_1,k_2)=\frac{R+1}{2}.
\tag{9}
\]

The minimum is attained by

\[
k_-=\frac{R-1}{2},
\qquad
k_+=\frac{R+1}{2}.
\tag{10}
\]

Hence the least possible maximum common-descendant index is

\[
\frac{L(R+1)}2.
\tag{11}
\]

### Proof

Because \(k_1k_2\) is a unit modulo \(R\), equation (8) is equivalent to

\[
k_1+k_2\equiv0\pmod R.
\tag{12}
\]

The two positive integers have sum at least \(R\), so their maximum is at least \((R+1)/2\).  The pair in (10) consists of distinct integers greater than \(1\), and each is coprime to \(R\): any common divisor with \(R\) would divide \(R\) and \(R\pm1\).  Their sum is \(R\), so they attain the bound.  ∎

This is the sharp lower bound left open by the previous CRT construction.  It depends on the accumulated product \(R\), not merely on one primitive channel.

## 4. The height reversal

At the exact minimum (10), the total real value of the two new Mersenne terms satisfies

\[
\begin{aligned}
w_{Lk_-}+w_{Lk_+}
&\le
2^{1-Lk_-}+2^{1-Lk_+}\\
&<
2^{\,2-L(R-1)/2}.
\end{aligned}
\tag{13}
\]

Thus the forced service height grows linearly in \(LR\), while the service value decays exponentially in \(LR\).  Increasing the accumulated primitive denominator demand makes the real cost smaller.

This behavior is compatible with the exact Mersenne divisor lattice.  The pair (10) preserves every primitive prime-power cancellation in (7), and equation (13) can be made arbitrarily small by enlarging \(C\).  There is no lower Archimedean mass attached to the preservation of those channels.

## 5. More than two descendants

The same calculation gives the general positive-height bound.  Suppose \(m\ge2\), the positive integers \(k_1,\ldots,k_m\) are units modulo \(R\), and

\[
\sum_{j=1}^m k_j^{-1}\equiv0\pmod R.
\tag{14}
\]

If \(H=\max_j k_j\), then

\[
R
\le
\sum_{j=1}^m\prod_{\ell\ne j}k_\ell
\le
mH^{m-1}.
\tag{15}
\]

The first inequality holds because the middle integer is positive and divisible by \(R\).  Therefore

\[
H\ge\left(\frac Rm\right)^{1/(m-1)}.
\tag{16}
\]

The exponent in (16) deteriorates as the number of available descendants grows.  Reciprocal divergence alone neither limits \(m\) nor forces a fixed-\(m\) regime, so (16) gives no uniform obstruction in the dense-support case.

## 6. Consequence for the dense-support attack

The height-sensitive capacity proposal does not yield an unconditional Archimedean contradiction.

For one descendant, Theorem 1 proves the exact minimum \(P(a)-1\), but (5) shows that the corresponding Mersenne value is exponentially smaller than \(w_a\).  For an accumulated cancelled modulus, Theorem 2 proves the exact two-descendant minimum \((R+1)/2\), but (13) again makes the real contribution exponentially small.  Allowing more descendants weakens the height lower bound to (16).

Each finite configuration can be embedded, without changing its prefix identities, in a cofinite support.  Such a support has density one and divergent reciprocal index sum.  Later cofinite terms may reopen the channels, so this is not a rational Mersenne construction and not an all-cutoff cancellation theorem.  It is a counterexample to the proposed coercive step: neither the exact service height nor the real value of the required descendants supplies an incompatible inequality.

Any remaining height argument needs an additional statement that rationality forces a lower real tail mass associated with a \(p\)-adic cancellation.  The calculations above show that such a statement cannot follow from the Mersenne divisor lattice, primitive moduli, positivity, or reciprocal divergence alone.
