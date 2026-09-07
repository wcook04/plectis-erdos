# Moving primitive charges and the carry-periodicity boundary

This note closes two narrowly related questions. A fresh primitive divisor of
the new Mersenne denominator has a universal gap residue, so it cannot certify
the Archimedean sign. On the carry side, eventual periodicity would already
force the Boolean support to be finite by the existing common-multiple
theorem. Rationality supplies only tempering, and the precise remaining
obstruction is the scale distortion introduced by the support LCM.

## 1. A fresh primitive divisor sees the constant \(2\)

Retain the finite-cylinder notation
\[
 q_n=2^n-1,\qquad B_n=2D_n-q_nA_n,
\]
where \(D_n\) clears the target and all prefix denominators and
\(B_n/D_n\) is the normalized upper gap.

Let \(\ell\) be a primitive prime divisor of \(q_n\), and suppose \(\ell\)
does not divide the fixed target denominator. Primitivity gives
\(\ell\nmid q_k\) for \(k<n\), hence \(\ell\nmid D_n\). Directly from the
definition,
\[
 \boxed{B_nD_n^{-1}\equiv2\pmod\ell.}              \tag{1}
\]
The residue is independent of \(A_n\), the prefix, and the itinerary.

The six-block recurrence makes the same collapse visible. If
\[
 Q_r=\prod_{i=0}^5q_{r+i},
\]
then, modulo a primitive divisor \(\ell\mid q_{r+6}\), every term carrying
the preceding gap or the six-bit digit charge vanishes. What remains is
again
\[
 B_{r+6}D_{r+6}^{-1}\equiv2\pmod\ell.              \tag{2}
\]
Thus introducing a fresh cyclotomic factor at the block endpoint does not
create a sign-sensitive charge. It erases the history.

Prime powers beyond the exact divisibility of \(q_n\), or a relation between
different fresh primes, are not covered by (1). The no-go is specifically
for the natural residue at the rank where the primitive divisor first
appears.

## 2. Exact finite moving-charge shadows

Fix any finite Bellman word \(e=(e_0,\ldots,e_{m-1})\) at a rational clock
\(z\). Its inverse branch has the form
\[
 y=S_e(z)+\frac{Y}{d_m(z)}.                        \tag{3}
\]
At \(Y=2\), every inverse step lies strictly on the side of the threshold
specified by its digit: a zero inverse is \(Y'/(2+z')<1\), while a one
inverse is \(1+Y'/(2+z')\geq1\). Therefore there is a rational
\(\varepsilon>0\) such that the two rational points obtained from
\[
 Y_-=2-\varepsilon,\qquad Y_+=2+\varepsilon        \tag{4}
\]
have the same first \(m\) digits. The first remains below the finite survivor
boundary at depth \(m\); the second has crossed it.

At every rank in this common prefix, (1) assigns both points the same residue
\(2\) at the newly introduced primitive divisor. Hence every finite list of
these moving-prime observations is shared by an exact rational survivor
shadow and an exact rational escaping shadow. No finite induction whose
state consists only of the introduction residues can establish membership of
the root point.

## 3. Eventual carry periodicity would force finite support

Let \(A\subseteq\mathbb N\), let
\[
 f_A(n)=\#\{a\in A:a\mid n\},
\]
and suppose a positive natural-number carry satisfies
\[
 u_{j+1}+v f_A(c+j+1)=2u_j,\qquad v>0.             \tag{5}
\]
The Lean theorem shifted_state_unbounded_of_infinite_support in
RationalSupportCarrySkeleton.lean proves
\[
 A\text{ infinite}\quad\Longrightarrow\quad u
 \text{ unbounded}.                               \tag{6}
\]
Its proof is exactly the Boolean-ancestry/LCM composition. Given a proposed
bound \(H\), choose \(2H+1\) positive elements of \(A\), let \(L\) be a common
multiple, and apply one_add_mul_card_le_two_mul_shifted_state:
\[
 1+v|F|\leq2u_{L-c-1}.                            \tag{7}
\]
Thus a bounded carry, and in particular an eventually periodic carry, forces
\(A\) to be finite. Its Boolean Mersenne subsum is then a finite rational sum
and its reciprocal support mass is finite. If the rational digit stream and
\(u\) are eventually periodic, (5) also makes \(f_A\) eventually periodic,
but that extra conclusion is unnecessary: boundedness has already forced
finite support.

This corrects the contrary prose claim in CrossTargetDefectSearch.md that a
bounded carry need not imply finite support. An infinite set of supported
primes does not have uniformly bounded divisor incidence: the product of any
\(k\) distinct supported primes has divisor count at least \(k\). The
formal common-multiple theorem already encodes this argument.

## 4. The smallest surviving obstruction is LCM scale distortion

For a rational Boolean sum, the established carry is tempered:
\[
 \frac{u_n}{2^n}\longrightarrow0.                 \tag{8}
\]
Tempering is not boundedness or eventual periodicity. Combining (7) with
(8) only gives, at the support-dependent index \(L=L(F)\),
\[
 \frac{1+v|F|}{2^{L-c}}
 \leq \frac{u_{L-c-1}}{2^{L-c-1}}.                \tag{9}
\]
The left side can tend to zero extremely fast because \(L(F)\), an LCM or
even the product used in the formal proof, can dwarf \(|F|\). Therefore
(7) and (8) are fully compatible.

This is the genuinely nonlinear cross-scale obstruction. Boolean Möbius
ancestry turns support elements into a large pulse only after transporting
them to their common multiple, while the tempered boundary measures the
state on the exponential clock \(2^n\). The map
\[
 F\longmapsto L(F)\longmapsto 2^{L(F)}
\]
destroys the cardinality gain before tempering can see it. Any proof that
upgrades tempered carry to the bounded regime must control this scale
distortion; periodic rational digits and fresh primitive residues do not do
so.

No new Lean theorem is needed for the periodic implication: (6) is already
machine-checked. The new conclusion is the exact separation of cases:
eventual periodicity closes the infinite-support case immediately, whereas
tempering leaves precisely the LCM-height barrier.
