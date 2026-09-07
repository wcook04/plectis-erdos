# Hausdorff dimension of restricted Mersenne achievement sets

Ordinary proof. Historical novelty unassessed. This is a geometric
classification of subsums, not an arithmetic statement about rational
points, and it does not decide Erdős #257.

## Collision

The packet already records:

* `hereditary_mersenne_subachievement_topology` (Lean): compact, closed,
  nowhere dense, perfect for infinite allowed supports;
* `hereditary_mersenne_subachievement_measure` (Lean): measure \(2^{-c}\)
  for a finite omitted set of size \(c\), and zero for infinite complement;
* `arithmetic_stride_dimension` (advisory, pending Lean): the arithmetic
  progression \(m\mathbb N_+\) is Ahlfors regular of Hausdorff dimension
  \(1/m\), with a biased-entropy refinement.

The identity below is strictly more general than the dimension clause of
`arithmetic_stride_dimension`: it holds for every allowed index set \(J\),
not only for a single residue class. Periodic supports with \(0<r<d\)
allowed residues are now additionally Ahlfors \(r/d\)-regular, which
strengthens the r2 dimension formula in that periodic proper case. It does
**not** prove Ahlfors regularity for full support. Topology and Lebesgue
measure remain the Lean authority.

## Theorem

Let \(w_n=(2^n-1)^{-1}\) and
\[
A_J=\Bigl\{\sum_{n\in J}\varepsilon_n w_n:\varepsilon_n\in\{0,1\}\Bigr\},
\qquad
\underline d(J)=\liminf_{N\to\infty}\frac{\#\{J\cap[1,N]\}}{N}.
\]
Then \(\dim_H A_J=\underline d(J)\). In particular a periodic allowed set
with \(r\) residues per period \(d\) has dimension \(r/d\), recovering the
stride \(m\mathbb N_+\) as the case \(r=1\), \(d=m\).

**Upper bound.** The \(2^{k_N}\) allowed prefixes cover \(A_J\) by intervals
of length at most \(T_N=\sum_{n>N}w_n\le 2^{1-N}\). For \(s>\underline d(J)\)
choose \(s'\) between them and a subsequence with \(k_N\le s'N\). The sum of
\(s\)-th powers of those lengths is \(O\bigl(2^{(s'-s)N}\bigr)\to 0\).

**Lower bound.** Write \(e_n=w_n-2^{-n}\). Strict tail domination makes the
Mersenne coding unique, so the map sending a Mersenne subsum to the
corresponding binary subsum is well-defined, order-preserving and
\(1\)-Lipschitz from \(A_J\) onto the restricted binary set \(D_J\). Lipschitz
maps do not increase Hausdorff dimension, so it is enough to prove
\(\dim_H D_J\ge\underline d(J)\). Place independent fair bits on the indices
of \(J\). Every dyadic interval of length \(2^{-N}\) has mass at most
\(2^{-k_N}\). For \(0<s<\underline d(J)\) one has \(k_N\ge sN\) for large
\(N\), and the mass-distribution principle supplies a Frostman measure of
exponent \(s\).

This does not classify any rational point of \(A_J\). Fair-coin almost-sure
irrationality on infinite \(J\) is already Kovač–Tao, Proposition 2.1; it is
not restated as a new theorem here.

## Periodic Ahlfors regularity when \(r<d\)

Let \(J\subseteq\mathbb N_{>0}\) be periodic of period \(d\), with \(r\)
allowed residues, where \(0<r<d\). Then \(A_J\) is Ahlfors regular of
dimension \(s=r/d\) with respect to fair independent digits on the allowed
positions: its coding measure \(\mu\) satisfies
\[
c\rho^s\le\mu(B(x,\rho))\le C\rho^s
\qquad(x\in A_J,\ 0<\rho\le\operatorname{diam} A_J).
\]
Consequently \(0<\mathcal H^s(A_J)<\infty\). If the allowed residue classes
carry independent Bernoulli probabilities \(p_1,\ldots,p_r\in(0,1)\), the
pushforward is exact-dimensional of dimension
\[
\frac{\sum_{i=1}^r\bigl[-p_i\log p_i-(1-p_i)\log(1-p_i)\bigr]}{d\log 2}.
\]

**Proof.** Give allowed digit sequences the ultrametric \(2^{-k}\), where
\(k\) is the first differing exponent. The coding map has upper distance
bound \(|\pi(\varepsilon)-\pi(\varepsilon')|\le w_k+\sum_{n>k}w_n\le 4\cdot 2^{-k}\).
For a lower bound, strict full-tail domination gives
\[
w_k-\sum_{n>k,\,n\in J}w_n
=\Bigl(w_k-\sum_{n>k}w_n\Bigr)+\sum_{n>k,\,n\notin J}w_n.
\]
Because \(J\) is proper and periodic, some forbidden exponent \(m\) lies
between \(k+1\) and \(k+d\). The right side exceeds \(w_m>2^{-m}\ge 2^{-d}2^{-k}\).
Thus coding is bi-Lipschitz from this ultrametric space onto \(A_J\).

The number of allowed positions up to \(N\) is \(sN+O(1)\). A fair cylinder
through rank \(N\) has mass \(2^{-sN+O(1)}\). Ultrametric balls are
cylinders, and the gaps between successive allowed positions are at most
\(d\), so these estimates give the asserted two-sided \(\rho^s\) bounds.
Bi-Lipschitz transport preserves them. The standard covering proof then
gives positive finite \(s\)-dimensional Hausdorff measure.

For biased digits, group coordinates into complete periods. The negative
logarithm of the probability of the realised digit word in one period is
an i.i.d. bounded random variable of mean
\(H=\sum_i[-p_i\log p_i-(1-p_i)\log(1-p_i)]\). The strong law gives cylinder
log-mass \(-mH+o(m)\) through \(m\) periods. Dividing by log-radius
\(-md\log 2+O(1)\), and using the same bounded-gap and bi-Lipschitz
comparisons, gives local dimension almost surely. ∎

The hypothesis \(r<d\) is essential: the lower Lipschitz bound uses a
forbidden coordinate within bounded distance. With every position allowed,
the adjacent-code gap at rank \(k\) is of order \(4^{-k}\), so that
argument fails. The unrestricted set still has measure one. No Ahlfors
assertion for full support is inferred here. This is not an arithmetic
exclusion of any rational point. Kovač–Tao remains the attribution for
fair-coin almost-sure irrationality.
