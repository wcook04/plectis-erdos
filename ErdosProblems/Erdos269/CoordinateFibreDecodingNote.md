# Coordinate-fibre decoding for finite prime supports

**Claim boundary, stated first.** This note proves irrationality of
coordinate fibres \(\Phi_{P,p}(x)=\sum_{n\ge0}1/H_P(xp^n)\). It does **not**
prove irrationality of the repeated three-prime series (Erdős #269). The
parent remains open. Novelty is unverified; the argument is elementary.

**Collision with the corpus.** The appendix of
`PurePowerIrrationalityNote.md` headed “Assessment of the proposed
orbit-closure repair, 2026-09-06” already restores unshifted binary
\(\Sigma_2\) by an orbit-closure lemma. That repair is **not** new here. The
gain is a decoding argument with a sharper confinement estimate: every
shifted fibre for \(\{2,3,5\}\), both larger-prime fibres of every triple,
and the largest-prime fibre of every finite \(P\) with \(|P|\ge2\). Channels
3 and 5 of \(\{2,3,5\}\), which the orbit-closure repair left open, are
included. `PurePowerIrrationality.lean` supplies generic consumers; it does
not currently prove the theorems below.

**Linear identity already registered.** The packet identity
`running_height_prime_power_telescope` is
\(\Sigma_2+2\Sigma_3+4\Sigma_5=1\). Three irrational fibres with an exact
rational relation. Do not infer irrationality of their infinite sum.

Exact finite checks:
`ErdosProblems/Erdos269/scripts/check_coordinate_fibre_decoding.py --quick`.

Type B source: r3 file 05, advisory until this ordinary review. Registered
onset \(u+1+2v+3w\) in the short note is **not** replaced by the sharper
onset recorded in §E.

## A. Decoding lemma

Let \((b_n)_{n\ge0}\) take values in a finite set \(A\) of integers
\(\ge2\), and set
\[
 z_n=\sum_{k\ge1}\frac1{b_n b_{n+1}\cdots b_{n+k-1}}.
\]
Suppose \(z_n\le M\) for all \(n\) and the intervals
\(I_b=(1/b,(1+M)/b]\) for \(b\in A\) are pairwise disjoint. Then \(z_0\) is
rational if and only if \((b_n)\) is eventually periodic.

**Proof.** Absolute convergence follows from \(b_n\ge2\). Splitting the
first term gives \(z_{n+1}=b_n z_n-1\), so \(z_n=(1+z_{n+1})/b_n\in I_{b_n}\).

If \(z_0=A/D\) is rational, iteration shows \(D z_n\) is integral for every
\(n\). Positivity and the uniform bound put the orbit in the finite set
\((1/D)\mathbb Z\cap(0,M]\). Hence \(z_s=z_t\) for some \(s<t\). Disjointness
identifies \(b_s=b_t\); the recurrence identifies \(z_{s+1}=z_{t+1}\).
Induction gives equality of the future radix words, with period \(t-s\) from
\(s\) onwards.

Conversely, after an eventually periodic radix word reaches a period of
length \(t\), one period gives \(z_N=(R+z_N)/P\) with \(P\) the product of
the period radices and \(R\) the accumulated forcing for digits one. Thus
\(z_N=R/(P-1)\) is rational, and finitely many backward steps give rational
\(z_0\). \(\square\)

A sufficient disjointness test is \(\min_{b<b'} b'/b>1+M\). Finite rational
state space alone does not force a periodic radix word when decoding fails.

## B. Uniform data for \(\{2,3,5\}\)

Write \(H(x)=2^{\lfloor\log_2 x\rfloor}3^{\lfloor\log_3 x\rfloor}
5^{\lfloor\log_5 x\rfloor}\). Fix \(p\in\{2,3,5\}\), \(x\ge1\), and put
\(A_n=H(xp^n)\), \(b_n=A_{n+1}/A_n\), \(z_n=A_n\sum_{m>n}A_m^{-1}\).

| \(p\) | Possible \(b_n\) | Bound \(M\) | Min adjacent ratio | \(1+M\) |
|---|---|---|---|---|
| 2 | 2, 6, 10, 30 | \(7/11\) | \(5/3\) | \(18/11\) |
| 3 | 6, 12, 30, 60 | \(1/5\) | \(2\) | \(6/5\) |
| 5 | 60, 120, 180, 360 | \(1/59\) | \(3/2\) | \(60/59\) |

In every row the penultimate entry exceeds the last, so the intervals
\(I_b\) are disjoint.

**Alphabets.** For a prime \(q\), the increment
\(\lfloor\log_q x+(n+1)\log_q p\rfloor-\lfloor\log_q x+n\log_q p\rfloor\)
lies in \(\{\lfloor\log_q p\rfloor,\lceil\log_q p\rceil\}\). In the
\(p\)-coordinate it is exactly one. For \(p=2\) the other increments lie in
\(\{0,1\}\); for \(p=3\) the 2-increment lies in \(\{1,2\}\) and the
5-increment in \(\{0,1\}\); for \(p=5\) they lie in \(\{2,3\}\) and
\(\{1,2\}\). Multiplying gives the three alphabets.

**Confinement.** For \(p=3\), every radix is at least 6, so
\(z_n\le\sum_{k\ge1}6^{-k}=1/5\). For \(p=5\), the same with 60 gives
\(1/59\).

For \(p=2\), \(b_n b_{n+1}=H(4x\,2^n)/H(x\,2^n)\ge12\): the 2-coordinate
contributes four, and \(4>3\) forces a power of 3 in \((y,4y)\) for
\(y=x2^n\). Every product of \(2j\) consecutive radices is at least
\(12^j\), and every product of \(2j+1\) consecutive radices is at least
\(2\cdot12^j\). Therefore
\[
 z_n\le\sum_{j\ge0}\Bigl(\frac1{2\cdot12^j}+\frac1{12^{j+1}}\Bigr)=\frac7{11}.
\]
Finally \(18/11<5/3\) because \(54<55\). The letters 6 and 10 satisfy
\(\inf I_6-\sup I_{10}=1/6-18/110=1/330>0\).

## C. Fibre theorem

**Theorem.** For every real \(x\ge1\) and every \(p\in\{2,3,5\}\),
\[
 \Phi_p(x)=\sum_{n\ge0}\frac1{H(xp^n)}\notin\mathbb Q.
\]
In particular each \(\Sigma_p=\sum_{n\ge1}1/H(p^n)\) is irrational, and every
coordinate fibre with the other two exponents fixed is irrational.

**Proof.** Each \(A_n\) is a positive integer dividing \(A_{n+1}\), and
\(A_{n+1}\ge p A_n\). The state of §B satisfies
\(z_n=A_n\Phi_p(x)-\sum_{m=0}^n A_n/A_m\) with the finite sum integral.
Rationality of \(\Phi_p(x)\) would make every \(z_n\) rational with one
fixed denominator. Disjoint intervals and §A would force \((b_n)\)
eventually periodic.

Choose a prime \(q\in\{2,3,5\}\) different from \(p\). Unique factorisation
makes \(\alpha=\log_q p\) irrational. But
\(v_q(b_n)=\lfloor\gamma+(n+1)\alpha\rfloor-\lfloor\gamma+n\alpha\rfloor\)
with \(\gamma=\log_q x\). An eventually periodic integer sequence of period
\(t\) has rational Cesàro mean. Telescoping gives mean \(\alpha\), a
contradiction. Taking \(x=p\) gives \(\Sigma_p\); taking \(x\) to be the
product of the fixed powers of the other two primes gives every coordinate
fibre. \(\square\)

**Why this does not prove the parent.** The full repeated series has
nonconstant shell-count digits \(X_{a+1}=b_a X_a-m_a\) and quadratically
growing states. Bounded rational state space and digit-one decoding are
absent. The identity \(\Sigma_2+2\Sigma_3+4\Sigma_5=1\) is the exact
warning: group \((p_j-1)/H(t_j)=1/H_{j-1}-1/H_j\) along the merged
prime-power word.

## D. Largest-prime fibres, and the middle prime of a triple

Let \(P\) be any finite set of at least two distinct primes,
\(H_P(t)=\prod_{q\in P}q^{\lfloor\log_q t\rfloor}\), and
\(\Phi_{P,p}(x)=\sum_{n\ge0}1/H_P(xp^n)\) for \(x\ge1\).

**Theorem.** If \(p=\max P\), then \(\Phi_{P,p}(x)\) is irrational for every
real \(x\ge1\). If \(P\) has exactly three elements, the same conclusion
holds for either of its two larger primes.

**Proof for the largest prime.** Put \(V=\prod_{q\in P\setminus\{p\}}q\) and
\(M_0=p\prod_{q\ne p}q^{\lfloor\log_q p\rfloor}\). Each radix is \(M_0 d\)
for a squarefree divisor \(d\) of \(V\). Since \(p\) is largest, every
displayed logarithmic floor is at least one, so \(M_0\ge pV>V\). The tail
has geometric bound \(z_n\le1/(M_0-1)\). For distinct divisors \(d<d'\) of
\(V\),
\[
 \frac{d'}{d}\ge1+\frac1d\ge1+\frac1{V-1}>1+\frac1{M_0-1}.
\]
Decoding intervals are disjoint. Rationality would force eventual
periodicity, and the valuation at any \(q\ne p\) contradicts the irrational
mean \(\log_q p\).

**Proof for the middle prime of a triple.** Write the other two primes as
\(q<p<r\). Here \(M_0=pq^{\lfloor\log_q p\rfloor}\ge pq\), and the four
radices are \(M_0,M_0q,M_0r,M_0qr\). The least successive ratio is
\(\min(q,r/q)\). Since \(r-q\ge1\) and \(M_0-1>q\),
\[
 1+\frac1{M_0-1}<1+\frac1q\le\frac rq,\qquad
 1+\frac1{M_0-1}<2\le q.
\]
The geometric tail bound again gives disjoint intervals. \(\square\)

The binary \(7/11\) bound is the extra step covering the smallest prime in
\(\{2,3,5\}\). None of these fibre assertions implies irrationality of the
parent multidimensional sum.

## E. Memorandum: onset (not used in the short note)

Assume \(S=A/D\) in lowest terms and \(X_a=h_a S-Z_a\) with \(Z_a\in\mathbb Z\)
and \(h_a=2^{a-1}3^{\lfloor a\log_3 2\rfloor}5^{\lfloor a\log_5 2\rfloor}\).
The reduced denominator of \(X_a\) is \(D/\gcd(D,h_a)\). Writing
\(D=2^u3^v5^w B\) with \((B,30)=1\), the least dyadic onset after which
\(BX_a\) is integral is
\[
 a_*=\max\bigl\{u+1,\lceil v\log_2 3\rceil,\lceil w\log_2 5\rceil\bigr\}.
\]
The integer onset \(\max(u+1,2v,3w)\) also suffices and improves the
registered additive onset \(u+1+2v+3w\). **The short note keeps the
registered onset until this comparison is independently checked against
`exists_reducedCarry_of_value_eq_rat`.** The remaining target, with the
denominator, is: \(BX_a\notin\mathbb Z\) for every \(a\ge1\) and every
positive \(B\) coprime to 30.

## F. Finite rank distance (correction, not a short-note theorem)

The live-note sentence that a rank-deficient \(n\times n\) approximation
must incur half the carry jump is **false**. For \(c=1/5\),
\[
 T=\begin{pmatrix}1/5&1\\1/5&1/5\end{pmatrix},\qquad
 A=\begin{pmatrix}3/10&9/10\\1/10&3/10\end{pmatrix}
\]
satisfy \(\det A=0\) and \(\|T-A\|_{\max}=1/10<2/5\).

The infinite uniform threshold \((1-c)/2\) is unaffected: distinct columns
of the infinite carry matrix are distance \(1-c\) apart in the supremum
norm, so a finite-separated-rank approximant closer than half that gap would
place infinitely many uniformly separated points in a bounded subset of a
finite-dimensional space.

The sharp finite distance to rank deficiency for the staircase \(T_n(c)\)
is \(O(1/n)\):
\[
 \operatorname{dist}_{\max}(T_n(c),\{\det=0\})
 =\frac{1-c}{2n-1+c^{-1}}\quad(n\text{ even}),\qquad
 \frac{1-c}{2n-3+c^{-1}}\quad(n\text{ odd}).
\]
This formula is ordinary, with an exact finite regression through dimension
10. It is **not** inserted into the short note. The infinite compactness
argument is.

## G. Quadratic caps are not automatically equivalences

`cofinalLocalWindowEscape_of_irrational_of_quadratic` is the **forward**
implication for any cap dominated by \(c(B)(n+1)^2\). The actual
if-and-only-if specialises to the registered valid cap \(90B(a+1)^2\). The
zero cap \(G\equiv0\) makes least-positive-residue escape automatic, so an
upper-quadratic bound alone is not a reverse implication. Cap 0 is a
witness, not a counterexample to the parent series.
