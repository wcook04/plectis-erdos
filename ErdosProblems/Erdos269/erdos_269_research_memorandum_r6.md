---
title: "Finite kernels and source-compatible perturbations"
subtitle: "Erdős #269: round-6 research memorandum"
author: "Research memorandum prepared for Will Cook"
date: "7 September 2026"
lang: en-GB
fontsize: 11pt
geometry: [a4paper, margin=26mm]
---

## 1. The mathematical distinction to retain

The live short note's principal theorem remains the arbitrary-order non-separability of the three-prime running-LCM kernel. Its proof identifies a binary carry whose consecutive column differences have disjoint interval supports. The finite cut-rank proposition added in round 5 describes the resulting finite-dimensional linear algebra completely over a field.

This memorandum develops three further consequences and constructions. First, the same column differences give a normal form over a ring, identifying exactly which residue characteristics lose rank. Second, a source-compatible redistribution of the actual cell multiplicities preserves every complete block sum in two prime channels while producing an interval of possible scalar sums. Preservation in all three channels, together with a short unchanged prefix, instead forces every multiplicity to remain unchanged. Third, the continuum carry kernel has an explicitly computable spectrum, which explains the distinction between uniform and mean-square approximation.

The ring normal form is a short extension of the existing flagship. The redistribution theorem and the spectral theorem are separate ordinary results, suitable initially for the long record. Complete ordinary proofs are given below. Their novelty has not been established. The accompanying Lean file contains finite algebra only and was not compiled in this review. No result here proves irrationality of the repeated three-prime series.

The mathematical source for the existing rank mechanism is the supplied live `01_short_note.tex`, Theorem `res:infinite-rank` and Proposition `res:finite-cut-rank`. The existing three-channel rigidity theorem is `ThreeChannelBlockRigidity.lean`, particularly `channelBlockNull_iff_channelPotential` and `channelCoboundary_eq_zero_of_two_anchors`. Those results are antecedents to this memorandum, not new claims of this return. The public versions were read at the packet's pin, `32545d77c4b5cfd72ebd36c8dcd2418bf7cc4d31`.

## 2. An arithmetic normal form for every finite cut matrix

### 2.1 The normal form over a ring

Let $R$ be a commutative ring, let $c\in R$ be a unit, and let $m\ge1$. Define
$$
v_s=(\underbrace{1,\ldots,1}_{s},\underbrace{c,\ldots,c}_{m-s})^{\mathsf T},
\qquad 0\le s\le m.
$$
Let $C_E$ be a nonempty matrix of these columns, and let $E\subseteq\{0,\ldots,m\}$ be the set of cuts that occur, counting each repeated cut once. Write
$$
\rho=|E|-\mathbf1_{\{0,m\}\subseteq E}.
$$

**Theorem 2.1 (arithmetic cut normal form).** Invertible row and column operations over $R$ transform $C_E$ to a rectangular diagonal matrix with nonzero-designated entries
$$
1,\quad \underbrace{1-c,\ldots,1-c}_{\rho-1},
$$
and all remaining entries zero. The assertion allows $1-c$ to be a zero divisor, or zero. It is a matrix-equivalence statement, rather than a rank convention over a ring.

*Proof.* Subtract representatives from duplicate columns. List the remaining cuts as $k_1<\cdots<k_t$, and replace successive columns by their differences, working from the last column backwards. Besides the first column, the columns become
$$
(1-c)\mathbf1_{[k_j,k_{j+1})},\qquad 1\le j<t.
$$
Within each interval all rows coincide; subtract one representative from the others. The surviving row types are a prefix row $(1,0,\ldots,0)$ when $k_1>0$, an interval row $(c,(1-c)e_j)$ for each gap, and a suffix row $(c,0,\ldots,0)$ when $k_t<m$.

If there is a prefix or suffix, its first entry is a unit. Use it as pivot to clear the first coordinate of the interval rows. This leaves $1$ and $t-1$ copies of $1-c$, with zero rows and columns elsewhere. If both prefix and suffix are absent, the cuts include $0,m$ and only the $t-1$ interval rows remain. Pivot on the unit $c$ in one interval row. Subtract that row from the other interval rows. In the difference columns, those rows are $(1-c)(e_j-e_1)$. Clearing the first pivot row leaves an identity submatrix of size $t-2$, multiplied by $1-c$, and one dependent column. Thus the diagonal entries are $1$ and $t-2$ copies of $1-c$. These are the two cases in the formula for $\rho$. Every operation described is invertible. $\square$

Over a field with $c\ne0,1$, this recovers the existing cut-rank formula. The proof also explains why the two extreme cuts cause the only loss: their columns are proportional.

### 2.2 The exact bad residue characteristics

For distinct primes $p,q,r$, let
$$
H(x)=p^{\lfloor\log_p x\rfloor}q^{\lfloor\log_q x\rfloor}r^{\lfloor\log_r x\rfloor},
\qquad K(i,j,k)=H(p^iq^jr^k)^{-1}.
$$
The live factorisation is
$$
K(i,j,k)=U_i(k)^{-1}C_{ij}V_j(k)^{-1},\qquad
C_{ij}=r^{-\mathbf1_{\{x_i+y_j\ge1\}}},
$$
where $x_i=\{i\log_r p\}$ and $y_j=\{j\log_r q\}$. Every $U_i,V_j$ is a product of powers of $p,q,r$.

**Corollary 2.2.** Over $\mathbb Z[1/(pqr)]$, every nonempty finite sampled kernel matrix of rational rank $\rho$ is equivalent to
$$
\operatorname{diag}(1,r-1,\ldots,r-1,0,\ldots),
$$
with $\rho-1$ copies of $r-1$. The normal form is independent of $k$.

*Proof.* The row and column factors are units in the stated ring. Apply Theorem 2.1 with $c=1/r$, then multiply the diagonal entries by suitable units. $\square$

Let $B\ge2$ satisfy $(B,pqr)=1$. Reduction is well defined on this localisation. The image of the corresponding map between finite free $\mathbb Z/B\mathbb Z$-modules has cardinality
$$
\boxed{\quad B\left(\frac{B}{\gcd(B,r-1)}\right)^{\rho-1}.\quad} \tag{2.1}
$$
For a prime $\ell\notin\{p,q,r\}$, the rank is $\rho$ if $\ell\nmid r-1$, and is $1$ if $\ell\mid r-1$. At modulus $\ell^s$, putting $e=v_\ell(r-1)$, the image cardinality is
$$
\ell^{s+(\rho-1)\max(s-e,0)}.
$$
These assertions follow coordinatewise from the diagonal form: multiplication by $d$ on $\mathbb Z/B\mathbb Z$ has image of size $B/\gcd(B,d)$.

For $\{2,3,5\}$, every admissible $B$ is odd, so $4=r-1$ is a unit. Consequently every finite sampled rank survives in the precise sense of the normal form, and every staircase minor selected by the live theorem is invertible modulo every $B$ coprime to $30$, simultaneously for all $k$. This last statement also has a four-line direct proof from the live determinant
$$
\det T_n(1/5)=5^{-1}(-4/5)^{n-1}.
$$
It is the version proposed as a short-note corollary.

There is an exact general criterion: the selected staircase minors survive modulo **every** $B$ coprime to $pqr$ if and only if every prime divisor of $r-1$ lies in $\{p,q\}$. Necessity follows by taking $B$ to be any prime divisor outside that set, and sufficiency follows from the determinant. For example, a fixed-layer kernel for $(p,q,r)=(2,3,11)$ has rank one modulo $5$, although it has arbitrary-order rational minors. This example concerns the stated flattening; it makes no claim that all tensor flattenings collapse.

Matrix equivalence, Smith normal forms and cokernel decomposition are classical tools; Stanley's survey [S] supplies that background. The particular normal form above is derived explicitly rather than attributed to the survey. Its scope is linear algebra. It does not force a scalar pairing of the kernel with its actual multiplicities to be irrational.

## 3. Weighted redistribution: an interval while two channels are fixed

### 3.1 A general construction principle

Let $t_0<t_1<\cdots$ be boundaries, with integer heights $H_n$ satisfying
$$
H_n=p_nH_{n-1},\qquad p_n\ge2,
$$
where $H_{-1}=1$. Let positive integer multiplicities $\mu_n$ give a convergent sum $\sum_n\mu_n/H_n$.

Choose a channel value $r\ge2$ and a sequence of indices
$$
n_0<n_1<n_2<\cdots,\qquad p_{n_j}=r.
$$
Set $A_j=H_{n_j}$ and assume
$$
2\le R_j:=A_j/A_{j-1}\le R_*\qquad(j\ge1).
$$
Let $M\ge1$ and suppose the chosen cells have capacity
$$
\mu_{n_j}\ge M(R_*-1)+1\qquad(j\ge1).
$$
All other boundaries will be called fixed boundaries.

**Theorem 3.1 (interval realisation with fixed boundary sums).** For each
$$
0\le\Delta\le\frac{(r-1)M}{A_0}
$$
there are positive integer multiplicities $\mu'_n$ such that
$$
\sum_{n\ge0}\frac{\mu'_n-\mu_n}{H_n}=\Delta,
$$
$$
|\mu'_n-\mu_n|\le M(R_*-1),\qquad
\mu'_n\equiv\mu_n\pmod M,
$$
and the multiplicities before $n_0$ are unchanged. Every complete block between any two fixed boundaries has exactly its original unweighted multiplicity sum.

*Proof.* Cantor expansion in the integer radices $R_j$ gives digits
$$
0\le a_j\le R_j-1,\qquad
\Delta=(r-1)M\sum_{j\ge1}\frac{a_j}{A_j}.
$$
For completeness, apply the greedy recurrence to $z_0=A_0\Delta/((r-1)M)\in[0,1)$:
$$
a_j=\lfloor R_jz_{j-1}\rfloor,\qquad z_j=R_jz_{j-1}-a_j.
$$
The remainder after $L$ steps is $(r-1)Mz_L/A_L$, which tends to zero. For the upper endpoint take $a_j=R_j-1$ and telescope. This representation step is classical Cantor expansion [C].

Define a potential on the boundary indices by
$$
v_{n_j}=Ma_j\quad(j\ge1),\qquad v_n=0\text{ otherwise},
$$
and put
$$
\epsilon_n=v_{n+1}-v_n,\qquad \mu'_n=\mu_n+\epsilon_n. \tag{3.1}
$$
The potential lies in $[0,M(R_*-1)]$. At an index where $v_n>0$, the capacity assumption gives $\mu'_n\ge\mu_n-v_n\ge1$. At any other index $\epsilon_n\ge0$, so positivity again holds. The bound and the congruence are immediate.

For fixed boundary indices $a,b$,
$$
\sum_{n=a}^{b-1}\epsilon_n=v_b-v_a=0.
$$
Thus every specified block total is preserved.

Weighted summation by parts gives
$$
\sum_{n\ge0}\frac{\epsilon_n}{H_n}
=\sum_{n\ge1}v_n\left(\frac1{H_{n-1}}-\frac1{H_n}\right)
=(r-1)\sum_{j\ge1}\frac{Ma_j}{A_j}=\Delta.
$$
The initial potential is zero; the terminal boundary term tends to zero because the potential is bounded and $H_n\ge2^{n+1}$. This also proves convergence of the perturbation series. $\square$

The potential is a local redistribution: it adds mass to the cell just before a selected boundary and removes the same mass from the cell just after it. Unweighted block totals telescope. Reciprocal weights distinguish the two cells, and the jump ratio supplies the factor $r-1$.

### 3.2 Actual positive capacities for the $\{2,3,5\}$ word

Now let $t_n$ enumerate all positive powers of $2,3,5$, beginning at $t_0=2$. Let $p_n$ be the prime of $t_n$ and put
$$
H_n=H(t_n),\qquad
\mu_n=\#\{2^i3^j5^k:t_n\le2^i3^j5^k<t_{n+1}\}.
$$
Every cell contains its left endpoint, so $\mu_n\ge1$. The actual repeated value is
$$
S=1+\sum_{n\ge0}\mu_n/H_n.
$$
We construct enough free cells in the five-power channel. All numerical constants below are exact; none is claimed to be optimal.

Put $\rho_0=27/25$. Call an exponent $e\ge1$ good if neither a two-power nor a three-power lies in $(5^e,\rho_0 5^e)$. The cell starting at $5^e$ then contains $[5^e,\rho_0 5^e)$.

**Lemma 3.2.** Every three consecutive positive exponents contain a good exponent.

*Proof.* For a prime $p=2,3$, being bad in the $p$-channel means that the phase $\{e\log_p5\}$ belongs to an open circular interval of length $\log_p\rho_0$. The three consecutive phases are a translate of those for exponents $0,1,2$.

For $p=2$, their normalised representatives are $1,5/4,25/16$. Their smallest cyclic multiplicative gap is $5/4>\rho_0$. For $p=3$, the representatives are $1,5/3,25/9$, whose smallest cyclic gap is $27/25=\rho_0$. An open interval of the stated length contains at most one of the three phases in each channel. At most two of the three exponents are bad, which proves the claim. Equality at an interval endpoint counts as good. $\square$

**Lemma 3.3.** For every $e\ge1$, the interval $[5^e,\rho_0 5^e)$ contains at least $1+\lfloor e/25\rfloor$ distinct $\{2,5\}$-smooth integers.

*Proof.* If $1\le k\le e$ and
$$
5^k<2^{\lceil k\log_2 5\rceil}<\rho_0 5^k,
$$
then
$$
x_k=2^{\lceil k\log_2 5\rceil}5^{e-k}
$$
lies in the stated interval. Different $k$ give distinct five-adic valuations. The endpoint $5^e$ is another point.

It remains to obtain one suitable $k$ in each block of 25 consecutive indices. The circular phases $\{j\log_2 5\}$, $0\le j<25$, have maximum multiplicative gap
$$
g=\frac{5^{22}}{2^{51}}=\frac{2384185791015625}{2251799813685248}<\frac{27}{25}. \tag{3.2}
$$
Here is a complete finite certificate. In increasing order the exponents of the representatives $5^j/2^{\lfloor j\log_2 5\rfloor}$ are
$$
\begin{gathered}
0,22,19,16,13,10,7,4,1,23,20,17,14,\
11,8,5,2,24,21,18,15,12,9,6,3.
\end{gathered}
$$
The cyclic consecutive ratios are 22 copies of $128/125$ and three copies of $5^{22}/2^{51}$. Both exceed one, their product is two, and the latter is the larger. These are integer-power comparisons; the accompanying checker verifies the list and its gaps exactly.

Every arc of logarithmic length $\log_2\rho_0$ therefore contains one of these 25 phases, and the same is true after translation. Apply this to the arc $(1-\log_2\rho_0,1)$. It supplies one suitable $k$ in every consecutive block of 25 indices. Endpoints cause no equality because $\rho_0$ has a prime factor three. The resulting count proves the lemma. $\square$

The good exponents $e_0<e_1<\cdots$ have gaps at most three. Consequently their heights satisfy
$$
2\le\frac{H(5^{e_j})}{H(5^{e_{j-1}})}
\le 2^7 3^5 5^3=3\,888\,000=:R_* . \tag{3.3}
$$
The ratio is an integer. The upper bound follows by increasing the argument by at most $5^3$: the exponent increases in the two- and three-channels are at most $7$ and $5$, respectively, and the five-channel increase is at most $3$.

### 3.3 Two exact block families still permit a rational total

**Theorem 3.4 (two-channel-preserving interval theorem).** Fix an arbitrary finite prefix of the actual multiplicities and an integer $M\ge1$. There exist $\delta>0$ and a constant
$$
C=3\,887\,999M
$$
such that every value in $[S,S+\delta]$ is realised by positive integer multiplicities $\mu'_n$ with the following properties: the actual height word is unchanged; the protected prefix is unchanged; $|\mu'_n-\mu_n|\le C$ and $\mu'_n\equiv\mu_n\pmod M$ for all $n$; every complete block between two powers of two has the actual total multiplicity; and every complete block between two powers of three has the actual total multiplicity.

*Proof.* Choose a good exponent $e_0\ge25C$ sufficiently far beyond the protected prefix, and enumerate every subsequent good exponent. Lemma 3.3 makes the actual multiplicity at each chosen five-power cell at least $C+1$. Lemma 3.2 and (3.3) give the bounded integer radices required by Theorem 3.1. Apply that theorem with free channel $r=5$. One may take
$$
\delta=\frac{4M}{H(5^{e_0})}.
$$
The potential vanishes at every two- and three-power boundary, so both complete block families are preserved. $\square$

Since a nondegenerate real interval contains rational numbers, all these invariants are compatible with a rational total. Choosing $M$ divisible by any prescribed finite list of moduli preserves that entire list of congruences simultaneously. The start can be moved arbitrarily far out. The theorem asserts existence and a real greedy construction; it supplies no favourable complexity bound for locating a desired rational target.

The modified multiplicities need not come from the original smooth integers. They retain the stated source statistics exactly, but the omitted third-channel distribution changes. The theorem is a countermodel to an information set, not a counterexample to the original irrationality question.

A further exact bound clarifies how close the scalar tails remain. At a dyadic cutoff, with the source normalisation $X_a=H(2^a)T_a/2$, the construction gives
$$
0\le X'_a-X_a\le C/2. \tag{3.4}
$$
Indeed, at its boundary the potential is zero. The fully height-normalised perturbation is a nonnegative sum of future potentials with weights
$$
H_k\left(\frac1{H_{j-1}}-\frac1{H_j}\right),\qquad j>k,
$$
and those weights sum to one. Divide by two for the source's normalisation. In particular, one may choose a dyadic rational total; its smooth denominator is eventually absorbed, so the modified dyadic tails become integral while staying within the bound (3.4). The ordinary boundary-clearing argument continues to apply because all modified coefficients are integers on the same height cells.

### 3.4 Adding the third block family restores identifiability

**Proposition 3.5 (existing rigidity, specialised).** Suppose an integer perturbation $\epsilon_n$ preserves the complete block sums between every pair of boundaries of the same channel, for all three channels. If the initial transitions $2\to3$ and $2\to5$ have zero perturbation, then $\epsilon_n=0$ for every $n$.

*Proof.* Let $V_N=\sum_{n<N}\epsilon_n$. Block preservation says that $V_N$ depends only on the channel of boundary $N$. Hence $\epsilon_n=C(p_{n+1})-C(p_n)$ for a function $C$ on three elements. The two zero transitions give $C(2)=C(3)=C(5)$, so every difference vanishes. This is exactly the mechanism already formalised in `ThreeChannelBlockRigidity.lean`. $\square$

For the actual boundary word the transitions occur at $2\to3$ and $4\to5$. Thus preserving the first three cell multiplicities supplies both anchors. The contrast is exact: two complete channel families plus any finite prefix admit an interval; all three families plus these anchors determine every coefficient.

This is identifiability of the source, not irrationality of its weighted total. It gives a precise boundary for arguments based only on complete block counts.

### 3.5 Why this does not contradict the round-5 thin-set theorem

The earlier thin-set theorem concerned canonical, one-sided digit corrections with
$$
0\le d'_a-d_a\le M(b_a-1)
$$
and forced zero corrections at certain radix-two positions. It correctly proves a null, dimension-deficient correction set for that class.

The present construction uses signed differences $v_{n+1}-v_n$. The resulting multiplicities remain strictly positive, but the changes can have either sign. That larger class supports the interval in Theorem 3.4, even with two complete block families fixed. Consequently the round-5 conclusion must not be paraphrased as a theorem that arbitrary shell-preserving bounded perturbations form a thin set.

The reusable principle is Theorem 3.1: prescribe a potential that vanishes on protected boundaries, then use positive capacity at free cells and integer radix expansion to prescribe the weighted change. Its antecedents are the corpus's bounded-perturbation construction for #251, the #269 fixed-modulus splice, and classical Cantor expansion. The two actual block families and the positivity capacity proof are the additional content here.

## 4. The carry has an exact continuum spectrum

The normalised carry also admits a useful analytic interpretation. Let $0<c<1$ and consider
$$
\mathcal C_c(x,y)=c+(1-c)\mathbf1_{\{x+y<1\}},\qquad 0\le x,y\le1.
$$
Its integral operator on $L^2(0,1)$ is
$$
(T_cf)(x)=c\int_0^1f(y)\,dy+(1-c)\int_0^{1-x}f(y)\,dy.
$$
It is a reflected Volterra operator plus a rank-one operator. Passing from an integral eigenproblem to a differential boundary problem is a standard method for Volterra operators; see [V]. The calculation below identifies this particular kernel explicitly.

### 4.1 Eigenvalues and eigenfunctions

Put $a=1-c$ and
$$
\theta=2\arctan\frac{1-c}{1+c}=\frac\pi2-2\arctan c.
$$

**Theorem 4.1.** The operator $T_c$ is compact, self-adjoint and injective. Its nonzero eigenvalues are simple and are precisely
$$
\boxed{\lambda_n=\frac{1-c}{\theta+2\pi n},\qquad n\in\mathbb Z.} \tag{4.1}
$$
An orthonormal eigenbasis is
$$
\phi_n(x)=\sqrt{\frac{2}{1+c^2}}
\bigl(\cos(k_nx)-c\sin(k_nx)\bigr),\qquad k_n=\theta+2\pi n.
$$

*Proof.* Symmetry and square integrability of the kernel give compactness and self-adjointness. If $T_cf=0$, differentiating in the weak sense gives $-af(1-x)=0$, hence injectivity.

For $T_cf=\lambda f$, $\lambda\ne0$, the integral formula first gives an absolutely continuous representative, and then
$$
\lambda f'(x)=-af(1-x),\qquad f''(x)=-(a/\lambda)^2f(x).
$$
The endpoint values imply $f(1)=cf(0)$. Write the signed quantity $k=a/\lambda$. Then $f'(0)=-kc f(0)$, so
$$
f(x)=A(\cos(kx)-c\sin(kx)).
$$
Here $A\ne0$, since otherwise the solution is identically zero. The conditions at $x=1$ give
$$
\cos k-c\sin k=c,\qquad \sin k+c\cos k=1.
$$
Solving yields
$$
\cos k=\frac{2c}{1+c^2},\qquad
\sin k=\frac{1-c^2}{1+c^2},
$$
so $k=\theta+2\pi n$. Conversely each such function satisfies the derivative identity and the integral equation at $x=0$, because its integral equals $a/k$. Therefore it is an eigenfunction with eigenvalue $a/k$.

The squared norm of the unnormalised function is $(1+c^2)/2$; substituting the two displayed trigonometric values cancels its oscillatory correction. Different eigenvalues are orthogonal. The spectral theorem for compact self-adjoint operators, together with injectivity, gives completeness. $\square$

The squared Hilbert--Schmidt norm provides a useful independent identity:
$$
\sum_{n\in\mathbb Z}\lambda_n^2
=\int_0^1\!\int_0^1|\mathcal C_c(x,y)|^2\,dx\,dy
=\frac{1+c^2}{2}.
$$

### 4.2 Exact mean-square approximation and the actual rotation samples

The singular values, in decreasing order, are
$$
\frac a\theta,\quad\frac a{2\pi-\theta},\quad
\frac a{2\pi+\theta},\quad\frac a{4\pi-\theta},\quad\ldots.
$$
Writing them as $s_1\ge s_2\ge\cdots$, the spectral truncation theorem gives
$$
\inf_{\operatorname{rank}F\le d}
\|\mathcal C_c-F\|_{L^2((0,1)^2)}
=\left(\sum_{j>d}s_j^2\right)^{1/2}
\sim\frac{1-c}{\pi\sqrt d}. \tag{4.2}
$$
The asymptotic follows from $s_j\sim(1-c)/(\pi j)$.

Let $\alpha,\beta$ be individually irrational and
$$
(C_N)_{ij}=\mathcal C_c(\{i\alpha\},\{j\beta\}),\qquad 0\le i,j<N.
$$
For every fixed $d$,
$$
\lim_{N\to\infty}\frac1N
\inf_{\operatorname{rank}A\le d}\|C_N-A\|_F
=\left(\sum_{j>d}s_j^2\right)^{1/2}. \tag{4.3}
$$

*Proof.* Sort the row phases and column phases separately. Individual equidistribution implies that their maximum distances from the corresponding uniform quantile intervals tend to zero. Call these distances $\varepsilon_x,\varepsilon_y$. Regard the permuted matrix as a step kernel on the $N\times N$ equal partition. It differs from $\mathcal C_c$ only in the strip
$$
|x+y-1|\le\varepsilon_x+\varepsilon_y,
$$
up to null boundary sets. Its Hilbert--Schmidt error is at most
$$
(1-c)\sqrt{2(\varepsilon_x+\varepsilon_y)}.
$$
Distance to the set of rank-at-most-$d$ kernels is a 1-Lipschitz function of the ambient Hilbert--Schmidt norm. The step-kernel distance equals $N^{-1}$ times the matrix Frobenius distance: projecting a candidate approximation onto the step spaces in each variable cannot increase either error or rank. This proves (4.3). It also proves convergence of every fixed singular value $\sigma_j(C_N)/N$ to $s_j$. $\square$

For the running-LCM carry take $\alpha=\log_r p$ and $\beta=\log_r q$. Their individual irrationality is sufficient; no rational independence of $1,\alpha,\beta$ is used. The limit in (4.3) keeps $d$ fixed. An assertion with $d=d(N)$ needs a quantitative discrepancy estimate and is not included.

### 4.3 The norm distinction becomes visible

For thresholds $\tau\ne\sigma$, the corresponding continuum columns satisfy
$$
\|v_\tau-v_\sigma\|_\infty=1-c,
\qquad
\|v_\tau-v_\sigma\|_2=(1-c)\sqrt{|\tau-\sigma|}.
$$
Thus the threshold family is non-precompact in the supremum norm and compact in the mean-square metric. This explains how the existing positive infinite uniform approximation threshold coexists with the decay (4.2). The operator here is the normalised carry, not the unbounded actual tail cocycle. Its spectral solution does not discharge the packet's nonstationary arithmetic obligation.

## 5. A shorter complete route from multiplicities to the registered carry bound

The short note need not spend several pages on elementary finite-shell lemmas before it reaches its actual recurrence. The following argument proves the deliberately loose cap already used by the registered window criterion. It does not improve the stronger majorant already present in the corpus.

Let $s_n$ be the actual reciprocal mass in $[2^n,2^{n+1})$. Fixing the three- and five-exponents allows at most one two-exponent in such a shell. Both fixed exponents range from $0$ to $n$, so its number of smooth points is at most $(n+1)^2$. Since $H(x)>x^3/30$,
$$
s_n\le30(n+1)^2 8^{-n}.
$$
Writing $h_a=H(2^a)/2\le8^a/2$ gives
$$
X_a=h_a\sum_{j\ge0}s_{a+j}
\le15(a+1)^2\sum_{j\ge0}(j+1)^2 8^{-j}
=\frac{8640}{343}(a+1)^2
<90(a+1)^2. \tag{5.1}
$$
This also proves summability. The coefficient $8640/343$ is much weaker than the source's specialised $\widetilde Q$ at the natural jump scale. Its purpose is proof economy at the existing cap, not a new optimisation claim.

For each smooth $x<2^{a+1}$, the strict two-channel exponent inequality gives $2H(x)\mid H(2^{a+1})$. Hence the literal integer forcing is
$$
m_a=\sum_{\substack{x\text{ smooth}\\2^a\le x<2^{a+1}}}
\frac{H(2^{a+1})}{2H(x)}\in\mathbb N.
$$
With $b_a=H(2^{a+1})/H(2^a)\in\{2,6,10,30\}$, splitting one shell yields
$$
X_{a+1}=b_aX_a-m_a.
$$
For $a\ge1$, prefix clearing gives $X_a=h_aS-Z_a$ with $Z_a\in\mathbb Z$. If $S=A/D$ and $D=2^u3^v5^wB$, $(B,30)=1$, then the registered onset $a_0=u+1+2v+3w$ makes $2^u3^v5^w$ divide $h_a$. Thus $BX_a$ is a positive integer bounded by $90B(a+1)^2$ for all $a\ge a_0$.

This establishes the actual bridge with visible finite data and a complete elementary bound. The sharper count and jump-constraint results must be retained through the accompanying long-record migration. The main note loses no target-level conclusion by using the simpler proof at its existing cap.

## 6. What these results rule out, and what remains

The information boundary is now more specific than a list of failed heuristics.

**Linear independence.** The three-prime carry is maximally rich along selected finite restrictions, even modulo every admissible denominator for $\{2,3,5\}$. A scalar irrationality proof still needs an arithmetic functional or approximation whose nonvanishing is tied to this richness. Arbitrary rank alone supplies no such pairing.

**Choice of norm.** The uniform obstruction is exact, but mean-square low-rank approximation is effective with a completely explicit spectrum. A method whose success depends on an unspecified notion of finite-dimensional approximation is underdetermined until it names its norm and its denominator control.

**Source statistics.** The actual height word, any finite prefix, all congruences modulo a fixed modulus, bounded perturbation size, and every dyadic and ternary complete block total still permit a rational total. Theorem 3.4 is a witness against an argument using only those invariants. Adding all three block families identifies the actual coefficients, but does not itself evaluate their sum.

**Lifts.** The existing carry-lift identity has a weighted defect. Ordinary block-nullity is an additional premise, not a consequence of bounded lift error. The three-channel rigidity theorem cannot be applied until a source-faithful construction supplies that premise and its anchors. The new two-channel theorem makes dropping the third family untenable as a general rescue.

**Equivalent criteria.** The residue-window criterion at a valid polynomial cap is an exact change of coordinates. It does not become a new source-specific producer merely because it is easier to test finitely. A concrete approximation theorem, a nonzero weighted block defect, or an actual residue construction would supply additional mathematics.

The strongest immediate follow-up questions are correspondingly specific. Can a bounded rationalising lift satisfying all three actual channel constraints be constructed or excluded without assuming its unweighted block-nullity? Which weighted identities, weaker than full identification of every cell, exclude the interval construction of Theorem 3.4? Can the explicit arithmetic cut normal form be coupled to an actual summation functional with denominator and error control? The spectral calculation suggests a quantitative approximation problem, but the error estimate must be compared with arithmetic denominators rather than only with an analytic norm.

No universal answer to these questions is proved here. Each names a missing construction or estimate rather than replacing the original problem with an equivalent slogan.

## 7. Short-note organisation and evidence

The proposed edit keeps the live title and the exact statement of `res:infinite-rank`. The first page now states that result in the problem's notation; the proof immediately displays the threshold matrix. The inexpensive modular-minor corollary follows the determinant. The two-prime theorem is presented through its two polynomials in one Hecke--Mahler value, with Fan's attribution retained. The remaining sections define actual multiplicities, prove the actual recurrence and denominator bridge using (5.1), and state one precisely quantified arithmetic question.

The larger redistribution and spectral theorems remain in this memorandum. They should be checked and compared with prior literature before any manuscript or registry promotion. This follows the distinction in Tao's writing advice [T1]: inexpensive consequences of the main theorem belong near it, whereas a substantial separate development needs its own mathematical purpose. His partial-progress advice [T2] is applied here through explicit falsifying constructions and their hypotheses, rather than through assertions of significance.

The supplied older long record requires labelled insertions for the live finite cut-rank formula, the improved jump-constraint majorant, the later actual bridge and several later ordinary results. The separate migration file distinguishes those inherited omissions from the new results of this return. It also identifies the old sections that receive the material removed from the short note.

The exact checker performs 29,073 finite checks: localised integer Smith forms, modular image cardinalities, the circle-cover certificate, finite actual multiplicity redistributions, complete block preservation, weighted summation by parts, mixed-radix remainders and spectral boundary algebra. It contains no floating-point arithmetic. The infinite results rely on the proofs above, not on the check count. The checker does not rebuild Lean or replay the original large denominator scans. The authored Lean file is confined to finite algebra and explicit integer inequalities.

## References and scope of comparison

**[S]** Richard P. Stanley, *Smith normal form in combinatorics*, arXiv:1602.00166 (2016), author's survey: <https://math.mit.edu/~rstan/papers/snf_survey.pdf>. Used for standard matrix-equivalence, invariant-factor and cokernel background. Theorem 2.1 above is proved here; this source is not cited as already containing it.

**[C]** Émilie Charlier and Célia Cisternino, *Expansions in Cantor real bases*, arXiv:2102.07722v1 (2021): <https://arxiv.org/html/2102.07722v1>. Used to situate the classical Cantor expansion underlying Theorem 3.1. The preservation of two actual block families and the capacity construction in Theorem 3.4 are not claimed to follow from that paper alone.

**[V]** Thomas Ransford and Nathan Walsh, *Norms of polynomials of the Volterra operator*, arXiv:2206.09947v2 (2022): <https://arxiv.org/html/2206.09947v2>. The introduction discusses the standard reduction of Volterra eigenproblems to differential boundary problems. The reflected, rank-one-perturbed kernel in Section 4 is calculated explicitly in this memorandum. A comprehensive search for a subsuming spectral formula has not been completed.

**[T1]** Terence Tao, *Maximising the results-to-effort ratio* (2010, expanded 2019): <https://terrytao.wordpress.com/advice-on-writing-papers/maximising-the-results-to-effort-ratio/>.

**[T2]** Terence Tao, *On the importance of partial progress*: <https://terrytao.wordpress.com/career-advice/on-the-importance-of-partial-progress/>.

**[P]** User-supplied round-6 live note, research packet, authored long-record parts and Lean source slice. The mathematical snapshot is `e9a122bf7cf9ff7a20e45a6215876b3825aeee18`; the public browsing pin is `32545d77c4b5cfd72ebd36c8dcd2418bf7cc4d31`. The existing three-channel theorem was read through the connected repository at that pin. No repository files were changed.

These comparisons identify antecedents to the methods used here. They are not an exhaustive priority search or evidence that an unlocated theorem does not exist.
