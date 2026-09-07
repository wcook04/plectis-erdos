---
title: "Rational-base measures and geometric Hankel asymptotics"
subtitle: "Erdős 1049: sixth-round mathematical return"
author: "Research review, 7 September 2026"
date: ""
---

# 1. Claims, dependencies and scope

The live R6 short note proves an explicit irrationality region and an exact formal Hankel order. Those theorems remain the lead. This return adds a quantitative consequence of the same rational-base forms, a Schur expansion for the separate geometric-moment construction, and two finite diagnostic principles for the remaining local-to-real problem.

The assertions below are ordinary proofs. The accompanying Lean files are uncompiled candidates. The quantitative selector wrapper in the supplied corpus is already reported checked by the R5 desk; this return does not claim to have checked it again. None of the results below proves irrationality at base $3/2$. Bibliographical novelty of the additional asymptotic statements is unconfirmed.

The two source families are kept separate throughout. Section 2 uses the **2004 polynomial linear forms**. Sections 3–6 use the **2016 normalised moment rows**. Sections 7–8 concern generic lattice geometry and a separate lacunary countermodel. There is no denominator transfer between the two Zudilin constructions.

**New relative to this packet.** The rational-base irrationality-exponent formula in Theorem 2.2 is a direct quantitative consequence of the live flagship. The exact Schur identity in Theorem 3.1 explains the geometric Gram expansion. Theorem 4.1 computes its first correction; Theorem 4.2 identifies a stability principle under exponentially small changes of the atom weights. Section 5 calculates a further polar derivative and Theorem 6.1 obtains a $1/N$ correction to the earlier R3 candidate. The finite strip lemma identifies the geometry of a highly concentrated modular fibre. The lacunary example shows why the regular-scale hypothesis in the R4 obstruction cannot simply be omitted.

**Already present.** The rational-base cutoff, positive-moment representation, formal exponent and leading coefficient, $O_q(N)$ residual bound, Smith-index formulas, quantitative binning criterion, and R4 narrow-family regular-scale obstruction are not new claims here. Their roles are stated when used.

# 2. A quantitative consequence of the live irrationality region

Write
\[
F(x)=\sum_{n\ge1}\frac1{x^n-1},\qquad
C_1=1091/2,\quad \theta^*=C_0/C_1.
\]
The constant $C_0$ and its thirteen-interval formula are those of the live rational-base theorem. Its source label is `res:rational-base-threshold`, and its cutoff is
\[
\theta^*=0.405683021384060541\ldots.
\]

For the same source construction, put
\[
\Lambda_n(X)=U_n(X)F(X)-V_n(X),\qquad U_n,V_n\in\mathbb Z[X],
\]
with raw degree $K_n$ and cancelled degree $W_n$. The live proof establishes, for fixed $x>1$,
\[
K_n/n^2\to C_1,\qquad (K_n-W_n)/n^2\to C_0,
\qquad \log\Lambda_n(x)=-(K_n-W_n)\log x+O_x(n),
\tag{2.1}
\]
and $\Lambda_n(x)>0$. The polynomial inclusion is [Z04, Lemma 7, (23)].

## 2.1 A finite rational-separation lemma

The long record already uses the general $1+\alpha/\beta$ measure argument in the proof of `res:archcap` (lines 952–982 of the supplied TeX). The extraction here is the explicit **rational-base** bound, using the pointwise source estimate below, and its uniformity over positive powers. The general irrationality-measure method is not a new invention.

**Lemma 2.1.** Let $A,B,p,q$ be integers, $q>0$, and let $\xi$ be real. Put $L=A\xi-B$. If $2q|L|\le1$, then
\[
\boxed{|L|\le |A|\,|\xi-p/q|.}
\tag{2.2}
\]

**Proof.** If $Ap/q-B=0$, equality holds. Otherwise $Ap-Bq$ is a nonzero integer, so
\[
1/q\le |Ap/q-B|\le |L|+|A|\,|\xi-p/q|.
\]
Since $2|L|\le1/q$, subtraction proves (2.2). No independence of two approximating rows is required. $\square$

The lemma is useful because it also covers the possibility that the proposed rational approximation is exactly the ratio of one source row. That case does not require an adjacent-determinant argument.

## 2.2 The source coefficient bound

The raw first coefficient $A_n(X)$ is a sum of at most $\beta$ signed Laurent monomials times two Gaussian polynomials. Each Gaussian polynomial has nonnegative integer coefficients and coefficient sum equal to the corresponding ordinary binomial coefficient. Its coefficient sum is therefore at most $2^\beta$. Consequently
\[
\|A_n\|_1\le \beta 2^{2\beta}=\exp(O(n)).
\]
Every exponent in the raw expression is at most $K_n$. For fixed $x>1$ this gives
\[
|A_n(x)|\le x^{K_n}\exp(O(n)).
\]
The normalising multiplier is $X^{-M_n}D_{15n}(X)/\Omega_n(X)$. Its logarithm at $x$ equals $(W_n-K_n)\log x+O_x(n)$ by the same cyclotomic estimate already used for (2.1). Hence
\[
\boxed{|U_n(x)|\le x^{W_n}\exp(O_x(n)).}
\tag{2.3}
\]
This uses coefficient norms only for the raw Laurent expressions. The cancelled $U_n,V_n$ are ordinary polynomials, as required by the main theorem.

## 2.3 The irrationality-exponent bound

For irrational $\xi$, let $\mu_{\rm irr}(\xi)$ denote the supremum of the real numbers $\nu$ for which $|\xi-p/q|<q^{-\nu}$ has infinitely many reduced rational solutions with $q>0$.

**Theorem 2.2.** Suppose $a>b\ge1$ are coprime and $\theta=\log b/\log a<\theta^*$. For every positive integer $r$,
\[
\boxed{
\mu_{\rm irr}\!\left(F((a/b)^r)\right)
\le \frac{1-\theta}{\theta^*-\theta}.
}
\tag{2.4}
\]
The exponent bound is independent of $r$. Constants and starting denominators in the approximation inequalities may depend on $r$.

**Proof.** It suffices first to take $r=1$. Clear the rational-base denominator in the source forms:
\[
Q_n=b^{W_n}U_n(a/b),\quad P_n=b^{W_n}V_n(a/b),\quad
L_n=Q_nF(a/b)-P_n>0.
\]
These are integer coefficients. Set
\[
\alpha=(C_1-C_0)\log a,\qquad
\tau=C_0\log a-C_1\log b>0.
\]
Equations (2.1)–(2.3) give
\[
\log L_n=-\tau n^2+o(n^2),\qquad
|Q_n|\le\exp(\alpha n^2+o(n^2)).
\tag{2.5}
\]
Fix a small $\eta>0$ with $\eta<\tau$. For sufficiently large $n$,
\[
e^{-(\tau+\eta)n^2}\le L_n\le e^{-(\tau-\eta)n^2},
\qquad |Q_n|\le e^{(\alpha+\eta)n^2}.
\]
Given a sufficiently large denominator $q$, choose
\[
n=\left\lceil\sqrt{\frac{\log(2q)}{\tau-\eta}}\right\rceil.
\]
Then $2qL_n\le1$. In particular $Q_n\ne0$, since otherwise the positive $L_n$ would be an integer smaller than one. Lemma 2.1 yields, for every numerator $p$,
\[
|F(a/b)-p/q|\ge L_n/|Q_n|
\ge e^{-(\alpha+\tau+2\eta)n^2}
=q^{-(\alpha+\tau+2\eta)/(\tau-\eta)-o(1)}.
\]
Letting $\eta\downarrow0$ proves $\mu_{\rm irr}\le1+\alpha/\tau$.
Algebra gives
\[
1+\alpha/\tau
=\frac{C_1(\log a-\log b)}{C_0\log a-C_1\log b}
=\frac{1-\theta}{\theta^*-\theta}.
\]
Replacing $(a,b)$ by $(a^r,b^r)$ multiplies both $\alpha$ and $\tau$ by $r$, and leaves $\theta$ unchanged. $\square$

For $b=1$, (2.4) reduces to $C_1/C_0$, exactly the uniform integer-base exponent in [Z04]. For the power family in the title, the bound is in the rigorously certified interval
\[
300.4269<\frac{1-\log4/\log31}{\theta^*-\log4/\log31}<300.4270<301.
\tag{2.6}
\]
This is a finite irrationality measure, not a claim of sharpness. Its value is quantitative scope at negligible additional proof cost. It adds no new base to the sufficient region.

The exact certificate in `checks/check_r6.py` sums 512 terms of each trigamma difference. The summands are positive decreasing functions $f(k)$, so their remaining sum is between $\int_{512}^{\infty}f$ and $f(512)+\int_{512}^{\infty}f$. It bounds logarithms by the positive atanh series and $\pi$ by the alternating Machin formula. All comparisons in (2.6) use rational arithmetic. Floating-point numbers in the receipt are display values only.

# 3. An exact Schur expansion for geometric moments

Fix $0<q<1$. Let $a_k>0$ satisfy at most polynomial growth, and define
\[
v_m=\sum_{k\ge0}a_kq^{(m+1)k},\qquad
V_N=\det(v_{i+j})_{0\le i,j<N}.
\]
Put
\[
B_N=\frac{N(N-1)(2N-1)}6,\qquad
\mathcal G_N=q^{B_N}\left(\prod_{k=0}^{N-1}a_k\right)
\prod_{d=1}^{N-1}(1-q^d)^{2(N-d)}.
\tag{3.1}
\]
For a partition $\lambda=(\lambda_1\ge\cdots\ge\lambda_N\ge0)$, the Schur polynomial is defined by the alternant quotient
\[
s_\lambda(x_1,\ldots,x_N)
=\frac{\det(x_i^{\lambda_j+N-j})_{i,j=1}^N}
{\det(x_i^{N-j})_{i,j=1}^N}.
\]
This quotient is a symmetric polynomial. The Schur measure and its Cauchy normalisation are classical [O00, Section 2.1].

**Theorem 3.1.** For every $N\ge1$,
\[
\boxed{
\frac{V_N}{\mathcal G_N}
=\sum_{\ell(\lambda)\le N}
q^{|\lambda|}s_\lambda(1,q,\ldots,q^{N-1})^2
\prod_{j=1}^{\ell(\lambda)}
\frac{a_{N-j+\lambda_j}}{a_{N-j}}.
}
\tag{3.2}
\]
All summands are nonnegative.

**Proof.** The moment matrix is a Gram matrix. Finite Cauchy–Binet followed by convergence of the truncated moments gives
\[
V_N=\sum_{k_0<\cdots<k_{N-1}}
\left(\prod_i a_{k_i}q^{k_i}\right)
\prod_{i<j}(q^{k_i}-q^{k_j})^2.
\]
Write $k_i=i+\lambda_{N-i}$, which bijects increasing tuples with partitions of length at most $N$. The ratio of the two Vandermonde determinants is $s_\lambda(1,q,\ldots,q^{N-1})$. The ratio of the factors $q^{\sum k_i}$ is $q^{|\lambda|}$, and the atom-weight ratio is the last product in (3.2). The tuple $k_i=i$ contributes (3.1). $\square$

For constant atom weights the last product is one. The Cauchy identity evaluates the sum exactly:
\[
\sum_{\ell(\lambda)\le N}q^{|\lambda|}s_\lambda(1,q,\ldots,q^{N-1})^2
=\prod_{i,j=0}^{N-1}(1-q^{i+j+1})^{-1}.
\tag{3.3}
\]
As $N\to\infty$, this tends to
\[
\mathcal M(q)=\prod_{d\ge1}(1-q^d)^{-d}.
\tag{3.4}
\]
Thus the determinant is a Schur partition sum with a precisely specified multiplicative perturbation of its atom weights. The unique formal least-order tuple is the empty partition. The other partitions give the analytic correction.

# 4. A universal first correction and stability of the polar part

## 4.1 Polynomial atom weights

Assume
\[
a_k=p(k)+O(\rho^{-k}),\qquad \rho>1,
\tag{4.1}
\]
where $p$ is a real polynomial of degree $d\ge0$ with positive leading coefficient, and $a_k>0$ for every $k$. Define
\[
T(q)=\sum_{j\ge1}\frac{j q^j}{1-q^j}.
\]

**Theorem 4.1.** Under (4.1),
\[
\boxed{
\frac{V_N}{\mathcal G_N}
=\mathcal M(q)\left(1+\frac{dT(q)}{N}+O_q(N^{-2})\right).
}
\tag{4.2}
\]
Constants may depend on the entire fixed weight sequence. The parameter $q$ is fixed; no uniform assertion as $q\uparrow1$ is made.

**Proof.** Let
\[
w_q(\lambda)=q^{|\lambda|}s_\lambda(1,q,q^2,\ldots)^2,
\qquad
\chi_N(\lambda)=\prod_{j=1}^{\ell(\lambda)}
\frac{a_{N-j+\lambda_j}}{a_{N-j}}.
\]
For $r=\ell(\lambda)$ the principal specialisation formula gives
\[
s_\lambda(1,q,q^2,\ldots)
=\frac{q^{n(\lambda)}}{\prod_{(i,j)\in\lambda}(1-q^{h_{ij}})},
\quad n(\lambda)=\sum_{j\ge1}(j-1)\lambda_j,
\tag{4.3}
\]
where $h_{ij}$ is the hook length of the box $(i,j)$. Within one row these hook lengths are distinct positive integers, so the denominator product over that row is at least $P=(q;q)_\infty$. Hence
\[
w_q(\lambda)\le P^{-2r}q^{\sum_{j=1}^r(2j-1)\lambda_j}.
\]
Positivity and (4.1) imply constants $c,C>0$ with
$c(k+1)^d\le a_k\le C(k+1)^d$ for all $k$. Therefore
\[
\chi_N(\lambda)\le(C/c)^r\prod_j(\lambda_j+1)^d.
\tag{4.4}
\]
The product of these two bounds has a finite exponential moment in $|\lambda|$, uniformly in $N$. To see this, choose $\varepsilon>0$ with $qe^\varepsilon<1$, sum first over unrestricted $\lambda_j\ge1$, and use
\[
\sum_{h\ge1}(h+1)^d(q^{2j-1}e^\varepsilon)^h
\le C_{q,d,\varepsilon}q^{2j-1}.
\]
The remaining sum over $r$ is bounded by $\sum_r C_0^r q^{r^2}<\infty$.

For $|\lambda|\le N/2$, polynomial asymptotics and (4.1) give, uniformly,
\[
\log\chi_N(\lambda)
=\frac{d|\lambda|}{N}
+O\!\left(\frac{|\lambda|^2+|\lambda|}{N^2}\right),
\]
so
\[
\chi_N(\lambda)
=1+\frac{d|\lambda|}{N}
+O\!\left(\frac{|\lambda|^2+|\lambda|}{N^2}\right).
\tag{4.5}
\]
One way to verify the uniform bound is to differentiate $\log p(x)$ for large $x$. Its derivative is $d/(x+1)+O((x+1)^{-2})$. Integrate from $N-j$ to $N-j+\lambda_j$ and sum; $\sum j\lambda_j$ and $\sum\lambda_j^2$ are bounded by a constant times $|\lambda|^2+|\lambda|$. The exponentially small error in (4.1) is absorbed uniformly because $N-j\ge N/2$.

The finite-alphabet correction is
\[
\frac{s_\lambda(1,q,\ldots,q^{N-1})}
{s_\lambda(1,q,q^2,\ldots)}
=\prod_{(i,j)\in\lambda}(1-q^{N+j-i}).
\tag{4.6}
\]
For $|\lambda|\le N/2$ its square differs from one by at most
$2|\lambda|q^{N/2}$. The remaining partitions have exponentially small total contribution by (4.4). Thus (3.2), (4.5) and the exponential-moment bound yield
\[
V_N/\mathcal G_N
=\sum_\lambda w_q(\lambda)
+\frac dN\sum_\lambda |\lambda|w_q(\lambda)+O_q(N^{-2}).
\]
The first sum is $\mathcal M(q)$. To compute the second, introduce an **independent marking variable** $z$:
\[
Z(z,q)=\sum_\lambda z^{|\lambda|}s_\lambda(1,q,q^2,\ldots)^2
=\prod_{i,j\ge0}(1-zq^{i+j})^{-1}.
\]
Then
\[
\left.z\frac{\partial}{\partial z}\log Z(z,q)\right|_{z=q}
=\sum_{m\ge1}\frac{m q^m}{1-q^m}=T(q).
\tag{4.7}
\]
In particular the expectation of $|\lambda|$ under the normalised measure is $T(q)$. Differentiating $\mathcal M(q)$ with respect to $q$ instead would also differentiate the Schur specialisation and would give the wrong observable. Equation (4.2) follows. $\square$

The principal-specialisation formulas (4.3) and (4.6) also follow directly by setting $x_i=q^{i-1}$ in the alternant quotient and cancelling its Vandermonde products. They are used here with positive real $q$, so no sign or cancellation estimate is hidden in these formulas.

## 4.2 The analytic part changes only the limiting constant

**Theorem 4.2 (stability under an analytic perturbation).** Let $a_k$ and $\widetilde a_k$ be positive sequences satisfying (4.1) with the same polynomial $p$. Form $V_N(a)$ and $V_N(\widetilde a)$ using the same $q$. There is a $c>0$ such that
\[
\boxed{
\frac{V_N(a)}{V_N(\widetilde a)}
=\left(\prod_{k\ge0}\frac{a_k}{\widetilde a_k}\right)
\bigl(1+O(e^{-cN})\bigr).
}
\tag{4.8}
\]
The infinite product converges absolutely to a positive number.

**Proof.** Put $r_k=a_k/\widetilde a_k$. Then $r_k=1+O(\rho_0^{-k})$ for some $\rho_0>1$. The ratio of the two ground terms in (3.1) is $\prod_{k<N}r_k$, and this differs from $\prod_{k\ge0}r_k$ by $O(\rho_0^{-N})$ relatively.

For partitions of length at most $N/2$, every altered index $N-j$ is at least $N/2$. Therefore
\[
\frac{\chi_N^{a}(\lambda)}{\chi_N^{\widetilde a}(\lambda)}
=\prod_{j\le\ell(\lambda)}\frac{r_{N-j+\lambda_j}}{r_{N-j}}
=1+O(N\rho_0^{-N/2})
\]
uniformly, with no bound on the sizes of the parts needed. The partitions of greater length have $|\lambda|>N/2$; the common majorant from the proof of Theorem 4.1 makes their contribution $O(e^{-c_0N})$. Both partition sums are at least one because the empty partition contributes one. Their ratio is therefore $1+O(e^{-cN})$. Combine this with the ground terms. $\square$

If two generating functions each consist of the same finite polar part at $w=1$ plus a function analytic on a disc of radius greater than one, their coefficient sequences satisfy this hypothesis. Thus that finite polar part controls every algebraic correction to the determinant; the analytic remainder affects its overall constant. This statement is independent of the Lambert benchmark.

**Why the larger disc is necessary.** Equality of the polar parts at $1$ alone is insufficient. Take $a_k=1$ and $\widetilde a_k=1+\varepsilon(-1)^k$, where $0<\varepsilon<1$. Their generating functions are
\[
\frac1{1-w},\qquad \frac1{1-w}+\frac{\varepsilon}{1+w}.
\]
They have the same pole at $1$, but the second has another pole at $-1$. Both weight sequences are positive. Formula (3.2) and the majorant in (4.4), now with $d=0$, show that their partition sums are bounded above and below by positive constants independent of $N$. The ratio of ground terms is
\[
\prod_{k<N}(1+\varepsilon(-1)^k)
=(1-\varepsilon^2)^{\lfloor N/2\rfloor}
(1+\varepsilon)^{N\bmod2}.
\]
Consequently
\[
\log\frac{V_N(\widetilde a)}{V_N(a)}
=\frac N2\log(1-\varepsilon^2)+O_{q,\varepsilon}(1),
\]
not a convergent constant. The analytic-continuation hypothesis rules out precisely this additional boundary singularity.

# 5. A further polar identity for the actual 2016 rows

Now specialise to the registered positive moments
\[
v_m=(q;q)_m^3\sum_{t\ge0}q^{(m+1)t}
\frac{(q^{t+1};q)_m}{(q^{m+t+1};q)_{m+1}}.
\tag{5.1}
\]
These are the normalised rows from [Z16], with $x=z=1$. Put
\[
G_q(w)=\frac1{(w;q)_\infty^3}
\sum_{t\ge0}\frac{w^t}{(q;q)_t}
\frac{(q^tw^2;q)_\infty}{(q^tw;q)_\infty^2},
\qquad
\sum_{k\ge0}a_kw^k=P^4G_q(w).
\tag{5.2}
\]
The source product identities give $v_m=\sum a_kq^{(m+1)k}$. The coefficient positivity in the packet follows by factoring each numerator into
\[
(q^tw^2;q)_\infty
=(q^{t/2}w;q)_\infty(-q^{t/2}w;q)_\infty
(q^{(t+1)/2}w;q)_\infty(-q^{(t+1)/2}w;q)_\infty.
\]
Pair the two positive-sign factors with two copies of $(w;q)_\infty$ and use the $q$-binomial ratio with nonnegative coefficients. The remaining products and reciprocal products have nonnegative coefficients. The $t=0$ summand gives strict positivity in every degree.

Define
\[
S=F(1/q)=\sum_{j\ge1}\frac{q^j}{1-q^j},\qquad
T=\sum_{j\ge1}\frac{j q^j}{1-q^j},\qquad
D(w)=P^4(1-w)^4G_q(w).
\]

**Proposition 5.1.** The function $D$ extends analytically to a disc of radius greater than one, and
\[
\boxed{D(1)=3,\qquad D'(1)=2+8S,\qquad
D''(1)=21S^2+3S+3T.}
\tag{5.3}
\]
The first two identities appeared in the R3 candidate. The third is the additional coefficient needed for the next determinant term.

**Proof.** Set
\[
Q(w)=(qw;q)_\infty,\quad
R(w)=\frac{(qw^2;q)_\infty}{Q(w)^2},
\quad
f_t(w)=\frac{(q^tw^2;q)_\infty}{(q;q)_t(q^tw;q)_\infty^2}\quad(t\ge1).
\]
Choose $1<r<q^{-1/2}$. Uniformly on $|w|\le r$, the products give
$f_t(w)=P^{-1}+O_q(q^t)$. Hence
\[
E(w)=\sum_{t\ge1}w^t(f_t(w)-P^{-1})
\]
is analytic on $|w|<r$ since $rq<1$. Separating the $t=0$ term and summing the geometric constant terms gives
\[
D(w)=P^4Q(w)^{-3}
\left((1+w)R(w)+\frac wP+(1-w)E(w)\right).
\tag{5.4}
\]
All factors on the right are analytic on a slightly smaller disc of radius greater than one.

The elementary identities
\[
T=\sum_{j\ge1}\frac{q^j}{(1-q^j)^2},\qquad
\sum_{j\ge1}\frac{q^{2j}}{(1-q^j)^2}=T-S
\]
follow by absolutely convergent double sums. Logarithmic differentiation yields
\[
Q(1)=P,\quad Q'(1)/Q(1)=-S,\quad
(\log Q)''(1)=-(T-S),
\]
\[
R(1)=P^{-1},\quad R'(1)=0,\quad R''(1)=-2T/P.
\]
Moreover
\[
f_t(1)=\frac1{P(1-q^t)},\qquad f_t'(1)=0.
\]
The derivative vanishes because the numerator's logarithmic derivative has a factor $2$, exactly cancelled by the squared denominator. Consequently
\[
E(1)=S/P,\qquad E'(1)=T/P.
\]
Write (5.4) as $A(w)B(w)$. At $w=1$,
\[
A=P,\quad A'=3PS,\quad
A''=P(9S^2+3T-3S),
\]
\[
B=3/P,\quad B'=(2-S)/P,\quad B''=-6T/P.
\]
The product rule gives (5.3), including
\[
D''=3(9S^2+3T-3S)+6S(2-S)-6T
=21S^2+3S+3T.
\]
The differentiation is justified by normal convergence on the indicated larger disc. $\square$

Taylor expansion through order three at $w=1$ now shows that $a_k$ is a cubic polynomial in $k$ plus an exponentially small error:
\[
a_k=3\binom{k+3}{3}-(2+8S)\binom{k+2}{2}
+\tfrac12D''(1)(k+1)-\tfrac16D'''(1)+O(\rho^{-k}).
\tag{5.5}
\]
With $c_k=(k+1)^2(k+2)/2$ and $t=k+1$, it follows that
\[
\frac{a_k}{c_k}=1-\frac{8S}{t}
+\frac{D''(1)}{t^2}+O_q(t^{-3}),
\]
\[
\boxed{
\log(a_k/c_k)=\frac{\alpha}{t}+\frac{\beta}{t^2}+O_q(t^{-3}),
\quad \alpha=-8S,\quad \beta=-11S^2+3S+3T.
}
\tag{5.6}
\]
Only the cubic polar part is needed for the algebraic expansion; Theorem 4.2 explains the role of all remaining coefficients.

# 6. The first correction to the fixed-q determinant asymptotic

Let
\[
C_N=\prod_{k<N}c_k=\frac{(N!)^2(N+1)!}{2^N},\qquad
\mathcal A(q)=\prod_{k\ge0}\left[
\frac{a_k}{c_k}\left(\frac{k+1}{k+2}\right)^{-8S}\right].
\tag{6.1}
\]
The product is positive and converges absolutely: the $1/(k+1)$ terms in its logarithm cancel. Put $K(q)=\mathcal A(q)\mathcal M(q)^3$.

**Theorem 6.1.** For each fixed $0<q<1$, the moments (5.1) satisfy
\[
\boxed{
V_N=K(q)C_Nq^{B_N}P^{2N}N^{-8S}
\left(1+\frac{11S^2-7S}{N}+O_q(N^{-2})\right),
\qquad S=F(1/q).
}
\tag{6.2}
\]

**Proof.** Summing (5.6) and using
$H_N=\log N+\gamma+1/(2N)+O(N^{-2})$ and
$\sum_{t\le N}t^{-2}=\zeta(2)-1/N+O(N^{-2})$ gives
\[
\prod_{k<N}a_k/c_k
=\mathcal A(q)N^{-8S}
\left(1+\frac{11S^2-7S-3T}{N}+O_q(N^{-2})\right).
\tag{6.3}
\]
The $O(t^{-3})$ tail contributes $O(N^{-2})$ to the logarithm. The constant is exactly (6.1), by telescoping.

The finite Vandermonde correction satisfies
\[
\prod_{d<N}(1-q^d)^{2(N-d)}
=P^{2N}\mathcal M(q)^2\bigl(1+O_q(Nq^N)\bigr).
\tag{6.4}
\]
This follows by taking logarithms and bounding the omitted convergent tails. Theorem 4.1 with $d=3$ supplies the remaining factor
\[
V_N/\mathcal G_N
=\mathcal M(q)\left(1+\frac{3T}{N}+O_q(N^{-2})\right).
\tag{6.5}
\]
The $-3T/N$ in (6.3) cancels the $+3T/N$ in (6.5). Multiplying (6.3)–(6.5) proves (6.2). $\square$

This cancellation has a specific explanation. The weighted Lambert series $T(q)$ enters the second polar coefficient of the atom generating function and also the expected size of a Schur partition. Those are distinct calculations. Their contributions cancel in the first correction of the fully normalised determinant, leaving a polynomial in the original Lambert value $S$.

The leading part of (6.2) was an R3 candidate, held outside the short note. This return supplies an exact Schur representation, a quantitative domination argument, an additional derivative and independent regression checks. It is therefore additional evidence and a strengthening, rather than another request to promote the unchanged R3 claim.

At $q=2/3$, (6.2) places $F(3/2)$ in an exponent and a correction coefficient. It does not force that number to be irrational. Rational approximation sequences can have rational power-law exponents; there is no contradiction without an additional arithmetic argument. The 2004 denominator divisor is not an input to (6.2).

## 6.1 Independent checks

The exact finite-support Schur identity was checked for 12 cases: $q=1/4,1/2,2/3$ and $N=1,2,3,4$, with distinct positive polynomial atom weights. Each comparison used exact rational determinants and exact alternants.

A separate numerical recurrence expanded the literal $G_q$ through coefficient 1050 at $q=1/4$. It did not insert the claimed polar coefficients. With $t=k+1$, the quantity $t^2(a_k/c_k-1+8S/t)$ approaches the prediction $D''(1)=6.597846319\ldots$; its values at $k=200,400,800,1000$ were approximately $6.55708,6.57736,6.58758,6.58963$.

For the partition sum, 18,460 partitions of size at most 28 were enumerated. A constant-free difference of the full normalised logarithms at $N$ and $2N$ tests the coefficient $11S^2-7S=-0.997127929\ldots$. At $N=80,160,320$, the estimates were $-0.9407433,-0.9690233,-0.9830982$. These floating-point tests have no certified rounding or infinite-tail bounds. They are regression checks, separate from the proofs.

# 7. What a concentrated modular fibre must look like

The supplied R5 quantitative criterion already says that enough selectors, modular signatures and short real bins yield a small nonzero remainder collision. What remains is an estimate on the actual primitive remainders. The following finite geometric observation narrows the possible shape of such concentration.

**Lemma 7.1 (a thin strip forces an affine line).** Let $\Gamma\subset\mathbb Z^2$ be a rank-two lattice of index $I>0$. Let $\mathcal X$ be a finite set in one affine coset of $\Gamma$. Suppose, for some real $\xi$, all first coordinates lie in an interval of length $W$ and all errors $A\xi-B$ lie in an interval of length $\delta$. If
\[
\boxed{2W\delta<I,}
\tag{7.1}
\]
then the points of $\mathcal X$ are collinear. If there are two distinct points, the line has a rational direction.

**Proof.** Fix any three points $x_0,x_1,x_2$. Their two difference vectors $u=x_1-x_0$, $v=x_2-x_0$ lie in $\Gamma$. Their first coordinates have absolute value at most $W$, and their errors have absolute value at most $\delta$. Since the shear $(A,B)\mapsto(A,A\xi-B)$ preserves absolute determinant,
\[
|\det(u,v)|\le |u_1|\,|v_1\xi-v_2|+
|v_1|\,|u_1\xi-u_2|\le2W\delta<I.
\]
The determinant is an integer multiple of $I$, so it is zero. If there are two distinct points, take them as the fixed pair to see that every other point lies on their line. Its direction is their integer difference. $\square$

The constant 2 is deliberately sufficient rather than optimal. A rectangle-area argument improves it to 1; that improvement is not needed here.

For a modular selector fibre in the original row lattice $\Lambda$, after subtraction of an anchor and division by $D$ the difference lattice is
\[
\Gamma_D=(\Lambda\cap D\mathbb Z^2)/D,
\qquad I_D=g/\gcd(g,D).
\]
If a bin has raw first-coordinate width $W$ and raw error width $D/n$, then its divided widths are $W/D$ and $1/n$. Thus
\[
2W/(Dn)<I_D
\]
forces its distinct selector points onto one rational line.

This does not forbid a successful collision. Several points on one rational line can have distinct, very close real errors. It says that a successful concentration argument in this regime must control occupancy along rational directions. General two-dimensional volume heuristics cannot stand in for that information. Exact multiplicity, conditional range, and line occupancy are different quantities.

The already-proved global-span obstruction for the narrow R4 family remains intact. Lemma 7.1 neither re-proves it nor excludes the wide family's endpoint. It identifies an additional structural feature to check in a candidate successful bin.

# 8. A countermodel showing why the scale hypothesis matters

The R4 narrow-family theorem excludes eventual bounded divided errors on a regular scale. It explicitly retains the possibility of a sufficiently sparse successful subsequence. The following separate elementary construction shows that the regularity cannot be deleted from a general precision-height obstruction.

Put $d_n=4^n$, $x=2/9$, and define the real and two-adic sums separately:
\[
\xi_\infty=\sum_{j\ge0}x^{4^j}\in\mathbb R,
\qquad
\xi_2=\sum_{j\ge0}x^{4^j}\in\mathbb Q_2.
\]
Both converge in their stated fields. Set
\[
Q_n=9^{d_n},\qquad
P_n=\sum_{j=0}^n2^{d_j}9^{d_n-d_j}.
\]
Then $0<P_n<Q_n$ and $\gcd(P_n,Q_n)=1$, since $P_n\equiv2^{d_n}\pmod3$.
The real remainder satisfies
\[
\boxed{
0<Q_n\xi_\infty-P_n
\le\frac97\left(\frac{16}{729}\right)^{d_n}\longrightarrow0.
}
\tag{8.1}
\]
Indeed the omitted exponents form a subset of the integers at least $4d_n$, so the real tail is at most $x^{4d_n}/(1-x)$; multiply by $Q_n$.

The two-adic omitted terms have strictly increasing valuations, giving exactly
\[
\boxed{v_2(Q_n\xi_2-P_n)=4d_n.}
\tag{8.2}
\]
Nevertheless the real coefficient height is only $Q_n=9^{d_n}$, whereas the two-adic precision is $2^{4d_n}=16^{d_n}$. There is a strict exponential precision-height gap alongside nonzero real errors tending to zero.

The adjacent determinant explains why no contradiction results:
\[
Q_{n+1}=Q_n^4,\qquad
P_{n+1}=P_nQ_n^3+2^{4d_n},
\]
\[
\boxed{P_{n+1}Q_n-P_nQ_{n+1}=Q_n2^{4d_n}\ne0.}
\tag{8.3}
\]
The next height is measured on scale $4d_n$, not $d_n+o(d_n)$. Its contribution prevents the integer determinant from becoming too small. The scale ratio is $d_{n+1}/d_n=4$.

This is a countermodel to omitting the regular-scale hypothesis, not a source family for $F(3/2)$. The series is a classical type of lacunary construction; no novelty is claimed for the construction itself. Its exact comparison with the R4 precision-height mechanism is the relevant use. It also shows why a sparse subsequence should be assessed with actual consecutive heights, rather than by reusing a theorem whose scale ratio tends to one.

# 9. Consequences for the paper and the next experiment

The live short note already has a coherent leading proof. The inexpensive addition is (2.4), following the power-family corollary. It quantitatively strengthens the exact same theorem and recovers the inherited integer-base bound at $b=1$. There is no need to retitle the note or place an unadjudicated Hankel strengthening in its abstract.

The final finite theorem should use the strongest already-landed selector statement. Its hypotheses must mention **conditional** exact multiplicity and real bin diameter. The subsequent inequality should involve the primitive remainder range, not the bounded unnormalised hypergeometric remainder. The supplied patch makes that replacement and links the existing finite wrapper at the unchanged public pin.

The additional geometric-moment results have a separate natural organisation: positive moments, exact Schur expansion, polar-part stability, universal first correction, then the Lambert specialisation. That is a potential companion argument whose general theorem can be used independently of the original benchmark. Its relationship to known Schur-measure and Hankel asymptotic work needs further bibliographical adjudication.

For the wide primitive source family, the unresolved sufficient input remains a conditional concentration estimate at the scale of $D_n/n$, with exact multiplicity controlled without assuming irrationality. Lemma 7.1 suggests recording the rational directions of large occupied bins as well as their widths. Section 8 shows that a deliberately sparse scale is a distinct route; it supplies no reason to assume such a scale works for the actual source.

A useful experiment would record, for one explicitly declared primitive source family and modulus, the actual image size, the distribution of conditional real spans, exact selector multiplicities, and affine ranks of occupied narrow bins. Certified real intervals are needed to distinguish near collisions from exact or numerically unresolved collisions. None of those data should be replaced by row counts or raw remainder bounds.

# 10. References and evidence

\begingroup\small

[Z04] W. Zudilin, *Heine's basic transform and a permutation group for q-harmonic series*, Acta Arithmetica 111 (2004), 153–164. Lemma 7, (23), supplies the polynomial inclusion; Section 5, (25)–(26), supplies the inherited constants and integer-base measure. DOI: 10.4064/aa111-2-4. Primary text: <https://www.impan.pl/shop/en/publication/transaction/download/product/82435>.

[Z16] W. Zudilin, *On the irrationality of generalized q-logarithm*, Research in Number Theory 2 (2016), arXiv:1601.02688v2. Sections 3–4 give the distinct normalised Hankel construction. Section 2 announces rational-base and quantitative extensions without computing the logarithmic constant there. <https://arxiv.org/html/1601.02688v2>.

[O00] A. Okounkov, *Infinite wedge and random partitions*, Selecta Mathematica 7 (2001), 57–81; arXiv:math/9907127v3 (2 February 2000). Section 2.1 defines the Schur measure and its Cauchy normalisation. The Schur formalism is antecedent mathematics, not a claimed invention here. <https://arxiv.org/html/math/9907127v3>.

[T] T. Tao, *Maximising the results-to-effort ratio*. The editorial use in this return is to extract the inexpensive quantitative corollary while keeping the more substantial, unadjudicated asymptotic argument separate. <https://terrytao.wordpress.com/advice-on-writing-papers/maximising-the-results-to-effort-ratio/>.

[Packet] R6 files `01_short_note.tex`, `04_r5_disposition.md`, `08_mandate.md`, and the supplied `Erdos1049` slice. Exact starting SHA-256 and patch-result SHA-256 are in `patches/manifest.json`. The public source pin is `32545d77c4b5cfd72ebd36c8dcd2418bf7cc4d31`; the live ZIP governs discrepancies.

[Prior] R3 fixed-q candidate and R4 primitive-family dossier, as identified in the supplied corpus. Their accepted and advisory parts are distinguished above. This return does not treat earlier assistant prose as an independent review receipt.

[Scope of search] The current announcement of Koizumi–Yokoi, arXiv:2608.26918, was located in RIKEN's publication list. Its full text was not available through the retrieval attempted here. Exact priority against that and other Hankel asymptotic work is therefore not certified. No claim of best-known status or novelty is made from search absence.

\endgroup
