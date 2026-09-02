# A single common descendant can remove every natural primitive factor of a rational tail

Let

\[
M_n=2^n-1.
\]

The primitive-channel argument for a hypothetical rational Boolean Mersenne
subseries produces prime powers in the reduced denominators of its tails. This
note determines exactly how such a prime power changes when one selected term
is removed. It then applies the Chinese remainder theorem to all natural
primitive factors simultaneously.

The result is an exclusion. A single common descendant can remove arbitrarily
many natural primitive factors from a rational tail denominator, and the
descendant can be placed arbitrarily far out. Its reciprocal can therefore be
smaller than any prescribed positive real budget. Consequently, positivity
does not impose an upper service height for primitive channels.

The arguments below are deductions in elementary rational arithmetic. The
accompanying script checks the displayed transition law and several exact CRT
instances. No rational infinite Boolean Mersenne subseries is constructed.

## 1. Exact transition of a reduced denominator

Let

\[
x=\frac uq>0,
\qquad
\gcd(u,q)=1,
\]

and suppose that \(M>0\) satisfies \(1/M<x\). Write

\[
y=x-\frac1M=\frac{uM-q}{qM}>0.
\]

For a prime \(p\), put

\[
\alpha=v_p(q),
\qquad
\beta=v_p(M),
\qquad
\gamma=v_p(\operatorname{den}(y)),
\]

where the denominator of \(y\) is reduced.

### Proposition 1 (one-step denominator law)

Suppose that \(\alpha>0\). If \(\alpha\ne\beta\), then

\[
\gamma=\max\{\alpha,\beta\}.
\tag{1}
\]

If \(\alpha=\beta\), write \(q=p^\alpha q_0\) and
\(M=p^\alpha M_0\). Then

\[
\gamma=
\max\bigl\{0,\alpha-v_p(uM_0-q_0)\bigr\}.
\tag{2}
\]

In particular, the \(p\)-part of the reduced denominator can decrease only if

\[
v_p(M)=v_p(q)
\quad\text{and}\quad
u\frac{M}{p^\alpha}
\equiv
\frac{q}{p^\alpha}
\pmod p.
\tag{3}
\]

It disappears completely if and only if the congruence in (3) holds modulo
\(p^\alpha\).

### Proof

Since \(\alpha>0\) and \(\gcd(u,q)=1\), the integer \(u\) is a
\(p\)-adic unit. If \(\beta<\alpha\), then

\[
v_p(uM-q)=\beta.
\]

If \(\beta>\alpha\), then \(v_p(uM-q)=\alpha\). Reduction of the
fraction \((uM-q)/(qM)\) gives (1) in both cases.

If \(\alpha=\beta\), then

\[
uM-q=p^\alpha(uM_0-q_0).
\]

The denominator \(qM\) has \(p\)-adic valuation \(2\alpha\), which
gives (2). The last two assertions follow immediately. \(\square\)

Thus subtraction by a denominator having too little or too much \(p\)-adic
height cannot reduce the old \(p\)-part. Exact height matching is necessary.

## 2. Primitive Mersenne channels

Fix \(a\ge2\), \(a\ne6\), and let \(p\) be a primitive prime divisor of
\(M_a\). Put

\[
\mu=v_p(M_a).
\]

Primitivity and LTE give, for \(n=ak\),

\[
v_p(M_n)=\mu+v_p(k),
\tag{4}
\]

whereas \(v_p(M_n)=0\) when \(a\nmid n\). Proposition 1 therefore has
the following consequence.

### Corollary 2 (exact service layer)

Suppose that \(v_p(q)=\mu+e\), where \(e\ge0\). Subtracting
\(1/M_n\) can decrease the \(p\)-part of the denominator of \(x\) only if

\[
n=ak
\quad\text{and}\quad
v_p(k)=e.
\tag{5}
\]

In particular, a non-descendant of \(a\) preserves the old \(p\)-part
exactly.

This is the reduced-denominator form of the maximal-layer condition in the
finite primitive-channel calculation. It does not imply that a service term
must occur.

## 3. Simultaneous removal by one common descendant

For \(a\ne6\), define the natural primitive part

\[
P(a)=
\prod_{\substack{p\mid M_a\\ \operatorname{ord}_p(2)=a}}
p^{v_p(M_a)}.
\tag{6}
\]

The integers \(P(a)\) are pairwise coprime as \(a\) varies. Let \(B\)
be a finite set of integers at least \(2\), none equal to \(6\), and put

\[
L=\operatorname{lcm}(B),
\qquad
R=\prod_{a\in B}P(a).
\tag{7}
\]

Assume that

\[
\gcd(L/a,P(a))=1
\qquad(a\in B).
\tag{8}
\]

Let \(x=u/q>0\) be reduced, and suppose that the \(R\)-part of \(q\) is
exactly \(R\):

\[
R\mid q,
\qquad
\gcd(q/R,R)=1.
\tag{9}
\]

### Theorem 3 (cofinal one-descendant service)

There is a unit residue class \(k_0\pmod R\) such that, for every sufficiently
large positive integer \(k\equiv k_0\pmod R\), the integer \(n=Lk\)
satisfies

\[
0<\frac1{M_n}<x
\tag{10}
\]

and the reduced denominator of

\[
x-\frac1{M_n}
\]

is coprime to \(R\).

More strongly, for every \(\varepsilon>0\) and every \(H>0\), \(k\) may be
chosen so that

\[
n>H,
\qquad
\frac1{M_n}<\varepsilon.
\tag{11}
\]

### Proof

Fix \(a\in B\) and a primitive prime-power factor
\(p^\mu\mathrel{\Vert}P(a)\). Write

\[
d_a=L/a,
\qquad
q=p^\mu q_p,
\qquad
M_a=p^\mu W_{a,p}.
\]

Every factor in

\[
t_{a,p}
\equiv
d_a^{-1}u^{-1}q_pW_{a,p}^{-1}
\pmod{p^\mu}
\tag{12}
\]

is a unit modulo \(p\). The prime powers occurring in \(R\) are pairwise
coprime, so the Chinese remainder theorem gives one unit class
\(k_0\pmod R\) satisfying

\[
k_0\equiv t_{a,p}\pmod{p^\mu}
\tag{13}
\]

for every \(a\in B\) and every primitive
\(p^\mu\mathrel{\Vert}P(a)\).

Take \(k\equiv k_0\pmod R\) and put \(n=Lk\). The multiplier of \(a\)
in \(n\) is \(d_ak\), a \(p\)-adic unit. Hence

\[
v_p(M_n)=v_p(M_a)=\mu.
\tag{14}
\]

Moreover,

\[
\frac{M_n}{M_a}
=1+2^a+\cdots+2^{a(d_ak-1)}
\equiv d_ak\pmod{p^\mu},
\tag{15}
\]

because \(2^a\equiv1\pmod{p^\mu}\). Equations (12)--(15) give

\[
u\frac{M_n}{p^\mu}
\equiv
uW_{a,p}d_ak
\equiv q_p
=\frac q{p^\mu}
\pmod{p^\mu}.
\tag{16}
\]

Proposition 1 shows that \(p\) does not divide the reduced denominator after
the subtraction. This holds for every prime-power factor in \(R\), proving the
coprimality assertion.

The positive representatives of one residue class modulo \(R\) are
unbounded. Since \(M_{Lk}=2^{Lk}-1\to\infty\) along these representatives,
we may impose (10) and (11) simultaneously. \(\square\)

The hypothesis permits arbitrarily large anchor families. For
\(B=\{2,4,\ldots,2^r\}\), the quotient \(L/a\) is a power of \(2\),
whereas every \(P(a)\) is odd, so (8) holds.

For example, take \(B=\{2,4,8\}\). Then

\[
L=8,
\qquad
R=P(2)P(4)P(8)=3\cdot5\cdot17=255.
\]

For \(x=1/255\), equations (12)--(13) give \(k\equiv1\pmod{255}\).
Every \(k=1+255t\) with \(t\ge1\) gives

\[
\gcd\left(
\operatorname{den}\left(\frac1{255}-\frac1{M_{8k}}\right),
255
\right)=1.
\]

The first representative \(k=1\) would exhaust the tail exactly. All later
representatives give positive remainders, and their reciprocals tend to zero.

## 4. The direction of the Archimedean inequality

Suppose that \(x=u/q\) is the complete positive tail at some cutoff and that
\(n\) is its next selected exponent. Positivity gives

\[
\frac1{M_n}<\frac uq,
\qquad\text{hence}\qquad
M_n>\frac qu.
\tag{17}
\]

Thus the real tail imposes a lower bound on the next denominator. It does not
give an upper bound on \(n\). Theorem 3 shows that the simultaneous service
class contains arbitrarily large \(n\), so (17) and the CRT congruences are
compatible. In fact the service cost \(1/M_n\) has infimum zero within that
one class.

This rules out an argument of the following form: rational-tail integrality
forces old primitive channels to be serviced, the required common descendant
is too late, and positivity makes such a late service term unaffordable. A
later Mersenne reciprocal is cheaper, not more expensive.

The theorem does not show that a hypothetical rational support selects the
service class. It proves that denominator cancellation, if demanded, has no
finite Archimedean deadline.

## 5. Persistence is also compatible with the transition law

The opposite behavior does not give a contradiction either.

For the Sylvester unit-fraction series, the \(N\)-th tail is

\[
\tau_N=\frac1{P_N},
\qquad
P_N=\prod_{j\le N}q_j,
\]

and the next denominator \(q_{N+1}\) is coprime to \(P_N\). Proposition 1
with \(\beta=0<\alpha\) shows that every old prime-power exponent in the
reduced tail denominator persists. This agrees with the exact identity
\(\tau_{N+1}=1/P_{N+1}\). Hence positivity, rationality, exact cross-cutoff
recurrences, and arbitrarily small real tails do not force service in a
general unit-fraction series.

There is a Mersenne-specific conditional version. If the support consists of
prime exponents and its Mersenne subseries were rational, then no later
selected exponent is a multiple of an earlier prime exponent \(a\). Corollary
2 would preserve every primitive \(p\mid M_a\), apart from the finitely many
primes already occurring in the denominator of the total value, through all
later rational tails. This is consistent with the elementary upper bound by
the prefix common denominator: each persistent prime already occurs in the
anchor denominator \(M_a\).

The two tests leave no denominator-only dichotomy. A channel may persist
forever without violating real convergence. For every family satisfying
(8)--(9), all of its natural primitive channels may instead be removed by one
arbitrarily late common descendant. Any contradiction must use additional
information coupling the actual Boolean support across infinitely many
cutoffs. Reduced-denominator integrality and Archimedean affordability do not
supply that coupling.
