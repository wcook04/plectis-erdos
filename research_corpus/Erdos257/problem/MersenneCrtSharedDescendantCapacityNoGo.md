# CRT compression of primitive-channel demand in the Mersenne divisor lattice

Let

\[
M_n=2^n-1.
\]

The notes
[`PrimitivePrimeBoundedWindowNoncancellation.md`](PrimitivePrimeBoundedWindowNoncancellation.md)
and
[`SylvesterJointChannelCountermodel.md`](SylvesterJointChannelCountermodel.md)
show, respectively, that primitive channels cannot cancel in a short multiplier window and that independent tail-denominator channels do not by themselves imply irrationality.  This note tests a different proposal: charge each primitive-channel demand to a later selected multiple in the index divisibility lattice.

That counting mechanism fails.  Two common descendants can cancel the complete primitive prime-power parts of arbitrarily many ancestors at once.  The construction works to every finite depth and uses the exact relation

\[
M_a\mid M_n\quad\Longleftrightarrow\quad a\mid n.
\]

## 1. Primitive parts and normalized residues

For \(a\ne6\), define the primitive part of \(M_a\) by

\[
P(a)=
\prod_{\substack{p\mid M_a\\ \operatorname{ord}_p(2)=a}}
p^{v_p(M_a)}.
\tag{1}
\]

Bang--Zsigmondy gives \(P(a)>1\).  If \(a\ne b\), then \(P(a)\) and \(P(b)\) are coprime, because a prime has only one multiplicative order.

Suppose \(n=ak\) and \(\gcd(k,P(a))=1\).  The factorization

\[
M_{ak}=M_a(1+2^a+\cdots+2^{a(k-1)})
\]

and the congruence \(2^a\equiv1\pmod{P(a)}\) give

\[
\frac{M_{ak}}{M_a}\equiv k\pmod{P(a)}.
\tag{2}
\]

For a finite support \(B\), define

\[
\rho_a(B)=
\sum_{\substack{n\in B\\a\mid n}}
(n/a)^{-1}\pmod{P(a)},
\tag{3}
\]

provided every multiplier \(n/a\) occurring in the sum is a unit modulo \(P(a)\).

### Lemma 1 (full primitive-part cancellation)

If \(\rho_a(B)=0\pmod{P(a)}\), then

\[
\sum_{n\in B}\frac1{M_n}
\]

is \(p\)-integral for every primitive prime \(p\mid M_a\).

### Proof

Fix such a prime, and write \(\mu=v_p(M_a)\).  If \(a\nmid n\), then \(p\nmid M_n\), so \(1/M_n\) is \(p\)-integral.  If \(n=ak\), then \(\gcd(k,p)=1\), LTE gives \(v_p(M_{ak})=\mu\), and (2) gives

\[
\frac{p^\mu}{M_{ak}}
\equiv
\left(\frac{M_a}{p^\mu}\right)^{-1}k^{-1}
\pmod{p^\mu}.
\]

The sum of the normalized residues therefore vanishes modulo \(p^\mu\).  The terms with indices divisible by \(a\) have \(p\)-integral sum, and so do the remaining terms.  ∎

This cancels the whole primitive prime power, not only its leading residue modulo \(p\).

## 2. Two shared descendants

We use one elementary fact about odd moduli.

### Lemma 2 (two-unit decomposition)

If \(Q\) is odd, then every residue \(t\pmod Q\) is a sum of two units modulo \(Q\).

### Proof

For every prime \(p\mid Q\), choose \(u_p\pmod p\) with

\[
u_p\ne0,
\qquad
u_p\ne t\pmod p.
\]

There is such a class because \(p\ge3\).  The Chinese remainder theorem gives \(u\pmod Q\) which reduces to \(u_p\) at every \(p\mid Q\).  Then both \(u\) and \(t-u\) are units modulo \(Q\).  ∎

Let \(B\) be a finite set of distinct positive integers, none equal to \(6\), and put \(L=\operatorname{lcm}(B)\).  Assume

\[
\gcd(L/a,P(a))=1
\qquad(a\in B).
\tag{4}
\]

Condition (4) implies that every existing multiplier \(n/a\), with \(a\mid n\) and \(n\in B\), is a unit modulo \(P(a)\), so all residues (3) are defined.

### Theorem 3 (shared-descendant cancellation)

Under (4), there are distinct integers \(k_1,k_2>1\) such that, for

\[
n_1=Lk_1,
\qquad
n_2=Lk_2,
\qquad
B'=B\cup\{n_1,n_2\},
\]

one has

\[
\rho_a(B')=0\pmod{P(a)}
\qquad(a\in B).
\tag{5}
\]

The integers \(k_1,k_2\) may additionally be chosen with

\[
1<\frac{k_2}{k_1}<2.
\tag{6}
\]

### Proof

Fix \(a\in B\), put \(d_a=L/a\), and let \(c_a=\rho_a(B)\).  By (4), \(d_a\) is a unit modulo \(P(a)\).  Lemma 2 supplies units \(u_a,v_a\pmod{P(a)}\) satisfying

\[
u_a+v_a\equiv-d_ac_a\pmod{P(a)}.
\tag{7}
\]

The moduli \(P(a)\), \(a\in B\), are pairwise coprime.  Apply the Chinese remainder theorem twice to choose unit residue classes \(r_1,r_2\) such that

\[
r_1^{-1}\equiv u_a,
\qquad
r_2^{-1}\equiv v_a
\pmod{P(a)}
\qquad(a\in B).
\tag{8}
\]

Let \(R=\prod_{a\in B}P(a)\).  Replacing \(r_1,r_2\) by sufficiently large positive representatives of their classes modulo \(R\), using adjacent translates if the two classes coincide, gives distinct \(k_1,k_2>1\) satisfying (6).

Both new indices are multiples of every \(a\in B\).  Their multipliers relative to \(a\) are \(d_ak_1\) and \(d_ak_2\), so (7)--(8) give

\[
\begin{aligned}
\rho_a(B')
&\equiv
c_a+(d_ak_1)^{-1}+(d_ak_2)^{-1}\\
&\equiv
c_a+d_a^{-1}(u_a+v_a)\\
&\equiv0
\pmod{P(a)}.
\end{aligned}
\]

This proves (5).  ∎

Thus two selected indices can discharge every primitive prime-power channel attached to every member of an arbitrarily large finite support \(B\).  There is no Hall-type lower bound assigning one future selected index to each existing channel or anchor.

## 3. Arbitrary-depth construction

The shared-descendant step can be iterated without losing its hypothesis.

Start with

\[
B_0=\{2,4,8,\ldots,2^r\}.
\tag{9}
\]

If \(L_0=2^r\), then \(L_0/a\) is a power of two for every \(a\in B_0\), while \(P(a)\) is odd.  Hence (4) holds.

Apply Theorem 3, choosing \(k_1<k_2<2k_1\), and set

\[
B_1=B_0\cup\{L_0k_1,L_0k_2\}.
\]

For each old \(a\in B_0\), the new least common multiple divided by \(a\) is still a unit modulo \(P(a)\), because both new multipliers are units.  For a new index \(n_i=L_0k_i\),

\[
\frac{\operatorname{lcm}(L_0k_1,L_0k_2)}{n_i}
\le k_{3-i}<2k_i\le L_0k_i=n_i.
\]

Every primitive prime divisor of \(M_{n_i}\) is larger than \(n_i\).  It therefore cannot divide the displayed quotient.  Condition (4) holds for \(B_1\).

Induction gives finite supports

\[
B_0\subset B_1\subset\cdots\subset B_h
\tag{10}
\]

such that \(B_{j+1}\setminus B_j\) has exactly two elements and

\[
\rho_a(B_{j+1})=0\pmod{P(a)}
\qquad(a\in B_j).
\tag{11}
\]

At the next step, equation (11) is preserved for all older anchors while the two current frontier indices are also cancelled.  Consequently, for every prescribed demand count \(r\) and depth \(h\), two new indices per level service all primitive channels below a frontier of size two.

Let \(X_h=\max B_h\).  The finite prefix can be embedded in the cofinite support

\[
A_h=B_h\cup\{n\in\mathbf N:n>X_h\}.
\tag{12}

Then \(A_h\) has natural density one and

\[
\sum_{n\in A_h}\frac1n=\infty,
\]

while every cancellation identity (11) remains exact at its stated cutoff.  Hence reciprocal divergence cannot repair any finite-depth demand-versus-counting-capacity inequality.

## 4. What the construction does and does not show

The construction is genuinely Mersenne-specific: it uses the order criterion for divisibility, the quotient congruence (2), the full primitive parts \(P(a)\), and common descendants in the index divisibility lattice.

It proves that raw descendant count is not a viable capacity.  The same two descendants can service arbitrarily many old channels, and this sharing persists through any prescribed finite number of generations.

It does **not** produce a rational Mersenne reciprocal sum.  The cofinite extension in (12) preserves finite cancellation certificates but may reopen channels after \(X_h\), and the infinite sparse iteration of (10) has no proved rational value.  A global irrationality argument may still exist, but it must charge something that the CRT construction consumes.

The construction identifies the only place where such a resource could enter.  If

\[
R_B=\prod_{a\in B}P(a),
\]

then the two service multipliers are selected modulo \(R_B\).  CRT supplies representatives below \(R_B\), and the proof may enlarge them by multiples of \(R_B\).  Their logarithmic height can therefore be of order

\[
\log R_B=\sum_{a\in B}\log P(a).
\]

The present argument does not prove that this height is necessary; special residue vectors may have much smaller solutions.  A viable all-depth theorem would need a lower bound for every service solution and then compare it with an independent Archimedean restriction on how far common descendants may lie.  Reciprocal divergence alone supplies no such restriction: it is compatible with the cofinite tail (12).

This is the exact failure of the proposed capacity mechanism.  It does not rule out a height-sensitive argument, but it rules out any proof that treats later selected indices as one-use service units.
