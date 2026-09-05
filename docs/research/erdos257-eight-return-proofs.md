# Retained analytic proofs from the September 2026 Erdős 257 batch

These are ordinary mathematical proofs reviewed during batch assimilation.
They are not Lean-checked theorems. The mathematical statements, proof bodies,
and examples below were mechanically extracted from the four distinct analytic
returns; their original digests and admission reviews are bound in
[the audit and provenance record](erdos257-eight-return-audit.json).
The campaign's stronger compositions, repaired boundaries, and countermodels
are in [the synthesis](erdos257-eight-return-synthesis.md).

The prose retains the originating proof notation. Source-local theorem numbers
restart in each part. First-person statements about what a return has proved
are historical attribution, not a second proof authority. No external peer
review or theorem-priority claim is implied.

For the prime-power part, the imported analytic theorem is Tao–Teräväinen,
[arXiv:2512.01739v2, Theorem 3.1](https://arxiv.org/html/2512.01739v2#S3.Thmtheorem1).
Its equidistributed case, small-prime condition, progression uniformity and
exceptional logarithmic measure were checked against the primary text.
The full-prime theorem and the authors' stated full-prime-power extension remain
their results; arbitrary thinning is the returned extension reviewed here.

---

# Part r1: Divisibility-weighted irrationality

Write

$$
S_b(A)=\sum_{a\in A}\frac1{b^a-1},
\qquad b\in\mathbb N,\quad b\ge2,
$$

where \(A\subseteq\mathbb N_{>0}\). The imported premise proves irrationality when \(A\) is infinite and \(\sum_{a\in A}1/a<\infty\). The result proved here replaces that hypothesis by an explicit, strictly weaker weighted condition. 

### Theorem 1 — Divisibility-weighted irrationality

Let \(\mathcal P\) be a finite nonempty set of primes. Define the \(\mathcal P\)-part of an integer \(a\ge1\) by

$$
h(a)=\prod_{p\in\mathcal P}p^{v_p(a)}.
$$

Thus \(h(a)\mid a\), and \(a/h(a)\) is coprime to every prime in \(\mathcal P\).

For an integer \(b\ge2\), put

$$
W_{b,\mathcal P}(A)
=
\sum_{a\in A}
\frac{h(a)}{a\bigl(b^{h(a)}-1\bigr)}.
\tag{1}
$$

If \(A\) is infinite and

$$
W_{b,\mathcal P}(A)<\infty,
\tag{2}
$$

then

$$
\boxed{S_b(A)\notin\mathbb Q.}
\tag{3}
$$

More precisely, define

$$
\Delta_{b,A}(m)
=
\sum_{a\in A}
\frac{b^{\,m\bmod a}-1}{b^a-1}.
\tag{4}
$$

Under (2), for every \(\varepsilon>0\) and every \(N\), there is an integer \(m\ge\max\{N,1\}\) such that

$$
0<\Delta_{b,A}(m)<\varepsilon.
\tag{5}
$$

In particular, taking \(\mathcal P=\{2\}\), the condition is

$$
\boxed{
\sum_{a\in A}
\frac{2^{v_2(a)}}{a\bigl(2^{\,2^{v_2(a)}}-1\bigr)}
<\infty.
}
\tag{6}
$$

Condition (6) implies irrationality of \(S_b(A)\) at **every integer base \(b\ge2\)**.

The shifted-atom and GCD-orbit identities used below belong to the imported framework in `ReciprocalSupportIrrationality.lean`. The new step is the finite averaging over observation lengths, followed by the divisibility decomposition that proves (5) under (2).

---

## 1. The exact integer obstruction

For \(a,m\ge1\), write

$$
m=ka+r,\qquad 0\le r<a.
$$

Then

$$
\frac{b^m-1}{b^a-1}
-
\frac{b^r-1}{b^a-1}
=
\sum_{j=1}^{k}b^{m-ja}.
$$

Summing over \(a\in A\) gives

$$
\boxed{
\Delta_{b,A}(m)
=
(b^m-1)S_b(A)-J_{b,A}(m),
}
\tag{7}
$$

where

$$
J_{b,A}(m)
=
\sum_{\substack{a\in A\\a\le m}}
\ \sum_{j=1}^{\lfloor m/a\rfloor}b^{m-ja}
\in\mathbb Z.
\tag{8}
$$

There is no infinite integer sum in (8). Only \(a\le m\) contribute.

The series in (4) converges for every fixed \(m\), since its summands are nonnegative and at most

$$
\frac{b^m}{b^a-1}.
$$

Moreover, if \(A\) is infinite, some \(a\in A\) satisfies \(a>m\). Its contribution to (4) is strictly positive. Hence

$$
\Delta_{b,A}(m)>0
\qquad(m\ge1).
\tag{9}
$$

Suppose now that \(S_b(A)=u/v\), where \(v>0\). Equation (7) implies

$$
v\Delta_{b,A}(m)\in\mathbb Z.
$$

Together with (9), this gives the uniform separation

$$
\boxed{\Delta_{b,A}(m)\ge\frac1v\qquad(m\ge1).}
\tag{10}
$$

Thus proving (5) proves irrationality. Everything that follows is directed at producing those small positive displacements.

---

## 2. Two finite estimates

For convenience, write

$$
\phi_a(m)=\frac{b^{\,m\bmod a}}{b^a-1},
\qquad
d_a(m)=\phi_a(m)-\frac1{b^a-1}.
$$

Then \(d_a(m)\ge0\) and

$$
\Delta_{b,A}(m)=\sum_{a\in A}d_a(m).
$$

### Lemma 2 — Finite GCD-orbit estimate

Let \(Q,a,T\ge1\), and put \(g=\gcd(Q,a)\). Then

$$
\frac1T\sum_{t=1}^{T}d_a(tQ)
\le
\frac{g}{a(b^g-1)}
+
\frac1{T(b^g-1)}.
\tag{11}
$$

**Proof.** The sequence \(tQ\bmod a\) has period \(a/g\), and one period visits

$$
0,g,2g,\ldots,a-g
$$

exactly once. Consequently,

$$
\sum_{t=1}^{a/g}\phi_a(tQ)
=
\frac{1+b^g+\cdots+b^{a-g}}{b^a-1}
=
\frac1{b^g-1}.
\tag{12}
$$

Split \(1,\ldots,T\) into complete periods and one incomplete period. Positivity bounds the incomplete period by another complete period:

$$
\sum_{t=1}^{T}\phi_a(tQ)
\le
\left(\frac{Tg}{a}+1\right)\frac1{b^g-1}.
$$

Subtracting the nonnegative constant contribution \(T/(b^a-1)\) proves (11). \(\square\)

We shall use the elementary monotonicity

$$
n\longmapsto \frac{n}{b^n-1}
\quad\text{is decreasing on }\mathbb N_{>0}.
\tag{13}
$$

Indeed,

$$
n(b^{n+1}-1)-(n+1)(b^n-1)
=
b^n\bigl(n(b-1)-1\bigr)+1>0.
$$

### Lemma 3 — The outer tail costs at most \(4/T\)

For \(Y=QT\),

$$
\frac1T\sum_{t=1}^{T}
\sum_{\substack{a\in A\\a>Y}}d_a(tQ)
\le \frac4T.
\tag{14}
$$

**Proof.** If \(a>Y\ge tQ\), then \(tQ\bmod a=tQ\). Since \(b\ge2\),

$$
d_a(tQ)
\le \frac{b^{tQ}}{b^a-1}
\le 2\,2^{tQ-a}.
$$

Therefore

$$
\sum_{a>Y}d_a(tQ)\le 2\,2^{tQ-Y}.
$$

Also,

$$
\sum_{t=1}^{T}2^{tQ-Y}
=
\sum_{j=0}^{T-1}2^{-jQ}
\le2.
$$

Division by \(T\) proves (14). \(\square\)

---

## 3. Averaging over observation lengths

The incomplete-period term in (11) cannot simply be discarded when ordinary reciprocal mass diverges. The following finite identity controls it.

### Lemma 4 — Weighted averaging over dyadic observation lengths

Let \(\alpha_a\ge0\), and suppose

$$
\sum_{a\ge1}\frac{\alpha_a}{a}<\infty.
$$

For integers \(Q,M\ge1\),

$$
\boxed{
\sum_{j=M}^{2M-1}
\frac1{2^j}
\sum_{a\le Q2^j}\alpha_a
\le
2Q\sum_{a\ge1}\frac{\alpha_a}{a}.
}
\tag{15}
$$

**Proof.** For a fixed \(a\), the admissible \(j\)'s satisfy \(2^j\ge a/Q\). Their geometric sum obeys

$$
\sum_{\substack{M\le j<2M\\a\le Q2^j}}2^{-j}
\le \frac{2Q}{a}.
\tag{16}
$$

Multiply by \(\alpha_a\) and sum over \(a\).

The left side involves only finitely many \(j\) and integers \(a\le Q2^{2M-1}\), so its rearrangement is finite. The convergent series on the right is merely an upper bound. \(\square\)

This lemma provides \(M\) possible observation lengths,

$$
2^M,2^{M+1},\ldots,2^{2M-1},
$$

without paying \(M\) times the incomplete-period error.

---

## 4. Proof of Theorem 1

Fix \(b,\mathcal P,A\) as in the theorem, and abbreviate

$$
W=W_{b,\mathcal P}(A)<\infty.
$$

Let \(\varepsilon>0\). Choose a finite \(F\subseteq A\) such that

$$
\sum_{a\in A\setminus F}
\frac{h(a)}{a(b^{h(a)}-1)}
<\varepsilon.
\tag{17}
$$

Set

$$
L=\operatorname{lcm}(F),
$$

with \(L=1\) when \(F=\varnothing\).

The finite set \(F\), and hence \(L\), are fixed for the remainder of the argument.

Put

$$
p_*=\max\mathcal P,\qquad r=|\mathcal P|.
$$

For a large integer \(H\), define

$$
Q_0(H)=
\prod_{p\in\mathcal P}p^{\lfloor\log_p H\rfloor},
\qquad
Q=LQ_0(H),
\qquad
G=\left\lfloor\frac{H}{p_*}\right\rfloor.
\tag{18}
$$

We take \(H\ge2p_*\), so \(G\ge1\). Notice that

$$
Q\le LH^r.
\tag{19}
$$

Every atom indexed by \(F\) is frozen:

$$
a\in F\implies a\mid Q\implies d_a(tQ)=0.
\tag{20}
$$

The remaining atoms separate into two classes.

### 4.1. Small \(\mathcal P\)-part

If \(h(a)\le H\), every prime-power component of \(h(a)\) is at most \(H\). Thus

$$
h(a)\mid Q_0(H),
\qquad
\gcd(Q,a)\ge h(a).
$$

By (11) and (13),

$$
\frac1T\sum_{t=1}^{T}d_a(tQ)
\le
\frac{h(a)}{a(b^{h(a)}-1)}
+
\frac1{T(b^{h(a)}-1)}.
\tag{21}
$$

Consequently, the contribution of \(a\in A\setminus F\) with
\(a\le QT\) and \(h(a)\le H\) is at most

$$
\varepsilon+
\frac1T
\sum_{\substack{a\in A\\a\le QT\\h(a)\le H}}
\frac1{b^{h(a)}-1}.
\tag{22}
$$

The first term has already been paid for by (17). The second will be paid for by Lemma 4.

### 4.2. Large \(\mathcal P\)-part

If \(h(a)>H\), then

$$
\gcd(Q,a)\ge G.
\tag{23}
$$

To verify this, first suppose every prime-power component of \(h(a)\) is at most \(H\). Then \(h(a)\mid Q_0(H)\), so the GCD is greater than \(H\).

Otherwise some \(p^{v_p(a)}>H\). The GCD contains

$$
p^{\lfloor\log_p H\rfloor}>\frac Hp\ge\frac H{p_*},
$$

which again proves (23).

Therefore (11) and (13) give, for these atoms,

$$
\frac1T\sum_{t=1}^{T}d_a(tQ)
\le
\frac{G}{a(b^G-1)}
+
\frac1{T(b^G-1)}.
$$

Summing over \(a\le QT\), and enlarging to all positive integers in that range, bounds the large-part contribution by

$$
\frac{G(1+\log(QT))+Q}{b^G-1}.
\tag{24}
$$

Here we used

$$
\sum_{a\le QT}\frac1a\le1+\log(QT),
\qquad
\frac{\#\{a\le QT\}}T=Q.
$$

### 4.3. Combining the estimates

Define the finite average

$$
\mathcal A(Q,T)
=
\frac1T\sum_{t=1}^{T}\Delta_{b,A}(tQ).
$$

Equations (14), (22), and (24) yield

$$
\begin{aligned}
\mathcal A(Q,T)
\le {}&
\varepsilon+
\frac1T
\sum_{\substack{a\in A\\a\le QT\\h(a)\le H}}
\frac1{b^{h(a)}-1}\\
&+
\frac{G(1+\log(QT))+Q}{b^G-1}
+\frac4T.
\end{aligned}
\tag{25}
$$

Now set

$$
M=\left\lfloor b^{G/2}\right\rfloor
\tag{26}
$$

and average (25) over \(T=2^j\), where \(M\le j<2M\).

Apply Lemma 4 with

$$
\alpha_a=
\frac{\mathbf1_A(a)}{b^{h(a)}-1}.
$$

Its required summability follows from

$$
\sum_a\frac{\alpha_a}{a}
=
\sum_{a\in A}\frac1{a(b^{h(a)}-1)}
\le W.
\tag{27}
$$

We obtain the decisive finite bound

$$
\boxed{
\begin{aligned}
\frac1M\sum_{j=M}^{2M-1}\mathcal A(Q,2^j)
\le {}&
\varepsilon+\frac{2QW}{M}\\
&+
\frac{G(1+\log Q+2M\log2)+Q}{b^G-1}
+4\,2^{-M}.
\end{aligned}
}
\tag{28}
$$

Every term following \(\varepsilon\) tends to zero as \(H\to\infty\). Indeed,

$$
Q\le LH^r,\qquad
G=\frac{H}{p_*}+O(1),\qquad
M\asymp b^{G/2}.
$$

Hence

$$
\frac QM\to0,\qquad
\frac{GM}{b^G}\to0,\qquad
\frac{G\log Q+Q}{b^G}\to0,
\qquad
2^{-M}\to0.
\tag{29}
$$

Thus, for sufficiently large \(H\),

$$
\frac1M\sum_{j=M}^{2M-1}\mathcal A(Q,2^j)<2\varepsilon.
$$

This is a finite convex average of the numbers
\(\Delta_{b,A}(tQ)\). At least one of them is less than \(2\varepsilon\).

All of them are strictly positive by (9). Moreover,

$$
m=tQ\ge Q\longrightarrow\infty,
$$

because \(\mathcal P\ne\varnothing\). Since \(\varepsilon\) was arbitrary, this proves (5), including its cofinal quantifier.

Finally, (5) contradicts the rational separation (10). Therefore \(S_b(A)\) is irrational. \(\square\)

---

## 5. Immediate consequences

### Corollary 5 — Stability under reciprocal-summable additions

Suppose \(C\subseteq\mathbb N_{>0}\) satisfies

$$
W_{b,\mathcal P}(C)<\infty,
$$

and \(E\subseteq\mathbb N_{>0}\) satisfies

$$
\sum_{a\in E}\frac1a<\infty.
$$

Then every infinite subset \(A\subseteq C\cup E\) has irrational \(S_b(A)\).

**Proof.** Since \(b^h-1\ge h\),

$$
\frac{h}{a(b^h-1)}\le\frac1a.
$$

Therefore

$$
W_{b,\mathcal P}(A)
\le
W_{b,\mathcal P}(C)+\sum_{a\in E}\frac1a<\infty.
$$

Apply Theorem 1. \(\square\)

In particular, a condition imposed only at base two gives the conclusion at every larger integer base, because

$$
W_{b,\mathcal P}(A)\le W_{2,\mathcal P}(A)
\qquad(b\ge2).
$$

This proves irrationality for the union itself and all its infinite subsets. It does not infer irrationality by adding two separately irrational numbers.

### Corollary 6 — Nested divisibility filtrations

Let

$$
1=d_0\mid d_1\mid d_2\mid\cdots
$$

be strictly increasing, and define

$$
h_{\mathcal D}(a)=\max\{d_j:d_j\mid a\}.
$$

If \(A\) is infinite and

$$
\sum_{a\in A}
\frac{h_{\mathcal D}(a)}
     {a(b^{h_{\mathcal D}(a)}-1)}
<\infty,
\tag{30}
$$

then \(S_b(A)\) is irrational.

**Proof.** In the preceding proof take

$$
H=d_K,\qquad Q_0(H)=H,\qquad G=H.
$$

If \(h_{\mathcal D}(a)\le H\), it divides \(H\). If
\(h_{\mathcal D}(a)>H\), then \(H\mid h_{\mathcal D}(a)\mid a\).
Thus both GCD estimates hold, while \(Q=LH\). All subsequent estimates, including (28), apply unchanged. \(\square\)

---

## 6. A reciprocal-divergent family with short gaps

The new hypothesis genuinely reaches beyond ordinary reciprocal summability.

For \(k\ge0\), define the integer

$$
B_k=2^{\,2^{\,2^k-k}},
\tag{31}
$$

and let

$$
A^\star
=
\{a\ge1:a\le B_{v_2(a)}\}.
\tag{32}
$$

Then:

$$
\sum_{a\in A^\star}\frac1a=\infty,
\qquad
W_{2,\{2\}}(A^\star)<\infty,
\tag{33}
$$

and the consecutive elements \(a_1<a_2<\cdots\) satisfy

$$
a_{j+1}-a_j=O(\log\log a_j).
\tag{34}
$$

Consequently, **every infinite subset of \(A^\star\)** has irrational Mersenne reciprocal sum, at every integer base.

### Weighted summability

Put \(h=2^k\). The \(k\)-th valuation layer contributes

$$
\begin{aligned}
\sum_{\substack{a\le B_k\\v_2(a)=k}}
\frac{2^k}{a(2^{2^k}-1)}
&=
\frac1{2^h-1}
\sum_{\substack{u\le B_k/h\\u\ \mathrm{odd}}}\frac1u\\
&\le
\frac{1+\log B_k}{2^h-1}.
\end{aligned}
\tag{35}
$$

But

$$
\log B_k=(\log2)\,2^{2^k-k},
$$

so

$$
\frac{1+\log B_k}{2^{2^k}-1}
\le
2^{1-2^k}+2(\log2)\,2^{-k}.
\tag{36}
$$

The right side is summable over \(k\).

### Ordinary reciprocal divergence

For \(U\ge2\),

$$
\sum_{\substack{u\le U\\u\ \mathrm{odd}}}\frac1u
\ge \frac12\log(U/2).
$$

For sufficiently large \(k\), this gives

$$
\begin{aligned}
\sum_{\substack{a\le B_k\\v_2(a)=k}}\frac1a
&\ge
\frac{\log B_k-\log(4\cdot2^k)}{2^{k+1}}\\
&=
\frac{\log2}{2^{k+1}}
\left(2^{2^k-k}-k-2\right).
\end{aligned}
\tag{37}
$$

The last expression tends to infinity. In particular, the total reciprocal mass diverges.

### Short gaps

Let \(x\) be large, and choose the least \(k\) such that \(B_k\ge2x\). Then

$$
B_{k-1}<2x.
$$

For \(k\ge4\),

$$
2^{k-2}
\le
2^{k-1}-(k-1)
=
\log_2\log_2 B_{k-1}
<
\log_2\log_2(2x).
\tag{38}
$$

Thus

$$
2^{k+1}<8\log_2\log_2(2x).
\tag{39}
$$

There is an integer

$$
a\equiv2^k\pmod{2^{k+1}}
$$

in \((x,x+2^{k+1}]\). For large \(x\), (39) ensures \(a\le2x\le B_k\). Since \(v_2(a)=k\), this integer belongs to \(A^\star\), proving (34).

Every fixed valuation layer is finite. Therefore, beyond a finite initial segment, all elements of \(A^\star\) are divisible by \(2^K\), for every fixed \(K\). Its natural density is consequently zero. Together with infinitude, this also rules out eventual periodicity.

### Comparison with the supplied large-gap criterion

The corpus separately proves an explicit LCM-height escape criterion:

$$
\liminf_{j\to\infty}
\mathcal D_j\,2^{2-a_{j+1}}=0,
\qquad
\mathcal D_j=
\operatorname{lcm}_{i\le j}(2^{a_i}-1).
\tag{40}
$$

Its burst-and-escape example has very large gaps between successive blocks.

For \(A^\star\), the expression in (40) instead tends to infinity. Indeed,

$$
\mathcal D_j
\ge
\frac{(2^{a_{j-1}}-1)(2^{a_j}-1)}
     {2^{\gcd(a_{j-1},a_j)}-1},
$$

and

$$
\gcd(a_{j-1},a_j)
\le a_j-a_{j-1}
=O(\log\log a_j).
$$

Using (34),

$$
\log_2\!\left(\mathcal D_j2^{2-a_{j+1}}\right)
\ge a_j-O(\log\log a_j)\longrightarrow\infty.
\tag{41}
$$

Thus the explicit unreduced-LCM escape criterion does not explain this example. Equation (41) does not, by itself, make a claim about stronger estimates using the *reduced* denominator.

---

## 7. Why the order of averaging matters

There is a useful exact boundary to the argument.

### Proposition 7

If

$$
\sum_{a\in A}\frac1a=\infty,
$$

then for every fixed positive integer \(Q\),

$$
\frac1T\sum_{t=1}^{T}\Delta_{b,A}(tQ)
\longrightarrow+\infty
\qquad(T\to\infty).
\tag{42}
$$

**Proof.** For each fixed \(a\), its shifted-atom mean is

$$
\frac{\gcd(Q,a)}
     {a(b^{\gcd(Q,a)}-1)}
\ge
\frac1{a(b^Q-1)}.
\tag{43}
$$

Hence the sum of the individual means over \(a\in A\) diverges.

Given any desired lower bound, choose a finite subset of \(A\) whose sum of means exceeds that bound plus \(S_b(A)\). Its finite orbit average converges to that sum of means. The remaining shifted atoms are nonnegative. Subtracting the fixed baseline \(S_b(A)\) proves (42). \(\square\)

In particular, the proof of Theorem 1 cannot be replaced by taking \(T\to\infty\) at a fixed \(Q\). For the reciprocal-divergent example above, that would give the opposite behaviour.

What (28) proves is a diagonal statement: \(Q\) changes, and among a finite family of observation lengths appropriate to that \(Q\), one has a small average. No fixed-modulus limiting assertion is being promoted to a uniform one.

---


---

# Part r3: Quantitative reciprocal-mass growth

## 1. The quantitative theorem

Let \(b\ge2\) be an integer and let \(A\subseteq\mathbb N_{>0}\) be infinite. Write

$$
S_b(A)=\sum_{a\in A}\frac1{b^a-1},
\qquad
H_A(x)=\sum_{\substack{a\in A\\a\le x}}\frac1a.
$$

Fix the tower sequence

$$
T_0=2,\qquad T_{j+1}=2^{T_j},
$$

and, for \(x\ge2\), put

$$
\ell(x)=\min\{j\ge0:x\le T_j\}.
$$

This differs from the usual base-two iterated logarithm by at most a fixed additive constant.

For a positive reduced rational \(p/q\), factor

$$
q=q_{\mathrm s}q_{\mathrm c},
$$

where every prime factor of \(q_{\mathrm s}\) divides \(b\), and
\(\gcd(q_{\mathrm c},b)=1\). These two factors are coprime. Let

$$
0\le c<q_{\mathrm s},
\qquad
c q_{\mathrm c}\equiv p\pmod{q_{\mathrm s}},
$$

with \(c=0\) when \(q_{\mathrm s}=1\), and define

$$
\lambda_b(p/q)=1-\frac{c}{q_{\mathrm s}}\in(0,1].
\tag{1}
$$

### Theorem 1 — quantitative reciprocal-mass growth

If

$$
S_b(A)=\frac pq,
$$

then

$$
\boxed{\displaystyle
\liminf_{x\to\infty}\frac{H_A(x)}{\ell(x)}
\ge \frac{\lambda_b(p/q)}2>0.}
\tag{2}
$$

In particular, if \(\gcd(q,b)=1\), then

$$
\boxed{\displaystyle
\liminf_{x\to\infty}\frac{H_A(x)}{\ell(x)}\ge\frac12.}
\tag{3}
$$

Consequently:

### Corollary 2 — sub-iterated-logarithmic reciprocal mass

If \(A\) is infinite and

$$
H_A(x)=o(\ell(x)),
\tag{4}
$$

then \(S_b(A)\) is irrational for every integer \(b\ge2\).

The assertion is a **liminf** bound. It is not an ordinary logarithmic-density bound, and no optimality claim is made for the coefficient \(1/2\).

## 2. The exact arithmetic starting point

Use the corpus’s shifted-atom representation

$$
u_a(n)=\frac{b^{\,n\bmod a}}{b^a-1},
\qquad
U_A(n)=\sum_{a\in A}u_a(n).
\tag{5}
$$

The binary version and its exact GCD orbit sum are established in
`ReciprocalSupportIrrationality.lean`. The new argument below replaces the infinite averaging step by a finite estimate.

For completeness, the identities needed from this representation are short enough to record explicitly.

For each \(a,n\),

$$
\frac{b^n}{b^a-1}
=
\sum_{j=1}^{\lfloor n/a\rfloor}b^{n-ja}
+\frac{b^{\,n\bmod a}}{b^a-1}.
$$

Hence

$$
U_A(n)=b^nS_b(A)-I_A(n),
\tag{6}
$$

where

$$
I_A(n)=
\sum_{\substack{a\in A\\a\le n}}
\sum_{j=1}^{\lfloor n/a\rfloor}b^{n-ja}
\in\mathbb Z.
$$

All sums in (5) converge: only finitely many terms have \(a\le n\), and for \(a>n\) the summand is \(b^n/(b^a-1)\).

Moreover,

$$
u_a(n)\ge u_a(0)
$$

for every \(a,n\). Since \(A\) is infinite, for every \(n>0\) there is an \(a\in A\) with \(a>n\), and that atom satisfies a strict inequality. Therefore

$$
\boxed{U_A(n)>U_A(0)=S_b(A)\qquad(n>0).}
\tag{7}
$$

This is where infinitude enters. For finite supports, a common period can freeze every atom and make the difference zero.

### Lemma 3 — the rational phase gap

Suppose \(S_b(A)=p/q\). Choose \(h\ge1\) such that

$$
b^h\equiv1\pmod{q_{\mathrm c}},
$$

taking \(h=1\) when \(q_{\mathrm c}=1\), and choose \(\nu\ge0\) such that

$$
q_{\mathrm s}\mid b^\nu.
$$

Then

$$
h\mid n,\quad n\ge\nu,\quad n>0
\quad\Longrightarrow\quad
U_A(n)-U_A(0)\ge\lambda_b(p/q).
\tag{8}
$$

**Proof.** By the definition of \(c\), there is an integer \(k\) such that

$$
\frac pq=\frac{c}{q_{\mathrm s}}+\frac{k}{q_{\mathrm c}}.
$$

For the stated \(n\), the second summand of

$$
(b^n-1)\frac pq
=
(b^n-1)\frac{c}{q_{\mathrm s}}
+(b^n-1)\frac{k}{q_{\mathrm c}}
$$

is an integer, while the first belongs to
\(\mathbb Z-c/q_{\mathrm s}\). Equation (6) consequently gives

$$
U_A(n)-U_A(0)\in\mathbb Z-\frac{c}{q_{\mathrm s}}.
$$

By (7), this number is strictly positive. The least positive member of that lattice is \(1-c/q_{\mathrm s}\), including the case \(c=0\). This proves (8). \(\square\)

For the binary targets in the packet, the respective gaps are

$$
\lambda_2(1/21)=1,\qquad
\lambda_2(4/9)=1,\qquad
\lambda_2(1/2)=\frac12.
\tag{9}
$$

## 3. The finite-window inequality

For \(L,a\ge1\), set

$$
g_L(a)=\gcd(L,a).
$$

For \(X\ge M\), define

$$
\mathcal H_L(M,X)
=
\sum_{\substack{a\in A\\M<a\le X}}
\frac{g_L(a)}
     {a\bigl(b^{g_L(a)}-1\bigr)}
\tag{10}
$$

and

$$
\mathcal E_L(M,X)
=
\sum_{\substack{a\in A\\M<a\le X}}
\frac1{a\bigl(b^{g_L(a)}-1\bigr)}.
\tag{11}
$$

The first quantity retains the exact GCD orbit mean. In particular, the argument does not replace divisibility structure by an independence assumption.

### Proposition 4 — finite logarithmic-scale accumulation

Assume \(S_b(A)=p/q\), and abbreviate \(\lambda=\lambda_b(p/q)\). Let \(M,L\ge1\) satisfy

$$
L\ge\max\{M,\nu\},\qquad h\mid L,
\qquad
a\mid L\quad\text{for every }a\in A\cap[1,M].
\tag{12}
$$

For every integer \(J\ge1\), put

$$
X=L2^{J-1}.
$$

Then

$$
\boxed{\displaystyle
J\lambda
<
J\mathcal H_L(M,X)+2L\mathcal E_L(M,X)+4.}
\tag{13}
$$

Consequently,

$$
\boxed{\displaystyle
(J+2L)\bigl(H_A(X)-H_A(M)\bigr)>J\lambda-4.}
\tag{14}
$$

**Proof.**

We first bound a single atom over a finite orbit segment. Put

$$
g=\gcd(L,a),\qquad r=a/g.
$$

The residues \(kL\bmod a\), for \(1\le k\le r\), are exactly

$$
0,g,2g,\ldots,a-g
$$

in some order. Therefore

$$
\sum_{k=1}^{r}u_a(kL)
=
\frac{\sum_{j=0}^{r-1}b^{gj}}{b^a-1}
=
\frac1{b^g-1}.
\tag{15}
$$

Every complete block of \(r\) consecutive samples has this same sum. A remaining partial block has no greater sum, since its terms are nonnegative. Thus, for every \(K\ge1\),

$$
\frac1K\sum_{k=1}^{K}u_a(kL)
\le
\frac{g}{a(b^g-1)}
+\frac1{K(b^g-1)}.
\tag{16}
$$

We next bound all conductors beyond the largest sampled index. For \(Y\ge1\),

$$
\sum_{a>Y}\frac1{b^a-1}
<
\frac1{(b-1)(b^Y-1)}.
\tag{17}
$$

Indeed, writing \(a=Y+s\),

$$
b^{Y+s}-1>b^s(b^Y-1),
$$

and summing the resulting geometric majorant proves (17).

If \(a>KL\), then \(kL\bmod a=kL\) for every \(1\le k\le K\). Hence

$$
\begin{aligned}
\frac1K\sum_{k=1}^{K}
 \sum_{\substack{a\in A\\a>KL}}u_a(kL)
&\le
\frac1K\left(\sum_{k=1}^{K}b^{kL}\right)
\left(\sum_{a>KL}\frac1{b^a-1}\right)\\
&<
\frac{b^L}{K(b-1)(b^L-1)}
\le\frac2K.
\end{aligned}
\tag{18}
$$

Now average \(U_A(kL)-U_A(0)\). Every conductor \(a\le M\) in \(A\) divides \(L\), so its displacement is exactly zero. For the remaining conductors, dropping their subtracted zero-shift values gives an upper bound. Combining (8), (16), and (18),

$$
\lambda
<
\mathcal H_L(M,KL)
+\frac1K
 \sum_{\substack{a\in A\\M<a\le KL}}
 \frac1{b^{g_L(a)}-1}
+\frac2K.
\tag{19}
$$

Apply (19) with

$$
K_i=2^i,\qquad 0\le i<J,
$$

and sum over \(i\). The first terms total at most
\(J\mathcal H_L(M,X)\).

For the second terms, interchange the two **finite** sums:

$$
\begin{aligned}
&\sum_{i=0}^{J-1}2^{-i}
 \sum_{\substack{a\in A\\M<a\le L2^i}}
 \frac1{b^{g_L(a)}-1}\\
&\qquad=
\sum_{\substack{a\in A\\M<a\le X}}
 \frac1{b^{g_L(a)}-1}
 \sum_{\substack{0\le i<J\\a\le L2^i}}2^{-i}.
\end{aligned}
\tag{20}
$$

For every \(a\le X\),

$$
\sum_{\substack{0\le i<J\\a\le L2^i}}2^{-i}
\le\frac{2L}{a}.
\tag{21}
$$

When \(a\le L\), this follows from \(\sum_{i\ge0}2^{-i}=2\). Otherwise, start the geometric sum at
\(\lceil\log_2(a/L)\rceil\).

Equations (20)–(21) bound the second terms by
\(2L\mathcal E_L(M,X)\). The final terms total strictly less than

$$
\sum_{i=0}^{\infty}2^{1-i}=4.
$$

This proves (13).

Finally,

$$
b^g-1\ge g\qquad(g\ge1),
$$

so

$$
\mathcal E_L(M,X)
\le\mathcal H_L(M,X)
\le H_A(X)-H_A(M).
$$

Substitution into (13) proves (14). \(\square\)

The important point is the treatment of the terminal segment in (18) and the finite interchange in (20). Neither requires reciprocal summability, an asymptotic density, or a limiting average over the support.

## 4. Proof of the quantitative theorem

Fix \(0<\eta<1\). For sufficiently large integers \(M\), choose

$$
L(M)=h\,\operatorname{lcm}(1,2,\ldots,M)
\tag{22}
$$

and

$$
J(M)=
\left\lceil\frac{2L(M)+4/\lambda}{\eta}\right\rceil,
\qquad
X(M)=L(M)2^{J(M)-1}.
\tag{23}
$$

The hypotheses of Proposition 4 hold once \(M\ge\nu\).

Equation (14) gives

$$
H_A(X(M))-H_A(M)
>
\frac{J(M)\lambda-4}{J(M)+2L(M)}
\ge\lambda(1-\eta).
\tag{24}
$$

For the last inequality, observe that

$$
\begin{aligned}
&J\lambda-4-\lambda(1-\eta)(J+2L)\\
&\qquad=\eta\lambda J-4-2\lambda(1-\eta)L
\ge 2\eta\lambda L\ge0.
\end{aligned}
$$

We require an explicit bound on the distance to the next mass increment. The elementary estimate

$$
L(M)\le hM!\le hM^M
$$

is sufficient. With \(h,\lambda,\eta\) fixed, (23) gives

$$
J(M)\le C L(M)
$$

for a constant \(C\). Consequently, for all sufficiently large \(M\),

$$
\log_2\log_2 X(M)
\le 2M\log_2M,
$$

and hence

$$
X(M)\le 2^{\,2^{\,2M\log_2M}}.
\tag{25}
$$

Choose \(k_0\) sufficiently large and define

$$
M_j=\sqrt{T_{k_0+2j}}.
\tag{26}
$$

These are integers. If \(k=k_0+2j\), then

$$
\begin{aligned}
M_{j+1}
&=\sqrt{T_{k+2}}
 =2^{T_{k+1}/2}\\
&=2^{\,2^{\,T_k-1}}
 =2^{\,2^{\,M_j^2-1}}.
\end{aligned}
\tag{27}
$$

For sufficiently large \(M_j\),

$$
2M_j\log_2M_j\le M_j^2-1.
$$

Thus (25)–(27) imply

$$
X(M_j)\le M_{j+1}.
$$

By monotonicity of \(H_A\), equation (24) now yields

$$
H_A(M_{j+1})-H_A(M_j)>\lambda(1-\eta).
\tag{28}
$$

Therefore

$$
H_A(M_j)\ge H_A(M_0)+j\lambda(1-\eta).
\tag{29}
$$

For sufficiently large \(k\),

$$
T_{k-1}<\sqrt{T_k}<T_k.
$$

Hence

$$
\ell(M_j)=k_0+2j.
$$

If \(M_j\le x<M_{j+1}\), then

$$
H_A(x)\ge H_A(M_j),
\qquad
\ell(x)\le k_0+2j+2.
$$

It follows from (29) that

$$
\liminf_{x\to\infty}\frac{H_A(x)}{\ell(x)}
\ge\frac{\lambda(1-\eta)}2.
$$

Since \(\eta\) was arbitrary,

$$
\liminf_{x\to\infty}\frac{H_A(x)}{\ell(x)}
\ge\frac{\lambda}2.
$$

This proves Theorem 1. Corollary 2 follows immediately: a rational value would give a strictly positive lower bound incompatible with (4). \(\square\)

## 5. A reciprocal-divergent application

The extension beyond reciprocal summability is nonempty. It also need not rely on large gaps between successive selected exponents.

Set

$$
t_j=T_{j+1}\qquad(j\ge1)
$$

and define

$$
B_j=
\left\{
t_j,t_j+1,\ldots,
t_j+\left\lfloor\frac{t_j}{j}\right\rfloor
\right\}.
$$

Let

$$
\boxed{\displaystyle
A=\{m^2:m\ge1\}\ \cup\ \bigcup_{j\ge1}B_j.}
\tag{30}
$$

### Proposition 5

The support (30) satisfies

$$
\sum_{a\in A}\frac1a=\infty,
\qquad
H_A(x)=o(\ell(x)).
\tag{31}
$$

Consequently,

$$
\sum_{a\in A}\frac1{b^a-1}
$$

is irrational for every integer \(b\ge2\).

**Proof.** The blocks are disjoint, since

$$
t_j+\left\lfloor t_j/j\right\rfloor
\le2t_j<2^{t_j}=t_{j+1}.
$$

Each block contributes at least

$$
\sum_{a\in B_j}\frac1a
\ge
\frac{t_j/j}{2t_j}
=\frac1{2j}.
$$

This proves reciprocal divergence.

For the upper bound,

$$
\sum_{a\in B_j}\frac1a
\le\frac1j+\frac1{t_j}.
$$

The square support has finite reciprocal mass, and
\(\sum_j1/t_j<\infty\). Thus, whenever \(t_j\le x<t_{j+1}\),

$$
H_A(x)
\le C+\sum_{i=1}^{j}\frac1i
\le C'+\log j.
$$

But \(\ell(x)\ge\ell(t_j)=j+1\). Therefore

$$
\frac{H_A(x)}{\ell(x)}
\le\frac{C'+\log j}{j+1}\longrightarrow0.
$$

Corollary 2 completes the proof. \(\square\)

The square background matters: this example is not merely a sequence of isolated blocks with enormous empty gaps.

Indeed, enumerate it as \(a_1<a_2<\cdots\), and put

$$
\mathcal D_r=
\operatorname{lcm}_{i\le r}(2^{a_i}-1).
$$

If \(m=\lfloor\sqrt{a_r}\rfloor\), then both \(m^2\) and \((m-1)^2\) occur in the selected prefix. Their Mersenne denominators are coprime, because

$$
\gcd(m^2,(m-1)^2)=1
$$

and

$$
\gcd(2^u-1,2^v-1)=2^{\gcd(u,v)}-1.
$$

Also \(a_{r+1}\le(m+1)^2\). Consequently, for large \(r\),

$$
\log_2\mathcal D_r-a_{r+1}
>
m^2+(m-1)^2-2-(m+1)^2
=m^2-4m-2.
$$

Thus

$$
\mathcal D_r\,2^{2-a_{r+1}}\longrightarrow\infty.
\tag{32}
$$

In particular, the displayed LCM-height escape condition
\(\liminf_r\mathcal D_r2^{2-a_{r+1}}=0\) is not what proves this example irrational. This observation does **not** assert failure of every possible reduced-denominator argument.


---

# Part r7: Prime-power support irrationality

# Irrationality for arbitrary prime-power supports

Write

$$
\mathcal P_{\mathrm{pow}}=\{p^k:p\text{ prime},\ k\ge1\}.
$$

**Theorem 1.** Let \(b\ge2\) be an integer and let \(A\subseteq\mathcal P_{\mathrm{pow}}\) be infinite. Then

$$
\boxed{\displaystyle
\sum_{a\in A}\frac1{b^a-1}\notin\mathbb Q.}
\tag{1}
$$

Consequently, the same conclusion holds whenever, for some fixed positive integer \(m\), all but finitely many elements of \(A\) belong to

$$
m\mathcal P_{\mathrm{pow}}=\{mp^k:p\text{ prime},\ k\ge1\}.
\tag{2}
$$

The supplied reciprocal-summability theorem is an imported premise. It already covers the case

$$
\sum_{\substack{p\ \mathrm{prime}\\p\in A}}\frac1p<\infty,
$$

because

$$
\sum_p\sum_{k\ge2}\frac1{p^k}
=\sum_p\frac1{p(p-1)}
\le \sum_{n\ge2}\frac1{n(n-1)}
=1.
\tag{3}
$$

Thus the new argument concerns the divergent first-prime layer, not the already-settled sparse case. 

The deep external input is the equidistributed case of Tao–Teräväinen’s quantitative correlation theorem, Theorem 3.1. Their stated irrationality application treats the full prime support, and they indicate a prime-power extension; the arbitrary-selection assertion (1) is the result proved here, rather than an assertion attributed to their paper. ([arXiv][1])

## 1. The prime-local identity

For \(A\subseteq\mathcal P_{\mathrm{pow}}\), put

$$
\alpha_{p,k}=\mathbf1_A(p^k),\qquad
f(n)=\sum_{d\mid n}\mathbf1_A(d).
$$

Then

$$
f(n)=\sum_p\sum_{1\le k\le v_p(n)}\alpha_{p,k},
\qquad
0\le f(n)\le\Omega(n)\le\frac{\log n}{\log2}.
\tag{4}
$$

Absolute convergence gives the exact Lambert identity

$$
\sum_{a\in A}\frac1{b^a-1}
=\sum_{n\ge1}\frac{f(n)}{b^n}.
\tag{5}
$$

The essential localisation is

$$
\boxed{f(pn)-f(n)=\alpha_{p,v_p(n)+1}.}
\tag{6}
$$

In particular,

$$
f(pn)=f(n)+\alpha_{p,1}+\eta_p(n),
\qquad
|\eta_p(n)|\le\mathbf1_{p\mid n}.
\tag{7}
$$

This is exact, including when \(p\notin A\), when some higher power of \(p\) is selected, and when \(p\mid n\). Its proof is simply that multiplication by \(p\) changes only the \(p\)-adic valuation and introduces exactly one additional possible selected prime-power divisor.

The dilation primes therefore need **not** belong to the selected support. Arbitrary thinning does not remove the supply of dilation parameters.

Suppose, towards a contradiction, that the value in (5) is rational, with denominator \(D\ge1\). Set

$$
q=D(b-1).
$$

For every nonnegative integer \(u\),

$$
q\sum_{h\ge1}\frac{f(u+h)}{b^h}\in\mathbb Z.
\tag{8}
$$

If \(p\mid u\), equation (7) consequently gives

$$
q\sum_{h\ge1}\frac{f(u+ph)}{b^h}
\equiv
q\sum_{h\ge1}\frac{\eta_p(u/p+h)}{b^h}
\pmod1,
\tag{9}
$$

because the constant contribution

$$
q\alpha_{p,1}\sum_{h\ge1}b^{-h}
=D\alpha_{p,1}
$$

is an integer. The right-hand side has absolute value at most

$$
q\sum_{h\ge1}b^{-h}\mathbf1_{p^2\mid u+ph}.
\tag{10}
$$

Thus the entire failure of exact dilation invariance is confined to a prime-square divisibility event.

## 2. A uniform large-prime cancellation lemma

We first establish the analytic ingredient needed for arbitrary thinning.

Throughout, \(e(x)=\exp(2\pi i x)\). A quantity bounded by \((\log X)^{o(1)}\) means that it is at most \((\log X)^\varepsilon\), eventually, for every fixed \(\varepsilon>0\).

**Lemma 2.** For each sufficiently large \(X\), let \(T_X\) be any subset of the primes in

$$
(X^{1/100},3X].
$$

Let \(Q_X\) be a positive integer, \(a_X\) a residue modulo \(Q_X\), and \(r_i\) distinct integer shifts satisfying

$$
Q_X+\max_i|r_i|\le(\log X)^{o(1)}.
\tag{11}
$$

Let real coefficients \(c_i\) satisfy

$$
\sum_i c_i=0,\qquad
\sum_i|c_i|\le C,\qquad
\sum_i c_i^2=o(1).
\tag{12}
$$

Then there is a choice \(N=N_X\in[\sqrt X,X]\) such that, for \(n\) uniformly distributed over

$$
\{n\in\mathbb Z:N<n\le2N,\ n\equiv a_X\pmod{Q_X}\},
$$

one has

$$
\mathbb E\left|
\sum_i c_i\sum_{\substack{p\in T_X\\p\mid n+r_i}}1
\right|^2=o(1).
\tag{13}
$$

No density assumption is imposed on \(T_X\).

### Proof

We use the following precise consequence of the equidistributed case of Tao–Teräväinen’s Theorem 3.1. Suppose \(g,h\) are \(1\)-bounded multiplicative functions, \(g\) is real-valued, and, uniformly for \(X^{0.4}\le Y\le X\),

$$
\sum_{\substack{Y<n\le2Y\\n\equiv a\pmod r}}g(n)
=\frac Yr\,\delta_Y+O(Y/\mathcal L)
\tag{14}
$$

for all \(a,r\), where \(1\le\mathcal L\le\log X\). Suppose also

$$
g(p)=1
\quad\text{when}\quad
e^{(\log X)^{1/11}}\le p\le e^{(\log X)^{1/10}}.
\tag{15}
$$

Then, outside an exceptional set of logarithmic measure
\(O(\mathcal L^{-c}\log X)\), the two-point centred correlation on progressions is \(O(\mathcal L^{-c})\), uniformly for distinct shifts, progression modulus and residue bounded by \(\mathcal L^c\), for an absolute \(c>0\). ([arXiv][1])

We check these hypotheses for the functions actually required.

Choose

$$
\mathcal L=(\log X)^{1/4},
\qquad
J=\lfloor(\log X)^\gamma\rfloor,
$$

where \(\gamma>0\) is sufficiently small compared with \(c\). Partition
\((X^{1/100},3X]\) into \(J\) intervals \(I_j\) of equal logarithmic-logarithmic width. Elementary prime-counting bounds and partial summation give

$$
\sum_{p\in I_j}\frac1p\ll \frac1J.
\tag{16}
$$

Put \(T_j=T_X\cap I_j\), and define the completely multiplicative function

$$
g_j(p)=
\begin{cases}
0,&p\in T_j,\\
1,&p\notin T_j.
\end{cases}
\tag{17}
$$

Thus \(g_j(n)\) indicates that \(n\) has no prime divisor from \(T_j\).

For completeness, the equidistribution estimate is uniform even when \(T_j\) is chosen arbitrarily. Inclusion–exclusion gives

$$
g_j(n)=
\sum_{\substack{d\mid n\\d\ \mathrm{squarefree}\\p\mid d\Rightarrow p\in T_j}}
\mu(d).
\tag{18}
$$

The number of possible \(d\le2Y\) in this sum is

$$
O(Y/\log X),\qquad X^{0.4}\le Y\le X.
\tag{19}
$$

Here is an elementary justification. Each such \(d>1\) has at most \(101\) prime factors, all exceeding \(X^{1/100}\). For each fixed number \(k\) of factors, sum first over the first \(k-1\) prime factors, with product \(m\), and then use

$$
\pi(2Y/m)\ll \frac{Y}{m\log X}.
$$

The reciprocal sum of primes between \(X^{1/100}\) and \(2X\) is bounded by an absolute constant. Summing over \(k\le101\) proves (19).

For \(r\le\mathcal L\), every \(d\) in (18) is coprime to \(r\). Counting each progression of multiples of \(d\), and using (19) to sum the integer-part errors, proves

$$
\sum_{\substack{Y<n\le2Y\\n\equiv a\pmod r}}g_j(n)
=\frac Yr\,\delta_{j,Y}+O(Y/\log X),
\tag{20}
$$

where \(\delta_{j,Y}\) is the ordinary interval mean of \(g_j\). For \(r>\mathcal L\), the required error \(O(Y/\mathcal L)\) follows directly from the trivial progression count. Condition (15) holds because every forbidden prime exceeds \(X^{1/100}\).

Apply the correlation theorem to all pairs \((g_j,g_k)\), and also to \((g_j,1)\). There are \(O(J^2)\) applications. Since

$$
J^2\mathcal L^{-c}=o(1),
$$

their exceptional sets do not cover \([\sqrt X,X]\). Choose \(N\) outside their union. The bounds (11) put the actual progression and shifts inside the permitted range.

Let

$$
Y_j(n)=\sum_{\substack{p\in T_j\\p\mid n}}1.
$$

Every integer at most \(3X\) has at most \(102\) prime factors exceeding \(X^{1/100}\). Consequently

$$
Y_j(n)=1-g_j(n)+E_j(n),
$$

where

$$
E_j(n)\ge0,\qquad
\sum_j E_j(n)\le102,
$$

and \(E_j(n)\neq0\) requires two distinct primes from \(T_j\) to divide \(n\).

By (16), counting multiples of pairs of primes gives, on the chosen progression,

$$
\mathbb P\bigl(Y_j(n+r_i)\ge2\bigr)
\ll \frac{Q_X}{J^2}.
\tag{21}
$$

It follows that replacing \(Y_j\) by \(1-g_j\), after summing over \(j\) and taking the linear combination with coefficients \(c_i\), changes the expression in (13) by a term whose second moment is

$$
O(Q_X/J)=o(1).
\tag{22}
$$

Define

$$
Z_i(n)=\sum_{j=1}^J\bigl(g_j(n+r_i)-\delta_{j,N}\bigr).
$$

These variables are uniformly bounded: the sum counts, after centring, the number of intervals \(T_j\) represented among the large prime divisors, and that number is at most \(102\).

For \(i\neq i'\), the correlation theorem and its application with second function \(1\) give

$$
\mathbb E Z_iZ_{i'}\ll J^2\mathcal L^{-c}.
\tag{23}
$$

The diagonal second moments are \(O(1)\). Therefore

$$
\mathbb E\left|\sum_i c_iZ_i\right|^2
\ll
\sum_i c_i^2+
\left(\sum_i|c_i|\right)^2J^2\mathcal L^{-c}
=o(1).
\tag{24}
$$

The constant terms disappear because \(\sum_i c_i=0\). Together with (22), this proves (13). ∎

The distinction between (13) and a density assertion is important: it produces a genuine averaging scale for the specified, possibly very irregular, prime set. It does not replace that set by a random model.

## 3. Choose the scale from selected reciprocal mass

We now prove Theorem 1 in the remaining case

$$
S:=A\cap\mathcal P,\qquad
\sum_{p\in S}\frac1p=\infty.
\tag{25}
$$

Let \(X\to\infty\), and put

$$
t=\sum_{\substack{p\in S\\p\le X}}\frac1p,
\qquad L=\log t.
$$

Thus \(t\to\infty\), without any assumed rate. Choose

$$
\begin{aligned}
K&=\left\lfloor\frac{2\log L}{\log2}\right\rfloor,
&
H&=\lceil L^2\rceil,
&
P&=\lceil e^{L^3}\rceil,\\
M&=2\lceil t\rceil,
&
R&=X^{1/t^2},
&
R_+&=X^{1/100}.
\end{aligned}
\tag{26}
$$

In particular,

$$
2^K\asymp L^2.
$$

For the fixed base \(b\), write

$$
\vartheta_K=\left(\frac2{b^2}\right)^K.
$$

Then

$$
\vartheta_K\asymp L^{-\beta_b},
\qquad
\beta_b=4\log_2b-2\ge2.
\tag{27}
$$

The two estimates we will use are

$$
t\vartheta_K\longrightarrow\infty,
\qquad
L\vartheta_K\longrightarrow0.
\tag{28}
$$

These both hold even when the divergence in (25) is arbitrarily slow. That is the purpose of using \(t\), rather than \(\log\log X\), to set \(K\).

### A cube of dilation primes

There are integers \(p_0,v_1,\ldots,v_K\) such that

$$
p_\epsilon=p_0+\sum_{j=1}^K\epsilon_jv_j,
\qquad \epsilon\in\{0,1\}^K,
\tag{29}
$$

are distinct primes in \([P/2,P]\), and all the shifts

$$
r_{\epsilon,h}
=p_\epsilon h-\sum_{j=1}^Kj\epsilon_jv_j
=p_0h+\sum_{j=1}^K(h-j)\epsilon_jv_j
\tag{30}
$$

are distinct for \(K+1\le h\le K+H\).

Here are the counting details. Embed the primes in \([P/2,P]\) in a cyclic group of prime order between \(5P\) and \(10P\). Their density is \(\gg1/\log P\). Repeated Cauchy–Schwarz gives a proportion at least

$$
(c/\log P)^{2^K}
$$

of affine \(K\)-cubes lying entirely in that set. The probability of a coincidence between two vertices, or between two of the specified shifts, is

$$
O(2^{2K}H^2/P).
$$

The linear equations defining those coincidences are nonzero over the chosen prime field. Our parameters satisfy

$$
\frac{2^{2K}H^2}{P}
=o\bigl((c/\log P)^{2^K}\bigr),
$$

so a cube avoiding all coincidences exists. The vertices lift uniquely to primes in \([P/2,P]\); adjacent differences lift consistently to integers of absolute value at most \(P/2\). This gives (29)–(30) over the integers.

No selection condition \(p_\epsilon\in S\) has been used.

### Construct a genuine arithmetic progression

Let \(\mathcal I\) index the pairs \((\epsilon,h)\) with \(1\le h\le H\), and abbreviate

$$
r_i=r_{\epsilon,K+h}.
$$

Let \(W\) be the product of the nonzero pairwise differences \(r_i-r_j\). Declare a prime *exceptional* if it divides \(W\), is one of the \(p_\epsilon\), or is at most

$$
z=\lfloor L\rfloor.
$$

We choose one residue class \(n\equiv a\pmod Q\) with the following properties:

$$
n\equiv \sum_{j=1}^Kj\epsilon_jv_j\pmod{p_\epsilon}
\quad\text{for every }\epsilon;
\tag{31}
$$

$$
p_\epsilon^2\nmid n+r_{\epsilon,h}
\quad(1\le h\le H);
\tag{32}
$$

and, for every exceptional prime \(p\), every valuation

$$
v_p(n+r_i),\qquad i\in\mathcal I,
$$

is fixed throughout the progression.

To construct it, first impose (31). For a cube prime, lift the prescribed residue modulo \(p_\epsilon\) to a residue modulo \(p_\epsilon^2\), avoiding the residue classes prohibited by (32) and by the near shifts \(r_i\). There are at most \(|\mathcal I|+H<p_\epsilon\) forbidden lifts.

For every other exceptional prime \(p\), choose \(e_p\) with \(p^{e_p}>|\mathcal I|\), and choose a residue modulo \(p^{e_p}\) avoiding all \(-r_i\). Then each relevant valuation is strictly below \(e_p\) and is fixed. The Chinese remainder theorem combines these choices.

The construction gives

$$
\log Q=O(L^C)
\tag{33}
$$

for some absolute constant \(C\). Indeed,

$$
|\mathcal I|=2^KH=O(L^4),\qquad
\log|W|=O(L^C),
$$

and the extra prime powers cost only another polynomial in \(L\).

Since \(t\ll\log\log X\),

$$
Q+\max_i|r_i|\le(\log X)^{o(1)}.
\tag{34}
$$

Also every exceptional prime is smaller than \(R\), eventually.

## 4. Rationality forces a characteristic function of modulus one

Define

$$
c_{\epsilon,h}
=q(-1)^{|\epsilon|}b^{-K-h},
\qquad 1\le h\le H.
\tag{35}
$$

These coefficients satisfy

$$
\sum_{\epsilon,h}c_{\epsilon,h}=0,
\qquad
\sum_{\epsilon,h}|c_{\epsilon,h}|\le D,
\tag{36}
$$

and

$$
v_K:=\sum_{\epsilon,h}c_{\epsilon,h}^2
=q^2\left(\frac2{b^2}\right)^K
\sum_{h=1}^H b^{-2h}
\asymp_{b,D}\vartheta_K.
\tag{37}
$$

Apply (9) with dilation prime \(p_\epsilon\) and initial point

$$
n-\sum_{j=1}^Kj\epsilon_jv_j.
$$

Condition (31) makes that initial point divisible by \(p_\epsilon\). It is positive when \(n\asymp N\), \(N\ge\sqrt X\).

Take the alternating sum over \(\epsilon\). For \(1\le h\le K\), the shift \(r_{\epsilon,h}\) is independent of \(\epsilon_h\); those terms cancel exactly. Conditions (32) and (10) bound the remaining dilation error by

$$
O(q\,2^Kb^{-H})=o(1).
\tag{38}
$$

We may also truncate the surviving sum at \(h=H\). Here the potentially delicate point is that \(t\) may be much smaller than \(\log\log X\).

For any shift \(r\) of size at most

$$
O\bigl(PK(\log\log X)^2\bigr),
$$

averaging (4) on the progression gives

$$
\mathbb E f(n+r)\ll t+\log Q+1\ll t.
\tag{39}
$$

For primes not dividing \(Q\), count multiples directly. Their first-power contribution is bounded by

$$
\sum_{\substack{p\in S\\p\le3N}}\frac1p
+O\!\left(\frac{Q\pi(3N)}N\right)
\ll t+1.
$$

Higher powers contribute

$$
O(1)+O(Q\log N/\sqrt N).
$$

For a prime with \(p^e\Vert Q\), the expected valuation is at most

$$
e+\frac1{p-1}+O(Q\log N/N).
$$

Summing these contributions proves (39).

Consequently the intermediate tail costs \(O(tb^{-H})=o(1)\). Beyond

$$
H_+=\lceil(\log\log X)^2\rceil,
$$

the pointwise bound \(f(m)\le\log m/\log2\) gives a tail

$$
O\bigl(b^{-H_+}(\log X+H_+)\bigr)=o(1).
$$

Thus, uniformly for eligible \(N\in[\sqrt X,X]\),

$$
\boxed{\displaystyle
\mathbb E e\!\left(\sum_i c_i f(n+r_i)\right)=1+o(1).}
\tag{40}
$$

Every congruence here was imposed on actual integers \(n\). No relaxed residue system or putative orbit has replaced the original support.

## 5. Remove higher prime powers

For exceptional primes, all the near-shift valuations are fixed. Their entire contribution to the argument of \(e\) in (40) is therefore a deterministic constant \(C_X\).

For nonexceptional primes, remove all powers \(p^k\), \(k\ge2\). For each near shift,

$$
\begin{aligned}
\mathbb E
\sum_{\substack{p\ \mathrm{nonexceptional}\\k\ge2}}
\alpha_{p,k}\mathbf1_{p^k\mid n+r_i}
&\ll
\sum_{p>z}\sum_{k\ge2}\frac1{p^k}
+\frac QN\,O(\sqrt N\log N)\\
&\ll
\frac1z+\frac{Q\log N}{\sqrt N}
=o(1).
\end{aligned}
\tag{41}
$$

Using the bounded sum of absolute coefficients in (36), their total removal changes (40) by \(o(1)\).

For a nonexceptional selected prime \(p\in S\), put

$$
X_p(n)=\sum_i c_i\mathbf1_{p\mid n+r_i}.
\tag{42}
$$

We have reduced (40) to

$$
\mathbb E e\!\left(C_X+\sum_{\substack{p\in S\\p\ \mathrm{nonexceptional}}}X_p(n)\right)
=1+o(1).
\tag{43}
$$

## 6. Remove large primes, but retain a divergent variance

Split the remaining selected primes into

$$
\mathcal C=\{p\in S:p\le R,\ p\ \mathrm{nonexceptional}\},
$$

$$
\mathcal D=\{p\in S:R<p\le R_+\},
\qquad
\mathcal V=\{p\in S:R_+<p\le3X\}.
$$

For a nonexceptional prime \(p\), the shifts \(r_i\) are distinct modulo \(p\). Under the uniform distribution modulo \(p\),

$$
\mathbb E_{\bmod p}X_p=0,
\qquad
\mathbb E_{\bmod p}X_p^2=\frac{v_K}{p}.
\tag{44}
$$

For distinct nonexceptional primes, the uniform product mean is zero by the Chinese remainder theorem.

Counting periods on our progression therefore yields

$$
\mathbb E\left|\sum_{p\in\mathcal D}X_p\right|^2
\ll
v_K\sum_{R<p\le R_+}\frac1p
+\frac{QR_+^4}{N}.
\tag{45}
$$

Prime-counting estimates give

$$
\sum_{R<p\le R_+}\frac1p\ll\log t=L.
$$

Equations (28), (34), and \(N\ge\sqrt X\) show that (45) is \(o(1)\).

For \(\mathcal V\), apply Lemma 2 with \(T_X=\mathcal V\), the progression already constructed, and the coefficients (35). Equations (34), (36), and (37) verify every hypothesis. Choose the resulting scale \(N\). Then

$$
\mathbb E\left|\sum_{p\in\mathcal V}X_p\right|^2=o(1).
\tag{46}
$$

Both removals are legitimate in (43), by Cauchy–Schwarz and the Lipschitz bound for \(e\). We conclude that

$$
\boxed{\displaystyle
\left|\mathbb E e\!\left(\sum_{p\in\mathcal C}X_p(n)\right)\right|
=1+o(1).}
\tag{47}
$$

On the other hand, the core retains almost all the selected reciprocal mass:

$$
\sum_{p\in\mathcal C}\frac1p=t-O(\log t).
\tag{48}
$$

Indeed, primes above \(R=X^{1/t^2}\) cost only \(O(\log t)\) in reciprocal mass. All exceptional primes are at most \(e^{O(L^3)}\), so even the reciprocal sum of *all* primes up to that bound is \(O(\log L)\).

Consequently,

$$
v_K\sum_{p\in\mathcal C}\frac1p
\asymp t\vartheta_K
\longrightarrow\infty.
\tag{49}
$$

It remains to turn (49) into a contradiction to (47), without assuming independence that the progression has not supplied.

## 7. Justify the independent comparison

For each \(p\in\mathcal C\), let \(U_p\) be the random variable obtained by evaluating \(X_p\) at a uniform residue modulo \(p\), with the \(U_p\) mutually independent. Put

$$
Z(n)=\sum_{p\in\mathcal C}X_p(n),
\qquad
Z^*=\sum_{p\in\mathcal C}U_p.
$$

Then, exactly,

$$
\mathbb E U_p=0,\qquad
\operatorname{Var}(U_p)=\frac{v_K}{p},
\qquad
|U_p|\le q b^{-K-1}=o(1).
\tag{50}
$$

We claim

$$
\mathbb E e(Z)-\mathbb E e(Z^*)=o(1).
\tag{51}
$$

For \(0\le j\le M\), expand the \(j\)-th moments into ordered prime tuples. A monomial involving \(j\) primes has period at most \(R^j\), coprime to \(Q\). Its average on the progression differs from its uniform period average by at most

$$
O\!\left(\frac QN C_0^jR^j\right)
$$

for a constant \(C_0\) depending only on \(b,D\). There are at most \(R^j\) ordered tuples. Thus

$$
\left|\mathbb E Z^j-\mathbb E(Z^*)^j\right|
\ll \frac QN(C_0R^2)^j.
\tag{52}
$$

It follows that

$$
\Delta_M:=
\sum_{j=0}^M\frac{(2\pi)^j}{j!}
\left|\mathbb E Z^j-\mathbb E(Z^*)^j\right|
=o(1),
\tag{53}
$$

because

$$
\frac QN(M+1)(C_1R^2)^M
\le X^{-1/2+o(1)}.
$$

Here \(M=2\lceil t\rceil\), so \(R^{2M}=X^{O(1/t)}\).

To control the Taylor remainder, use (50). For either sign,

$$
\mathbb E\exp(\pm2\pi e\,U_p)
\le
\exp\!\left(C_2\operatorname{Var}(U_p)\right).
$$

Independence gives

$$
\mathbb E\exp(\pm2\pi e\,Z^*)
\le
\exp\!\left(C_2v_K\sum_{p\in\mathcal C}\frac1p\right)
=\exp(o(t)).
\tag{54}
$$

Since \(M\) is even,

$$
\frac{(2\pi)^M}{M!}\mathbb E|Z^*|^M
\le
e^{-M}
\left(
\mathbb E e^{2\pi eZ^*}
+\mathbb E e^{-2\pi eZ^*}
\right)
=o(1).
\tag{55}
$$

Equation (53) supplies the same remainder bound for \(Z\). Taylor expansion now proves (51).

Finally, if a real random variable \(U\) has sufficiently small range and \(U'\) is an independent copy, then

$$
|\mathbb E e(U)|^2
=\mathbb E\cos(2\pi(U-U'))
\le1-c_0\operatorname{Var}(U).
\tag{56}
$$

This follows from \(1-\cos(2\pi x)\gg x^2\) on a fixed neighbourhood of zero and

$$
\mathbb E(U-U')^2=2\operatorname{Var}(U).
$$

Applying (56) to (50),

$$
\begin{aligned}
|\mathbb E e(Z^*)|
&=\prod_{p\in\mathcal C}|\mathbb E e(U_p)|\\
&\le
\exp\!\left(-c_1v_K\sum_{p\in\mathcal C}\frac1p\right)
\longrightarrow0
\end{aligned}
\tag{57}
$$

by (49).

Equations (51) and (57) contradict (47). Hence the rationality assumption was false.

This proves Theorem 1 when the selected prime layer has divergent reciprocal mass. Equation (3) and the imported reciprocal-summability theorem prove the remaining case.

For the stated extension, remove the finitely many exceptional indices and write the remainder as

$$
\{mp^k:p^k\in B\},
\qquad B\subseteq\mathcal P_{\mathrm{pow}}\text{ infinite}.
$$

Then

$$
\sum_{p^k\in B}\frac1{b^{mp^k}-1}
=
\sum_{p^k\in B}\frac1{(b^m)^{p^k}-1}
$$

is irrational by Theorem 1 at base \(b^m\). Restoring finitely many rational summands preserves irrationality. ∎


---

# Part r8: Fractional divisor covers

## 1. The new theorem

For \(A\subseteq\mathbb N_{>0}\), write

$$
f_A(n)=\#\{a\in A:a\mid n\},
\qquad
S_A(b)=\sum_{a\in A}\frac1{b^a-1},
$$

where \(b\ge2\) is an integer. Define the shifted-atom sum

$$
U_{A,b}(n)=
\sum_{a\in A}\frac{b^{\,n\bmod a}}{b^a-1}
\qquad(n\ge0).
$$

The new hypothesis concerns a cover by finite supports, not the reciprocal mass of \(A\).

### Theorem 1 — Positive fractional-divisor covers

Let \(0<\alpha\le1\). Suppose that \(F_1,F_2,\ldots\) are finite subsets of \(\mathbb N_{>0}\), and that there are nonnegative real coefficients \(c_{j,d}\) satisfying

$$
f_{F_j}(n)^\alpha
\le
\sum_{d\mid n}c_{j,d}
\qquad(j,n\ge1),
\tag{1}
$$

and

$$
\sum_{j\ge1}\sum_{d\ge1}\frac{c_{j,d}}d<\infty.
\tag{2}
$$

Put

$$
H=\bigcup_{j\ge1}F_j.
$$

Then, for every infinite \(A\subseteq H\), every integer \(b\ge2\), every finite \(P\subseteq A\), and every \(\varepsilon>0\), there are arbitrarily large positive integers \(n\) such that

$$
\operatorname{lcm}(P)\mid n,
\qquad
0<U_{A,b}(n)-S_A(b)<\varepsilon.
\tag{3}
$$

Here the least common multiple of the empty set is \(1\).

Consequently,

$$
\boxed{\quad
S_A(b)\notin\mathbb Q
\quad\text{for every infinite }A\subseteq H
\text{ and every integer }b\ge2.
\quad}
\tag{4}
$$

No coprimality is required between the sets \(F_j\), their elements, or the divisors supporting the coefficients \(c_{j,d}\).

The essential point is that **a summable positive divisor majorant for a fractional power of the incidence count is sufficient**. The first moment itself may have divergent mean.

## 2. The averaging identity that preserves overlap

The required uniformity in the growing prefix LCM comes from an exact identity.

### Lemma 2 — Positive divisor resolvents on an arbitrary progression

Let \(B>1\), let \(L\ge1\) be an integer, and let \(c_d\ge0\) satisfy

$$
C=\sum_{d\ge1}\frac{c_d}{d}<\infty.
$$

Set

$$
h(n)=\sum_{d\mid n}c_d.
$$

Then

$$
\begin{aligned}
&\lim_{X\to\infty}\frac1X
 \sum_{m=1}^{X}\sum_{r\ge1}B^{-r}h(Lm+r)\\
&\qquad=
\sum_{d\ge1}
c_d\,
\frac{\gcd(d,L)}
{d\bigl(B^{\gcd(d,L)}-1\bigr)}
\le
\frac{C}{B-1}.
\end{aligned}
\tag{5}
$$

In particular, the upper bound is independent of \(L\).

#### Proof

Fix \(d,r\ge1\), and put \(g=\gcd(d,L)\). The congruence

$$
Lm\equiv-r\pmod d
$$

has no solution unless \(g\mid r\). When \(g\mid r\), its solutions form one residue class modulo \(d/g\). Therefore

$$
\lim_{X\to\infty}
\frac1X\#\{1\le m\le X:d\mid Lm+r\}
=
\begin{cases}
g/d,&g\mid r,\\
0,&g\nmid r.
\end{cases}
\tag{6}
$$

The infinite-sum interchange needs justification. For every \(X\ge1\),

$$
\begin{aligned}
\frac1X\#\{1\le m\le X:d\mid Lm+r\}
&\le \frac1X\left\lfloor\frac{LX+r}{d}\right\rfloor\\
&\le \frac{L+r}{d}.
\end{aligned}
\tag{7}
$$

Thus the summands are dominated by a summable family:

$$
\sum_{d,r\ge1}
c_dB^{-r}\frac{L+r}{d}
=
C\sum_{r\ge1}(L+r)B^{-r}
<\infty.
\tag{8}
$$

Dominated convergence and (6) give

$$
\begin{aligned}
\lim_{X\to\infty}\frac1X
 \sum_{m\le X}\sum_{r\ge1}B^{-r}h(Lm+r)
&=
\sum_d c_d\frac gd\sum_{s\ge1}B^{-gs}\\
&=
\sum_d c_d\frac{g}{d(B^g-1)}.
\end{aligned}
\tag{9}
$$

Finally,

$$
B^g-1=(B-1)(1+B+\cdots+B^{g-1})
\ge g(B-1).
\tag{10}
$$

Substitution yields (5). \(\square\)

This identity handles the overlap that invalidates a coprime incidence transplant. A common divisor \(g\) increases the progression density by \(g\), but simultaneously restricts the possible future offsets to multiples of \(g\). The geometric resolvent pays for that increased density exactly.

## 3. Proof of Theorem 1

We first record the two exact identities used by the irrationality consumer.

For every \(A\subseteq\mathbb N_{>0}\),

$$
U_{A,b}(n)
=
\sum_{r\ge1}b^{-r}f_A(n+r).
\tag{11}
$$

Indeed, for a fixed \(a\), putting \(t=n\bmod a\),

$$
\sum_{\substack{r\ge1\\a\mid n+r}}b^{-r}
=
\frac{b^t}{b^a-1}.
$$

All terms are nonnegative, so summation may be interchanged. Both sides are finite; for example, \(f_A(n+r)\le n+r\).

The second identity is

$$
U_{A,b}(n)=b^nS_A(b)-J_{A,b}(n),
\qquad
J_{A,b}(n)\in\mathbb Z,
\tag{12}
$$

where explicitly

$$
J_{A,b}(n)=
\sum_{\substack{a\in A\\a\le n}}
\frac{b^n-b^{\,n\bmod a}}{b^a-1}.
\tag{13}
$$

Every summand in (13) is an integer, and the sum is finite.

If \(A\) is infinite, then for every \(n\ge1\),

$$
U_{A,b}(n)>S_A(b).
\tag{14}
$$

Each shifted atom is at least its value at \(n=0\). Moreover, some \(a\in A\) satisfies \(a>n\), and its contribution to the difference is

$$
\frac{b^n-1}{b^a-1}>0.
$$

We now prove the close returns.

Let

$$
E_J=\bigcup_{j\le J}F_j,
\qquad
L_J=\operatorname{lcm}(E_J),
\qquad
T_J=A\setminus E_J,
$$

and put

$$
C_J=\sum_{j>J}\sum_{d\ge1}\frac{c_{j,d}}d.
\tag{15}
$$

By (2), \(C_J\to0\).

Every member of \(T_J\) belongs to some \(F_j\) with \(j>J\). Since \(0<\alpha\le1\), subadditivity gives

$$
\begin{aligned}
f_{T_J}(u)^\alpha
&\le
\left(\sum_{j>J}f_{F_j}(u)\right)^\alpha\\
&\le
\sum_{j>J}f_{F_j}(u)^\alpha\\
&\le
\sum_{d\mid u}c_d^{(J)},
\end{aligned}
\tag{16}
$$

where

$$
c_d^{(J)}=\sum_{j>J}c_{j,d},
\qquad
\sum_d\frac{c_d^{(J)}}d=C_J.
\tag{17}
$$

Applying subadditivity once more, now to (11), yields

$$
\begin{aligned}
U_{T_J,b}(n)^\alpha
&\le
\sum_{r\ge1}b^{-\alpha r}f_{T_J}(n+r)^\alpha\\
&\le
\sum_{r\ge1}b^{-\alpha r}
\sum_{d\mid n+r}c_d^{(J)}.
\end{aligned}
\tag{18}
$$

Lemma 2, with \(B=b^\alpha\) and \(L=L_J\), therefore implies

$$
\limsup_{X\to\infty}\frac1X
\sum_{m\le X}U_{T_J,b}(L_Jm)^\alpha
\le
\frac{C_J}{b^\alpha-1}.
\tag{19}
$$

Choose \(J\) large enough that

$$
P\subseteq E_J,
\qquad
\frac{C_J}{b^\alpha-1}<\varepsilon^\alpha.
\tag{20}
$$

There must be arbitrarily large \(m\) for which

$$
U_{T_J,b}(L_Jm)<\varepsilon.
\tag{21}
$$

Otherwise every sufficiently late summand on the left of (19) would be at least \(\varepsilon^\alpha\), contradicting (19)–(20).

For \(n=L_Jm\), all atoms belonging to \(A\cap E_J\) return exactly to their values at zero. Hence

$$
U_{A,b}(n)-S_A(b)
=
U_{T_J,b}(n)-S_{T_J}(b).
\tag{22}
$$

Combining (14), (21), and (22) gives

$$
0<U_{A,b}(n)-S_A(b)<\varepsilon.
$$

Also, \(\operatorname{lcm}(P)\mid L_J\mid n\). This proves (3), with its cofinal quantifier.

Finally, suppose

$$
S_A(b)=p/q,\qquad p\in\mathbb Z,\quad q\in\mathbb N_{>0}.
$$

By (12),

$$
q\bigl(U_{A,b}(n)-S_A(b)\bigr)
=
(b^n-1)p-qJ_{A,b}(n)\in\mathbb Z.
\tag{23}
$$

Choose the return in (3) with \(\varepsilon=1/q\). Then (23) is an integer strictly between \(0\) and \(1\), a contradiction.

This argument requires neither \(\gcd(q,b)=1\) nor an eventually periodic residue class. In particular, denominators divisible by the base cause no exceptional case. \(\square\)

## 4. Exact majorants for complete divisor frames

The cover condition is useful because a substantial class of finite frames has an explicit positive expansion.

For \(M\ge1\), let

$$
D(M)=\{d\ge1:d\mid M\}.
$$

For \(g,M\ge1\), define

$$
F(g,M)=gD(M).
\tag{24}
$$

Define a multiplicative function \(\beta_\alpha\) by

$$
\beta_\alpha(1)=1,
\qquad
\beta_\alpha(p^e)=(e+1)^\alpha-e^\alpha
\quad(e\ge1).
\tag{25}
$$

All its values are nonnegative.

### Proposition 3 — Exact fractional incidence expansion

For every \(g,M,n\ge1\),

$$
f_{F(g,M)}(n)^\alpha
=
\sum_{d\mid M}\beta_\alpha(d)\,\mathbf1_{gd\mid n}.
\tag{26}
$$

Consequently, the positive-divisor cost of this expansion is

$$
\begin{aligned}
K_\alpha(g,M)
&=\frac1g\sum_{d\mid M}\frac{\beta_\alpha(d)}d\\
&=
\frac1g
\prod_{p^e\parallel M}
\left(
1+\sum_{i=1}^e
\frac{(i+1)^\alpha-i^\alpha}{p^i}
\right).
\end{aligned}
\tag{27}
$$

For squarefree \(M\), this becomes

$$
\boxed{\quad
K_\alpha(g,M)
=
\frac1g
\prod_{p\mid M}
\left(1+\frac{2^\alpha-1}{p}\right).
\quad}
\tag{28}
$$

There is no assumption that \(g\) and \(M\) are coprime.

#### Proof

Both sides of (26) vanish if \(g\nmid n\). If \(g\mid n\), put

$$
v=\gcd(M,n/g).
$$

Then

$$
f_{F(g,M)}(n)=\tau(v).
$$

For every prime power \(p^e\),

$$
\sum_{i=0}^e\beta_\alpha(p^i)
=
1+\sum_{i=1}^e\bigl((i+1)^\alpha-i^\alpha\bigr)
=
(e+1)^\alpha.
$$

Multiplicativity therefore gives

$$
\sum_{d\mid v}\beta_\alpha(d)
=
\prod_{p^e\parallel v}(e+1)^\alpha
=
\tau(v)^\alpha.
$$

This is (26). Equations (27)–(28) follow by factoring the finite divisor sum. \(\square\)

In fact, (27) is the **least possible cost of any nonnegative divisor majorant** for \(f_{F(g,M)}^\alpha\). Its ordinary periodic mean is exactly \(K_\alpha(g,M)\), by (26). Any majorant

$$
f_{F(g,M)}(n)^\alpha\le\sum_{d\mid n}c_d
$$

with finite cost has mean at most

$$
\lim_{X\to\infty}\frac1X
\sum_{n\le X}\sum_{d\mid n}c_d
=
\sum_d\frac{c_d}{d}.
$$

The last interchange is justified by
\(\lfloor X/d\rfloor/X\le1/d\).
Thus every such majorant has cost at least (27), and (26) attains that cost.

Spending Proposition 3 immediately through Theorem 1 gives the following unconditional criterion.

### Corollary 4 — Hereditary irrationality on divisor-frame unions

Suppose that, for some \(0<\alpha\le1\),

$$
\sum_{j\ge1}K_\alpha(g_j,M_j)<\infty.
\tag{29}
$$

Then every infinite subset

$$
A\subseteq\bigcup_{j\ge1}g_jD(M_j)
$$

satisfies

$$
\sum_{a\in A}\frac1{b^a-1}\notin\mathbb Q
\qquad(b\ge2).
\tag{30}
$$

The frames may overlap arbitrarily.

## 5. An explicit reciprocal-divergent host

We now discharge every hypothesis of Corollary 4 for one explicitly defined host.

Start with the prime

$$
g_1=17.
$$

Given \(g_j\), let \(\mathcal P_j\) be the consecutive primes immediately following \(g_j\), stopping at the first prime for which

$$
R_j:=\prod_{p\in\mathcal P_j}\left(1+\frac1p\right)\ge g_j.
\tag{31}
$$

Write

$$
h_j=\max\mathcal P_j,
\qquad
M_j=\prod_{p\in\mathcal P_j}p,
$$

and let \(g_{j+1}\) be the next prime after \(h_j\). Finally, put

$$
H=\bigcup_{j\ge1}g_jD(M_j).
\tag{32}
$$

The stopping rule is finite. Indeed,

$$
\prod_{p\le x}\left(1+\frac1p\right)
=
\prod_{p\le x}(1-p^{-1})^{-1}
\prod_{p\le x}(1-p^{-2}).
$$

The first product is at least \(\sum_{n\le x}1/n\), while the second is at least

$$
\prod_{n=2}^\infty(1-n^{-2})=\frac12.
$$

Thus the product over primes diverges, as does every fixed tail product.

Minimality of the stopping point gives

$$
g_j\le R_j<g_j\left(1+\frac1{h_j}\right)<\frac32g_j.
\tag{33}
$$

We also have a useful elementary growth estimate. Since \(g_j,h_j\) are odd,

$$
\begin{aligned}
\log R_j
&\le\sum_{g_j<p\le h_j}\frac1p\\
&\le
\sum_{\substack{g_j<n\le h_j\\n\text{ odd}}}\frac1n\\
&\le\frac12\int_{g_j}^{h_j}\frac{dt}{t}
=\frac12\log(h_j/g_j).
\end{aligned}
$$

Together with \(R_j\ge g_j\), this yields

$$
h_j\ge g_j^3,
\qquad
g_{j+1}>g_j^3.
\tag{34}
$$

In particular,

$$
g_j\ge16^j.
\tag{35}
$$

### Theorem 5 — A reciprocal-divergent moving-frame support with hereditary irrationality

The support \(H\) defined by (31)–(32) has the following properties:

$$
\sum_{a\in H}\frac1a=\infty,
\tag{36}
$$

every \(a\in H\) is squarefree, and for every \(d>1\),

$$
\#\{a\in H:d\mid a\}<\infty.
\tag{37}
$$

Every pairwise-coprime \(C\subseteq H\) satisfies

$$
\sum_{c\in C}\frac1c<\infty.
\tag{38}
$$

Nevertheless, for every infinite \(A\subseteq H\) and every integer \(b\ge2\),

$$
\boxed{\qquad
\sum_{a\in A}\frac1{b^a-1}\notin\mathbb Q.
\qquad}
\tag{39}
$$

#### Proof

The prime sets

$$
\{g_j\}\cup\mathcal P_j
$$

are mutually disjoint. Thus the frames \(g_jD(M_j)\) are disjoint, and all their elements are squarefree.

The reciprocal mass of frame \(j\) is

$$
\sum_{a\in g_jD(M_j)}\frac1a
=
\frac1{g_j}\prod_{p\in\mathcal P_j}\left(1+\frac1p\right)
=
\frac{R_j}{g_j}\ge1.
\tag{40}
$$

Summing proves (36).

For \(d>1\), choose a prime \(p\mid d\). That prime occurs in at most one frame’s prime set. Consequently, every element of \(H\) divisible by \(d\) lies in that one finite frame. This proves (37).

Every pairwise-coprime subfamily contains at most one element of each frame, because all elements of frame \(j\) are divisible by \(g_j\). Hence

$$
\sum_{c\in C}\frac1c
\le\sum_j\frac1{g_j}
\le\sum_j16^{-j}<\infty,
\tag{41}
$$

which proves (38).

It remains to prove irrationality, rather than merely describe the support.

Fix any \(0<\alpha<1\), and write

$$
c_\alpha=2^\alpha-1.
$$

Concavity of \(x\mapsto x^\alpha\), applied to the chord between \(1\) and \(2\), gives

$$
1+c_\alpha t\le(1+t)^\alpha
\qquad(0\le t\le1).
\tag{42}
$$

Using (28), (33), (35), and (42),

$$
\begin{aligned}
K_\alpha(g_j,M_j)
&=
\frac1{g_j}
\prod_{p\in\mathcal P_j}
\left(1+\frac{c_\alpha}{p}\right)\\
&\le
\frac{R_j^\alpha}{g_j}\\
&<
\left(\frac32\right)^\alpha g_j^{\alpha-1}\\
&\le
\left(\frac32\right)^\alpha
16^{-j(1-\alpha)}.
\end{aligned}
\tag{43}
$$

The final series is summable. Corollary 4 therefore proves (39). \(\square\)

This construction also locates the moment boundary exactly:

$$
\sum_jK_\alpha(g_j,M_j)<\infty
\quad\text{for every fixed }0<\alpha<1,
\tag{44}
$$

whereas

$$
\sum_jK_1(g_j,M_j)
=
\sum_j\frac{R_j}{g_j}
=
\infty.
\tag{45}
$$

No uniform limit as \(\alpha\uparrow1\) is used.

## 6. The host does not rely on LCM-height escape

The irrationality proof above is elementary and does not require information about prime gaps. The following additional structural assertion uses the standard consequence

$$
p_{k+1}/p_k\longrightarrow1
\tag{46}
$$

of the prime number theorem—the same input used in the corpus’s moving-clique no-large-gap argument.

### Proposition 6 — Consecutive ranks and prefix LCM height

Enumerate \(H\) increasingly:

$$
H=\{a_1<a_2<\cdots\}.
$$

Then

$$
\frac{a_{m+1}}{a_m}\longrightarrow1.
\tag{47}
$$

Furthermore, setting

$$
\mathcal D_m=
\operatorname{lcm}_{i\le m}(2^{a_i}-1),
$$

we have

$$
a_{m+1}<\log_2\mathcal D_m
\qquad\text{for all sufficiently large }m.
\tag{48}
$$

#### Proof

Within frame \(j\), consider just the following two subsets of \(H\):

$$
\{g_jp:p\in\mathcal P_j\},
\tag{49}
$$

and

$$
\{g_jpq:p,q\in\mathcal P_j,\ p<q\}.
\tag{50}
$$

Let \(\eta_j\) be the supremum of the ratios of consecutive primes at or beyond \(g_j\), minus \(1\). By (46), \(\eta_j\to0\).

Consecutive values in (49) have ratio at most \(1+\eta_j\). The same bound holds for the ordered values in (50). To see this, take a nonmaximum product \(pq\), \(p<q\). If \(q\) is not the last prime of \(\mathcal P_j\), replace it by the next prime. Otherwise replace \(p\) by the next prime; this remains below \(q\) unless \(pq\) was already the maximum product. Either operation gives a larger admissible product with ratio at most \(1+\eta_j\).

The numerical ranges of (49) and (50) overlap for all sufficiently large \(j\). Their relevant endpoints are

$$
\min(49)\sim g_j^2,\qquad
\max(49)=g_jh_j,
$$

and

$$
\min(50)\sim g_j^3,\qquad
\max(50)\sim g_jh_j^2.
$$

The within-frame overlap follows from \(h_j\ge g_j^3\).

There is also overlap between successive frames. Since

$$
g_{j+1}\sim h_j,
$$

the first value in (49) for frame \(j+1\) is asymptotic to \(h_j^2\), whereas the last value in (50) for frame \(j\) is asymptotic to \(g_jh_j^2\).

Thus these anchor sets cover, by overlapping numerical ranges, every sufficiently large scale, and their multiplicative gaps tend uniformly to \(1\) as their frame indices tend to infinity. Adding the remaining elements of \(H\) cannot enlarge a gap. This proves (47).

Now let \(u<v\) be consecutive sufficiently large elements of \(H\). If they belong to different frames, \(\gcd(u,v)=1\).

If they belong to the same frame, write

$$
u=g_jd,\qquad v=g_je,\qquad d,e\mid M_j.
$$

The divisibility \(u\mid v\) would imply

$$
v/u\ge\min\mathcal P_j\longrightarrow\infty,
$$

contrary to (47). Hence some prime \(p\in\mathcal P_j\) divides \(d\) but not \(e\), and

$$
\gcd(u,v)\le u/p=o(u).
$$

Since each fixed frame is finite, the frame indices of elements tending to infinity also tend to infinity. We have proved

$$
\gcd(a_{m-1},a_m)=o(a_m).
\tag{51}
$$

The exact Mersenne gcd identity gives

$$
\gcd(2^u-1,2^v-1)=2^{\gcd(u,v)}-1.
$$

Therefore

$$
\begin{aligned}
\log_2\mathcal D_m
&\ge
\log_2\operatorname{lcm}
(2^{a_{m-1}}-1,2^{a_m}-1)\\
&>
a_{m-1}+a_m-\gcd(a_{m-1},a_m)-2\\
&=(2-o(1))a_m.
\end{aligned}
\tag{52}
$$

But (47) gives \(a_{m+1}=(1+o(1))a_m\). This proves (48). \(\square\)

In particular,

$$
\mathcal D_m\,2^{\,2-a_{m+1}}\longrightarrow\infty.
\tag{53}
$$

Thus the corpus’s sufficient LCM-height escape condition
\(\liminf_m\mathcal D_m2^{2-a_{m+1}}=0\) does not account for this host. This statement concerns that explicit LCM criterion; it does not assert that every conceivable reduced-denominator argument has been excluded.

## 7. Exact composition with the existing floor

At \(\alpha=1\), Theorem 1 recovers the activated reciprocal-summability theorem: take singleton frames

$$
F_j=\{a_j\},\qquad c_{j,d}=\mathbf1_{d=a_j}.
$$

Then (2) is exactly

$$
\sum_j\frac1{a_j}<\infty.
$$

Conversely, a finite-cost cover at \(\alpha=1\) necessarily has reciprocal-summable union. Averaging (1) gives

$$
\sum_{a\in F_j}\frac1a
\le\sum_d\frac{c_{j,d}}d,
$$

and therefore

$$
\sum_{a\in H}\frac1a
\le
\sum_j\sum_{a\in F_j}\frac1a
\le
\sum_{j,d}\frac{c_{j,d}}d<\infty.
\tag{54}
$$

Thus the passage to \(\alpha<1\) is a genuine extension, not a different notation for reciprocal summability. The complete dependency chain is

$$
\begin{gathered}
\text{positive fractional-divisor majorants of summable cost}\\
\Downarrow\quad\text{Lemma 2, uniformly in the prefix LCM}\\
\text{cofinal positive returns to the initial shifted-atom value}\\
\Downarrow\quad\text{exact rational lattice identity (23)}\\
\text{irrationality for every infinite sub-support}.
\end{gathered}
\tag{55}
$$

For the explicit \(H\), Proposition 3 and estimate (43) discharge the first line. Neither a greedy-survival assumption nor a cofinal repair assumption occurs anywhere in this chain.

The relevant repository comparisons were made at
`wcook04/plectis-erdos`, commit
`3e015b5798083379a8260a47295ea68247b94fbd`, particularly against
`problem/WeightedGcdFrameMovingCliqueCounterexample.md` and
`problem/BurstEscapeSupportIrrationality.md` under
`research_corpus/Erdos257/`.
The former supplies the obstruction being bypassed; the latter supplies the height criterion distinguished by (53). The results proved above are ordinary mathematical proofs, not newly Lean-checked declarations.



[1]: https://arxiv.org/html/2512.01739v2


---

# Retained obstruction and consumer proofs: r1

## 8. The remaining parent implication

For the launched denominator-\(21\) route, let

$$
s_R=\texttt{twentyOneEvenQuotientGreedyRemainder}(R),
\qquad
D_R=\texttt{twentyOneEvenQuotientGreedySupport}(R).
$$

The strongest applicable consumer is the cap-free normalised-defect consumer. In particular,

$$
\boxed{
\liminf_{R\to\infty}\frac{s_R}{4^R}=0
}
\tag{44}
$$

would put \(1/21\) in the Mersenne achievement set. This is weaker than requiring \(s_R\le2^R\) cofinally. The supplied source proves the corresponding compactness consumer and proves that non-membership produces the eventual affine-supercapacity branch.

For completeness, the composition is exact. Define

$$
V_R=\sum_{a\in D_R}\frac1{2^a-1},
\quad
\Phi_R=\sum_{a\in D_R}
\left\{\frac{4^R}{2^a-1}\right\},
\quad
\theta_R=\left\{\frac{4^R}{21}\right\}.
$$

The quotient-row definition gives

$$
s_R
=
4^R\left(\frac1{21}-V_R\right)+\Phi_R-\theta_R.
\tag{45}
$$

Since \(|D_R|\le R\),

$$
\left|V_R-\frac1{21}\right|
\le
\frac{s_R+R+1}{4^R}.
\tag{46}
$$

Thus (44) supplies finite achievement-set points tending to \(1/21\). Closedness gives membership. The supplied finite-support exclusion then makes every such representation infinite, producing a counterexample to universal irrationality. 

**Equation (44) is not proved here.**

The new weighted theorem does not silently discharge it. In a hypothetical fatal branch, the selected support is cofinite. For every fixed finite prime set \(\mathcal P\), that support contains all sufficiently large integers congruent to \(1\) modulo \(\prod_{p\in\mathcal P}p\). On those integers \(h(a)=1\), so their contribution to (1) is

$$
\frac1{(b-1)a},
$$

whose sum diverges. Hence the fatal cofinite support lies outside the new theorem’s hypotheses.

### The minimal affine failure certificate

The literal eventual recurrence is

$$
s_{R+1}
=
4s_R+p_R-\ell_R-(2^{R+1}+1),
\tag{47}
$$

where

$$
p_R=\left\lfloor\frac{4(4^R\bmod21)}{21}\right\rfloor
$$

and

$$
\ell_R=
2\#\{a\in D_R:a\mid2R+1\}
+
\#\{a\in D_R:a\mid2R+2\}.
\tag{48}
$$

This is the stipulated affine object. 

Set

$$
\eta_R=s_R-2^R.
$$

Then

$$
\eta_{R+1}=4\eta_R+p_R-\ell_R-1.
\tag{49}
$$

The recurrence, the actual divisor-load formula, and a cofinite support word do **not** by themselves forbid permanent positive \(\eta_R\). Take the alternative initial data

$$
D_R=\{5,6,\ldots,R\}\quad(R\ge8),
\qquad
\eta_8=1.
$$

At \(R=8\), \((p_R,\ell_R)=(3,1)\), so \(\eta_9=5\). At \(R=9\), \((p_R,\ell_R)=(0,1)\), so \(\eta_{10}=18\).

For every \(R\ge10\),

$$
\ell_R\le3|D_R|=3(R-4).
$$

Consequently,

$$
\eta_R\ge R
\implies
\eta_{R+1}
\ge4R-3(R-4)-1
=R+11
\ge R+1.
$$

Induction proves

$$
\eta_R>0\qquad(R\ge8).
\tag{50}
$$

This is an all-depth countermodel to the proposed local inference, not a counterexample to Erdős 257: its initial state is not the canonical denominator-\(21\) initial history.

The same distinction appears directly in the actual fatal branch. There, eventual alignment identifies \(D_R\) with prefixes of its cofinite selected support \(A\). Equation (45) gives

$$
\lim_{R\to\infty}\frac{s_R-2^R}{4^R}
=
\frac1{21}-S_2(A).
\tag{51}
$$

Fatality makes the right side strictly positive. The free exponential coefficient is precisely the unrepresented mass. Its positivity is not a contradiction.

Therefore an argument closing (44) must use information that excludes this positive coefficient for the **actual canonical history**. Bounds on the eventual pulse, cofinite continuation, or affine growth alone do not do so.

---

### Proof status and corpus composition

The unconditional advance is Theorem 1, together with its nested-filtration form and hereditary stability under reciprocal-summable additions. It strictly extends the supplied reciprocal-summability regime and proves the original irrationality conclusion for the reciprocal-divergent family in (32) and every infinite subset of it.

The imported mathematical dependencies were read at commit
`3e015b5798083379a8260a47295ea68247b94fbd` of `wcook04/plectis-erdos`: the shifted-atom framework in `shared_lean/ReciprocalSupportIrrationality.lean`, the denominator comparison in `problem/BurstEscapeSupportIrrationality.md`, and the canonical quotient and compactness consumers in `TwentyOneQuotientGreedy.lean`. No external literature theorem is required for the new proof.

These are ordinary mathematical proofs; the new weighted theorem has **not** been checked in Lean.

**The weighted-support theorem is unconditional. The vanishing of the canonical denominator-\(21\) normalised defect, and the unrestricted parent theorem, remain unproved in this response.**


---

# Retained obstruction and consumer proofs: r8

## 8. The remaining implication and the minimal failure certificates

Let \(\mathscr C\) be the class of supports admitting the cover in Theorem 1 for at least one \(0<\alpha\le1\). What has now been proved is

$$
A\in\mathscr C,\quad A\text{ infinite}
\quad\Longrightarrow\quad
S_A(2)\notin\mathbb Q.
\tag{56}
$$

The single remaining implication for completing the universal direction by this partition is

$$
\boxed{\quad
A\notin\mathscr C,\quad A\text{ infinite}
\quad\Longrightarrow\quad
S_A(2)\notin\mathbb Q.
\quad}
\tag{57}
$$

I have not proved (57), nor constructed a rational counterexample in its domain. Three exact facts prevent treating the present argument as a complete proof.

### Finite-cost covers are not forced by infinitude or reciprocal divergence

The set of all primes admits no finite-cost cover of the kind in Theorem 1, for any \(0<\alpha\le1\).

Suppose otherwise. Since

$$
\sum_jc_{j,1}<\infty,
$$

only finitely many \(j\) have \(c_{j,1}\ge1/2\). Their finite frames contain only finitely many primes.

For every remaining prime \(p\), choose a frame \(F_{j(p)}\) containing \(p\). Evaluating (1) at \(n=p\) gives

$$
1\le f_{F_{j(p)}}(p)^\alpha
\le c_{j(p),1}+c_{j(p),p},
$$

so \(c_{j(p),p}>1/2\). Distinct primes give distinct coefficient positions, whence

$$
\sum_{j,d}\frac{c_{j,d}}d
\ge
\frac12\sum_{\text{all but finitely many }p}\frac1p
=\infty,
$$

a contradiction.

This is an obstruction to the **cover hypothesis**, not a rational Mersenne counterexample.

### Close returns cannot be asserted for every support

For \(A=\mathbb N_{>0}\) and \(b=2\),

$$
\begin{aligned}
U_{A,2}(n)-S_A(2)
&\ge
(2^n-1)\sum_{a>n}\frac1{2^a-1}\\
&>
(2^n-1)\sum_{a>n}2^{-a}\\
&=1-2^{-n}\ge\frac12
\qquad(n\ge1).
\end{aligned}
\tag{58}
$$

Thus the small-positive-return property used in Theorem 1 is strictly stronger than the desired irrationality conclusion. Extending it universally is not a viable way to discharge (57).

### Arbitrary fractional incidence counts do not have positive Möbius coefficients

For \(F=\{2,3\}\), the divisor expansion of \(f_F(n)^\alpha\) has coefficients \(1\) at \(2\) and \(3\), but its coefficient at \(6\) is

$$
2^\alpha-2<0\qquad(0<\alpha<1).
\tag{59}
$$

Consequently, one cannot apply Lemma 2 to a general Möbius expansion while silently assuming positivity. Complete divisor frames have the positive factorisation (26); arbitrary supports need not.

These certificates identify the precise limitation. The new mechanism controls concentrated incidence through positive fractional moments and retains all gcd overlap in the progression average. It does not establish the global arithmetic noncollapse needed for supports outside that class, and it does not discharge the corpus’s rational-target survival producers. **The unrestricted Erdős 257 endpoint therefore remains unproved in this response.**


---

# Retained obstruction and consumer proofs: r5

## 1. The existing defect coordinate

Put

$$
w_a=\frac1{2^a-1}.
$$

For a real target \(0\le x<1\), let

$$
r_0=x,\qquad
b_n=\mathbf 1_{\{r_{n-1}\ge w_n\}},\qquad
r_n=r_{n-1}-b_nw_n,
$$

and write

$$
A=\{n\ge1:b_n=1\}.
$$

Since \(x<1=w_1\), we have \(1\notin A\).

Use the selected-divisor coefficient and the binary prefix numerator

$$
f(n)=\#\{a\in A:a\mid n\},
\qquad
P_N=\sum_{m=1}^{N}f(m)2^{N-m}.
$$

The target floor and its defect are

$$
t_N=\lfloor 2^Nx\rfloor,\qquad Q_N=t_N-P_N,
$$

and the target digit is

$$
\varepsilon_n=t_n-2t_{n-1}\in\{0,1\}.
$$

These are the corpus’s actual rational-greedy defect coordinates when \(x\) is rational; in particular, at \(x=4/9\) they are precisely `fourNinthsGreedyDefect` and the corresponding shifted floor-bit indexing. The nonnegativity and recurrence below are already established there.

The identities needed here are

$$
\boxed{Q_N\ge0}
\tag{1}
$$

and

$$
\boxed{Q_n=2Q_{n-1}+\varepsilon_n-f(n).}
\tag{2}
$$

For completeness, the reason (1) does **not** assume survival is

$$
P_N
=
\sum_{\substack{a\in A\\a\le N}}
\left\lfloor\frac{2^N}{2^a-1}\right\rfloor
\le
\left\lfloor
2^N\sum_{\substack{a\in A\\a\le N}}w_a
\right\rfloor
\le \lfloor2^Nx\rfloor.
$$

The final inequality uses only the defining greedy condition \(r_N\ge0\). It does not use the unproved upper bound of the remainder by the available tail.

Define the one-step defect increment

$$
\Delta_n=Q_n-Q_{n-1}.
$$

A repair at rank \(n\) means \(\Delta_n\le0\).

Applying (2) twice gives the exact identity

$$
\boxed{
4\Delta_n
=
Q_{n+1}+f(n+1)-2f(n)
+2\varepsilon_n-\varepsilon_{n+1}.
}
\tag{3}
$$

Consequently,

$$
\boxed{
4\Delta_n\ge f(n+1)-2f(n)-1.
}
\tag{4}
$$

The successor \(n+1\) is essential. A large selected-divisor coefficient there forces a large enough incoming defect to finance it. When the coefficient at \(n\) is bounded, that financing forces an increase at \(n\).

## 2. Prime-row amplification

### Theorem 1 — Finite selections force infinitely many prime-cofactor increases

Fix \(M\ge1\), and put

$$
c_M=f(M)+\tau(M),
$$

where \(\tau\) is the ordinary divisor-counting function.

Let \(F\subseteq A\) be a finite set such that

$$
\gcd(a,M)=1\qquad(a\in F),
$$

and write \(K=|F|\). Then there are arbitrarily large primes \(p\) for which

$$
\boxed{
4\Delta_{Mp}\ge K-2c_M-1.
}
\tag{5}
$$

More precisely, let

$$
L=\operatorname{lcm}\{a:a\in F\}.
$$

Every sufficiently large prime in the explicitly specified residue class

$$
\boxed{Mp\equiv-1\pmod L}
\tag{6}
$$

satisfies (5).

#### Proof

We may suppose \(F\ne\varnothing\), since the applications all have \(K>0\).

The coprimality hypotheses give \(\gcd(M,L)=1\). Thus there is a residue \(c\pmod L\) satisfying

$$
Mc\equiv-1\pmod L.
$$

This residue is a unit modulo \(L\): any common divisor of \(c\) and \(L\) would divide both \(Mc\) and \(Mc+1\).

Dirichlet’s theorem therefore supplies arbitrarily large primes

$$
p\equiv c\pmod L.
$$

The exact external theorem used is the existence of primes beyond every cutoff in a coprime residue class; it is also recorded in mathlib as `Nat.forall_exists_prime_gt_and_modEq`. ([Lean Community][1])

Choose such a prime with

$$
p>\max(M,\max F).
$$

Every \(a\in F\) divides \(Mp+1\). Since every member of \(F\) is an actual, permanently selected exponent,

$$
f(Mp+1)\ge K.
\tag{7}
$$

Because \(p\nmid M\), the divisors of \(Mp\) split disjointly into

$$
\{d:d\mid M\}
\quad\text{and}\quad
\{pd:d\mid M\}.
$$

Hence

$$
f(Mp)
=
f(M)+\#\{d\mid M:pd\in A\}
\le f(M)+\tau(M)=c_M.
\tag{8}
$$

Substituting (7) and (8) into (4) proves (5). No assumption about membership of \(x\) in the achievement set has been made. ∎

### Corollary 1 — Infinite support forces unbounded prime jumps

If \(A\) is infinite, then for every integer \(H\ge1\) and every cutoff \(X\), there is a prime \(p>X\) such that

$$
\boxed{Q_p-Q_{p-1}\ge H.}
\tag{9}
$$

#### Proof

Take \(M=1\). Since \(1\notin A\),

$$
c_1=f(1)+\tau(1)=1.
$$

Choose \(F\subseteq A\) with

$$
|F|=4H+3.
$$

Theorem 1 gives arbitrarily large primes satisfying

$$
4\Delta_p\ge (4H+3)-2-1=4H.
$$

Thus \(\Delta_p\ge H\). ∎

This is a global consequence of genuine support persistence. Once the finitely many exponents in \(F\) have been selected, their simultaneous future incidence can be forced at arbitrarily large ranks. Their effect cannot be discarded by retaining only the bounded divisor supply at the preceding prime.

### Corollary 2 — Bounded prime jumps detect finite greedy support

For the actual greedy orbit of \(0\le x<1\), the following are equivalent:

$$
A\text{ is finite};
\qquad
\{Q_p-Q_{p-1}:p\text{ prime}\}\text{ is bounded above}.
\tag{10}
$$

#### Proof

The reverse implication is Corollary 1.

Suppose \(A=F\) is finite. Then necessarily

$$
x=\sum_{a\in F}w_a.
\tag{11}
$$

Indeed, a positive remaining difference after the last selected exponent would eventually exceed a later weight, forcing another selection.

For each \(a\ge2\),

$$
\frac{2^N}{2^a-1}
=
\left\lfloor\frac{2^N}{2^a-1}\right\rfloor
+
\frac{2^{N\bmod a}}{2^a-1},
$$

and the last term lies strictly between zero and one. Therefore

$$
Q_N
=
\left\lfloor
\sum_{a\in F}\frac{2^{N\bmod a}}{2^a-1}
\right\rfloor,
\tag{12}
$$

so \(Q_N<|F|\). In particular, all defect increments are bounded above. ∎

### Theorem 2 — Exact rigidity of eventual repair at every prime

For \(0\le x<1\), the following are equivalent:

$$
\boxed{
\exists X\ \forall p>X\text{ prime},\quad Q_p\le Q_{p-1};
}
\tag{13}
$$

$$
\boxed{
x=0
\quad\text{or}\quad
x=\frac1{2^a-1}\text{ for some }a\ge2.
}
\tag{14}
$$

#### Proof

Assume (13). The finitely many smaller prime increments do not affect boundedness, so Corollary 2 implies that \(A=F\) is finite. Equation (11) follows.

Suppose \(|F|\ge2\), and set

$$
L=\operatorname{lcm}(F).
$$

Choose an arbitrarily large prime

$$
p\equiv-1\pmod L.
$$

For every \(a\in F\),

$$
(p-1)\bmod a=a-2,
\qquad
p\bmod a=a-1.
$$

Put

$$
\alpha=\sum_{a\in F}\frac{2^{a-2}}{2^a-1}.
$$

Each summand is strictly greater than \(1/4\), hence

$$
\alpha>\frac{|F|}{4}\ge\frac12.
$$

By (12),

$$
Q_{p-1}=\lfloor\alpha\rfloor,
\qquad
Q_p=\lfloor2\alpha\rfloor.
$$

For every \(\alpha>1/2\),

$$
\lfloor2\alpha\rfloor-\lfloor\alpha\rfloor\ge1.
$$

Thus \(\Delta_p\ge1\) at arbitrarily large primes, contradicting (13).

Therefore \(|F|\le1\), which gives (14).

Conversely, for \(x=0\) the support is empty and \(Q_N=0\). For \(x=w_a\), greedy skips all smaller exponents, selects \(a\), and thereafter has zero remainder. Directly,

$$
P_N=\lfloor2^Nx\rfloor
$$

for every \(N\), so again \(Q_N=0\). ∎

## 3. An unconditional failure of the actual modulus-\(420\) producer

Now fix

$$
x=\frac49.
$$

The corpus’s four-parent load is

$$
U(n)=
\#\left(
\{a\in A:a\mid n/2\}
\cup
\{a\in A:a\mid n/3\}
\cup
\{a\in A:a\mid n/5\}
\cup
\{a\in A:a\mid n/7\}
\right),
\qquad 420\mid n.
\tag{15}
$$

This is exactly `fourNinthsTetraprimeUnionLoad`, not a replacement load.

The proposed all-depth producer is

$$
Q_{420k-1}\le U(420k)\qquad(k\ge1).
\tag{16}
$$

Its prime-cofactor restriction is also explicitly packaged in the source as `FourNinthsMultiple420LargePrimeBoundary`.

### Theorem 3 — Cofinal actual violations at prime cofactors

For the actual \(4/9\)-greedy orbit, there are arbitrarily large primes \(p\) such that

$$
\boxed{Q_{420p}-Q_{420p-1}\ge2}
\tag{17}
$$

and

$$
\boxed{Q_{420p-1}-U(420p)\ge3.}
\tag{18}
$$

Consequently, both `FourNinthsMultiple420TetraprimeRepair` and `FourNinthsMultiple420LargePrimeBoundary` are false. Even their versions restricted to all sufficiently large relevant rows are false.

### The finite certificate

The proof needs only the actual greedy decisions through rank \(727\).

Exact integer enclosure verifies that there are \(356\) selections through that rank, including the following eighty exponents coprime to \(420\):

$$
\begin{aligned}
F=\{&
13,17,23,37,43,61,71,73,89,101,103,107,\\
&121,127,131,137,139,157,167,179,191,197,211,221,\\
&223,229,247,251,253,257,289,299,307,311,323,341,\\
&349,353,359,367,377,389,391,419,439,443,449,451,\\
&479,499,503,517,523,527,529,533,541,557,559,569,\\
&571,577,587,599,611,617,629,641,647,649,659,671,\\
&677,689,697,701,703,709,713,727\}.
\end{aligned}
\tag{19}
$$

The same calculation verifies

$$
A\cap\{d:d\mid420\}
=
\{2,4,5,7,12,20,21,28,30,60,105,210,420\}.
\tag{20}
$$

In particular,

$$
f(420)=13,\qquad 420\in A.
\tag{21}
$$

Here is the complete integer verifier. I executed it with the displayed parameters; all \(727\) decisions were certified without an ambiguous comparison.

```python
from math import gcd, lcm

def certificate():
    H, N = 2048, 727
    S = 1 << H

    # Invariant: lo / S <= actual greedy remainder <= hi / S.
    lo, rem = divmod(4 * S, 9)
    hi = lo + int(rem != 0)
    A = set()

    for n in range(1, N + 1):
        m = (1 << n) - 1

        if lo * m >= S:
            # The actual remainder is at least 1/m: certify a take.
            wlo, rem = divmod(S, m)
            whi = wlo + int(rem != 0)
            lo -= whi
            hi -= wlo
            A.add(n)

        elif hi * m < S:
            # The actual remainder is strictly below 1/m: certify a skip.
            pass

        else:
            # No numerical guess is permitted.
            raise ArithmeticError(("ambiguous decision", n))

        assert 0 <= lo <= hi

    F = {a for a in A if gcd(a, 420) == 1}
    D = {a for a in A if 420 % a == 0}

    assert len(A) == 356
    assert len(F) == 80 and max(F) == 727
    assert D == {
        2, 4, 5, 7, 12, 20, 21, 28, 30, 60, 105, 210, 420
    }
    assert hi - lo == 357

    L = lcm(*F)
    c = (-pow(420, -1, L)) % L
    assert gcd(c, L) == 1
    assert (420 * c + 1) % L == 0

    return len(A), len(F), len(D), hi - lo

print(certificate())
# (356, 80, 13, 357)
```

The enclosure argument proves the verifier’s scope. Initially,

$$
\frac{\mathrm{lo}}{S}\le\frac49\le\frac{\mathrm{hi}}S.
$$

A take is made only when the lower endpoint is at least the exact weight. A skip is made only when the upper endpoint is strictly smaller than that weight. On a take, the subtracted weight has the certified enclosure

$$
\frac{\mathrm{wlo}}S\le\frac1m\le\frac{\mathrm{whi}}S,
$$

which gives the displayed updated enclosure. Induction therefore identifies every recorded bit with the actual greedy bit. The finite calculation certifies precisely the stated prefix facts; it makes no assumption about survival beyond rank \(727\).

### Proof of Theorem 3

Let

$$
L=\operatorname{lcm}(F),
\qquad
420c\equiv-1\pmod L.
$$

Every member of \(F\) is coprime to \(420\), so \(c\) is a unit modulo \(L\). There are arbitrarily large primes

$$
p\equiv c\pmod L.
$$

Take \(p>727\), and put

$$
n=420p.
$$

All eighty certified exponents divide \(n+1\), so

$$
f(n+1)\ge80.
\tag{22}
$$

On the other hand,

$$
420=2^2\cdot3\cdot5\cdot7,
\qquad
\tau(420)=3\cdot2^3=24.
$$

Using (21) and the disjoint divisor decomposition at a prime cofactor,

$$
f(n)\le f(420)+\tau(420)=13+24=37.
\tag{23}
$$

Because \(n\equiv0\pmod6\),

$$
\left\{\frac{4\,2^{n-1}}9\right\}=\frac29,
\qquad
\left\{\frac{4\,2^n}9\right\}=\frac49.
$$

Both following binary floor digits are zero:

$$
\varepsilon_n=\varepsilon_{n+1}=0.
\tag{24}
$$

Thus (3), (22), and (23) give

$$
4\Delta_n
=
Q_{n+1}+f(n+1)-2f(n)
\ge80-74=6.
$$

Since \(\Delta_n\) is an integer,

$$
\Delta_n\ge2,
$$

proving (17).

To obtain the exact causal inequality, observe that among the divisors of \(420p\), the only ones absent from the union of the four parent-divisor sets in (15) are

$$
420\quad\text{and}\quad420p.
\tag{25}
$$

Indeed, every divisor has the form \(d\) or \(pd\), with \(d\mid420\). Unless it is one of the two displayed exceptions, its complementary divisor contains one of \(2,3,5,7\), placing it in the corresponding parent column.

Since \(420\in A\), equation (25) gives

$$
f(n)-U(n)=1+b_n.
\tag{26}
$$

Using \(\varepsilon_n=0\) in (2),

$$
\Delta_n=Q_{n-1}-f(n).
$$

Therefore

$$
Q_{n-1}-U(n)
=
\Delta_n+f(n)-U(n)
=
\Delta_n+1+b_n
\ge3.
$$

This proves (18). ∎

The finite computation and the infinite conclusion play different roles. The computation supplies eighty immutable selections and the exact coefficient at \(420\). Dirichlet’s theorem supplies the unbounded family of ranks. Nonnegativity of the **actual successor defect** supplies the inequality. No future support word has been manufactured.

## 4. What the result does—and does not—do to the parent proof

The modulus-\(420\) producer was stronger than the actual endpoint requirement. Its failure does not disprove \(4/9\)-membership. The existing consumer requires only

$$
\boxed{
\forall K\ \exists n\ge K:\quad Q_n\le Q_{n-1}.
}
\tag{27}
$$

The corpus proves that this cofinal-repair property yields an **infinite** support with sum exactly \(4/9\), using the established exclusion of finite \(4/9\)-representations.

It is useful to make the remaining distinction exact.

### Proposition — Cofinal repairs are equivalent to greedy survival

For the actual greedy orbit of any \(0\le x<1\),

$$
\boxed{
\lim_{N\to\infty}r_N=0
\quad\Longleftrightarrow\quad
\text{repairs occur beyond every cutoff}.
}
\tag{28}
$$

#### Proof

Since the remainders decrease and are nonnegative, let

$$
\delta=\lim_{N\to\infty}r_N.
$$

Suppose \(\delta>0\). The finite-prefix floor identity gives

$$
Q_N
=
2^Nr_N+
\sum_{\substack{a\in A\\a\le N}}
\frac{2^{N\bmod a}}{2^a-1}
-\{2^Nx\}
\ge 2^N\delta-1.
$$

Also

$$
f(N+1)\le\tau(N+1)\le2\sqrt{N+1}.
$$

Consequently, (2) implies

$$
Q_{N+1}-Q_N
\ge2^N\delta-1-2\sqrt{N+1}>0
$$

for all sufficiently large \(N\). Hence repairs are not cofinal.

Conversely, suppose \(\delta=0\). Then

$$
x=\sum_{a\in A}w_a
=\sum_{m\ge1}f(m)2^{-m}.
$$

The nonnegative double sum justifies the Lambert rearrangement. Subtracting the binary prefix gives

$$
Q_N+\{2^Nx\}
=
\sum_{k\ge1}f(N+k)2^{-k}.
$$

Using \(f(m)\le2\sqrt m\) and

$$
\sqrt{N+k}\le\sqrt N+k,
$$

we obtain

$$
Q_N
\le
2\sum_{k\ge1}(\sqrt N+k)2^{-k}
=
2\sqrt N+4.
\tag{29}
$$

If repairs ceased, the integer sequence \(Q_N\) would increase by at least one at every sufficiently late step. It would then grow at least linearly, contradicting (29). ∎

Thus the outstanding implication on this route remains precisely

$$
\boxed{
x=\frac49,\quad\text{actual greedy initial condition}
\quad\Longrightarrow\quad
\forall K\ \exists n\ge K:\ Q_n\le Q_{n-1}.
}
\tag{30}
$$

I have not established (30). Theorem 3 disproves a proposed sufficient producer for it, not the implication itself. In particular,

$$
\forall K\ \exists n\ge K:\Delta_n>0
$$

does not contradict

$$
\forall K\ \exists n\ge K:\Delta_n\le0.
$$

The dependency chain that would decide the original problem is still

$$
\text{actual \(4/9\) initial condition}
\ \xRightarrow{\ \text{unproved}\ }\ 
\text{cofinal repairs}
\ \xRightarrow{\ \text{established consumer}\ }\ 
\exists A\text{ infinite},\quad
\sum_{a\in A}w_a=\frac49.
$$

The final implication is available; the first is not discharged by the results above.

## 5. Two exact failure certificates for tempting continuations

### Cofinal increases do not imply non-membership, even for a rational target

Take

$$
x=w_2+w_3=\frac{10}{21}.
$$

Its actual greedy support is \(\{2,3\}\). Formula (12) gives

$$
Q_N=
\begin{cases}
1,&N\equiv5\pmod6,\\
0,&N\not\equiv5\pmod6.
\end{cases}
\tag{31}
$$

Hence there are infinitely many positive increments, including at every prime \(p\equiv5\pmod6\), and infinitely many repairs. Nevertheless the target is represented exactly.

This is why an infinite family of violations of (16) cannot be promoted to failure of \(4/9\)-membership.

### Even the complete selected-divisor word does not determine survival without the target remainder

Let

$$
T_2=\sum_{n\ge3}w_n.
$$

For \(n\ge4\),

$$
w_n\le\frac{16}{15}\,2^{-n},
$$

with strict inequality once \(n>4\). Thus

$$
T_2
<
\frac17+\frac{2}{15}
=
\frac{29}{105}
<
\frac3{10}
<
\frac13=w_2.
\tag{32}
$$

Consider two targets:

$$
x_0=T_2,\qquad x_1=\frac3{10}.
$$

For **both** targets, the actual greedy support is exactly

$$
A=\{3,4,5,\ldots\}.
$$

For \(x_0\), this follows by taking the complete remaining tail at every step. For \(x_1\), after skipping ranks \(1\) and \(2\), the remainder exceeds the entire available tail by the fixed positive amount

$$
\delta=\frac3{10}-T_2.
$$

Every later rank is therefore taken, and that positive difference persists.

The two orbits have identical selections, identical divisor coefficients, and identical selected-divisor ancestry at every depth. But one represents its target and the other does not:

$$
r_N(x_0)\longrightarrow0,
\qquad
r_N(x_1)\longrightarrow\delta>0.
$$

Accordingly, a proof using divisor supply while losing its coupling to the target remainder cannot establish (30). This example is a failure certificate for that inference, not a counterexample to Erdős 257.

---

The results proved here are the prime-row amplification theorem, the associated finite-support and single-weight rigidity statements, and the unconditional cofinal falsification of the actual modulus-\(420\) producer. The finite certificate was executed with exact integer arithmetic; no Lean verification of these new results is claimed.

The repository inputs used in that argument are the pinned `FourNinthsCofinalRepairConsumer.lean` and `FourNinthsPrimorialRepair.lean` sources at commit `3e015b5798083379a8260a47295ea68247b94fbd`. The only external theorem used materially is Dirichlet’s theorem in the coprime-residue form stated above.

**Neither universal irrationality nor an infinite rational-support counterexample has been established in this response.**

[1]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/PrimesInAP.html "https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/PrimesInAP.html"
