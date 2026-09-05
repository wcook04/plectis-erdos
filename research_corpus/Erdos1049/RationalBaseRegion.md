<!-- SPDX-FileCopyrightText: 2026 Will Cook -->
<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# An explicit rational-base region for the Lambert series

Write \(F(x)=\sum_{m\ge1}(x^m-1)^{-1}\), for real \(x>1\).

**Theorem.** If coprime integers \(a>b\ge1\) satisfy
\[
 \frac{\log b}{\log a}<\theta_*=\frac{C_0}{C_1},\qquad
 C_1=\frac{1091}{2},\quad C_0=266-\frac3{\pi^2}(225-J),
\]
then \(F(a/b)\) is irrational. Here \(J\) is the convergent sum defined in
Section 4. In particular, \(F((31/4)^r)\) is irrational for every integer
\(r\ge1\), because \(\log4/\log31<81/200<\theta_*\).

The approximate value \(0.405683021384\) of \(\theta_*\) is descriptive;
the proof uses exact definitions. The base \(3/2\) remains outside the region.
This is an ordinary analytic proof using published polynomial identities,
not an end-to-end Lean theorem. The
[exact parameter checker](../../experiments/erdos1049_region_parameters.py)
certifies the finite floor partition and parameter inequalities, not the
analytic argument or polynomial integrality.

## 1. The polynomial source input

Use W. Zudilin, *Heine's basic transform and a permutation group for
q-harmonic series*, Acta Arithmetica 111 (2004), 153–164
([publisher PDF](https://www.impan.pl/shop/en/publication/transaction/download/product/82435)).
Its main numerical theorem assumes an integer base. The input here is the
polynomial calculation in its proof, before evaluation.

For \(n\ge1\), put
\[
 (a_0,a_1,a_2;b_n)=(14n+1,12n+1,14n+1;27n+2),\qquad q=x^{-1}.
\]
With \((z;q)_k=\prod_{j=0}^{k-1}(1-zq^j)\), set
\[
 R_n(T)=\frac{(qT;q)_{a_1-1}}{(q;q)_{a_1-1}}
         \frac{(q;q)_{b_n-a_2-1}}{(q^{a_2}T;q)_{b_n-a_2-1}}T^{a_0},
 \qquad H_n(x)=\sum_{t\ge0}R_n(q^t).
\]
For \(a_2\le k\le b_n-1\), define
\[
 E_k=\frac{a_1(a_1-1)-(b_n-a_2)(b_n-a_2-1)+(b_n-k)(b_n-k-1)}2,
\]
\[
 A_k=(-1)^{a_1+a_2+k+1}x^{E_k}
       {k-1\brack a_1-1}_x{b_n-a_2-1\brack b_n-k-1}_x,
\]
where the brackets are Gaussian binomial polynomials. The partial-fraction
identities (8)–(11), pp. 156–157, give \(H_n=A_nF-B_n\), with
\[
 A_n=\sum_{k=a_2}^{b_n-1}A_kx^{a_0k},
\]
\[
 B_n=\sum_{k=a_2}^{b_n-1}A_kx^{a_0k}
 \left(\sum_{l=1}^{k-a_1}\frac1{x^l-1}
       +\sum_{j=1}^{a_0-1}\frac{x^{-j(k-a_1)}}{x^j-1}\right).
\]
These identities hold for real \(x>1\).

Let \(\Phi_l\) be the cyclotomic polynomial, and put
\[
 D_n=\prod_{l=1}^{15n}\Phi_l,\quad
 \Omega_n=\prod_{l=2}^{15n}\Phi_l^{\nu_l},\quad M_n=266n^2+34n+1,
\]
where
\[
 \nu_l=\max\{0,\lfloor14n/l\rfloor+\lfloor13n/l\rfloor
 -\lfloor12n/l\rfloor-\lfloor15n/l\rfloor,\,
 2\lfloor14n/l\rfloor-\lfloor13n/l\rfloor-\lfloor15n/l\rfloor\}.
\]
The polynomial conclusion of Lemmas 3–5 and 7, especially (16), (21)–(24), is
\[
 U_n=x^{-M_n}D_nA_n/\Omega_n\in\mathbb Z[x],\qquad
 V_n=x^{-M_n}D_nB_n/\Omega_n\in\mathbb Z[x].                 \tag{1}
\]

Here the distinction between a polynomial and its value is essential.
Lemma 4 derives powers of the polynomial \(x\) from explicit
Gaussian-binomial formulas. Lemma 7 compares the six Heine-transform images,
takes cyclotomic orders using (5), and cancels factors coprime to \(x\).
These operations occur in the polynomial ring: its monic irreducible factors
can be cancelled by Gauss's lemma. Display (24) distinguishes this polynomial
inclusion from the subsequent integer evaluation. No rational-base
denominator clearing is assumed in (1).

If the source is read as the inclusion
\(x^{-M_n}D_n\Omega_n^{-1}H_n\in\mathbb Z[x]F+\mathbb Z[x]\),
its coefficients are uniquely (1). Indeed,
\[
 F(1+\varepsilon)\asymp\varepsilon^{-1}\log(1/\varepsilon)
 \quad(\varepsilon\downarrow0),
\]
so \(F\) is not a rational function. For both bounds, split at
\(m\le1/\varepsilon\), where
\(m\varepsilon\le(1+\varepsilon)^m-1\le e\,m\varepsilon\),
and bound the remaining geometric tail by \(O(1/\varepsilon)\).
This growth cannot be an integer-order pole or zero. Two distinct rational
coefficient representations would express \(F\) as a rational function.

## 2. The actual degree determines the clearing cost

The degree of the \(k\)-th summand of \(A_n\) is
\[
 d_k=a_0k+E_k+(a_1-1)(k-a_1)+(b_n-k-1)(k-a_2).
\]
Successive degrees differ by \(40n+1-k>0\). The final summand therefore
cannot cancel, and
\[
 K_n=\deg A_n=(1091n^2+81n+2)/2,\qquad K_n/n^2\longrightarrow C_1.
\]
Every denominator in \(B_n\) divides \(D_n\), since its index is at most
\(15n\). Division by it lowers the degree by at least one; the additional
negative powers of \(x\) do not raise it. Thus
\[
 \deg U_n=W_n:=K_n-M_n+\sum_{l\le15n}\varphi(l)
                       -\sum_{l\le15n}\nu_l\varphi(l),\qquad
 \deg V_n\le W_n-1.                                      \tag{2}
\]
Consequently \(\widehat U_n=b^{W_n}U_n(a/b)\) and
\(\widehat V_n=b^{W_n}V_n(a/b)\) are integers.

## 3. Positive forms and their size

Set \(\Lambda_n=x^{-M_n}D_n\Omega_n^{-1}H_n=U_nF-V_n\).
Every factor of \(R_n(q^t)\) is positive. Each \(\Phi_l(x)\) is positive for
\(x>1\), by pairing conjugate roots and treating \(x-1,x+1\) separately.
Hence \(\Lambda_n(x)>0\).

Put \(P=(q;q)_\infty>0\). Each finite Pochhammer product in \(R_n(q^t)\)
lies between \(P\) and \(1\). Therefore
\[
 P^2q^{a_0t}\le R_n(q^t)\le P^{-2}q^{a_0t},\qquad
 P^2\le H_n(x)\le P^{-2}/(1-q^{a_0}),
\]
and \(\log H_n(x)=O_x(1)\). Möbius inversion gives
\[
 \log\Phi_l(x)=\varphi(l)\log x+
          \sum_{d\mid l}\mu(l/d)\log(1-x^{-d}).
\]
The correction has magnitude at most \(\tau(l)|\log(1-x^{-1})|\).
Since \(\nu_l\in\{0,1\}\), summing to \(15n\) costs \(O_x(n\log n)\), so
\[
 \log\Lambda_n(x)=-(K_n-W_n)\log x+o(n^2).                 \tag{3}
\]

## 4. The limiting constant

Define \(\psi_1(u)=\sum_{k\ge0}(k+u)^{-2}\). The 1-periodic function
\[
 \omega(y)=\max\{0,\lfloor14y\rfloor+\lfloor13y\rfloor
 -\lfloor12y\rfloor-\lfloor15y\rfloor,\,
 2\lfloor14y\rfloor-\lfloor13y\rfloor-\lfloor15y\rfloor\}
\]
is one on the following half-open intervals in \([0,1)\), zero elsewhere:

~~~
[1/14,1/12)  [1/7,1/6)    [3/14,1/4)   [2/7,1/3)
[5/14,2/5)   [3/7,7/15)   [1/2,8/15)   [4/7,3/5)
[9/14,2/3)   [5/7,11/15)  [11/14,4/5)  [6/7,13/15)
[13/14,14/15)
~~~

Partition at fractions with denominators 12, 13, 14, and 15: all floors are
right-continuous and constant on each cell. The exact checker verifies the
claimed values on every cell. Set
\[
 J=\sum_{[u,v)}(\psi_1(u)-\psi_1(v)).
\]
The classical estimate
\(\Phi(y):=\sum_{l\le y}\varphi(l)=3y^2/\pi^2+O(y\log y)\) implies
\[
 n^{-2}\sum_{\{n/l\}\in[u,v)}\varphi(l)
 \longrightarrow\frac3{\pi^2}\sum_{k\ge0}
                  ((k+u)^{-2}-(k+v)^{-2}).
\]
Indeed, the condition partitions \(l\) into
\((n/(k+v),n/(k+u)]\). Apply the estimate on the finitely many blocks
\(k\le L\). The other blocks lie below \(n/L\) and contribute \(O(n^2/L^2)\).
First let \(n\to\infty\), then \(L\to\infty\).
Since \(\nu_l=\omega(n/l)\), (2) gives
\[
 (K_n-W_n)/n^2\longrightarrow266-3(225-J)/\pi^2=C_0.        \tag{4}
\]

## 5. Irrationality and the explicit base

The positive integer linear form
\[
 \widehat\Lambda_n=b^{W_n}\Lambda_n(a/b)
                 =\widehat U_nF(a/b)-\widehat V_n
\]
satisfies, by (2)–(4),
\[
 n^{-2}\log\widehat\Lambda_n\longrightarrow C_1\log b-C_0\log a.
\]
The limit is negative in the asserted region. Rationality \(F(a/b)=P/Q\)
would make \(Q\widehat\Lambda_n\) a positive integer tending to zero,
a contradiction.

Keeping only the \(k=0\) terms in \(J\) gives
\[
 J\ge2015640690251/25971865920.
\]
Together with \(\pi>157/50\), this yields
\[
 C_0-(81/200)C_1>
              30066263041271/133370942304600>0.
\]
The integer comparison \(4^{200}<31^{81}\) proves the other half of the
membership test. Positive powers preserve the logarithmic ratio.
Also \(J\le\psi_1(1/14)\le196+\pi^2/6\), since the intervals are disjoint.
Hence \(C_0<266.5<C_1/2\), giving
\(\theta_*<1/2<\log2/\log3\).

The earlier Bundschuh–Väänänen criterion has cutoff \(1/2-1/\pi^2\):
*Arithmetical investigations of a certain infinite product*, Compositio
Mathematica 91 (1994), Theorem 2, pp. 176–177
([NUMDAM PDF](https://numdam.org/item/CM_1994__91_2_175_0.pdf)).
The base \(31/4\) is outside it, because
\(\log4/\log31>2/5>1/2-1/\pi^2\), using \(31^2<4^5\) and \(\pi^2<10\).
Thus the argument extends that explicit sufficient region using Zudilin's
forms; it does not prove irrationality at every rational base.
Zudilin's [2016 paper](https://arxiv.org/abs/1601.02688), at the end of its
introduction, already describes extensions to rational bases under a
computable logarithmic height condition without specifying the constant.
The contribution here is the explicit region and its complete clearing and
decay argument for the 2004 forms.

## Reproduction and evidence

From a fresh clone, with Python's standard library:

~~~sh
python3 experiments/erdos1049_region_parameters.py
~~~

The checker uses rational arithmetic, integer powers, and alternating-series
bounds on \(\pi\) via Machin's identity. Its success certifies finite
parameters, not the entire proof. The analytic dependencies and argument are
given above so they can be reviewed without a private checkout. This note
was prepared in Will Cook's AI-assisted mathematics programme; automated
auditing is not independent mathematical peer review.
