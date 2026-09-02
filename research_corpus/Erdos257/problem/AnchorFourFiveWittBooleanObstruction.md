# The Witt obstruction for the period-\(20\) binary lift of \(M(4,5)\)

## Status

This note proves a sharp obstruction, not membership of \(1/465\) in the
achievement set. The formal Lambert lift, the canonical Euler-product lift,
and the exponential ghost lift are different constructions. All three have
unique coordinates, and none has Boolean coordinates for the period-\(20\)
binary series of \(1/465\).

The first failures occur at different ranks:

\[
 \begin{array}{c|c|c}
 \text{formal lift} & \text{coordinate} & \text{first non-Boolean rank}\\ \hline
 \exp(B(z))=\prod_n(1-z^n)^{-x_n}
   & x_{18}=\tfrac12 & 18\\
 1+B(z)=\prod_n(1-z^n)^{-e_n}
   & e_{22}=-1 & 22\\
 B(z)=\sum_n a_n\dfrac{z^n}{1-z^n}
   & a_{26}=-1 & 26\\
 M(4,5;z)=\sum_n c_n\dfrac{z^n}{1-z^n}
   & c_{29}=2 & 29.
 \end{array}
\]

Consequently, a necklace, Lyndon-word, or big-Witt recursion cannot by itself
produce the desired Boolean Mersenne support from either natural formal lift.
Any successful construction must use an identity that is true after the
specialization \(z=1/2\) but is not an identity of formal power series.

## 1. The two formal series with value \(1/465\)

Put

\[
 M(4,5;z)
   =\frac{z^4}{1-z^4}\frac{z^5}{1-z^5}
   =\frac{z^9}{(1-z^4)(1-z^5)}.
\]

At \(z=1/2\), this is

\[
 M(4,5;1/2)=\frac1{(2^4-1)(2^5-1)}=\frac1{465}.
\]

The binary expansion of the same number has period \(20\). Define

\[
 S=\{9,13,14,17,18,19,20\},
 \qquad
 t_n=1_{\{n\bmod20\in S\}},
\]

where residues are represented by \(1,\ldots,20\), and let

\[
 B(z)=\sum_{n\ge1}t_nz^n
 =\frac{z^9+z^{13}+z^{14}+z^{17}+z^{18}+z^{19}+z^{20}}
        {1-z^{20}}.
\]

Indeed,

\[
 2^{11}+2^7+2^6+2^3+2^2+2+1=2255
   =\frac{2^{20}-1}{465},
\]

so \(B(1/2)=1/465\). However,
\(B(z)\ne M(4,5;z)\) as formal series. This distinction is exactly where
specialization at \(1/2\) loses the formal Witt rigidity.

## 2. Canonical Euler factorization: the rank-\(22\) obstruction

Every series \(F(z)\in1+z\mathbb Z[[z]]\) has a unique formal Euler
factorization

\[
 F(z)=\prod_{n\ge1}(1-z^n)^{-e_n},
 \qquad e_n\in\mathbb Z.
 \tag{1}
\]

Degreewise finiteness makes the product formal; the usual least-degree
argument gives uniqueness.

> **Theorem 2.1 (sharp positive Euler obstruction).** In the canonical
> factorization
> \[
>  1+B(z)=\prod_{n\ge1}(1-z^n)^{-e_n},
> \]
> all coordinates through rank \(21\) are Boolean, but
> \[
>  e_{22}=-1.
> \]
> In particular there is no factorization of \(1+B(z)\) with every
> \(e_n\in\{0,1\}\), or even with every \(e_n\ge0\).

**Proof.** Since the first nonzero coefficient of \(B\) is in degree \(9\),
successive coefficient comparison in (1) forces

\[
 e_9=e_{13}=e_{14}=e_{17}=e_{19}=e_{20}=1
\]

and every other \(e_n\) with \(n\le21\) to vanish. At degree \(18\), the
required coefficient \(1\) is already supplied by the term \(z^{18}\) in
\((1-z^9)^{-1}\), so \(e_{18}=0\).

At degree \(22\), the product of the already forced terms \(z^9\) and
\(z^{13}\) contributes \(1\). But \(t_{22}=0\). The only new factor able to
change the degree-\(22\) coefficient is
\((1-z^{22})^{-e_{22}}=1+e_{22}z^{22}+O(z^{44})\). Hence

\[
 0=[z^{22}](1+B)=1+e_{22},
\]

which gives \(e_{22}=-1\). The displayed coordinates also prove that rank
\(22\) is the first failure. \(\square\)

This is the elementary content of the necklace collision: the two primitive
letters of weights \(9\) and \(13\) create a composite word of weight \(22\),
while the prescribed binary series has a hole there. Reordering or
recursively regrouping Lyndon factors cannot remove the collision, because
the Euler coordinates in (1) are unique.

## 3. Lambert inversion: the rank-\(26\) obstruction

Suppose

\[
 B(z)=\sum_{n\ge1}a_n\frac{z^n}{1-z^n}.
 \tag{2}
\]

Comparing the coefficient of \(z^m\) gives

\[
 t_m=\sum_{n\mid m}a_n.
\]

Therefore Möbius inversion uniquely forces

\[
 a_m=\sum_{d\mid m}\mu(m/d)t_d.
 \tag{3}
\]

> **Theorem 3.1 (sharp Boolean Lambert obstruction).** The unique Lambert
> coordinates in (2) are Boolean through rank \(25\), whereas
> \[
>  a_{26}=-1.
> \]

**Proof.** Up to rank \(25\), the nonzero binary coefficients occur at

\[
 9,13,14,17,18,19,20.
\]

Among these, the only proper divisibility relation is \(9\mid18\). Formula
(3) therefore gives

\[
 a_9=a_{13}=a_{14}=a_{17}=a_{19}=a_{20}=1,
 \qquad a_{18}=t_{18}-t_9=0,
\]

and all other \(a_m\) for \(m\le25\) vanish. At rank \(26\), the divisors
are \(1,2,13,26\); among them only \(13\) has binary coefficient \(1\).
Thus

\[
 a_{26}=\mu(2)t_{13}=-1.
\]

This also proves first-failure sharpness. \(\square\)

The obstruction is stronger than a multiplicity collision: the binary hole
at \(26=2\cdot13\) demands a negative primitive Lambert atom to cancel the
copy of rank \(13\).

## 4. Exponential ghost normalization: the rank-\(18\) obstruction

A second standard use of big-Witt coordinates treats \(B\) as a logarithm:

\[
 \exp(B(z))=\prod_{n\ge1}(1-z^n)^{-x_n}.
 \tag{4}
\]

Taking formal logarithms yields

\[
 t_m=\sum_{n\mid m}\frac{n}{m}x_n,
 \qquad
 x_m=\frac1m\sum_{d\mid m}\mu(m/d)d\,t_d.
 \tag{5}
\]

> **Theorem 4.1 (sharp integral ghost obstruction).** In (4), the
> coordinates through rank \(17\) are Boolean, but
> \[
>  x_{18}=\frac12.
> \]
> Hence this normalization is not even integral, much less Boolean.

**Proof.** Before rank \(18\), no nonzero rank in the first period is a
multiple of an earlier nonzero rank, so (5) gives the obvious Boolean mask
at \(9,13,14,17\). At \(18\), only the divisors \(9\) and \(18\) have
nonzero \(t\)-value. Hence

\[
 x_{18}=\frac1{18}\bigl(18t_{18}-9t_9\bigr)=\frac12.
\]

Thus rank \(18\) is the first failure. \(\square\)

## 5. The original product lift: the rank-\(29\) collision

Write

\[
 M(4,5;z)=\sum_{m\ge1}r_mz^m,
\]

where \(r_m\) counts positive pairs \((i,j)\) with \(4i+5j=m\). Its unique
Lambert coordinates

\[
 M(4,5;z)=\sum_{n\ge1}c_n\frac{z^n}{1-z^n}
\]

are

\[
 c_n=\sum_{d\mid n}\mu(n/d)r_d.
\]

Equivalently, \(c_n\) counts the positive solutions
\((i,j)\) of \(4i+5j=n\) with \(\gcd(i,j)=1\).

> **Theorem 5.1 (sharp primitive-pair collision).** One has
> \(c_n\in\{0,1\}\) for \(n<29\), while
> \[
> c_{29}=2.
> \]

**Proof.** Two distinct positive solutions of \(4i+5j=n\) differ by
\((5k,-4k)\) for a nonzero integer \(k\). After interchanging the two
solutions if necessary, take \(k\ge1\). Positivity then gives
\(i\ge1\) and \(j-4k\ge1\), whence

\[
 n=4i+5j\ge4+5(4k+1)\ge29.
\]

Thus there is at most one positive solution below rank \(29\). At rank
\(29\), the two solutions

\[
 (i,j)=(1,5),\qquad (i',j')=(6,1)
\]

are both primitive, so \(c_{29}=2\). \(\square\)

## 6. Exact boundary of the no-go

These theorems rule out a formal positive-Witt solution. They do **not**
rule out a Boolean set \(A\subseteq\mathbb N\) satisfying

\[
 \sum_{n\in A}\frac1{2^n-1}=\frac1{465}.
\]

Such an equality asks only for equality after evaluation at \(z=1/2\):

\[
 \left.\sum_{n\in A}\frac{z^n}{1-z^n}\right|_{z=1/2}
   =M(4,5;1/2).
\]

Evaluation at one point is not injective on the relevant convergent series.
Therefore an actual construction must create a nonzero specialization-kernel
identity

\[
 K(z)=M(4,5;z)-\sum_{n\in A}\frac{z^n}{1-z^n},
 \qquad K(1/2)=0,
 \qquad K(z)\ne0.
\]

This is the precise transport criterion for any future Witt idea. A new
necklace recursion is relevant only if it explicitly exploits such a
specialization-kernel identity. If it remains an identity in
\(\mathbb Z[[z]]\), the rank-\(18\), \(22\), \(26\), or \(29\) uniqueness
obstruction applies, according to its normalization.
