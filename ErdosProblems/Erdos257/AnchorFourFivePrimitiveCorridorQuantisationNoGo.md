# Primitive quantisation of the \(1/465\) fatal corridor

Status: exact theorem and exact finite falsifier audit, 2026-08-21. The
theorem gives a product-specific obstruction, but it does not control the
dense-prefix common height and therefore does not prove the \(1/465\)
construction.

Put

\[
 M_n=2^n-1,\qquad x=M(4,5)=\frac1{465}.
\]

Let \(F\subseteq\{1,\ldots,r-1\}\), and choose \(H\) divisible by \(20\),
\(r\), \(r-1\), and every rank in \(F\). Write \(D=2^H-1\). At the common
height \(H\),

\[
 x=\frac{D}{155}M(2,H),\qquad
 w_n=3\frac{D}{M_n}M(2,H).
\]

Consequently the residual after the Boolean prefix \(F\) has coefficient

\[
 K=\frac D{155}-3\sum_{n\in F}\frac D{M_n}.       \tag{1}
\]

The rank-\(r\) duplicate/fatal corridor

\[
 2w_r\le x-\sum_{n\in F}w_n<w_{r-1}              \tag{2}
\]

is exactly

\[
 L:=6\frac D{M_r}\le K<
 U:=3\frac D{M_{r-1}}.                            \tag{3}
\]

Its integer width is

\[
 W=U-L=\frac{3D}{M_{r-1}M_r}.                    \tag{4}
\]

The quotient in (4) is integral because consecutive Mersenne numbers are
coprime and both divide \(D\).

## 1. The fresh primitive-coordinate theorem

Assume \(r>6\). Let \(p\) be a primitive prime divisor of \(M_r\), and put
\(e=v_p(D)\). Then every coefficient (1) satisfies

\[
 \boxed{K\equiv0\pmod {p^e}.}                    \tag{5}
\]

Indeed, primitiveness gives \(\operatorname{ord}_p(2)=r\), so
\(p\nmid M_n\) for every \(n<r\). Hence \(p^e\mid D/M_n\) for every prefix
rank. Also \(p\nmid155\): the primes dividing \(155=5\cdot31\) have orders
\(4\) and \(5\), while \(r>6\). Therefore \(p^e\mid D/155\), proving (5).

The upper endpoint in (3) obeys the same congruence because
\(p\nmid M_{r-1}\):

\[
 U\equiv0\pmod {p^e}.                             \tag{6}
\]

If (3) holds, \(U-K\) is therefore a positive multiple of \(p^e\). Since
\(K\ge L\), it is at most \(W\). Thus

\[
 \boxed{\text{a rank-}r\text{ fatal hit forces }W\ge p^e.}       \tag{7}
\]

In particular,

\[
 \boxed{W<p^e\quad\Longrightarrow\quad
 \text{the fixed }1/465\text{ charge misses the corridor}.}     \tag{8}
\]

Bang--Zsigmondy supplies such a primitive prime for every \(r>6\). Thus
(8) is an all-depth theorem whenever its explicit width hypothesis holds;
it is not a finite-search assertion.

## 2. Why this does not close the dense case

The conclusion (5) is only one-sided. The rank-\(r-1\) prefix atom cancels
the fresh primitive coordinate of \(M_{r-1}\), so there is no automatic
second congruence pinning \(K-L\). More importantly, (7) compares the
primitive spacing with the complete common-height corridor width. A dense
prefix forces \(H\) to contain many lower clocks, and the factors remaining
in \(D/(M_{r-1}M_r)\) are not controlled by the single fresh prime. The
width can therefore be much larger than \(p^e\). In that regime (5)--(6)
merely say that the interval may contain many admissible multiples.

There is also an invariance warning. Replacing a valid common height \(H_0\)
by \(qH_0\), where \(q\ne p\) is prime, leaves the \(p\)-adic valuation
fixed by the lifting-the-exponent lemma,

\[
 v_p(2^{qH_0}-1)=v_p(2^{H_0}-1),
\]

while the unreduced width in (4) grows exponentially with \(qH_0\).
Therefore a proof cannot manufacture (8) by choosing an advantageous LCM
presentation. It must cancel irrelevant common factors and control the
resulting lower-clock product, or introduce a genuinely joint
primitive-coordinate law.

This is the exact ceiling of the tempting argument that the product root is
zero in every new primitive coordinate. The statement is true, but it
quantises only \(U-K\); it does not bound the number of quantisation steps
inside the dense-support corridor.

## 3. Finite fixed-root audit

The companion script searches for a Boolean prefix whose residual lies in
(2). Reverse superincreasingness makes the search directed: for each \(r\),
take the lexicographically maximal Boolean sum below \(x-2w_r\), then test
whether it exceeds \(x-w_{r-1}\). If any prefix hits the corridor, it is the
unique candidate at that rank.

Exact rational arithmetic finds no hit through \(r=300\). This is only a
finite falsifier audit and is not used in the proof of (5)--(8).

Run:

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/anchor_four_five_primitive_corridor_quantisation.py
