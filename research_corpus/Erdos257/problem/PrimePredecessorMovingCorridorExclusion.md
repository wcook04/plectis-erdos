# A divisor-only moving-corridor exclusion at prime predecessors

Put
\[
 L_n(H)=\frac{2^H-1}{2^n-1}.
\]
After the root identity has left the coefficient \(1510\) at anchor \(15\),
a divisor-only Boolean prefix at common height \(H\) has coefficient
\[
 K=1510L_{15}(H)-3\sum_{n\in F}L_n(H),             \tag{1}
\]
where every \(n\in F\) divides \(H\).  This note excludes a nontrivial
infinite family of moving fatal corridors for (1).

## The theorem

Let \(q\) be a prime with
\[
 q\equiv29\pmod {30},
\]
and set \(r=q+1\) and \(H=qr\).  Let
\[
 F\subseteq\{n:n\mid H,\ n<r\}.
\]
Then the coefficient (1) cannot satisfy
\[
 6L_r(H)\le K<3L_{r-1}(H).                         \tag{2}
\]
Thus no divisor-only extraction below the protected rank \(r\) reaches the
rank-\(r\) fatal corridor at this height.

There are infinitely many such \(q\) by Dirichlet's theorem on primes in
arithmetic progressions.  Hence this is an infinite symbolic exclusion, not
a finite search statement.

## 1. The common cyclotomic quotient

For general \(r,r-1\mid H\), define
\[
 P_{H,>r}=\prod_{\substack{d\mid H\\d>r}}\Phi_d(2),
 \qquad
 D_{H,r}=\prod_{\substack{d\mid H\\d\le r}}\Phi_d(2).
\]
If \(n<r\) divides \(H\), then every factor in \(P_{H,>r}\) remains in
\(L_n(H)\).  The same is true of \(L_r(H)\) and \(L_{r-1}(H)\).  Since
\(15<r\), division by \(P_{H,>r}\) converts (1)--(2) into
\[
 \bar K=
 1510\frac{D_{H,r}}{2^{15}-1}
 -3\sum_{n\in F}\frac{D_{H,r}}{2^n-1},             \tag{3}
\]
and
\[
 6\frac{D_{H,r}}{2^r-1}\le\bar K
 <3\frac{D_{H,r}}{2^{r-1}-1}.                      \tag{4}
\]
All displayed quotients are integers.

## 2. The reduced corridor has width three

Because \(H=q(q+1)\) and \(q\) is prime, every divisor of \(H\) which is at
most \(r=q+1\) either divides \(r\) or equals \(q\).  Indeed, a divisor
containing the factor \(q\) and any further factor is at least \(2q>q+1\).
Consequently
\[
 D_{H,r}=(2^r-1)(2^q-1).                            \tag{5}
\]
The lower and upper endpoints in (4) are therefore
\[
 6(2^q-1)\quad\hbox{and}\quad3(2^{q+1}-1),
\]
whose difference is exactly
\[
 3(2^{q+1}-1)-6(2^q-1)=3.                          \tag{6}
\]

## 3. Primitive charge separates every integer in the corridor

Let \(p_r\) be a primitive prime divisor of \(2^r-1\).  It exists by the
Bang--Zsigmondy theorem because \(r\ge30\), and
\(\operatorname{ord}_{p_r}(2)=r\).  In particular \(p_r\ge r+1>3\).

The factor carrying \(p_r\) occurs in \(D_{H,r}\).  It is not cancelled in
any summand of (3), since every denominator there has exponent strictly
less than \(r\).  Hence
\[
 \bar K\equiv0\pmod {p_r}.                         \tag{7}
\]
The upper endpoint \(U=3(2^r-1)\) also vanishes modulo \(p_r\).  If (4)
held, (6) would give
\[
 0<U-\bar K\le3,
\]
while (7) would make \(U-\bar K\) a positive multiple of \(p_r>3\), a
contradiction.

The mechanism is triangular.  Removing the cyclotomic factors above the
moving rank shrinks the corridor to three consecutive integer gaps, while
the newest primitive coordinate survives every earlier divisor atom and
forces the gap onto a lattice with spacing at least \(r+1\).

This theorem does **not** yet cover arbitrary \(H\) or ranks for which the
reduced width is large.  Its conclusion is exactly the stated infinite
prime-predecessor family.

Run

    ./repo-python formal_math/erdos257_period_noncollapse/scripts/prime_predecessor_moving_corridor_exclusion.py

for exact receipts at \(q=29,59,89\), including direct enumeration of all
divisor-prefix subsets in the first case.
