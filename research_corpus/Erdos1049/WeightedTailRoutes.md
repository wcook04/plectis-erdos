# Three mechanisms: proved results and the first missing arithmetic implication

Status: ordinary mathematical proofs, 20 September 2026. None of the infinite statements below has been compiled in Lean. Computations are corroboration, not substitutes for the proofs. Write
\[
q=b/a\in(0,1),\quad L=F(1/q),\quad P=(q;q)_\infty,
\quad \mathcal M(q)=\prod_{d\ge1}(1-q^d)^{-d}.
\]
The geometric-moment theorem and its proof are in the revised long manuscript, section `long1049:sec:sharp-fixed-base`.

## 1. A genuinely weighted tail determinant

Let
\[
S_m(q)=\sum_{r=1}^m\frac{q^r}{1-q^r},\qquad T_m(q)=L-S_m(q),
\qquad u_m(q)=\frac{T_m(q)}{1-q^{m+1}},
\qquad H_N(q)=\det(u_{i+j}(q))_{0\le i,j<N}.
\]
The factor depending on `i+j+1` is not a product of a row factor and a column factor. This is therefore a different Hankel determinant, not simply a scalar rescaling of the old determinant. That observation alone says nothing about an arithmetic gain.

### 1.1 Positive moments, nonvanishing and an exact real asymptotic

Expanding the two geometric sums, with nonnegative terms, gives
\[
T_m=\sum_{r\ge1}\frac{q^{(m+1)r}}{1-q^r},\qquad
u_m=\sum_{k\ge1}A_kq^{(m+1)k},
\quad A_k=\sum_{r=1}^k\frac1{1-q^r}=k+L-T_k.
\]
Consequently `H_N>0`: its positive Gram expansion contains, for example, the strictly positive tuple `(1,...,N)`.

**Theorem.** For fixed `0<q<1`,
\[
H_N(q)\sim K_{\rm tail}(q)\,N!\,N^L\,
q^{N(N+1)(2N+1)/6}P^{2N},
\]
where the positive constant is
\[
K_{\rm tail}(q)=\frac{\mathcal M(q)^3}{\Gamma(1+L)}
\prod_{k\ge1}\left(1-\frac{T_k}{k+L}\right).
\]

**Proof.** The weights `A_k` are positive, grow linearly, have fixed-shift ratios tending to one, and satisfy a polynomial uniform shift bound. Put `k=l+1`. Taking out `q^{i+j+1}` from the `(i,j)` entry multiplies the determinant by `q^{N^2}`. Apply the geometric-moment theorem to the weights `A_{l+1}`. The least-tuple exponent becomes
\[
B_N+N^2=\frac{N(N+1)(2N+1)}6.
\]
Furthermore
\[
\prod_{k=1}^N A_k
=\frac{\Gamma(N+1+L)}{\Gamma(1+L)}
 \prod_{k=1}^N\left(1-\frac{T_k}{k+L}\right).
\]
The last product converges to a positive number because `0<T_k<k+L` and `T_k=O_q(q^k)`. The gamma quotient is asymptotic to `N!N^L`. This proves the statement.

As a formal power series, the same least-tuple argument gives
\[
\operatorname{ord}_q H_N=B_N+N^2,
\qquad [q^{B_N+N^2}]H_N=N!.
\]
Here the formal coefficients of `A_k` have constant term `k`.

### 1.2 The rationality-hypothesis determinant

Replace the target value by a parameter:
\[
\widetilde u_m(\mu;q)=\frac{\mu-S_m(q)}{1-q^{m+1}},\qquad
\widetilde H_N(\mu;q)=\det(\widetilde u_{i+j}(\mu;q)).
\]
This is a rational function of `q` when `mu` is rational. Its moment weights are
\[
a_0=\mu-L,\qquad a_k=\mu-L+A_k\quad(k\ge1).
\]
Indeed the added constant `(mu-L)/(1-q^{m+1})` adds the same weight at every geometric support point, including `1`. At `q=0` the weights are `mu+k`. Thus, as a formal identity over `Q(mu)`,
\[
\operatorname{ord}_q\widetilde H_N=B_N,\qquad
[q^{B_N}]\widetilde H_N=\mu(\mu+1)\cdots(\mu+N-1).
\]
On the actual target `mu=L(q)`, the atom at `1` disappears identically. That disappearance, not a cancellation guess, accounts for the additional `N^2` in the order of `H_N`.

### 1.3 Large cyclotomic poles survive every rational `mu >= 1/2`

This is stronger than a generic-parameter pole calculation: it applies under the hypothetical rationality of `F(3/2)`, since `F(3/2)>2`.

**Theorem.** Let `N>=1`, `N<=d<=2N-1` and `mu` be rational with `mu>=1/2`. The reduced rational function `widetilde H_N(mu;q)` has a pole of exact order `2N-d` along `Phi_d(q)`.

**Proof.** Take `zeta=exp(2*pi*i/d)`, and put
\[
h=d-N,\qquad k=2N-d,\qquad N=h+k.
\]
For `N=d=1`, the assertion follows directly from `mu/(1-q)`. In all other cases each entry has at most a simple pole at `zeta`: its index is `m<=2N-2<2d-1`, so at most one term of `S_m` has a pole, and that cannot coincide with the pole of `1/(1-q^{m+1})`.

The residue matrix is supported on the trailing `k` by `k` block. In that block it is antitriangular: its antidiagonal corresponds to `m=d-1`. Along that antidiagonal the numerator is
\[
\mu-S_{d-1}(\zeta)=\mu+\frac{d-1}{2}\ne0,
\]
since pairing `r` and `d-r` gives `S_{d-1}(zeta)=-(d-1)/2`. The residue block therefore has nonzero determinant. The coefficient of the highest possible pole, of order `k`, is this determinant times the determinant of the regular leading `h` by `h` principal block. It remains to prove the latter nonzero. If `h=0` this determinant is `1`.

Put `theta=pi/d`. For an entry of that leading block, write `m=i+j`, `t=m+1`. Then `0<t<d` and
\[
S_m(\zeta)=-\frac m2+\frac i2\sum_{r=1}^m\cot(r\theta).
\]
Multiply row `i` and column `j` by `exp(i(i+1/2)theta)` and `exp(i(j+1/2)theta)`, respectively. The resulting matrix is `R+iB`, with `R,B` real symmetric and
\[
B_{ij}=\frac{i+j+2\mu}{4\sin((i+j+1)\theta)}.
\]
The Euler beta integral gives the exact representation
\[
B_{ij}=\frac1{4\pi}\int_0^\infty
x^{(i+j+1)/d-1}
\left(\frac{2\mu-1}{1+x}+\frac{d x}{(1+x)^2}\right)dx.
\]
This is a positive-definite Gram matrix for the linearly independent functions
`1,x^{1/d},...,x^{(h-1)/d}`. The density is positive for every positive `x`, including at `mu=1/2`. The integral converges because `0<i+j+1<d`.

If `(R+iB)v=0` for a nonzero complex vector `v`, then the imaginary part of `v*(R+iB)v` is `v*Bv>0`, a contradiction. The leading block is therefore nonsingular. The pole order at `zeta` is exactly `k`. Rationality of `mu` transfers the same order to every primitive `d`th root, proving the asserted `Phi_d` valuation.

**Arithmetic consequence, with its precise limitation.** The polynomial denominator contains
\[
\prod_{d=N}^{2N-1}\Phi_d(q)^{2N-d},
\]
whose degree is
\[
\sum_{d=N}^{2N-1}(2N-d)\varphi(d)
=\frac4{\pi^2}N^3+O(N^2\log N).
\]
For example, partial summation follows from
`sum_{d<=x} phi(d)=3x^2/pi^2+O(x log x)`; integrating
`(2N-t)(6t/pi^2)` from `N` to `2N` gives `4N^3/pi^2`.
The real logarithmic decay has leading coefficient `1/3`, whereas
`4/pi^2-1/3=0.0719514...>0`.

This is a denominator obstruction over `Q(q)`, **not** a lower bound for the denominator of the specialised rational number at `q=b/a`. Coprime numerator and denominator polynomials can acquire a large common integer divisor on specialisation. No bound excluding such cancellation was proved here. The exact missing implication for this route is to control these specialisation gcds, as well as the remaining endpoint factors, for this same `widetilde H_N` and parameter `mu=L`. It would be incorrect to infer either an irrationality theorem or an unconditional integer-height no-go from the polynomial degree alone.

`checks/weighted_tail_exact.py` verifies the formal generic leading coefficient and the high cyclotomic exponents for ranks `1,...,4`. These checks suggested the theorem; the positive-definite argument above proves it at every rank and every allowed rational parameter.

## 2. Congruence-constrained tails: an exact primitive lattice calculation

The following rules out a tempting but false way of calling the scalar tail system “higher rank”. It does not rule out genuinely independent approximation coordinates.

Let `a>b>=1` be coprime. Write
\[
S_m(b/a)=P_m/Q_m
\]
in lowest terms, with `Q_m>0`; set `P_0=0,Q_0=1`. The primitive integer row of the tail is `(Q_m,P_m)`, representing `Q_m F(a/b)-P_m`.

**Proposition.** Every `Q_m` is coprime to `ab`, and `b` divides every `P_m`. For each prefix containing `m=0,1`,
\[
\operatorname{span}_{\mathbb Z}\{(Q_m,P_m):0\le m<M\}
=\mathbb Z\times b\mathbb Z\qquad(M\ge2).
\]
The Smith invariants are exactly `(1,b)`; the gcd of all two by two minors is `b`; and its image modulo a positive integer `D` has cardinality
\[
\frac{D^2}{\gcd(b,D)}.
\]
Multiplication of any individual tail by a nonzero rational weight leaves its primitive integer row unchanged up to sign.

**Proof.** A common denominator of the partial sum is a product, or a least common multiple, of integers `a^r-b^r`, all coprime to `ab`. Each summand has numerator `b^r`, so the numerator with this common denominator is divisible by `b`. Reduction cannot remove any prime factor of `b`, proving the first assertions.

The first two rows are
\[
(1,0),\qquad(a-b,b).
\]
They generate `Z x bZ`: the second minus `(a-b)` times the first is `(0,b)`. Every later row already lies in that lattice. The Smith and image claims follow immediately, or by reducing those two generators.

Finally the one-dimensional rational subspace spanned by `(Q_m,P_m)` meets `Z^2` in exactly `Z(Q_m,P_m)`, since the pair is primitive. Clearing denominators and then dividing the coordinate gcd in any nonzero rational multiple returns this pair up to sign.

**Example at `3/2`.** The first three partial sums are `0`, `2`, `14/5`, with rows `(1,0),(1,2),(5,14)`. Their lattice is already `Z x 2Z`. In particular it has no three-adic image collapse, and only the single factor of two displayed in the image formula. Rational weights cannot improve this fact.

### Windows beginning later

For the window `s<=m<s+M`, `M>=2`, every pairwise minor is divisible by `b^{s+1}`. At a prime dividing `b`, the valuation of their gcd is exactly `(s+1)v_p(b)`; at a prime dividing `a`, it is zero. There may be additional gcd factors at primes coprime to `ab`.

To prove this, for `m<n` use
\[
Q_mP_n-P_mQ_n
=Q_mQ_n\sum_{r=m+1}^{n}\frac{b^r}{a^r-b^r}.
\]
The common denominators are units at primes dividing `ab`, and `m>=s`. For adjacent rows one has the exact identity
\[
Q_sP_{s+1}-P_sQ_{s+1}
=\frac{Q_sQ_{s+1}b^{s+1}}{a^{s+1}-b^{s+1}},
\]
which attains the claimed valuation at every prime dividing `b` and is a unit at every prime dividing `a`. This proves both endpoint assertions.

**Consumer.** The manuscript's Smith-image formula now has a concrete test family. Merely assembling many rationally weighted versions of these tails does not reduce the endpoint rank. The first missing implication for a congruence-constrained route is a genuinely different family whose primitive minors have extra useful valuations and whose divided real remainders remain nonzero and small. That is stronger than producing a collision in a finite residue space, and the above calculation explains why the naïve tail family does not supply it.

`checks/primitive_tail_lattice.py` uses exact fractions at `3/2,5/3,31/4,7/6`, checking prefixes through 32 and several later windows.

## 3. A different algebraic route: finite Rogers--Szegő weights

The revised long manuscript proves the identity
\[
\gamma_k(q)=\frac{R_k^{(2)}(q)R_k^{(3)}(q)}{(q;q)_k},\qquad
R_k^{(r)}(q)=\sum_{n_1+\cdots+n_r=k}
\frac{(q;q)_k}{\prod_j(q;q)_{n_j}}.
\]
Here `gamma_k=[w^k]G_q(w)` is the coefficient in the actual 2016 moment generating function, not in the 2004 polynomial linear form. The sums `R_k^(r)` are classical multivariate Rogers--Szegő polynomials at unit arguments; Vinroot, arXiv:1011.0984v1, supplies this terminology. The identity specialised to these weights is proved here by the `q`-Leibniz rule; no priority claim is made.

The product numerator has nonnegative integral coefficients, exact degree
\[
\left\lfloor\frac{k^2}{4}\right\rfloor+
\left\lfloor\frac{k^2}{3}\right\rfloor,
\]
and exact coefficient sum `6^k`. Thus it gives an explicit arithmetic description of the weights rather than only a positivity representation by infinite products. It is importantly different from row weighting: it changes how the same coefficients can be represented and manipulated.

### A further determinant consequence

For an integer `r>=1` put
\[
D_N^{(r)}=\det\big((q;q)_{i+j}^{\,r}\big)_{0\le i,j<N},
\qquad c_k^{(r)}=\binom{k+r-1}{r-1}.
\]
Then for fixed `q` there is a positive `K_r(q)` such that
\[
D_N^{(r)}\sim K_r(q)q^{B_N}P^{2N}
\left(\prod_{k<N}c_k^{(r)}\right)N^{-r(r-1)L}.
\]

Indeed
\[
(q;q)_m^{\,r}=P^r(q^{m+1};q)_\infty^{-r}
=\sum_{k\ge0} a_k^{(r)}q^{(m+1)k},\quad
 a_k^{(r)}=\frac{P^rR_k^{(r)}}{(q;q)_k}>0.
\]
For `r>=2`, write
\[
P^r(z;q)_\infty^{-r}
=(1-z)^{-r}\left(P/(qz;q)_\infty\right)^r.
\]
The analytic factor has value `1` and derivative `rL` at `z=1`. Coefficient extraction yields
\[
\frac{a_k^{(r)}}{c_k^{(r)}}
=1-\frac{r(r-1)L}{k+1}+O_q((k+1)^{-2}).
\]
The same positive coefficient bounds supply the shift hypotheses. The product argument and the geometric-moment theorem prove the claim. For `r=1`, the analytic factor instead gives an exponentially small error in `a_k^(1)-1`; the exponent `r(r-1)L` is zero, and the argument still applies.

In particular,
\[
\det\big((q;q)_{i+j}^2\big)
\sim K_2(q)N!q^{B_N}P^{2N}N^{-2L}.
\]
Thus the Lambert value appears in the logarithmic correction of a determinant whose entries are integral polynomials. This is an analytic encoding, not an irrationality proof: a rational number can occur in a logarithmic correction without violating integrality at any finite rank.

### The simplest recurrence and its limitation

For `R_n=R_n^(2)`,
\[
R_0=1,\quad R_1=2,\qquad
R_{n+1}=2R_n-(1-q^n)R_{n-1}.
\]
A short proof is to use
`E(z)^2=sum R_n z^n/(q;q)_n` and
`E(qz)^2=(1-z)^2E(z)^2`, then compare coefficients.
The same polar calculation gives
\[
R_n=\frac{n+1-2L}{P}+O_q(nq^n)+O_{q,R}(R^{-n})
\qquad(1<R<q^{-1}).
\]
The coefficient of `n` and the intercept therefore contain `1/P` and `L/P`. However, `R_n` is a polynomial of degree `floor(n^2/4)`; after evaluation at `b/a`, naïve denominator clearing is quadratic in `n`, while this connection-coefficient approximation has only linear exponential accuracy. It is not a new small integer linear form.

**First missing implication.** One would need a simultaneous or nonrectangular approximation construction exploiting this finite product/recurrence whose **primitive** coefficient height and local denominator cost are proved to be smaller than its real decay, while retaining nonvanishing. Merely observing two finite factors or a larger number of indexed rows does not establish approximation rank four, and no such claim is made here. The packet's correction in `RankBudgetLaw.md` is respected.

### Quantitative comparison with the packet's actual `3/2` deficit

For the *existing* cleared 2016 determinant, the supplied scalar-content and forced first-appearance factors together have extraction ceiling `2N^3-N`, whereas the stated sufficient extraction requirement is strictly greater than
\[
\frac{39}{41}(4N^3-3N^2).
\]
The difference is exactly
\[
\frac{N(74N^2-117N+41)}{41}>0\qquad(N\ge2).
\]
The positivity is immediate on writing
`74N^2-117N+41=74(N-2)^2+179(N-2)+103`.
Its leading size is `(74/41)N^3`. The sharp Hankel asymptotic now determines the linear term, logarithmic term and constant, but changes **none** of this cubic deficit. The finite weight factorisation supplies an arithmetic representation to investigate; it does not transfer a coefficient denominator directly into a saving for the cleared determinant.

This comparison composes the new real result with the intended existing consumer and explains exactly why it does not establish `F(3/2)` irrational.
