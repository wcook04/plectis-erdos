# A cyclotomic obstruction to divisor-supported special horizons

## Status

This note proves an exact obstruction to one natural special-horizon
strategy for \(M(4,5)=1/465\).  At a horizon divisible by \(20\), one might
try to select only ranks dividing the horizon, so that every quotient weight
is an exact repunit quotient.  No such construction can have terminal defect
in the source corridor.

The theorem does **not** exclude representations at multiples of \(20\)
whose selected ranks do not all divide the horizon.

## The obstruction

Let \(N\) be a positive multiple of \(20\), and put

\[
R_N=2^N-1,\qquad
H_N=\left\lfloor\frac{2^N}{465}\right\rfloor,\qquad
K_N=\frac N{20}.
\]

Since \(465\mid 2^{20}-1\), one has

\[
H_N=\frac{R_N}{465}.
\]

If \(d\mid N\), then the fixed-horizon quotient weight is also exact:

\[
q_{N,d}
=\left\lfloor\frac{2^N}{2^d-1}\right\rfloor
=\frac{R_N}{2^d-1}.
\]

> **Theorem.** There do not exist bits \(b_d\in\{0,1\}\), indexed by the
> divisors \(d\mid N\), and an integer \(e\) with \(0\le e\le K_N\), such
> that
> \[
> H_N-e=\sum_{d\mid N}b_dq_{N,d}.
> \tag{1}
> \]

### Proof

Bang--Zsigmondy supplies a primitive prime divisor \(p\) of \(2^N-1\).
The only exceptional exponent for \(2^n-1\) with \(n>1\) is \(n=6\), so
there is no exception when \(20\mid N\).  Primitivity gives

\[
\operatorname{ord}_p(2)=N,
\]

and hence

\[
p\equiv1\pmod N,\qquad p\ge N+1.
\tag{2}
\]

The same primitivity shows that \(p\) divides neither \(465\) nor
\(2^d-1\) for any proper divisor \(d<N\) of \(N\).

Divide (1) by \(R_N\), and move the possible rank-\(N\) term to the right:

\[
\frac1{465}
-\sum_{\substack{d\mid N\\d<N}}\frac{b_d}{2^d-1}
=\frac{e+b_N}{R_N}.
\tag{3}
\]

Write the left side in lowest terms as \(A/D\).  Every prime factor of \(D\)
comes from \(465\) or from some \(2^d-1\) with \(d<N\).  Therefore
\(p\nmid D\).  Cross-multiplication in (3) gives

\[
A R_N=(e+b_N)D.
\]

Because \(p\mid R_N\) and \(p\nmid D\), it follows that

\[
p\mid e+b_N.
\tag{4}
\]

But

\[
0\le e+b_N\le \frac N{20}+1<N+1\le p.
\]

Thus \(e+b_N=0\), so \(e=0\), \(b_N=0\), and (3) becomes a finite Boolean
identity

\[
\frac1{465}
=\sum_{\substack{d\mid N\\d<N}}\frac{b_d}{2^d-1}.
\tag{5}
\]

For completeness, (5) is itself impossible by the same primitive-prime
argument.  Every selected rank must be at least \(9\), because
\(w_d>1/465\) for \(d\le8\).  If \(m\) is the largest selected rank,
Bang--Zsigmondy gives a primitive prime divisor of \(2^m-1\).  It divides
neither \(465\) nor any earlier selected denominator.  Isolating the
rank-\(m\) term in (5) and cross-multiplying is then contradictory.
\(\square\)

## Consequence for special-horizon constructions

The most direct LCM-height plan is therefore unavailable.  Choosing
\(N\) to be a common multiple of every selected rank makes the quotient
identities algebraically cleaner, but it also exposes a new primitive prime
at the terminal cyclotomic layer.  The allowed corridor error
\(e\le N/20\) is too small to absorb that prime.

Any successful subsequence of horizons must retain genuinely nondivisor
ranks.  In particular, the still-open possibilities are unrestricted
multiples of \(20\), recursively chosen horizons with moving nondivisor
suffixes, or another construction not based on exact repunit divisibility.
