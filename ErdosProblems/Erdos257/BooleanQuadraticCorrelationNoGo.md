# Quadratic divisor correlations and the square-root boundary

Let $b_n\in\{0,1\}$, and put
\[
 f(n)=\sum_{d\mid n}b_d.
\]
Suppose that an integer carry satisfies
\[
 f(n)=2q_{n-1}+t_n-q_n,                               \tag{1}
\]
where $t_n\in\{0,1\}$. This note records the exact consequence of the
idempotence $b_n^2=b_n$ and compares its energy scale with a
$q_n=O(\sqrt n)$ boundary.

## 1. The Möbius correlation identity

Möbius inversion gives
\[
 b_n=\sum_{d\mid n}\mu(d)f(n/d).                     \tag{2}
\]
Thus Booleanity is equivalent to the pointwise quadratic identity
\[
 \left(\sum_{d\mid n}\mu(d)f(n/d)\right)^2
 =\sum_{d\mid n}\mu(d)f(n/d).                        \tag{3}
\]
After summing (3) with weight $1/n$ and writing
$L=[d,e]$, one obtains
\[
 \boxed{
 \sum_{n\leq N}\frac{b_n}{n}
 =\sum_{d,e\leq N}\frac{\mu(d)\mu(e)}{[d,e]}
   \sum_{m\leq N/[d,e]}
    \frac{f([d,e]m/d)f([d,e]m/e)}{m}.}                \tag{4}
\]
Substitution of (1) into every occurrence of $f$ makes (4) an exact
bilinear correlation identity for the carry on divisor-related scales.
The kernel in (4) is signed. Its diagonal part is positive, but the
off-diagonal part cannot be discarded.

There is also a positive correlation identity. Expanding the square of the
divisor sum directly gives
\[
 \boxed{
 \sum_{n\leq N}f(n)^2
 =\sum_{d,e\leq N}b_db_e
       \left\lfloor\frac{N}{[d,e]}\right\rfloor.}     \tag{5}
\]
The diagonal $d=e$ yields the unconditional lower bound
\[
 \sum_{n\leq N}(2q_{n-1}+t_n-q_n)^2
 \geq \sum_{d\leq N}b_d\left\lfloor\frac Nd\right\rfloor
 \geq N\sum_{d\leq N}\frac{b_d}{d}-\sum_{d\leq N}b_d. \tag{6}
\]
Consequently a divergent Boolean harmonic sum forces divergent mean-square
divisor load.

## 2. Why this does not reach the square-root boundary

The scale in (6) is too small. If $|q_n|\leq C\sqrt n$ at every rank, then
the left side of (6) has the crude upper bound $O(C^2N^2)$. On the other
hand,
\[
 \sum_{d\leq N}\frac{b_d}{d}\leq \sum_{d\leq N}\frac1d
 =O(\log N),
\]
so the lower bound supplied by Boolean energy is at most $O(N\log N)$.
There is a factor of order $N/\log N$ between the two scales. The same
defect remains on dyadic blocks: the harmonic contribution of
$N<d\leq2N$ is at most $\log2+o(1)$.

This is not merely a weakness of an estimate applied to (4). The diagonal
part of the right side of (4) can be much larger than its left side; the
signed off-diagonal correlations cancel the excess exactly. Thus (4) has no
coercive diagonal lower bound without an additional theorem controlling
Möbius cross-correlations.

## 3. Cofinite countermodels

Take $b_n=1$ for $n\geq M$ and $b_n=0$ otherwise, with $M\geq6$. Let $t_n$
be the period-six binary digits of $1/21$, and define $q_0=0$ and
\[
 q_n=2q_{n-1}+t_n-f(n).                               \tag{7}
\]
As shown in `SourceClockBorrowNoGo.md`, these carries are nonnegative and
have positive homogeneous flux. The Boolean harmonic sum diverges, and
both (3) and the summed laws (4)--(6) hold exactly.

These examples also obey the available square-root estimate at every
skipped rank. There are only the skipped ranks $n<M$; for $M=6$ their
carries are $0,0,0,0,1$, each smaller than $2\sqrt n+6$. After rank $M$
there is no skipped site on which that estimate imposes a restriction.
Therefore the following data are mutually compatible:

1. the exact rational digit source and recurrence (7);
2. nonnegative carry and positive limiting flux;
3. Boolean Möbius inversion and every quadratic identity above;
4. divergence of $\sum b_d/d$;
5. the square-root carry bound at every skipped rank.

The missing input is a cross-scale consequence of the actual greedy
comparison that creates quantitatively many controlled skipped ranks, or a
signed-correlation estimate unavailable for arbitrary Boolean divisor
words. Idempotence alone adds an exact quadratic law, but it does not
couple its energy to the ranks where the existing carry bound applies.

## 4. Reproduction

The script
`scripts/boolean_quadratic_correlation_audit.py` verifies (2)--(7) with
exact integer and rational arithmetic for the cofinite model and reports
the cancellation between the diagonal and off-diagonal terms in (4).
