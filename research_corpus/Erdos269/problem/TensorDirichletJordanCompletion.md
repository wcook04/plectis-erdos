# Erdős 269: tensor Dirichlet--Jordan completion for the value coordinate

## Statement

Let

\[
S=\sum_{i,j,k\geq 0}\frac1{H(2^i3^j5^k)},\qquad
H(s)=2^{\lfloor L\rfloor}3^{\lfloor L/\theta\rfloor}5^{\lfloor L/\phi\rfloor},
\]

where \(L=\log_2s\), \(\theta=\log_2 3\), and \(\phi=\log_2 5\).  Put
\(f_p(x)=p^{\{x\}}\), regarded as a one-periodic function with value \(1\) at
its discontinuity.  Let \(F_{p,M}\) be its symmetric Fourier partial sum over
\(|m|\leq M\).  Then the rectangular sums

\[
A_M=\sum_{i,j,k\geq0}\frac{
 F_{2,M}(L)F_{3,M}(L/\theta)F_{5,M}(L/\phi)}{8^i27^j125^k}
\]

exist absolutely for every \(M\), admit the mode-by-mode product of geometric
series displayed in `TorusCocycleAndDiophantineTypeLab.md`, and satisfy

\[
\lim_{M\to\infty} A_M=S+\frac{17}{2}.
\]

Thus the corrected rectangular symmetric Fourier identity is an ordinary
Fourier-analysis theorem.  It says nothing about irrationality, transcendence,
or exclusion of the exact-integral-tail branch.

## Proof

### 1. Pointwise coordinate and finite mode algebra

For \(s=2^i3^j5^k\), floor/fractional-part decomposition gives

\[
\frac1{H(s)}=
\frac{f_2(L)f_3(L/\theta)f_5(L/\phi)}{s^3}.
\]

For fixed \(M\), each \(F_{p,M}\) is a finite trigonometric polynomial.
Therefore the weighted lattice sum defining \(A_M\) can be expanded term by
term.  Its \((m_1,m_2,m_3)\)-term is the product of the three geometric series
with denominators

\[
(1-e(\lambda)/8)(1-e(\lambda\theta)/27)(1-e(\lambda\phi)/125),
\quad \lambda=m_1+m_2/\theta+m_3/\phi.
\]

This is finite algebra, not an exchange of an infinite Fourier series with the
lattice sum.

### 2. The needed domination

Each \(f_p\) is a periodic bounded-variation function: it is smooth off one
jump and its one-sided limits at that jump are \(1\) and \(p\).  The standard
Dirichlet--Jordan estimate gives a constant \(C_p\), independent of \(M\) and
of \(x\), such that

\[
|F_{p,M}(x)|\leq C_p,
\]

and gives pointwise convergence to \(f_p(x)\) away from an integer and to
\((1+p)/2\) at an integer.  (This is the usual uniform boundedness part of the
bounded-variation proof, not an \(L^\infty\) estimate for arbitrary bounded
functions.)

Consequently every summand of \(A_M\) is dominated by

\[
C_2C_3C_5\,8^{-i}27^{-j}125^{-k},
\]

and this majorant is summable on \(\mathbb N^3\).  Dominated convergence now
passes the rectangular symmetric limit through the lattice sum.

### 3. Locate the midpoint discrepancies

Unique factorization shows that \(L\in\mathbb Z\) precisely on the pure
\(2\)-axis, that \(L/\theta\in\mathbb Z\) precisely on the pure \(3\)-axis,
and that \(L/\phi\in\mathbb Z\) precisely on the pure \(5\)-axis.  Away from
these axes the pointwise limit is the original torus weight.  At \(p^n\),
\(n\geq1\), the midpoint replaces the corresponding factor \(1\) by
\((1+p)/2\), hence adds

\[
\frac{p-1}{2H(p^n)}.
\]

At the origin all three factors are midpoint values, so the excess is

\[
\frac{1+2}{2}\frac{1+3}{2}\frac{1+5}{2}-1=8.
\]

### 4. Sum the axis correction

The running height changes only at the merged sequence of pure prime powers.
At a pure power \(p^n\),

\[
\frac{p-1}{H(p^n)}=\frac1{H(p^n-1)}-\frac1{H(p^n)}.
\]

Finite initial portions telescope over that merged jump sequence.  Since
\(H\) tends to infinity,

\[
\sum_{p\in\{2,3,5\}}(p-1)\sum_{n\geq1}\frac1{H(p^n)}=1.
\]

The three axes therefore contribute \(1/2\), and the origin contributes \(8\).
The dominated-convergence limit is consequently \(S+17/2\), as claimed.

## Assurance and boundary

The proof uses the classical one-dimensional Dirichlet--Jordan theorem and its
uniform boundedness estimate for a fixed periodic bounded-variation function,
then ordinary dominated convergence.  It is an authored ordinary proof, not a
Lean theorem or independent analytic review.  The finite Fourier probe remains
a replay check only.  Completing this identity does not create the Diophantine
anti-concentration estimate needed for Erdős Problem 269.

## References

- C. Jordan, *Sur la série de Fourier*, Comptes rendus de l'Académie des
  sciences 92 (1881), 228--230: bounded-variation midpoint convergence.
- `TorusCocycleAndDiophantineTypeLab.md`: source-specific floor coordinate,
  geometric mode formula, and exact prime-axis telescope.
