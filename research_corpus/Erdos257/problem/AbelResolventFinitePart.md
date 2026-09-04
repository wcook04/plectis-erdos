# The Abel finite part of the future-divisor resolvent

Status: exact identities and exact finite computations, 2026-08-20.  The
harmonic-mass inequality in Section 4 is not proved at all depths.

## 1. Finite part of one labelled clock

Let \(D_R=\{d\leq R:b_d=1\}\), and let

\[
 \mathcal R_R(z)
 =\sum_{c\geq1}\nu_R(c)z^c
 =\sum_{d\in D_R}\frac{z^{\rho_R(d)}}{1-z^d},
 \qquad 0<z<1,
 \tag{1}
\]

where \(\rho_R(d)\in\{1,\ldots,d\}\) is determined by
\(d\mid2R+\rho_R(d)\).  Put

\[
 A_R=\sum_{d\in D_R}\frac1d.
 \tag{2}
\]

Writing \(s=1-z\), one has

\[
 z^\rho=1-\rho s+O(s^2),
 \qquad
 1-z^d=ds-\frac{d(d-1)}2s^2+O(s^3).
\]

It follows that

\[
 \frac{z^\rho}{1-z^d}
 =\frac1{d(1-z)}
  +\frac{d-1-2\rho}{2d}+O(1-z).
 \tag{3}
\]

Hence the Abel, equivalently Hadamard, finite part after removal of the simple
pole is

\[
 B_R
 :=\lim_{z\uparrow1}
   \left(\mathcal R_R(z)-\frac{A_R}{1-z}\right)
 =\sum_{d\in D_R}\frac{d-1-2\rho_R(d)}{2d}.
 \tag{4}
\]

If \(r_R(d)=2R\bmod d\in\{0,\ldots,d-1\}\), then
\(\rho_R(d)=d-r_R(d)\), with the value \(d\) when \(r_R(d)=0\).  Thus

\[
 \boxed{
 B_R=\sum_{d\in D_R}
 \left(\frac{r_R(d)}d-\frac12-\frac1{2d}\right).}
 \tag{5}
\]

Formula (5) is the Bernoulli-sawtooth term, including its value at an integer
phase.  The subtraction in (4) is essential: evaluation at \(z=1\) itself
diverges whenever \(D_R\) is nonempty.

## 2. Transport and equal weighting of the first two arrivals

The exact formal transport is

\[
 \mathcal R_{R+1}(z)
 =z^{-2}\bigl(\mathcal R_R(z)-\nu_R(1)z-\nu_R(2)z^2\bigr)
  +b_{R+1}\frac{z^{R+1}}{1-z^{R+1}}.
 \tag{6}
\]

Since \(z^{-2}=1+2(1-z)+O((1-z)^2)\), comparison of the pole and finite
terms in (6) gives

\[
\begin{split}
 A_{R+1}
  &=A_R+\frac{b_{R+1}}{R+1},\\
 B_{R+1}-B_R
  &=2A_R-\nu_R(1)-\nu_R(2)
    -b_{R+1}\frac{R+2}{2(R+1)}.
 \tag{7}
\end{split}
\]

The two consumed coefficients now have the same weight.  This differs from
the convergent evaluation at \(z=1/2\), whose shift removes
\(2\nu_R(1)+\nu_R(2)\).

Let \(F_N=P_N+c-2Q_N\), where \(c=4\) for the compensated \(1/21\) energy and
\(c=0\) for the \(90/511\) energy.  The exact two-step law is

\[
 F_{2R+2}-F_{2R}
 =\nu_R(1)+\nu_R(2)+2b_{R+1}
  -Q_{2R+1}-Q_{2R+2}.
 \tag{8}
\]

Combining (7) and (8), and putting \(J_R=F_{2R}+B_R\), gives

\[
 \boxed{
 J_{R+1}-J_R
 =2A_R+\frac{3R+2}{2(R+1)}b_{R+1}
  -Q_{2R+1}-Q_{2R+2}.}
 \tag{9}
\]

Thus the finite part removes the unequal divisor-arrival coefficients.
Equation (9) is not monotone even for \(90/511\); the first negative
one-step change is \(-1/3\), from \(R=3\) to \(R=4\).

## 3. The full finite part reconstructs the queue service

Let \(K_R=\#D_R\), and define

\[
 C_R=\frac{4R-1}{2}A_R-\frac{K_R}{2}.
 \tag{10}
\]

For each \(d\in D_R\), subtracting its summand in (5) from its summand in
(10) gives

\[
 \left(\frac{4R-1}{2d}-\frac12\right)
 -\left(\frac{r_R(d)}d-\frac12-\frac1{2d}\right)
 =\frac{2R-r_R(d)}d
 =\left\lfloor\frac{2R}{d}\right\rfloor.
\]

Therefore

\[
 \boxed{
 C_R-B_R
 =\sum_{d\in D_R}\left\lfloor\frac{2R}{d}\right\rfloor
 =D_{2R}.}
 \tag{11}
\]

If \(S_N=\sum_{n\leq N}Q_n\), the queue identity
\(F_N=c+D_N-S_N\) now becomes

\[
 J_R=c+C_R-S_{2R}.                                  \tag{12}
\]

The equal weights in (7) have a precise explanation: pole mass and finite
part together reconstruct the integer floor service.  Retaining the complete
finite part gives the same information as the existing queue coordinate.  In
particular, (12) does not by itself yield a new sign argument.

## 4. A harmonic-service sufficient condition for \(90/511\)

The finite part also gives a residue-free lower bound.  For any horizon \(N\),
put \(R=\lfloor N/2\rfloor\), and retain the definitions

\[
 A_R=\sum_{\substack{d\leq R\\b_d=1}}\frac1d,
 \qquad
 K_R=\sum_{d\leq R}b_d.
\]

For every \(d\leq R\),

\[
 \left\lfloor\frac Nd\right\rfloor
 \geq\frac{N+1}{d}-1.
 \tag{13}
\]

Consequently

\[
 D_N\geq(N+1)A_R-K_R.
 \tag{14}
\]

Define the harmonic-service potential

\[
 \boxed{
 \mathcal M_N
 =c+(N+1)A_{\lfloor N/2\rfloor}
   -K_{\lfloor N/2\rfloor}-S_N.}
 \tag{15}
\]

Equations (14) and the queue identity give

\[
 \boxed{\mathcal M_N\leq F_N.}                       \tag{16}
\]

Thus \(\mathcal M_N\geq0\) for every \(N\) is a sufficient condition for the
desired endpoint-energy inequality.  The exact slack is

\[
 F_N-\mathcal M_N
 =\sum_{\substack{d\leq N/2\\b_d=1}}
   \frac{d-1-(N\bmod d)}d\geq0.
 \tag{17}
\]

At an even boundary, (14) is also the sharp termwise consequence of the
finite-part estimate

\[
 B_R\leq\frac{K_R}{2}-\frac32A_R.
 \tag{18}
\]

The one-step recurrence for (15) contains no divisor residue:

\[
\begin{array}{ll}
 N=2R+1:&
 \mathcal M_N-\mathcal M_{N-1}=A_R-Q_N,\\[1mm]
 N=2R:&
 \mathcal M_N-\mathcal M_{N-1}
 =A_{R-1}+b_R\left(1+\dfrac1R\right)-Q_N.
\end{array}                                          \tag{19}
\]

For the target \(90/511\), the following all-depth inequality would imply
(SC0):

\[
 \boxed{
 \sum_{n\leq N}Q_n
 \leq
 (N+1)\sum_{\substack{d\leq N/2\\b_d=1}}\frac1d
 -\sum_{d\leq N/2}b_d.}
 \tag{20}
\]

Unlike (11), inequality (20) is not equivalent to (SC0); it is a stronger
sufficient statement obtained by discarding the nonnegative phase slack
(17).  It remains unproved.

## 5. Finite computations and counterexamples

For the greedy orbit of \(90/511\), exact rational computation through rank
\(5000\) found

\[
 \mathcal M_N\geq0,
\]

with equality exactly at \(N=1,\ldots,5\).  The smallest later value is

\[
 \mathcal M_9=\frac13.
 \tag{21}
\]

A separate 160-bit directed lower bound for the harmonic mass certifies
strict positivity at every rank \(6\leq N\leq50000\).  These are finite
computations, not a proof of (20).

The potential is not monotone.  For \(90/511\), its first negative increment
is

\[
 \mathcal M_8-\mathcal M_7=-\frac23,
\]

and its first negative period-nine increment is

\[
 \mathcal M_{29}-\mathcal M_{20}=-\frac{13}{10}.
\]

Thus neither one-step induction nor monotonicity on the nine source phases
can prove (20).

The following exact counterexamples delimit its scope.

* For the actual \(1/21\) greedy orbit with \(c=4\),
  \(\mathcal M_{13}=-1/5\), while \(F_{13}=0\).
* The same-cylinder target
  \(x^-=1/21-1/(3\cdot2^{63})\) has the same failure at rank \(13\).
  Moreover \(J_{32}=-742069/960960\), while its even energy is
  \(F_{64}=1\).  Positivity of the Abel potential \(J_R\) is not necessary
  for positivity of \(F_{2R}\).
* For the quotient-admissible fixed-source support
  \(A_6=\{d:d\geq6\}\), one has
  \(\mathcal M_7=F_7=-2\).
* The recut tail \(17/511\) has
  \(\mathcal M_9=F_9=-1\), whereas \(90/511\) has
  \(\mathcal M_9=1/3\).  The harmonic potential retains the rank-\(3\)
  support change which the common modulo-\(73\) phase orbit loses.

These examples show that (20) is target-specific.  It does not follow from
Booleanity, nonnegative quotient defect, the period-six source, or greedy
complementarity without the \(90/511\) source and support.

## 6. Reproduction

Run

    python3 formal_math/erdos257_period_noncollapse/scripts/abel_resolvent_finite_part_audit.py \
      --depth 5000 --direct-check-radius 80 --deep-90-depth 50000

The script checks the finite-part formula, transport, floor reconstruction,
queue identity, and recurrences by exact arithmetic.  The depth-\(50000\)
certificate uses a directed dyadic lower bound for \(A_R\); it does not use
floating-point sign decisions.
