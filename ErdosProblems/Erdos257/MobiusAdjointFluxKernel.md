# A positive Möbius--adjoint kernel for the flux at infinity

Status: exact theorem-discovery note, 2026-08-20.  The analytic identities
below have not been added to Lean.  They are deductions from the checked
carry recurrence and standard absolutely convergent rearrangements.  The
last section records a structural no-go: the strongest natural positive
linear adjoint splits the Mersenne atom into two exactly cancelling parts, so
it does not by itself force zero flux.

## 1. The multiple-Möbius transform

Let `A` be a Boolean support, write `b_d=1_A(d)`, and put

\[
 f_A(n)=\sum_{d\mid n}b_d.
\]

For an absolutely summable atom `h(d)`, define its Möbius transform over
multiples by

\[
 \phi_h(n)=\sum_{k\ge1}\mu(k)h(kn).
\]

Finite Möbius inversion followed by absolute convergence gives

\[
 \sum_{j\ge1}\phi_h(jd)=h(d),
 \qquad
 \sum_{n\ge1}\phi_h(n)f_A(n)=\sum_{d\ge1}b_dh(d).       \tag{1}
\]

Thus a test function on the divisor-count word can be designed to recover a
chosen atom on the original Boolean support.  This retains multiplicative
ancestry instead of testing the carry by an unrelated periodic weight.

## 2. The positive dyadic adjoint

Choose `h(d)=2^{-d}` and set

\[
 \Phi_n=\sum_{k\ge1}\mu(k)2^{-kn},
 \qquad
 \Psi_n=2\Phi_{n+1}-\Phi_n.                              \tag{2}
\]

Then (1) becomes

\[
 \sum_{j\ge1}\Phi_{jd}=2^{-d},
 \qquad
 \sum_{n\ge1}\Phi_nf_A(n)=\sum_{d\in A}2^{-d}.         \tag{3}
\]

The adjoint coefficient is strictly positive at every rank.  Indeed the
`k=1` term cancels in (2), and

\[
 \Psi_n
 =\sum_{k\ge2}\mu(k)(2^{1-k}-1)2^{-kn}.
\]

The `k=2` term is `2^{-2n-1}`.  A negative term requires `mu(k)=+1`; the
first possible such squarefree integer is `k=6`.  Discarding every other
positive term and bounding all possible negative terms in absolute value
therefore gives

\[
 \Psi_n\ge 2^{-2n-1}-\frac{2^{-6n}}{1-2^{-n}}>0.         \tag{4}
\]

Also `Phi_n=2^{-n}+O(4^{-n})` and `Psi_n=O(4^{-n})`.

## 3. Exact flux identity

For the actual `1/21` greedy support let

\[
 C_N=\texttt{twentyOneGreedyCarry}(N),
 \qquad
 \lambda=\lim_{N\to\infty}C_N/2^N.
\]

The checked recurrence `twentyOneGreedyCarry_succ` is

\[
 21f_A(n)=2C_{n-1}-C_n,
 \qquad C_0=1.                                           \tag{5}
\]

Finite summation by parts gives

\[
 21\sum_{n=1}^{N}\Phi_nf_A(n)
 =2\Phi_1C_0+\sum_{n=1}^{N-1}\Psi_nC_n-\Phi_NC_N.       \tag{6}
\]

The normalized carry is nonnegative and antitone by
`scaled_twentyOneGreedyCarry_antitone`, hence `0<=C_N<=2^N` and the limit
`lambda` exists.  Equations (2) and (4) make the bulk sum absolutely
convergent, while `Phi_N C_N -> lambda`.  Passing to the limit in (6) and
using (3) yields

\[
 \boxed{
 21\sum_{d\in A}2^{-d}
 =2\Phi_1+\sum_{n\ge1}\Psi_nC_n-\lambda.}                \tag{7}
\]

Unlike a local pulse identity, (7) sees the homogeneous shift
`C_n -> C_n+eta*2^n`: its boundary changes by `eta`, and its positive bulk
changes by

\[
 \eta\sum_{n\ge1}2^n\Psi_n
 =\eta(1-2\Phi_1).
\]

The latter equality is the telescoping limit of (2).

## 4. The complementary correction and exact cancellation

Put

\[
 e_d=\frac1{2^d(2^d-1)},
 \qquad
 \Theta_n=\sum_{k\ge1}\mu(k)e_{kn}.
\]

The classical Lambert--Möbius identity

\[
 \sum_{k\ge1}\frac{\mu(k)}{2^{kn}-1}=2^{-n}
\]

and `1/(2^d-1)=2^{-d}+e_d` imply

\[
 \Theta_n=2^{-n}-\Phi_n,
 \qquad
 2\Theta_{n+1}-\Theta_n=-\Psi_n.                         \tag{8}
\]

Here `Theta_n=O(4^{-n})`, so its boundary pairing with even a positive-flux
carry vanishes.  Applying the same summation by parts gives the exact
correction identity

\[
 \boxed{
 21\sum_{d\in A}e_d
 =1-2\Phi_1-\sum_{n\ge1}\Psi_nC_n.}                      \tag{9}
\]

Adding (7) and (9) recovers

\[
 21\sum_{d\in A}\frac1{2^d-1}=1-\lambda.                \tag{10}
\]

For the actual greedy orbit, the checked remainder/carry bridge identifies
`lambda` with `21` times the limiting greedy gap.

## 5. Consequence for invariant design

Equations (7)--(9) are a positive, flux-sensitive Boolean adjoint law:
`Psi_n>0`, the divisor convolution is inverted exactly, and the homogeneous
boundary is retained.  Nevertheless they do not force `lambda=0`.  The same
positive bulk occurs with opposite signs in the dyadic and Mersenne-correction
coordinates, and adding the two identities produces exactly the original
value/gap equation (10).

This kills a broad class of proposed linear zero-flux arguments.  Any test
obtained by splitting the Mersenne atom and applying a linear adjoint to the
carry can only redistribute the same boundary charge unless it supplies an
additional inequality coupling the two pieces.  The next invariant must use
something not present in a linear divisor word: for example the Boolean
idempotence `b_d^2=b_d`, pair correlations between dilation channels, or a
finite-volume exchange inequality.  Those are the first places where the
exact cancellation in (8) can genuinely break.

## 6. Audit and the first nonlinear identity

The multiple-Möbius inversion in (1) is valid: after interchanging the
absolutely convergent sums, the coefficient of (h(md)) is
(\sum_{k\mid m}\mu(k)), equal to (1) for (m=1) and (0) otherwise.
For (h(d)=2^{-d}), the positivity estimate (4) is also valid.  The negative
terms have (mu(k)=1), hence (k\ge6), and their total absolute value is at
most (2^{-6n}/(1-2^{-n})).  The boundary coefficient in (6) is exactly
(-\Phi_NC_N); since (2^N\Phi_N\to1), it tends to (-\lambda).  Finally,
(\Theta_n=2^{-n}-\Phi_n) and (2\Theta_{n+1}-\Theta_n=-\Psi_n), so the two
correction terms in (7) and (9) cancel exactly when added.  No sign or boundary
term is missing in (10).

There is a precise nonlinear consequence of Booleanity.  Write

\[
 f(n)=\frac{2C_{n-1}-C_n}{21},
 \qquad
 X_n=\sum_{d\mid n}\mu(d)\bigl(2C_{n/d-1}-C_{n/d}\bigr).
\]

Since (f=\mathbf 1_A*1), Boolean Möbius inversion says
(b_n=\mathbf1_A(n)=X_n/21), and (b_n^2=b_n) gives the exact quadratic
carry identity

\[
 X_n^2=21X_n,
 \qquad X_n\in\{0,21\}.                                  \tag{11}
\]

This is genuinely nonlinear and distinguishes a carry row from an arbitrary
real solution of the linear recurrence.  It does not yet force (\lambda=0\):
the (d=1) contribution in (X_n) is already the local pulse
\(21f(n)), and the remaining terms are divisor-scale pulses.  A Hardy- or
Poincare-type estimate would need to use greedy complementarity, not merely
(11), to compare these scales.

Indeed, omit complementarity and choose (M) so large that
\[
\sum_{d\ge M}\frac1{2^d-1}<\frac1{21}.
\]
Take the cofinite Boolean set (A=\{d:d\ge M\}), define
\(f(n)=\#\{d\mid n:d\in A\}\), anchor at the actual value (C_0=1), and solve

\[
 C_n=2C_{n-1}-21f(n).
\]

Then (C_n\ge0), and
\[
\frac{C_n}{2^n}\longrightarrow
1-21\sum_{d\ge M}\frac1{2^d-1}>0.
\]
Identity (11) still holds because (A) is Boolean.  Thus even the correct
denominator-(21) anchor, Möbius inversion, positivity, cofinite density, and
quadratic Booleanity do not force zero flux.  The missing hypothesis is
precisely the greedy complementarity condition tying the support decisions to
the residual.
