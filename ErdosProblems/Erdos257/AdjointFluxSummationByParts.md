# Adjoint summation by parts for the carry flux

Let (c_0,c_1,ldots) be a carry row and write

\[
 d_n=2c_{n-1}-c_n\qquad(n\ge1).
\]

For the denominator-(21) row, (d_n=21\,\operatorname{supportCoeff}(A)(n)).
The homogeneous solution (c_n=\lambda2^n) is the flux direction.

## 1. Exact finite identities

For any test sequence (arphi_1,ldots,arphi_N), direct reindexing gives

\[
 \sum_{n=1}^N\varphi_n d_n
 =2\varphi_1c_0
  +\sum_{n=1}^{N-1}(2\varphi_{n+1}-\varphi_n)c_n
  -\varphi_Nc_N.                                      \tag{1}
\]

The adjoint null test (arphi_n=2^{-n}) annihilates the bulk exactly:

\[
 \sum_{n=1}^N2^{-n}d_n=c_0-2^{-N}c_N.                 \tag{2}
\]

Hence, whenever (c_N/2^N\to\lambda),

\[
 \sum_{n\ge1}2^{-n}d_n=c_0-\lambda.                  \tag{3}

\]

This is the exact adjoint form of zero flux.  It also proves the required
separation property: replacing (c_n) by (c_n+\mu2^n) leaves every (d_n)
unchanged but changes the boundary limit from (lambda) to (lambda+mu).
No bulk test annihilating the homogeneous mode can detect that replacement;
the boundary term in (1) is indispensable.

More generally, put (arphi_n=2^{-n}psi_n).  Then

\[
 \sum_{n=1}^N2^{-n}\psi_nd_n
 =\psi_1c_0+
   \sum_{n=1}^{N-1}2^{-n}(\psi_{n+1}-\psi_n)c_n
   -2^{-N}\psi_Nc_N.                                  \tag{4}
\]

This is the useful adjoint family.  A period-six (psi) may encode the
denominator-(21) residue, but its bulk coefficient changes sign unless
(psi) is constant.  Thus periodicity alone cannot make the bulk term
sign-definite for all nonnegative carry rows.

## 2. Adversarial tests for periodic and multiplicative tests

Take a finite Boolean support (A=\{m\}) and the unscaled recurrence
(d_n=\mathbf1_{m\mid n}), (c_0=1).  Then

\[
 c_n=2^n-\sum_{k m\le n}2^{n-km},
\]

which is nonnegative.  If a periodic test (psi) has a rise at (n) and a
fall at (n+1), choosing (m=n) or (m=n+1) makes the first nonzero bulk
contribution occur with either sign.  Therefore no nonconstant periodic test
has a sign-definite bulk identity uniformly over finite Boolean supports.

The same placement test is adverse to completely multiplicative tests.  A
nonconstant completely multiplicative (psi) has some prime (p) with
(psi(p)\nepsi(1)); the singleton supports (A=\{p\}) and (A=\{p^2\})
place their first divisor pulses at different positions.  The bulk terms in
(4) therefore sample different values of (psi) before any global sign
conclusion can be drawn.  This falsifies the naive claim that multiplicativity
alone provides a positive adjoint functional; a stronger divisor-zeta
hypothesis would be needed.  This is an exact finite-support obstruction,
not a numerical-depth claim.

For the period-six denominator-(21) residue word, the same argument applies
to any nonconstant cyclic weighting: a Boolean support can place its first
divisor pulse at any chosen residue by taking a singleton rank in that residue
class.  The target period therefore supplies arithmetic labels but no universal
positivity functional.

## 3. What survives

The only universal sign-definite adjoint identity in this class is the constant
test, which is merely (2) after the dyadic normalization.  It quantizes the
weighted divisor mass to the flux boundary, but it does not control the dense
tail because the sum is exactly the original carry relation.

A genuinely new test would need an additional constraint unavailable to arbitrary
finite Boolean supports—for example, a divisor-zeta positivity inequality that
couples several ranks before applying (4).  Periodic target characters and
completely multiplicative characters alone cannot provide it.
