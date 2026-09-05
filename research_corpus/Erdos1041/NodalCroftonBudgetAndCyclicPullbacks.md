# Sharp nodal Crofton budget and cyclic pullbacks

## Status

Assimilated 2026-09-05 from Type B return batch
`erdos1041_20260905_eight_return_stream_01`, source
`state/formal_math/type_b_return_batches/erdos1041_20260905_eight_return_stream_01/sources/r05_nodal_crofton_cyclic_pullbacks.md`,
sections 1 to 3 and the general form of section 5. The arguments were
re-derived during assimilation. The exact deficit calibration is replayed by
`scripts/check_erdos1041_polygonal_shortening.py`. Erdos 1041 remains open.

## Authority boundary

Ordinary analytic statements, no Lean module. The return cites Eremenko and
Hayman, *On the length of lemniscates* (arXiv 0805.2295), printed page 7, for
the Euclidean Crofton formula and for a related sharp spherical inverse-image
estimate. The corpus already reads that paper in
`ReciprocalSweepBoundaryLab.md` and `RootCentredReciprocalSweep.md`. The sharp
constant `2nR`, the deficit decomposition and the equality rigidity below are
the return's contribution as read; their prior-art status is unassessed, and
the equality-case shape `w^n + e^(i phi) b` is close enough to standard nodal
rigidity that a literature check is required before any external claim.

## Statements

For a phase `phi` write

```text
Gamma_phi(f) = f^(-1)(e^(i phi) R) = {z : Im(e^(-i phi) f(z)) = 0},
L_{phi,c}(R) = H^1( Gamma_phi(f) cap closure D(c,R) ).
```

**Theorem 1 (sharp root-disc nodal budget).** If every root of the monic
degree-`n` polynomial `f` lies in `closure D(c,R)`, then for every `phi`

```text
L_{phi,c}(R) <= 2 n R,
```

and more precisely `2nR - L_{phi,c}(R) = D_phi(f) + T_{phi,c}(R)` where

```text
D_phi(f)     = (1/2) * integral_0^pi integral_R (n - N_phi(theta,t)) dt dtheta,
T_{phi,c}(R) = sum_{j=1}^{2n} integral_R^inf ( sqrt(1 + r^2 theta_j'(r)^2) - 1 ) dr,
```

`N_phi(theta,t)` counting transverse intersections of the line
`{Re(z e^(-i theta)) = t}` with `Gamma_phi(f)`, and `theta_j(r)` parametrising
the `2n` exterior radial graphs about `c`. Both terms are nonnegative and
finite. Equality holds exactly when `f(c+w) = w^n + e^(i phi) b` with `b` real
and `|b| <= R^n`, that is on centred regular polygons including the coincident
case.

**Lemma 1 (renormalised Crofton identity).** For any complex polynomial `P` of
degree `n` and `Gamma = {Re P = 0}`, the deficit
`D(P) = (1/2) integral_0^pi integral_R (n - N_P(theta,t)) dt dtheta` is finite
and nonnegative, and for every centre `c`

```text
lim_{S -> inf} [ H^1(Gamma cap closure D(c,S)) - 2 n S ] = -D(P).
```

**Exterior control (9) and the graph form (11).** For `|z - c| = r > R`,

```text
A(r,theta) = Re( (z-c) f'(z) / f(z) ) = sum_j Re( (z-c)/(z-a_j) ) > n/2,
```

so `arg f` increases strictly and winds `n` times around every such circle, each
circle meets `Gamma_phi(f)` in exactly `2n` points, and with
`B = Im((z-c) f'/f)` one has `r theta_j'(r) = -B/A` and

```text
sqrt(1 + r^2 theta_j'(r)^2) - 1 = |(z-c) f'(z)/f(z)| / Re((z-c) f'(z)/f(z)) - 1.
```

**Exact calibration.** For `Gamma_n = {Re z^n = 1}` each of the `2n` ends
satisfies `ds/dr = (1 - r^(-2n))^(-1/2)` for `r >= 1`, and

```text
D(Re z^n - 1) = (n-1) * B(1 - 1/(2n), 1/2)
              = 2 n sqrt(pi) Gamma(1 - 1/(2n)) / Gamma(1/2 - 1/(2n)),
```

which is `2.39628046947118441...` at `n = 2`, `4.48100520133312...` at `n = 3`
and `6.51815401657927...` at `n = 4`.

**The separation example.** For `f = z^n - r^n` with `0 < r < 1` and
`phi = pi/2`, `Gamma_phi(f) = r * Gamma_n` has `n` disjoint components, each
containing exactly one root, so it carries no root-to-root path at all, and its
total length inside the unit disc tends to zero as `r` increases to one.

**Theorem 2 (high cyclic pullbacks of every fixed polynomial).** Let `P` be
monic with all roots in the open unit disc and `P(0) != 0`. Let `Omega_0` be the
component of `{|P| < 1}` containing `0`. Then `Omega_0` contains a nonzero root
`a` of `P`. Choose `rho > 0` with `closure D(0,rho)` inside `Omega_0` and
`rho < |a|`, take a rectifiable path in `Omega_0` from `a` to the circle
`|w| = rho`, trim it at its first meeting, call it `gamma`, and set
`C_P = integral_gamma |dw|/|w| + pi`. Then for every integer `m > C_P` the
pullback `F_m(z) = P(z^m)` has two distinct roots joined inside `{|F_m| < 1}` by
a curve of length

```text
ell_m = (2/m) integral_gamma |w|^(1/m - 1) |dw| + (2 pi/m) rho^(1/m)
      <= 2 C_P / m < 2.
```

If `P(0) = 0`, `F_m` has a repeated root at zero for `m >= 2` and the indexed
formulation is immediate.

**Theorem 4, general form (all powers of a half-plane connector).** Suppose a
monic `P` of degree `d` with roots in the open unit disc has two roots `a_i,a_j`
and a rational `t` in `(0,1)` such that the three-segment path
`a_i -> t a_i -> t a_j -> a_j` lies in `{|P| < 1}` and in a rotated open
half-plane `{Re(e^(-i psi) w) > 1/2}`. Then for every integer `m >= 1` the
pullback `F_m(z) = P(z^m)` has two distinct roots joined inside `{|F_m| < 1}` by
a curve of length

```text
ell_m < 2 (1 - t^(1/m)) + (d_0 * 2^(1 - 1/m) / m) * t^(1/m)
      <= 2 - (2 - d_0) t,
```

where `d_0` is any bound with `|a_i - a_j| <= d_0`, and
`ell_m < 2(-log t + d_0)/m + O(m^(-2))`.

## Proofs

**Lemma 1.** Restricting `Re P` to a line gives a real polynomial of degree at
most `n`, so `N_P <= n` off the exceptional set of tangencies and lines on which
the restriction vanishes identically, and the integrand `n - N_P` is
nonnegative. Translate to `b = -a_{n-1}/(n a_n)` so that
`P(b+w) = a_n w^n + O(w^(n-2))`. The implicit function theorem near each zero of
`Re(a_n e^(i n theta))` produces `2n` exterior ends `z_j(r) = b + r u_j +
O(r^(-1))` with equally spaced unit directions `u_j` and angular derivatives
`O(r^(-3))`. Let `Sigma` be the `n` complete lines through `b` in those
directions. Tangent lines to the regular part of `Gamma` have uniformly bounded
distance from `b`, so outside a strip `|t| <= T` the count is `n` for almost
every direction, by comparison with the leading homogeneous term at large
offsets and by the absence of tangencies or singular crossings in between. This
already gives finiteness of `D(P)`. Applying Crofton to the two truncations and
subtracting, the bounded strip converges by dominated convergence, and outside
it the truncated count for each end is an indicator of the projection of its
cutoff endpoint. Since corresponding endpoints of `Gamma` and `Sigma` differ by
`O(S^(-1))`, the symmetric difference of the two indicator sets has measure
`O(S^(-1))` per end. Finally
`H^1(Sigma cap closure D(c,S)) = sum_k 2 sqrt(S^2 - d_k^2) = 2nS + O(S^(-1))`.

The endpoint-indicator step is stated for directions on which the projection
along an end is monotone. Directions within angle `O(S^(-2))` of an end
direction are not covered by it, since there the projection can be
nonmonotone over a bounded range. Their measure is `O(S^(-2))` and each
contributes at most `n`, so they change the estimate by `O(S^(-2))` and the
limit is unaffected. This is the one place where the return's `O(S^(-1))`
endpoint argument needs an extra sentence; the conclusion stands.

**Theorem 1.** Take `P = -i e^(-i phi) f`, so `{Re P = 0} = Gamma_phi(f)`. For
`|z-c| = r > R`, each summand of `A` is `Re(1/(1-zeta))` with
`zeta = (a_j-c)/(z-c)` of modulus below one, and `Re(1/(1-zeta)) > 1/2` on the
unit disc, giving `A > n/2 > 0`. Hence `arg f` is strictly monotone around each
such circle with total increase `2 pi n`, so `arg f` hits each of `phi` and
`phi + pi` exactly `n` times and the exterior part of `Gamma_phi(f)` is exactly
`2n` radial graphs. Polar arclength gives
`L(S) - L(R) = 2n(S-R) + sum_j integral_R^S (sqrt(1 + r^2 theta_j'^2) - 1) dr`,
and the integrand is `O(r^(-4))` by `theta_j' = O(r^(-3))`, so the tail
converges. Subtracting `2nS` and applying Lemma 1 as `S` increases gives the
decomposition, and nonnegativity of both terms gives `L(R) <= 2nR`. Roots or
critical points on `|z-c| = R` are handled by proving the identity at `R +
epsilon` and letting `epsilon` decrease to zero.

For `(11)`, write `z = c + r e^(i theta)`, so `d_theta log f = i(z-c) f'/f` and
`d_r log f = (z-c) f'/(r f)`. Taking imaginary parts, the constant-argument
condition gives `theta' = -(B/r)/A`, hence `r theta' = -B/A` and
`sqrt(1 + r^2 theta'^2) = sqrt(A^2+B^2)/A`.

**Rigidity.** Equality forces `T = 0`, so `theta_j' = 0` on every exterior end
and all `2n` ends are radial rays about `c`. The real polynomial
`H(w) = Im(e^(-i phi) f(c+w))` vanishes on each ray, hence on each supporting
line, so each of those lines divides `H`. The `2n` rays give at least `n`
distinct lines, and `H` has degree `n`, so there are exactly `n` and `H` is a
product of `n` homogeneous linear forms, hence homogeneous of degree `n` and
equal to its own leading part `Im(e^(-i phi) w^n)`. Therefore
`e^(-i phi)(f(c+w) - w^n)` is a polynomial that is real valued everywhere, so a
real constant `b`. Conversely `f(c+w) = w^n + e^(i phi) b` makes
`Gamma_phi(f)` exactly `n` lines through `c`, giving length `2nR` inside the
disc; the root hypothesis then requires `|b| <= R^n`.

**Calibration.** On an end of `Gamma_n`, `r^n cos(n theta) = 1` gives
`r theta' = r^(-n)(1 - r^(-2n))^(-1/2)` and `ds/dr = (1 - r^(-2n))^(-1/2)`, so
the truncated length is `2n integral_1^S (1-r^(-2n))^(-1/2) dr`. Using

```text
d/dr ( r sqrt(1 - r^(-2n)) ) = (1 + (n-1) r^(-2n)) / sqrt(1 - r^(-2n)),
```

the integral is `S sqrt(1-S^(-2n)) - (n-1) integral_1^S r^(-2n)(1-r^(-2n))^(-1/2) dr`,
so the deficit is `2n(n-1) J` with `J = integral_1^inf r^(-2n)(1-r^(-2n))^(-1/2) dr`.
The substitution `x = r^(-2n)` gives `J = (1/(2n)) B(1 - 1/(2n), 1/2)`, hence
`D = (n-1) B(1 - 1/(2n), 1/2)`. The gamma-quotient form follows from
`Gamma(3/2 - 1/(2n)) = (1/2 - 1/(2n)) Gamma(1/2 - 1/(2n))` together with
`(n-1)/(1/2 - 1/(2n)) = 2n`.

**Theorem 2.** `{|P| < 1}` is bounded, so `Omega_0` is a bounded component with
`|P| = 1` on its boundary. If `Omega_0` contained no zero of `P`, then
`log|P|` would be harmonic on `Omega_0`, zero on the boundary, and equal to
`log|P(0)| < 0` at an interior point, contradicting the minimum principle. Hence
`Omega_0` contains a root, and `P(0) != 0` makes it nonzero. To keep the path
inside the unit disc, choose `max_j |a_j| < r_* < 1`; for `r > r_*`,
`d_r log|P(r e^(i theta))| = (1/r) Re(z P'/P) > 0` by the same half-plane
inequality, so radial retraction onto `closure D(0,r_*)` does not increase
`|P|` and carries a path in `Omega_0` to a path in `Omega_0`. Form the loop
`gamma`, one positive circuit of `|w| = rho`, then `gamma` reversed. Its winding
number about zero is one, so the lift under `z -> z^m` starting at a root `z_0`
with `z_0^m = a` ends at `e^(2 pi i/m) z_0`, a different root for `m >= 2`.
Containment is exact because `|F_m(z)| = |P(w)|`. Since
`|dz| = (1/m)|w|^(1/m - 1)|dw|` and `|w| < 1` on the loop, the displayed length
formula and the bound `2 C_P/m` follow. Note `C_P > pi`, so `m > C_P` already
forces `m >= 4`.

**Theorem 4, general form.** The half-plane hypothesis puts the whole
three-segment path in a simply connected region missing zero, since every radial
point `s a_i` with `s in [t,1]` and every chord point
`t((1-u) a_i + u a_j)` inherits the strict half-plane bound. Choose one
holomorphic branch of `w^(1/m)` there and lift. The endpoints lie over distinct
base roots, so they are distinct roots of `F_m`, and containment is exact. The
lifted radial arms have total length
`(|a_i|^(1/m) + |a_j|^(1/m))(1 - t^(1/m)) < 2(1 - t^(1/m))`. On the chord,
`|(1-u)a_i + u a_j| > 1/2` by convexity of the half-plane, so
`|w|^(1/m - 1) < (t/2)^(1/m - 1)` and the lifted chord length is below
`(d_0 2^(1 - 1/m)/m) t^(1/m)`. Finally `2^(1-1/m)/m <= 1` for every `m >= 1` and
`t^(1/m) >= t`, so the bound collapses to `2 - (2 - d_0) t`. Expanding
`t^(1/m) = 1 + (log t)/m + O(m^(-2))` gives the asymptotic form.

## Consumers

`ReciprocalSweepBoundaryLab.md` and `RootCentredReciprocalSweep.md` record the
crude Crofton budget: a nodal level set of degree at most `2n` meets a line at
most `2n` times, so its length is at most `2 pi n`. Theorem 1 replaces `2 pi n`
by `2 n R` on the root disc, improves the constant by a factor `pi` at `R = 1`,
adds an exact deficit decomposition, and classifies equality. That is a strict
upgrade of the recorded budget.

The upgrade does not answer transfer question 2 of
`ReciprocalSweepBoundaryLab.md`, which asks whether the nodal length can be
charged to `n` root attachments so that one pair costs at most two. The
separation example above is the reason, and it is the same mechanism already
recorded in the Proposition of `RootCentredReciprocalSweep.md`: on `z^n - r^n`
the relevant sublevel set has `n` components with one root each. The return
reaches that obstruction from the phase side, and its conclusion is that a nodal
proof must add adaptive phase and component selection.

Theorem 2 sits beside two corpus pullback theorems and is subsumed by neither.
`CyclicTrinomialFiberCase.md` proves the target for `f(z) = (z-h)^(qm) +
a (z-h)^(qr) + c` for every `q >= 2`, that is arbitrary power but trinomial base.
`ClosePairCyclicQuotientCase.md` proves it for `f(z) = P((z-h)^q)` with arbitrary
`P` of degree `m` and every `q >= 2`, under the close-pair criterion
`max_{0<=y<=Y} Phi_m(y) <= 1` with `Phi_m(y) = y(1 + sqrt(1-y))^(m-2)` and
`Y = d^2/4`. Theorem 2 removes the close-pair hypothesis and pays for it with a
threshold `m > C_P`. The two pinned witnesses show the ranges are genuinely
different: their selected chords give `Phi_6(Y) = 3.0289` and
`Phi_9(Y) = 12.0835`, both far above one, so the close-pair criterion does not
reach them, while the half-plane form of Theorem 4 does, for every `m >= 1`.

`fixed_safe_monodromy_block_average_lift_length` should read Theorem 2 as
positive evidence that nontrivial monodromy plus a metric budget is achievable
in a whole all-degree family without any critical-hub selection. It supplies no
moved-block average for a general polynomial and does not discharge the
producer.

## Claim boundary

Theorem 1 is a sharp bound on the length of a whole inverse image of a line and
carries no component selection, so it does not by itself produce a root-to-root
path. The separation example proves that no strengthening of the scalar deficit
at a prescribed phase can force two roots into one nodal component. Theorem 2 is
a statement about high pullbacks of a fixed base polynomial, with a
base-dependent threshold, and says nothing about a general polynomial of degree
`m deg P`. The general form of Theorem 4 assumes a certified half-plane
three-segment connector as input. None of these proves Erdos 1041. Prior-art
status of Theorem 1 and of the deficit calibration is unassessed.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_polygonal_shortening.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_pinned_witness_hub_connectors.py
```
