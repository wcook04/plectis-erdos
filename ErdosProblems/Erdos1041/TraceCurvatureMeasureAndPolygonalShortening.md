# Trace-curvature measure and sharp polygonal shortening

## Status

Assimilated 2026-09-05 from Type B return batch
`erdos1041_20260905_eight_return_stream_01`, source
`state/formal_math/type_b_return_batches/erdos1041_20260905_eight_return_stream_01/sources/r01_inverse_fibre_curvature_polygonal_hub.md`,
sections 2 to 5. The analytic arguments were re-derived line by line during
assimilation and every step below was reproduced. The finite claims of section 4
are replayed by
`scripts/check_erdos1041_polygonal_shortening.py`. Erdos 1041 remains open.

## Authority boundary

These are ordinary analytic statements. No Lean module states them. The return
supplies the proofs; the assimilation supplies the re-derivation, the numerical
falsification probe, and the comparison against the corpus constants recorded in
`GroupedCriticalClusterMonodromy.md`. No literature-priority claim is made, and
the log-moment inequality of Theorem A is a Hadamard-type bound of a shape the
directory has already been bitten by once (see the prior-art caution in
`RootCentredReciprocalSweep.md`).

## Statements

Fix `f` monic of degree `n >= 3`. For a regular value `w` let `z_1(w),...,z_n(w)`
be the solutions of `f(z) = w`, let

```text
D_j(w) = product_{k<l, k,l != j} (z_l(w) - z_k(w))
```

be the omitted-root Vandermonde minors, and for `1 <= p <= 2` set

```text
H_p(w) = n^(2-n-2/p) * (sum_j |D_j(w)|^p)^(2/p),
N = (n-1)(n-2),    E = pi*N/n.
```

Continuation permutes the minors up to sign, so `H_p` is single valued.

**Theorem A (completed trace-curvature measure).** `mu_p = (1/2) Laplacian log H_p`
is a positive finite measure on the value plane with `mu_p(C) = E`, and

```text
log H_p(w) = (1/pi) * integral log|w - zeta| dmu_p(zeta).
```

If the roots of `f` lie in a disc of radius `R`, then

```text
(1/E) * integral log|zeta| dmu_p(zeta) <= n log R,
```

with equality exactly when the roots are a translated and rotated regular
`n`-gon of radius `R`. Equivalently, in derivative form,

```text
|Disc f| * n^(2-2/p-n) * (sum_j |f'(a_j)|^(-p))^(2/p) <= R^((n-1)(n-2)).
```

**Theorem B (curvature is an exact variance).** With `rho_p(w) = (sum_j
|z_j'(w)|^p)^(1/p)`, `q_j = -f''(z_j)/f'(z_j)^2` and weights
`omega_j = |z_j'|^p / sum_k |z_k'|^p`, at every regular value

```text
Laplacian log rho_p = p * V_p,
V_p = sum_j omega_j |q_j|^2 - |sum_j omega_j q_j|^2 >= 0.
```

The conformal metric `rho_p^2 |dw|^2` therefore has Gaussian curvature
`-p V_p / rho_p^2 <= 0`, and `mu_p = p V_p dA` away from critical values.

**Theorem C (exact collision masses).** For a critical value `v` put
`m_v = sum_{f(c)=v} (e_c - 1)` and `e_v = max_{f(c)=v} e_c`. Then

```text
mu_p = p V_p dA + pi * sum_v [ m_v - 2(1 - 1/e_v) ] delta_v,
```

the atom coefficients are nonnegative and independent of `p`, an isolated
`d`-fold ramification point carries mass `pi (d-1)(d-2)/d`, a simple critical
point carries no atom, and

```text
integral p V_p dA = 2 pi [ sum_v (1 - 1/e_v) - (1 - 1/n) ].
```

For `f = z^n - r^n` the whole measure collapses to `E * delta_{-r^n}`.

**Theorem D (sharp polygonal shortening).** Let `f(phi(u)) = v + u^d` with
`phi(0) = c`, `a = phi'(0) != 0`, `d >= 3`, `0 < |v| < 1`, and suppose the
straight value segment from `0` to `v` carries no other critical value and its
`d` relevant inverse branches reach distinct roots. Let `Lambda_0` be the total
length of those arms. Using the physical contour `phi(sigma P_s)` with
`sigma^d = -v/|v|` and `P_s` the regular `d`-gon of circumradius `s`,

```text
2 Lambda_s + Per(W_s) = 2 Lambda_0 - 2 d |a| (1 - sin(pi/d)) s + O(s^2),
```

and the coefficient is optimal among contours through the same `d` truncated-arm
endpoints.

**Lemma E (exact polygon containment).** For the regular `d`-gon `P_s` and
`s^d <= b`,

```text
max_{u in P_s} |b - u^d| = b + s^d cos^d(pi/d),
```

attained at an edge midpoint. The sufficient admissibility condition for
Theorem D is therefore `|v| + s^d cos^d(pi/d) < 1` together with `s^d < |v|`.

**Corollary F (regular family).** For `f_0 = z^n - r^n` with `0 < s < r` and
`r^n + s^n cos^n(pi/n) < 1`, every adjacent root pair is joined inside the open
unit lemniscate by a connector of length

```text
L_polygon = 2r - 2s (1 - sin(pi/n)).
```

**Theorem G (explicit coefficient neighbourhood).** Fix `n >= 3`, `0 < r < 1`
and `s` admissible for Corollary F. Put `m = s cos(pi/n)`,
`L_0 = 2r - 2s(1 - sin(pi/n))`, `g = 1 - L_0/2` and `R_* = r(1 + g/(4n))`. If
`f = z^n - r^n + h` with `h = sum_{k<n} h_k z^k` satisfies

```text
sum_k |h_k| R_*^k < (3g/16) m^n,      sum_k k |h_k| R_*^(k-1) <= (g n/4) m^(n-1),
```

then every adjacent pair in the continued labelling is joined inside `{|f|<1}`
by a curve of length at most `L_0/(1 - g/2) < 2`.

## Proofs

**Theorem A.** `log H_p` is `2 log` of the `l^p` norm of a locally holomorphic
vector, hence subharmonic off the critical values, and locally bounded above
across them, so the subharmonic extension exists. For large `w`,
`z_j(w) = w^(1/n) omega_j + O(1)` with `omega_j^n = 1`, and for the `n`-th roots
of unity `product_{k != j} |omega_j - omega_k| = n`, so the full Vandermonde has
modulus `n^(n/2)` and each minor has modulus `n^((n-2)/2)`. Substituting into
the definition, `sum_j |D_j|^p ~ |w|^(pN/(2n)) n^(1 + p(n-2)/2)`, and the
normalising constant `n^(2-n-2/p)` cancels every power of `n`, leaving
`H_p(w) = |w|^(N/n)(1 + O(|w|^(-1/n)))`. Integrating the Laplacian over a large
circle gives mass `pi N/n = E`. The potential in the statement has the same
Laplacian and the same behaviour at infinity, so the difference is an entire
harmonic function tending to zero, hence zero.

At `w = 0`, translate so the enclosing disc is centred at the origin; the minors
are translation invariant. With `A` the `n` by `n-1` matrix with rows
`(1, a_j, ..., a_j^(n-2))`, Cauchy-Binet gives `sum_j |D_j(0)|^2 = det(A* A)`,
so `H_2(0) = det(A* A)/n^(n-1)`. Hadamard bounds `det(A* A)` by the product of
column norms, each at most `n R^(2k)`, giving `H_2(0) <= R^N`. For `p <= 2` the
power-mean inequality `||x||_p^2 <= n^(2/p-1) ||x||_2^2` gives `H_p <= H_2`
pointwise. Evaluating the potential representation at zero and dividing by `E`
turns `log H_p(0) <= N log R` into `(1/E) integral log|zeta| dmu_p <= n log R`,
because `pi/E = n/N`.

Equality forces orthogonal columns and `|a_j| = R` for every `j`. Orthogonality
against the constant column gives `sum_j a_j^k = 0` for `1 <= k <= n-2`, so
Newton's identities give `e_1 = ... = e_{n-2} = 0`. Constant modulus gives the
self-inversive relation `e_(n-1) = e_n conj(e_1)/R^2 = 0`. Hence
`f = z^n - lambda` with `|lambda| = R^n` after translation, and that
configuration attains every inequality in the chain.

**Theorem B.** Put `u_j = log|z_j'|`, harmonic since `z_j'` is locally
holomorphic and nonvanishing. With `S = sum_j exp(p u_j)`,
`Laplacian log S = p sum_j omega_j Laplacian u_j + p^2 Var_omega(grad u)`, and
the first term vanishes, so `Laplacian log rho_p = (1/p) Laplacian log S =
p Var_omega(grad u)`. The complex representative of `grad u_j` is `conj(q_j)`
with `q_j = (d/dw) log z_j' = -f''(z_j)/f'(z_j)^2`. Nonnegativity is
Cauchy-Schwarz. The curvature formula is the standard conformal identity
`K = -rho^(-2) Laplacian log rho`. Since `|D_j| = |Delta| / |f'(z_j)|`, one has
`H_p = n^(2-n-2/p) |Disc(f-w)| rho_p^2`, and `log|Disc(f-w)|` is harmonic in `w`
off the critical values, so `mu_p = Laplacian log rho_p = p V_p dA` there.

**Theorem C.** `Disc(f-w)` is a polynomial in `w` vanishing to order `m_v` at a
critical value `v`, because a critical point `c` of local degree `e_c` is a root
of `f'` of multiplicity `e_c - 1`. Locally, a colliding group of size `e`
contributes `|z_j'| ~ |w-v|^(1/e - 1)`, and the largest `e` dominates
`rho_p`, giving `rho_p ~ C |w-v|^(-(1-1/e_v))`. Hence
`log H_p = [m_v - 2(1-1/e_v)] log|w-v| + O(1)`, and
`Laplacian log|w-v| = 2 pi delta_v` supplies the atom. Nonnegativity follows
from `m_v >= e_v - 1` and `e_v - 3 + 2/e_v = (e_v-1)(e_v-2)/e_v >= 0`. Summing
`m_v = n-1` over all critical values and subtracting from `E` gives the
absolutely continuous total.

**Theorem D.** The vertices `phi(sigma s zeta_j)` lie on the prescribed arms
because `f(phi(sigma s zeta_j)) = v - (v/|v|) s^d` is independent of `j`. The
removed terminal arm lengths sum to at least `d(|a| - M_s)s` with
`M_s = sup_{|u|<=s} |phi'(u) - a|`, and the polygon perimeter is at most
`2ds sin(pi/d)(|a| + M_s)`. Since `M_s = O(s)`, the first-order coefficient is
`-2d|a|(1 - sin(pi/d))`. Optimality holds because a closed rectifiable curve
through a point set has length at least the perimeter of the convex hull, and
that perimeter is `2d|a|s sin(pi/d) + O(s^2)` for `d` points in convex position.
The value image is a Jordan domain because the argument of `u^d` along one
polygon edge increases through exactly `2 pi`, and the restriction is proper of
degree `d` for small `s`.

**Lemma E.** `b - u^d` is holomorphic and invariant under `u -> e^(2 pi i/d) u`,
so its maximum modulus over `P_s` is attained on one edge. Parametrise that edge
as `u = s e^(i theta)(c + iy)` with `theta = pi/d`, `c = cos theta`,
`|y| <= sin theta`, so `b - u^d = b + s^d (c+iy)^d`. The `y`-derivative of the
squared modulus has the sign of `-b sin((d-1) varphi) + s^d rho^d sin varphi`,
where `c + iy = rho e^(i varphi)` with `0 <= varphi <= theta` and `rho <= 1`.
The identity `sin((d-1)varphi) - sin varphi = 2 cos(d varphi/2) sin((d-2)varphi/2)`
is nonnegative on that range, and `s^d <= b`, `rho <= 1` then make the
derivative nonpositive for `y >= 0`. The map `y -> -y` conjugates the value, so
the maximum sits at `y = 0`, where `u^d = -s^d cos^d(pi/d)`.

**Corollary F.** Apply Theorem D to `f_0 = z^n - r^n` with `phi = identity`,
`a = 1`, `v = -r^n`, `d = n`. The truncated arms have total length `n(r-s)` and
the perimeter is `2ns sin(pi/n)`, so the preimage-perimeter identity gives each
complete lift length `2(r-s) + 2s sin(pi/n)`. Lemma E gives the admissibility
condition `r^n + s^n cos^n(pi/n) < 1`.

**Theorem G.** Set `tau = g/4`, `eta = tau/n`. On the reference connector,
`m <= |w| <= r`. On `|z - w| = eta|w|`, the elementary bound
`|(1+zeta)^n - 1| >= 1 + 2 n eta - (1+eta)^n >= 1 + 2 tau - e^tau >= (3/4) tau`
gives `|z^n - w^n| >= (3g/16)|w|^n >= (3g/16) m^n`, which is exactly the
hypothesis on `h`. Rouche therefore yields a unique `Phi(w)` in that disc with
`f(Phi(w)) = w^n - r^n`; uniqueness uses `eta < 2 sin(pi/n)`, which holds
because `eta < 1/(4n)`. Differentiating gives `Phi' = n w^(n-1)/f'(Phi)`, and
the second hypothesis with `(1-eta)^(n-1) >= 1 - tau` gives
`|f'(Phi)| >= n|w|^(n-1)(1 - g/2)`, so `|Phi'| <= (1 - g/2)^(-1)`. The image of
the reference connector has length at most `L_0/(1-g/2) = 2(1-g)/(1-g/2) < 2`,
and its values are exactly those of the reference connector, so containment
transfers with no further modulus estimate.

## Consumers

`GroupedCriticalClusterMonodromy.md` records the corpus lollipop formula
`ell = 2r - 2(1 - pi/n)s` for the same regular family, with admissibility
`s^n < min(r^n, 1-r^n)`. Corollary F strictly improves both halves of that row:
`sin(pi/n) < pi/n` for every `n >= 2`, so the polygon subtracts strictly more,
and the containment condition gains the factor `cos^n(pi/n) < 1`. In degree
three the improvement changes the sign of the first variation. The circular
contour gives `2r + 2(pi/3 - 1)s`, which grows with `s`; the polygon gives
`2r - (2 - sqrt(3))s`, which shrinks. The measured gains at `n = 3,4,6,9` are
`0.181172`, `0.078291`, `0.023599` and `0.007046`.

Theorem G is the quantitative form of the qualitative Theorem 3 of
`GroupedCriticalClusterMonodromy.md`, which supplies an unquantified open
coefficient neighbourhood. Theorem G names the neighbourhood by explicit
coefficient sums and produces the curve. The `r -> 1` degeneration recorded there
survives: `g -> 0` as `L_0 -> 2`, so both hypotheses shrink.

Theorems A to C are the first entry in this directory of a value-plane curvature
measure attached to the whole inverse fibre. The corpus's nearest objects are the
Gram-determinant Fekete stability bound in `NearFeketeCuspLaw.md`
(`quantitative_fekete_stability_hadamard_defect`), which uses the full
`n` by `n` Vandermonde Gram rather than the omitted-root minors, and the
component lifetime transport identity. Theorem C's collision atom
`pi (d-1)(d-2)/d` is the completed replacement for the discriminant order alone,
and it vanishes at a simple critical point, which is the reason the regular model
concentrates its whole mass at one point.

The open producer `fixed_safe_monodromy_block_average_lift_length` consumes
Corollary F and Theorem G as a strictly better local rung on the regular family.
Neither closes it. Theorem A bounds a log-moment of the whole value-plane
measure, and the producer needs `2 Lambda(alpha,W) + Per(W)` on one admissible
moved block. The return names that gap explicitly, and the assimilation confirms
it: the log-moment bound integrates against the whole measure and carries no
per-block allocation.

## Claim boundary

Every statement above is a proved statement about a restricted object. Theorem A
is an inequality for a global measure. Theorem D is a first-order local surgery
under a hypothesis (an isolated `d`-fold critical value on a clean segment) that
is not proved to occur for a general configuration. Theorem G is a perturbative
theorem with explicit but small coefficient boxes. None of them selects a cluster
in a general configuration, none of them supplies the moved-block metric
allocation, and none of them proves Erdos 1041. The prior-art status of Theorem A
is unassessed.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_polygonal_shortening.py
```
