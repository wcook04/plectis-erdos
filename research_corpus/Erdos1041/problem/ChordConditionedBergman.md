# A chord-conditioned refinement of the Bergman geodesic bound

## Status

This note assimilates two independent returns of the 2026-09-05 eight-return
stream, `r02_chord_conditioned_bergman.md` and
`r04_endpoint_conditioned_bergman.md`. They prove the same theorem by two
different routes and bound its coefficient by two different closed forms. Every
step below was re-derived here; the verification findings, including one
invalid step in a published proof chain, are recorded in the authority boundary.

The theorem refines
[BergmanGeodesicInvariance.md](BergmanGeodesicInvariance.md) Theorem C' by
keeping the Euclidean separation of the two endpoints in the estimate instead of
discarding it. It supplies a strict improvement of the certificate of
[FirstTwoCriticalOptimizedBergman.md](FirstTwoCriticalOptimizedBergman.md)
Theorem 2 on an explicit rational cubic, and a new rational sufficient
condition for two-root components. **Erdős #1041 remains open** and nothing
below claims otherwise. The parent statement is unchanged: a monic polynomial
whose roots lie in the open unit disc has two roots joined inside `{|f| < 1}`
by a curve of length less than `2`.

## Authority boundary

Both returns were advisory on arrival. The following were checked here.

* Re-derived and correct: the Bergman kernel identities `(4)`, `(8)`, `(9)`;
  detailed balance and the intertwining of the Markov operator with the Bergman
  restriction operator; the single-crossing and total-variation computation
  giving `lam(x) <= x`; the two trace formulas and the parity split; the
  integration-by-parts operator `Q`, the stochastic comparison, and the closed
  form `b1`; both proofs of the analytic inequality; both sharpness
  constructions including univalence; the pinching lower bound; the two-root
  Blaschke normalisation `x = v/t`; the monotonicity of the window functions;
  the connected-cluster substitution; the moved-sheet summation; the global area
  estimate `Area{|f| < sigma} <= pi sigma^(2/n)`.
* Verified numerically: matrix `(14)` reproduces the exact trace closed form to
  `1e-15` at `r = 0.25, 0.5, 0.7, 0.9`, and its top eigenvalue on `h^perp`
  reproduces both returns' published eigenvalue tables to `1e-8` for
  `r <= 0.9`, agreeing to `2e-5` at `r = 0.99` where the truncation binds. The
  two returns compute the same spectral constant, which is one independent
  cross-check of the operator normalisations.
* One defect. The published proof of the `17/20` criterion in `r04` bounds
  `(1 - b(x)) d^2` by `3/10`, which requires `b(x) >= 7/10` and is false for
  small `x`, where `b(x)` tends to `0`. The conclusion survives. The repaired
  chain is the one proved under Consumers below, and it lands on the same constant
  `767/200`, because `1 - 7/10 = 3/10`.
* One hidden hypothesis made explicit. The substitution of `x` for `lam(x)` in
  the explicit form of the theorem needs `E - d^2 >= 0`, which follows from the
  activated bound `L^2 <= E` together with `d <= L`, and is stated as part of
  the theorem here.

## The parameter

Throughout, `Omega` is simply connected with finite area `A`, `a != b` lie in
`Omega`, `Gamma` is their hyperbolic geodesic, `L = length(Gamma)`,
`d = |a - b|`, `rho = rho_Omega(a,b)`, and

```text
x  =  (1 - sqrt(1-rho^2)) / (1 + sqrt(1-rho^2))  in (0,1),
E  =  (A/pi) log( 1/(1-rho^2) ) .
```

Equivalently `rho = 2 sqrt(x)/(1+x)`. The activated theorem is `L^2 <= E`.
`r02` writes `r` for `sqrt(x)` and `r04` writes `q` for `sqrt(x)`; the constants
`lam_*(r)` of `r02` and `lam(x)` of `r04` are the same function of `x`.

## Theorem 1, the chord-conditioned geodesic bound

> **Theorem 1.** There is a constant `lam(x) in (0,1)`, defined under Proof below, with
>
> ```text
> L^2 - d^2   <=   lam(x) ( E - d^2 ) ,        E - d^2 >= 0 ,
> ```
>
> and `lam(x)` is optimal: for each fixed `x` the supremum of
> `(L^2 - d^2)/(E - d^2)` over simply connected finite-area domains and pairs of
> points at that pseudohyperbolic distance equals `lam(x)`, and the supremum is
> already attained in the limit along conformal images of the disc.
>
> Two proved closed-form upper bounds are available,
>
> ```text
> b1(x)  =  ( x - (1-x^2) artanh(x) ) / x^2                                (r04)
> b2(x)  =  ( (1+x) artanh(sqrt x) - (1-x) arctan(sqrt x) ) / (4 sqrt x)   (r02)
> ```
>
> and `lam(x) <= min{ x, b1(x), b2(x) } `, with `b1(x) < x` for `0 < x < 1`.

`b1` is below `b2` at every point of a `10^-4` grid on `(0,1)`, and the two
agree to leading order: both expand as `(2/3)x + O(x^3)`, and
`b2(x) - b1(x) = (4/105) x^3 + O(x^5)`. The grid comparison is floating point,
so the note uses `min{b1, b2}` and records `b1` as the smaller one on the tested
set rather than asserting a proved inequality between them.

The gain over `L^2 <= E` is exactly `(1 - lam(x))(E - d^2)`, which is the part
of the analytic energy already spent on the displacement between the endpoints.

## Proof

### The operator

Use the Bergman space `A^2(D)` with `||g||^2 = (1/pi) int_D |g|^2 dA` and
reproducing kernel `K(z,w) = (1 - z conj(w))^{-2}`. Fix `s = sqrt(x)`, put
`I = [-s,s]`, and set

```text
h(z)  =  int_I K(z,y) dy  =  2s/(1 - x z^2) ,
H     =  ||h||^2  =  int_I h(y) dy  =  4 artanh(x)  =  log(1/(1-rho^2)) .
```

Let `S : A^2(D) -> L^2(I, dy/h)` be restriction, and `T = S^* S`, so that

```text
(T g)(z)  =  int_I g(y) K(z,y) dy / h(y) ,     <T g, g>  =  int_I |g|^2 dy/h .
```

`S` is compact because `I` is compactly contained in `D`, `T` is positive and
self-adjoint, `T h = h`, and `h` represents the endpoint functional:
`<g,h> = int_I g(y) dy`. Define

```text
lam(x)  =  || T restricted to h^perp || .
```

The unitary map `F |-> h F / sqrt(H)` intertwines the reversible Markov operator

```text
(P F)(y)  =  (1/h(y)) int_I F(w) (1 - y w)^{-2} dw ,
p_y(w)    =  (1 - x y^2) / ( 2 s (1 - y w)^2 ) ,
d nu(y)   =  h(y) dy / H
```

with `S S^*`, so `lam(x)` is also the largest eigenvalue of `P` on the
mean-zero subspace of `L^2(nu)`. Detailed balance is the symmetry of
`d nu(y) p_y(w) dw = dy dw / (H (1 - y w)^2)`. This is the object both returns
construct, in the two normalisations.

### The analytic inequality, two proofs

For `g in A^2(D)` write `l = int_I |g| dy`, `D_g = int_I g dy`, `E_g = ||g||^2`.
The claim is

```text
l^2  <=  |D_g|^2 + lam(x) ( H E_g - |D_g|^2 ) .                        (11)
```

*First proof, weighted Cauchy-Schwarz.* Split `g = (D_g/H) h + u` with
`u perp h`. Then `E_g = |D_g|^2/H + ||u||^2` and, since `T` preserves
`h^perp`, `<T g, g> = |D_g|^2/H + <T u, u> <= |D_g|^2/H + lam(x) ||u||^2`.
Cauchy-Schwarz against the weight `h` gives `l^2 <= H <T g, g>`. Combining the
two lines proves `(11)`.

*Second proof, unimodular decomposition.* Put `u = g/|g|` on `I`, so `|u| = 1`
almost everywhere and `l = <g, R_u>` with `R_u = int_I K(., y) u(y) dy`. Write
`u = m + u_0` with `m = int_I u d nu` and `u_0` mean-zero, so that
`||u_0||^2_{L^2(nu)} = 1 - |m|^2` and `||R_{u_0}||^2 <= H lam(x)(1 - |m|^2)`.
Also `R_1 = h`, `R_{u_0} perp h`, and `g = (D_g/H) h + g_0` with `g_0 perp h`.
Hence

```text
l  <=  |D_g| |m|  +  sqrt( E_g - |D_g|^2/H ) sqrt( H lam(x) (1 - |m|^2) ) ,
```

and `alpha y + beta sqrt(1-y^2) <= sqrt(alpha^2 + beta^2)` gives `(11)`.

The second proof is the proof of Lemma A of
[BergmanSegmentLengthBound.md](BergmanSegmentLengthBound.md) with one step
changed: that proof bounds `||Phi_u||^2` by `||Phi_1||^2` using positivity of
the kernel, and this one keeps the mean-zero part and pays for it with the
spectral gap. The refinement is exactly the defect in that positivity step.

### Transport

Choose a Riemann map `phi : D -> Omega` with `phi(-s) = a`, `phi(s) = b`, and
apply `(11)` to `g = phi'`. Then `E_g = A/pi`, `|D_g| = d`, `l = L`, and
`H = log(1/(1-rho^2))`, so `(11)` is Theorem 1. Since `d <= L` and
`L^2 <= H E_g = E`, the bracket `E - d^2` is nonnegative, which is what licenses
replacing `lam(x)` by any larger constant below `1`.

## Two bounds for the coefficient

### The contraction bound `lam(x) <= x`

The distribution function of the row `p_y` is
`F_y(w) = (w+s)(1 - s y) / (2 s (1 - y w))`, decreasing in `y`, and the density
ratio `p_{y'}/p_y` is increasing in `w` for `y < y'`, so the rows have a single
crossing and

```text
|| p_y - p_{y'} ||_TV  =  max_w ( F_y(w) - F_{y'}(w) )
                       <= F_{-s}(w) - F_{s}(w)  =  (x - w^2)/(1 - x w^2)  <=  x ,
```

with equality at `w = 0` for the two endpoint rows. Dobrushin contraction gives
`osc(P F) <= x osc(F)`, every eigenfunction with nonzero eigenvalue is
continuous, and the operator is positive, so every eigenvalue other than the
simple eigenvalue `1` lies in `[0, x]`.

### The trace bound `b2`

`T` commutes with `J g(z) = g(-z)`, and direct integration of `K(y,y)/h(y)`
and its alternating companion gives

```text
tr T      =  1/2 + (1+x) artanh(sqrt x) / (2 sqrt x) ,
tr (J T)  =  1/2 + (1-x) arctan(sqrt x) / (2 sqrt x) ,
```

so the trace on the odd subspace is `b2(x)` and the trace on the even subspace
after removing the eigenvalue at `h` is
`b_even(x) = b2(x) - 1/2 + (1-x) arctan(sqrt x)/(2 sqrt x) <= b2(x)`. The
operator is positive and preserves parity, `h` is even, so every eigenvalue on
`h^perp` is bounded by the larger of the two traces, which is `b2(x)`. When the
normalised conformal map is odd, `min{x, b_even(x)}` applies instead.

In the orthonormal basis `e_j(z) = sqrt(j+1) z^j` the matrix of `T` is exactly

```text
T_mn  =  sqrt((m+1)(n+1)) ( s^(m+n)/(m+n+1) - s^(m+n+4)/(m+n+3) )   m+n even,
T_mn  =  0                                                          m+n odd.    (14)
```

### The derivative bound `b1`

Differentiating `(P u)(y) = int_I u dF_y` after an integration by parts gives

```text
(P u)'(y)  =  (Q u')(y) ,
(Q psi)(y) =  int_I ( (x - w^2) / (2 s (1 - y w)^2) ) psi(w) dw ,
```

a positive operator. With the weight `W(y) = (1 - x^2 y^2)^{-1}` and the
substitutions `y = s Y`, `w = s Z`,

```text
Q W (y) / W (y)  =  x  Exp_{alpha}[ (1-Z^2)/(1 - x^2 Z^2) ] ,   alpha = x Y ,
```

for the probability density `p_alpha(Z) = (1-alpha^2)/(2(1-alpha Z)^2)` on
`(-1,1)`. Since
`Prob_alpha(|Z| <= tau) = (1-alpha^2) tau/(1 - alpha^2 tau^2) <= tau` for
`0 <= tau <= 1`, the variable `|Z|` is stochastically larger than a uniform
point of `[0,1]`, and the integrand is even and decreasing in `|Z|`, so

```text
Q W (y)  <=  x W(y) int_0^1 (1-Z^2)/(1-x^2 Z^2) dZ  =  b1(x) W(y) .
```

Applying this to `Q u' = lam(x) u'` for a nonconstant eigenfunction, and
cancelling the positive finite supremum of `|u'|/W`, gives `lam(x) <= b1(x)`.
The series

```text
b1(x)  =  2 sum_{j>=0} x^(2j+1) / ((2j+1)(2j+3)) ,
sum_{j>=0} 2/((2j+1)(2j+3))  =  1 ,
```

shows `b1` is increasing and `b1(x) < x` on `(0,1)`.

## Sharpness

Let `u` be a real unit eigenfunction on `h^perp` with `T u = lam(x) u` and set
`g_eps = h + i eps u`. Then `D_{g_eps} = H`, `E_{g_eps} = H + eps^2`, and

```text
l_eps  =  int_I sqrt( h^2 + eps^2 u^2 )  =  H + (lam(x)/2) eps^2 + O(eps^4) ,
```

because `int_I u^2/h = <T u, u> = lam(x)`. Hence the ratio in Theorem 1 tends to
`lam(x)`. The integral representation extends `T u` holomorphically to
`|z| < 1/s`, so `u` is bounded on the closed disc, while
`Re h(z) >= 2s/(1+x) > 0` on `D`. For small `eps` the function `g_eps` has
positive real part, so its primitive is univalent by Noshiro-Warschawski, and
the extremal sequence consists of genuine conformal maps onto finite-area
domains. The optimality is optimality of the affine coefficient. It does not
assert that Theorem 1 is attained for every separately prescribed triple
`(A, d, rho)`.

## The pinching lower bound

Testing the Rayleigh quotient of `P` on the mean-zero function `sgn(y)`, and
using `int_0^s int_{-s}^0 (1 - y w)^{-2} dy dw = log(1+x)`,

```text
lam(x)  >=  1 - 4 log(1+x)/H  =  1 - log(1+x)/artanh(x) ,                (26)
lam(x) H  >=  H - 4 log(1+x)  ->  infinity   as x -> 1 .
```

So `lam(x) -> 1` as `x -> 1`, and the refined fixed-component bound still
diverges when the two marked points become hyperbolically separated at bounded
area. On `f_r(z) = z^n - r^n` with `r -> 1` at level `1`, every root pair has
`1 - rho^2 -> 0` while the area stays bounded below, so the refined whole
component estimate is ineffective there. That family is settled by its own two
radial arms of length `2r < 2`, and by the grouped-loop construction of
`GroupedCriticalClusterMonodromy.md`, so this is a limitation of the estimate
rather than evidence against the parent. It is the same degeneration
`BergmanSegmentLengthBound.md` §6 already records for the activated bound.

## Consumers

### Two-root components

Let `Omega` be a component of `{|f| < t}` holding exactly two roots `a, b`, let
`c` be its unique critical point and `v = |f(c)|`. The degree-two Blaschke
normal form of [AffineNormalisedModuli.md](AffineNormalisedModuli.md) (B2)
places the two preimages at `+-sqrt(v/t)`, so `x = v/t`, and the image of
`[-sqrt x, sqrt x]` is the descent arc `Gamma_c`, which lies in `{|f| <= v}`
independently of `t`. That containment is the one
[MinimalHubWindowJoin.md](MinimalHubWindowJoin.md) makes load-bearing.
Theorem 1 gives

```text
length(Gamma_c)^2  <=  (1 - lam) d^2 + lam (2 Area(Omega)/pi) log((t+v)/(t-v)) ,
lam = min{ v/t, b1(v/t), b2(v/t) } ,      d = |a-b| .                    (15)
```

There is no pair-selection ambiguity: the chord, the critical point and the arc
belong to the same component. This is a strict strengthening of Theorem C of
[BergmanSegmentLengthBound.md](BergmanSegmentLengthBound.md), which is the case
`lam = 1`.

### The persistence window

Let `f` have degree `n >= 3` and let the two-root component persist for
`v < t < T`, where `T` is its own merger level in the sense of
`MinimalHubWindowJoin.md` Lemma 1. With the proper-component area estimate of
`ExteriorBlaschkeFibreCapacityGap.md` used by
[FirstTwoCriticalOptimizedBergman.md](FirstTwoCriticalOptimizedBergman.md),

```text
G(t)  =  2 (t/(n-1))^(2/n) log((t+v)/(t-v))  >=  (Area(Omega_t)/pi) H ,
F(t)  =  d^2 + (v/t)( G(t) - d^2 ) ,
length(Gamma_c)^2  <=  F(t)   for every regular t in the window .        (16)
```

`G` is strictly decreasing, which is Lemma 1 of that file. `G(t) >= d^2`
because the chord is no longer than the arc and the activated bound is at most
`G(t)`. Therefore

```text
F'(t)  =  (v/t) G'(t) - (v/t^2)( G(t) - d^2 )  <  0 ,                    (17)
```

so the bound is evaluated at the end of the window, and since `Gamma_c` does not
depend on `t`,

```text
length(Gamma_c)^2  <=  (1 - v/T) d^2 + (v/T) G(T) .                      (18)
```

If `v < 1` and the right side is below `4`, then `Gamma_c` joins two roots
inside `{|f| <= v} subset {|f| < 1}` with length below `2`, even when `T > 1`.
With `q = v/T` the criterion is

```text
q ( G(T) - 4 )  <  (1-q) ( 4 - d^2 ) ,                                   (19)
```

which retains the scalar condition `G(T) < 4` of
`FirstTwoCriticalOptimizedBergman.md` Theorem 2 and adds a regime where
`G(T) > 4` is paid for by the chord deficit. Replacing `q` by
`min{q, b1(q), b2(q)}` strengthens `(19)` further.

### A rational two-root criterion

> **Corollary 2.** Let `Omega` be a component of `{|f| < t}` with `t <= 1`
> holding exactly two distinct roots `a, b`, with critical point `c` and
> `v = |f(c)|`. If `|a - b| <= 1` and `v/t <= 17/20`, then those two roots are
> joined inside `Omega` by a curve with
>
> ```text
> L^2  <  767/200  <  4 ,        L  <  1.959 .
> ```

*Proof.* Write `A_f(sigma) = Area{|f| < sigma}`. Coarea, Cauchy-Schwarz and
planar isoperimetry give
`4 pi A_f(sigma) <= Perimeter^2 <= A_f'(sigma) int_{|f|=sigma} |f'| |dz|`, and
the last integral is `2 pi n sigma` by the degree of the boundary map, so
`sigma A_f'(sigma) >= (2/n) A_f(sigma)` at regular levels. Hence
`A_f(sigma)/sigma^(2/n)` is nondecreasing with limit `pi`, so
`A_f(sigma) <= pi sigma^(2/n)` and `Area(Omega) <= pi` for `t <= 1`. That is Pólya's bound of
[LemniscateCapacityBudget.md](LemniscateCapacityBudget.md) with a self-contained
derivation. With `A <= pi` and `d <= 1`, `(15)` gives

```text
L^2  <=  4 b1(x) artanh(x) + (1 - b1(x)) d^2  <=  1 + b1(x)( 4 artanh(x) - 1 ) .
```

If `4 artanh(x) <= 1` the right side is at most `1`. Otherwise both `b1` and
`artanh` are increasing and both factors are nonnegative, so the supremum over
`x <= 17/20` is at the endpoint, where the truncated series with geometric
remainders give the rational bounds `b1(17/20) < 7/10` and
`artanh(17/20) < 101/80`, hence

```text
L^2  <  1 + (7/10)( 4 * 101/80 - 1 )  =  1 + 567/200  =  767/200 .
```

The curve lies in `Omega subset {|f| < 1}`. ∎

The endpoint chain of the source return bounds `(1 - b1(x)) d^2` by `3/10`,
which fails for small `x`. The monotone chain above reaches the same constant.

### The rational cubic that separates the criteria

Take `u = 1011/1600`, `p = u^2 - 1/(4u) = 9364331/2588160000`, and

```text
f(z)  =  z^3 - p z - 1/4  =  (z - u)( z^2 + u z + 1/(4u) ) .
```

The roots are `u` and `-u/2 +- (i/2) sqrt(1/u - u^2)`, all inside the open unit
disc since `u < 1` and `|a|^2 = 1/(4u) < 1`, and

```text
d^2  =  1/u - u^2  =  3062635669/2588160000 .
```

The critical points are `+-sqrt(p/3)`, the two critical-value moduli are
`v = 1/4 - delta` and `T = 1/4 + delta` with `delta = 2(p/3)^(3/2)`, and
`delta^2 = 4p^3/27` is rational, so `delta` is enclosed by squaring. The
component born at level `v` contains the real critical point `-sqrt(p/3)`, hence
is invariant under conjugation, hence holds the conjugate pair rather than the
real root with one of them. Exact rational interval arithmetic gives

```text
G(T)  =  4.001477983659091...   >  4.0014 ,
F(T)  =  3.999590055126611...   <  3.9996 ,
```

and with the coefficient `b1(v/T) = 0.995304855...` in place of `v/T`,

```text
F_{b1}(T)  =  3.988246350142...  <  3.9883 .
```

So `FirstTwoCriticalOptimizedBergman.md` Theorem 2 does not fire on this cubic
and the chord-conditioned criterion does. This is a strict improvement of that
certificate on one polynomial. It is not a new degree range for the parent
theorem, and it does not show that every other certificate in the corpus fails
on this cubic.

### Connected clusters

Let `C` be a regular component of `{|f| < t}` with `k >= 2` roots and at least
two distinct root locations, `A_C = Area(C)`, `q_C` the largest normalised
internal critical-value modulus, and `D_C` the largest distance between two root
locations in `C`. Put `y = q_C^(2/k)`. The selection step of
[ConnectedClusterBergman.md](ConnectedClusterBergman.md) supplies two distinct
roots at pseudohyperbolic distance at most `2 q_C^(1/k)/(1+y)`, so their
parameter `x_0` satisfies `x_0 <= y`, and their joining curve is the conformal
image of the hyperbolic geodesic. Theorem 1 applied to that pair, then raising
`x_0` to `y` (legitimate because the bracket is nonnegative) and `d` to `D_C`
(legitimate because `1 - y > 0`), gives

```text
length(Gamma)^2  <=  (1-y) D_C^2 + (2 y A_C/pi) log((1+y)/(1-y)) .       (23)
```

Failure of the parent on `C` at a level `t <= 1` therefore forces

```text
A_C/pi  >=  ( 4 - (1-y) D_C^2 ) / ( 2 y log((1+y)/(1-y)) )               (24)
        =   2/log((1+y)/(1-y)) + (1-y)(4 - D_C^2)/( 2 y log((1+y)/(1-y)) ) , (25)
```

and the second term of `(25)` is positive whenever the roots lie in the open
unit disc. The activated certificate is `(23)` with the coefficient `y` in
front of the area replaced by `1` and the chord discarded, so `(23)` improves
the area coefficient by the factor `y` as well as retaining the chord.
Consequently the fixed-level pigeonhole of
[ConnectedClusterAreaForcing.md](ConnectedClusterAreaForcing.md) runs with the
per-component threshold `2/L_i` replaced by

```text
theta_i  =  max{ 2/L_i , ( 4 - (1-y_i) D_i^2 t^(-2/n) ) / ( 2 y_i L_i ) } ,
```

which is at least the activated one, so `sum_i theta_i >= 1` is a weaker
hypothesis than `(AF)`. The falsifying near-regular rows of that file are not
re-measured here, so no claim is made about whether the weaker hypothesis holds
on them.

### The chord deficit

`chord_deficit_length_identity` records `L(c) = (d_1 + d_2) + Dfc` with
`Dfc >= 0` the turning deficit, and `chord_deficit_polynomial_representation`
records that no estimate for `Dfc` is offered. Since `d_1 + d_2 >= |a-b|`,
Theorem 1 gives an upper bound of that shape,

```text
Dfc  <=  L - |a-b|  <=  lam(x) ( E - d^2 ) / ( L + d ) ,
```

in terms of the area and the pseudohyperbolic distance rather than in terms of
the critical divisor. It does not supply the polynomial-side estimate that file
asks for.

### Moved monodromy sheets

Let `Z_j : D -> C`, `j = 1..N`, be holomorphic extensions of complete lifts
along `I = [-sqrt x, sqrt x]` whose images lie in the admissible lemniscate,
with `Z_j(-sqrt x) = a_j`, `Z_j(sqrt x) = a_{tau(j)}` for a permutation `tau`,
and put `L_j = int_I |Z_j'|`, `d_j = |a_{tau(j)} - a_j|`,
`E_j = int_D |Z_j'|^2 dA` the Dirichlet energy with multiplicity,
`M = {j : tau(j) != j}`, `m = |M| > 0`, `nfix = N - m`, and
`Q = (4/pi) artanh(x) sum_j E_j`. Applying the inequality to each `Z_j'` and
averaging over the moved sheets,

```text
min_{j in M} L_j^2  <=  ( lam Q + (1-lam) sum_{j in M} d_j^2 ) / m .      (36)
```

If a construction supplies `Q <= 4N`, then

```text
(1-lam) sum_{j in M} ( 4 - d_j^2 )  >  4 lam nfix                           (37)
```

is sufficient for a moved lift of length below `2`, and with `Q <= 4N - dE`,

```text
(1-lam) sum_{j in M} ( 4 - d_j^2 ) + lam dE  >  4 lam nfix .                (38)
```

The three displays are ordinary consequences of Theorem 1 and summation. The
holomorphic extensions `Z_j` and the energy budget `Q <= 4N` are **not**
supplied, by either return or by this note, and `E_j` may not be replaced by the
area of a lemniscate component without a separate multiplicity estimate. This is
an alternative currency for the fixed-sheet deficit, and the launch problem of
`PartialClusterPreimagePerimeterIdentity.md` is untouched by it.

## Claim boundary

**Proved, by ordinary mathematics.** Theorem 1 with both proofs of `(11)` and
both transports; `lam(x) <= x`; the two trace formulas and `lam(x) <= b2(x)`;
the operator `Q`, the stochastic comparison and `lam(x) <= b1(x)`; the series
for `b1` and `b1(x) < x`; the sharpness construction and the univalence of its
extremals; the lower bound `(26)`; the two-root consumer `(15)`; the
monotonicity `(17)` and the window form `(18)`, `(19)`; Corollary 2 with the
repaired chain; the connected-cluster form `(23)`, `(24)`, `(25)`; the
moved-sheet displays `(36)`, `(37)`, `(38)` as implications from their stated
hypotheses; the global area estimate `Area{|f| < sigma} <= pi sigma^(2/n)`.

**Exact rational certificates.** The `17/20` inequalities `b1(17/20) < 7/10`,
`artanh(17/20) < 101/80` and `767/200 < 4`; and the cubic witness, where
`delta` is enclosed by squaring `4p^3/27`, `(T/2)^(2/3)` by cubing, and the
logarithm by the artanh series with its remainder bound, giving
`G(T) > 4.0014`, `F(T) < 3.9996`, `F_{b1}(T) < 3.9883`.

**Floating, with no proof authority.** Every numerical value of `lam(x)`,
including the tables of both returns; the statement that `b1` is below `b2` on
`(0,1)`, which is a `10^-4` grid measurement plus a local expansion at `0`; the
limiting critical ratios `0.862845`, `0.842721`, `0.813091`, `0.761594` of the
source return, of which only the last is exact, being `tanh(1)`; the random
polynomial ratios. The truncated matrix `(14)` is a principal compression, so
its computed top eigenvalue is a lower estimate of `lam(x)`, which is the safe
direction for a falsification arm and the unsafe direction for any claim that
`lam(x)` is smaller than a bound.

**Not first here.** The base bound is Theorem C' of
`BergmanGeodesicInvariance.md`; Lemma A and its unimodular proof are
`BergmanSegmentLengthBound.md`; the degree-two normal form is
`AffineNormalisedModuli.md`; the area estimate is Pólya's, recorded in
`LemniscateCapacityBudget.md`; the cluster selection is
`ConnectedClusterBergman.md`; the optimised level and exterior-fibre area gap
are `FirstTwoCriticalOptimizedBergman.md`; the window structure is
`MinimalHubWindowJoin.md`. No novelty is claimed for the spectral-gap
refinement of a positive kernel bound until a priority search on Bergman-space
and Markov-chain literature says otherwise. What is new here is the
composition.

**Erdős #1041 remains open.** Theorem 1 improves the inputs to the allocation
problem. It does not prove that some component satisfies `(23)` with right side
below `4`, it does not supply the moved-sheet hypotheses of `(36)` to `(38)`,
and the lower bound `(26)` shows that no choice of the affine coefficient
removes the pinching divergence.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_chord_conditioned_bergman.py --part all
```

| arm | what fails it |
|---|---|
| `RATIONAL1720` | `b1(17/20) >= 7/10`, `artanh(17/20) >= 101/80`, or the repaired endpoint chain misses `767/200` |
| `CUBIC` | a root leaves the open unit disc, `delta` or `(T/2)^(2/3)` is not enclosed by its integer power test, `G(T) <= 4.0014`, `F(T) >= 3.9996`, or `F_{b1}(T) >= 3.9883` |
| `SPECTRUM` | the truncated matrix `(14)` misses the exact trace, its top eigenvalue on `h^perp` exceeds `b1` or `b2`, falls below `(26)`, or is attained off the odd subspace |
| `RANDOM` | a random polynomial violates the explicit inequality with coefficient `b1(q^2)` at `q = 0.2, 0.5, 0.8, 0.95` |
