# Erdős 1041: the symmetric merge envelope is a theorem, and the loss from symmetry is an exact identity

## Status

This note assimilates the capacity and merge-envelope content of two Type B
returns in batch `erdos1041_20260905_eight_return_stream_01`:

* `sources/r06_capacity_evolution_merge_ceiling_2pow40.md`, §§1-5 and §9;
* `sources/r08_merge_envelope_low_critical_1over8.md`, Part II, §§7-10.

The two returns reach the same theorem by two independent derivations. They are
credited jointly throughout. The low-critical metric theorems in the same two
files (`mu <= 1/8` and `mu <= 2^-40`) are a separate lane and are not assimilated
here.

What lands:

1. an exact capacity-speed identity for a persistent component, which is new to
   this directory;
2. an exact decomposition of that speed into a symmetric term plus a
   non-negative fibre-variance defect;
3. the sharp next-merge envelope, which is exactly the inequality recorded as
   conjectural in equation (18) of [CapacitySaturationBridge.md](CapacitySaturationBridge.md) §4,
   together with its closed form;
4. an exact defect identity accounting for the two distinct losses;
5. equality rigidity, a polynomial sharpness family, the `k/m` large-degree
   scale, and an ancestral capacity growth law.

Theorem 3 of `CapacitySaturationBridge.md` (the radial spectator-drop ceiling)
is superseded quantitatively for `m >= 2` and is reproduced exactly at `m = 1`.
The conjecture flag on (18) is discharged.

**Erdős #1041 remains open.** Nothing below produces a curve of length under two
joining two roots inside `{|f|<1}` for an unrestricted monic polynomial with
roots in the open unit disc. The envelope is a statement about component
lifetimes in the level parameter, and it carries no metric conclusion by itself.

## Authority boundary

Every step below was re-derived and checked in this pass. The algebra is exact
and is replayed by
[`scripts/check_erdos1041_sharp_merge_envelope.py`](scripts/check_erdos1041_sharp_merge_envelope.py).
The arguments are ordinary complex analysis. They are not Lean-checked and have
not been independently reviewed.

No novelty is claimed against the potential-theory literature. The capacity
variation formula of §2 is the standard Hadamard shape derivative of the
exterior Green function, in the special case where the moving boundary is a
level curve of `log|f|`. It should be assumed known until a priority search says
otherwise. What is new to this directory is its use: the reciprocal boundary
speed is the object the exterior Blaschke fibre identity already controls, so
the two compose without an intervening symmetrisation theorem.

The corpus inputs consumed are the exterior component representation and the
harmonic-measure fibre identity of
[ExteriorBlaschkeFibreCapacityGap.md](ExteriorBlaschkeFibreCapacityGap.md)
Lemma 1 and Theorem 2, the exact component capacity of
[ComponentCapacityFormula.md](ComponentCapacityFormula.md) Theorem 1, and the
absence of bounded components of `{|f|>t}` from
[LemniscateCapacityBudget.md](LemniscateCapacityBudget.md) (A).

**Notation collision, recorded because it will bite a reader of the raw
returns.** `r06` writes `x_j` for the reciprocal boundary speed `1/|B'|` and
`Psi_{n,k}` for the envelope integral. `r08` writes `x_j` for `|B'|`, `y_j` for
its reciprocal, `Psi_{n,m}` for the boundary speed, and `I_{n,m}` for the
envelope integral. This note keeps corpus notation and names the two objects
`sigma_{n,k}` (speed) and `Psi_{n,k}` (envelope integral).

## 1. Component variables

`f` is monic of degree `n >= 2`. Let `U_t` be a component of `{|f|<t}`
containing exactly `k < n` roots with multiplicity, persistent on an interval of
regular levels. Put

```text
m = n - k >= 1,      N = n + m = 2n - k,      p0 = k/N,
c(t) = cap(closure U_t),      p(t) = c(t)^n/t.
```

Let `psi_t : {|zeta|>1} -> Chat \ closure(U_t)` be the exterior map normalised by
`psi_t(zeta) = c(t) zeta + O(1)`. Write `a_j = 1/conj(xi_j)` for the exterior
coordinates of the `m` excluded roots and

```text
B_t(zeta) = product_j (zeta - a_j)/(1 - conj(a_j) zeta).
```

The corpus exterior representation gives

```text
f(psi_t(zeta)) = unit * t * zeta^n / B_t(zeta),        p(t) = |B_t(0)|,     (1)
h_t(theta) = d/dtheta arg f(psi_t(e^{i theta})) = n - |B_t'(e^{i theta})| > 0,
(1/2pi) integral_0^{2pi} h_t(theta) dtheta = k,       0 < p(t) < p0.       (2)
```

The mean of `h_t` is `k` because `arg B_t` winds `m` times around the circle, so
`(1/2pi) integral |B_t'| dtheta = m`. The last inequality is the fibre-coupled
capacity gap. The whole of §§2-4 is the observation that the component is
allowed to move.

**Regularity of the persistence interval.** Neither return spells this step out,
and it is worth recording because the corpus already discharges it. Between `t`
and the first level `T` at which `U_t` acquires an excluded root, no critical
point of `f` lies on `partial U_t`. A boundary critical point at which no
excluded root arrives would have to pinch `partial U_t` against itself, and a
Jordan curve through the pinch inside `closure(U_t)` then traps the exterior
component containing infinity inside a bounded region. That contradicts
connectedness of the exterior, which is `LemniscateCapacityBudget.md` (A): the
set `{|f|>t}` has no bounded component. So the interval `(t,T)` is regular for
the selected component, with no genericity assumption, and critical events at
other components are irrelevant. Simultaneous attachment of several excluded
roots at `T` is admitted.

## 2. The capacity-speed identity

> **Theorem 1 (capacity speed).** On every regular persistence interval,
>
> ```text
> d log c / d log t = (1/2pi) integral_0^{2pi} dtheta / h_t(theta).        (3)
> ```
>
> Consequently `d log c/d log t >= 1/k`. When `k = n` the identity holds with
> `h_t = n` and gives the equality `c(t) = t^{1/n}`.

*Proof (return `r06`, Hadamard form).* Put `s = log t` and let `G_s` be the
Green function of the exterior of `closure(U_{e^s})` with pole at infinity, so
`G_s(z) = log|z| - log c(e^s) + o(1)`. The boundary is the level set
`{log|f| = s}`, so its outward normal velocity in `s` is `1/|grad log|f||`,
which is `t/|f'(z)|`. Since `G_s(psi_t(zeta)) = log|zeta|`, the boundary normal
derivative is `1/|psi_t'(e^{i theta})|`. Differentiating `f` along the boundary
gives `h_t(theta) = |f'(z)| |psi_t'(e^{i theta})| / t`. Differentiating the
boundary condition `G_s = 0` along the moving boundary,

```text
- partial_s G_s = v_normal * partial_normal G_s
                = (t/|f'|) * (1/|psi_t'|) = 1/h_t(theta).                  (4)
```

The function `-partial_s G_s` is harmonic in the exterior and bounded at
infinity, so its value at infinity is the average of its boundary values against
harmonic measure at infinity, which is uniform in the exterior circle
coordinate. The expansion of `G_s` identifies that value as `d log c/ds`. This
gives (3). Cauchy-Schwarz against the second identity of (2) gives
`1 <= k * d log c/d log t`. ∎

*Proof (return `r08`, holomorphic-quotient form).* With `F_t = psi_t` and a dot
for `d/ds`, the outward unit normal at `F_t(zeta)` is `zeta F_t'/|F_t'|` and the
normal velocity is `|F_t'|/h_t`, so

```text
Re[ F_t'(zeta)^{-1} zeta^{-1} Fdot_t(zeta) ] = 1/h_t(theta)   on |zeta| = 1.
```

The quotient `Fdot_t/(zeta F_t')` is holomorphic in `{|zeta|>1}` and equals
`cdot/c` at infinity. Taking its boundary mean gives (3). ∎

The two derivations agree on every sign. The content of (3) is that capacity
growth is driven by the **reciprocal** boundary speed, so it is dominated by the
slow arcs that precede an attachment. This is the reason the exterior fibre data
of `ExteriorBlaschkeFibreCapacityGap.md` is the right input.

**This identity is not present anywhere else in the directory.**
`ComponentCapacityFormula.md` Theorem 1 is the static identity
`n log cap = log t - Sigma` at one level, and `LastLobeCapacityLaw.md` is a
static rigidity at a merge level. Neither differentiates in `t`.

## 3. The fibre-variance identity

Let `d omega` be normalised angular measure on the unit circle. For `|w| = 1`
let `B_t(zeta_j) = w`, `j = 1..m`, counted with multiplicity, and put
`x_j(w) = 1/|B_t'(zeta_j)|`, so `x_j > 1/n` by (2). The corpus fibre identity is

```text
S(w) = sum_j x_j(w) = (1 - p^2)/|w - B_t(0)|^2.                            (5)
```

Define

```text
V(B_t) = integral_{|w|=1} sum_j (x_j - xbar)^2 / [ (n x_j - 1)(n xbar - 1)^2 ] d omega(w),
xbar = S/m.
```

> **Theorem 2 (exact fibre-variance decomposition).** `V(B_t) >= 0` and
>
> ```text
> d log c/d log t = 1/n + (m/n) sqrt( (1-p^2)/(k^2 - N^2 p^2) ) + V(B_t).   (6)
> ```
>
> Equivalently, with `sigma_{n,k}(p) := m sqrt(1-p^2)/sqrt(k^2 - N^2 p^2)`,
>
> ```text
> d log p/d log t = sigma_{n,k}(p) + n V(B_t) >= sigma_{n,k}(p).            (7)
> ```

*Proof.* Change variables under `B_t : T -> T`. On the `j`-th inverse branch
`dtheta = x_j d arg w` and `1/(n - |B_t'|) = x_j/(n x_j - 1)`, so (3) becomes

```text
d log c/d log t = integral_{|w|=1} sum_j x_j^2/(n x_j - 1) d omega(w).      (8)
```

With `g(x) = x^2/(nx-1)` on `x > 1/n` there is the exact identity

```text
g(x) - g(y) - g'(y)(x-y) = (x-y)^2 / [ (nx-1)(ny-1)^2 ].                    (9)
```

Apply (9) at `y = xbar` and sum over the fibre. The linear terms cancel, giving
`sum_j g(x_j) = S^2/(nS-m) + (fibre variance)`. Rotate so `B_t(0) = p >= 0`.
Then `S(e^{i phi}) = (1-p^2)/(1 + p^2 - 2p cos phi)`, and

```text
S^2/(nS-m) = S/n + (m/n) * S/(nS-m),
S/(nS-m)   = (1-p^2)/(k - N p^2 + 2 m p cos phi).                          (10)
```

The Poisson kernel integrates to one, so the first term contributes `1/n`. For
the second, the denominator is positive precisely when `k - N p^2 > 2 m p`,
which factors as `N(1-p)(p0 - p) > 0`, that is precisely on the admissible range
`0 < p < p0` supplied by (2). The discriminant factorises exactly:

```text
(k - N p^2)^2 - 4 m^2 p^2 = (1 - p^2)(k^2 - N^2 p^2).                      (11)
```

With `(1/2pi) integral dphi/(A + C cos phi) = 1/sqrt(A^2 - C^2)` for `A > |C|`,
the second term integrates to `(m/n) sqrt((1-p^2)/(k^2 - N^2 p^2))`. This is (6).
Equation (7) follows from `log p = n log c - log t`. ∎

`(11)` is the reason the closed form exists. The same factor `1 - p^2` that the
Poisson kernel supplies is the one that cancels against the radical.

## 4. The sharp merge envelope, with a closed form

Define, for `0 < p < p0`,

```text
Psi_{n,k}(p) = (1/m) integral_p^{p0} sqrt(k^2 - N^2 u^2) / (u sqrt(1-u^2)) du.  (12)
```

> **Theorem 3 (sharp next-merge envelope).** Let `T` be the first level above `t`
> at which the component `U_t` acquires an excluded root. Then
>
> ```text
> log(T/t) <= Psi_{n,k}(p(t)).                                             (13)
> ```
>
> Equivalently, let `y > 1` be the larger root of
>
> ```text
> y^2 - [ (k + N p^2)/(n p) ] y + 1 = 0,                                   (14)
> ```
>
> which satisfies `1 < y < 1/p`. Then
>
> ```text
> T/t <= F_{n,k}(p) := y^{n/m} (1 - p y)/(y - p) = exp(Psi_{n,k}(p)).      (15)
> ```

This is equation (18) of `CapacitySaturationBridge.md` §4, with `F_{n,k}` the
`b_sym/t` of its (14)-(15). The conjecture flag is discharged.

*Proof of (13).* Differentiating (12) and using (7),

```text
d/d log t Psi_{n,k}(p(t)) = Psi'(p) * p * d log p/d log t
                          = -1 - (n/m) sqrt((k^2-N^2p^2)/(1-p^2)) V(B_t).  (16)
```

`Psi_{n,k}` is non-negative and vanishes at `p0`, and `p(t)` is increasing and
bounded by `p0`, so `p(T-)` exists. Integrating (16) on `[log t, log t_2]` for
`t_2 < T` and discarding the two non-negative terms gives
`log(t_2/t) <= Psi_{n,k}(p(t))`. Let `t_2` rise to `T`. The argument does not
assume `p(T-) = p0`; an asymmetric component may attach strictly earlier, which
only strengthens the inequality. ∎

*Proof of (15).* Equation (14) is exactly equivalent to the stationary relation

```text
n (1 - p y)(y - p) = m y (1 - p^2),                                        (17)
```

as an identity of polynomials in `y` after clearing `-np`. Because (17) is the
stationarity condition of `log F` in `y`, the term carrying `y'(p)` cancels on
differentiation:

```text
d/dp log F(p) = -(y^2 - 1)/[(1-py)(y-p)].
```

Substituting (17) and `y - 1/y = sqrt((k^2 - N^2 p^2)(1-p^2))/(n p)`, which is
the discriminant of (14), gives

```text
d/dp log F(p) = - sqrt(k^2 - N^2 p^2)/(m p sqrt(1-p^2)) = Psi_{n,k}'(p).
```

At `p = p0` the quadratic has the double root `y = 1`, so `F(p0) = 1` and
`log F` and `Psi_{n,k}` both vanish there. Hence they agree on `(0,p0)`. The
bracket `1 < y < 1/p` follows from `N p^2 - 2 n p + k = N(p-1)(p-p0) > 0` and
from the value `Q(1/p) = m(1-p^2)/(n p^2) > 0` of the quadratic at `1/p`. ∎

### The exterior-model form

The proof uses only the exterior potential, so it applies to a rational model
with no polynomial behind it. Let `B` have degree `m < n`, `B(0) != 0`, and
`|B'(zeta)| < n` on the unit circle, and put `W(z) = z^n/B(z)`, whose exterior
zeros are `xi_j = 1/conj(a_j)`. Let `M(B)` be the least mountain-pass height of
`|W|` from the unit circle to any `xi_j`. Then

```text
M(B) <= F_{n,n-m}(|B(0)|).                                                 (18)
```

*Sketch.* `|W| = 1` on the unit circle. Grow the sublevel component of `|W|`
attached to the closed unit disc. All finite poles of `W` lie inside the
original disc, and a bounded complementary component of the growing set would be
a bounded component of a superlevel set of a function holomorphic there, which
the maximum principle excludes. The leading coefficient of `W` at infinity has
modulus `|B(0)|`, so the correct product variable is
`p(tau) = |B(0)| c(tau)^n/tau`, whose logarithmic derivative is again
`n d log c/d log tau - 1`. Every step of §§2-4 then applies verbatim. ∎

This is the mountain-pass version that `CapacitySaturationBridge.md` §4 named as
the natural analytic formulation of (18).

## 5. The exact defect identity

Write `q_j = n x_j - 1 > 0` on a fibre and `S_q = sum_j q_j = nP - m` with
`P = sum_j x_j`. The fibre defect admits three equal exact forms:

```text
sum_j x_j^2/(n x_j - 1) - P^2/(nP - m)
  = (1/n^2) [ sum_j 1/q_j - m^2/S_q ]                                      (19)
  = (1/(n^2 S_q)) sum_{i<j} (q_i - q_j)^2/(q_i q_j)
  = sum_j (x_j - xbar)^2 / [ (n x_j - 1)(n xbar - 1)^2 ].
```

The middle form is the return `r08` identity (9.1); the last is the tangent-line
remainder of return `r06`; the harmonic form in the first line is the shortest
route to non-negativity, since it is exactly the arithmetic-harmonic mean gap on
`q`. Set `D(B) = V(B)` for the angular mean of (19). Then (16) integrates to the
exact accounting

```text
Psi_{n,k}(p(t)) = log(T/t) + Psi_{n,k}(p_T)
                  + n integral_{log t}^{log T} D(B_{e^s})/sigma_{n,k}(p(e^s)) ds,  (20)
```

with `p_T = lim_{r -> T-} p(r)`. The two losses are separated. `Psi_{n,k}(p_T)`
is the merger that happens before capacity saturation. The integral is the
angular inequality of derivative speeds inside complete fibres. No excluded root
is dropped, and no capacity is reassigned to another component.

## 6. Equality rigidity

> **Theorem 4 (zero-defect class).** `D(B) = 0` if and only if
> `B = A^{-1}(e^{i alpha} z^m)` for a disc automorphism `A(w) = (w-b)/(1-conj(b)w)`
> with `b = B(0)`. Equivalently `B(z) = e^{i beta}(z^m - a)/(1 - conj(a) z^m)`
> for some `a` in the disc.

*Proof.* Vanishing of the defect forces all `|B'|` equal on every fibre, so by
(5) their common value is `m/P_b(w)` with `P_b` the Poisson kernel at `b = B(0)`.
On the circle `|A'(w)| = P_b(w)`, so `|(A o B)'| = m` identically. A degree-`m`
Blaschke product with constant boundary argument derivative `m` is
`e^{i alpha} z^m`. Conversely such a `B` has equally spaced fibres with equal
speeds. ∎

This is the `r08` route and it is the cleaner of the two. The `r06` route argues
that equal branch speeds keep the cyclic order, so the monodromy over one turn
of the target circle is the cyclic shift and the constant gaps are `2 pi/m`;
that step is correct and its order-preservation is worth stating explicitly.

The symmetric exterior model is therefore characterised exactly by equal inverse
angular speeds on every complete fibre. It is the zero-defect class, and the
finite-Blaschke searches recorded in `CapacitySaturationBridge.md` §4 were
measuring the sign of an identity.

## 7. Sharpness

Take

```text
f(z) = z^k (z^m - 1),        n = k + m.
```

Its nonzero critical points satisfy `z^m = k/n`, with common critical modulus

```text
beta = (m/n) (k/n)^{k/m}.
```

For `0 < t < beta` the component containing zero holds exactly `k` roots. The
radial segments to the `m` outer roots attain maximum modulus exactly `beta`, and
there is no intervening nonzero critical level, so the first attachment is at
`beta`, with all `m` roots arriving at once. The component is invariant under
rotation by `2 pi/m`, so its exterior zeros form a regular `m`-gon and

```text
B_p(zeta) = (zeta^m - p)/(1 - p zeta^m).
```

For `W(zeta) = t zeta^n/B_p(zeta)` the exterior critical points satisfy
`zeta^m = y` with `y` the larger root of (14), and their common modulus is
`t F_{n,k}(p)`. Those are the nonzero critical points of `f`, so

```text
beta/t = F_{n,k}(p(t)),
```

that is, equality holds in (13) at every level of this family. Since `F_{n,k}`
decreases strictly from infinity to one, every admissible `p` in `(0,p0)` is
realised. The envelope is therefore sharp among polynomial components, not only
among exterior models. The zero-defect condition of §6 is satisfied throughout,
which is why (20) closes with both losses equal to zero.

## 8. Asymptotics and the `k/m` scale

Two limits of the closed form:

```text
F_{n,k}(p) ~ [ m k^{k/m} / n^{n/m} ] p^{-k/m}                (p -> 0),      (21)
log F_{n,k}(p0 (1-eps)) = (sqrt(2)/3) (n^2-m^2)/(sqrt(n) m^{3/2}) eps^{3/2}
                          + O(eps^{5/2})                     (eps -> 0).    (22)
```

Equation (22) reproduces the exact symmetric-model cusp (17) of
`CapacitySaturationBridge.md` §4. That cusp was computed for the symmetric model
alone. It is now a universal upper envelope for every admissible component.

Equation (21) carries the exponent `k/m`. The spectator-drop ceiling of
`CapacitySaturationBridge.md` Theorem 3 carries `(n-1)/m`, because it discards
every spectator Blaschke factor. For fixed component arity `k` and growing
degree these are different scales. Taking `p = kappa^n` with `kappa` and `k`
fixed, the closed form has `F_{n,n-k}(kappa^n) -> kappa^{-k}`, while the older
bound grows exponentially in `n`. This is the large-degree fixed-arity shell
that the capacity source named as the reason its Theorem 3 was quantitatively
insufficient. A crude corollary of the same integral, using
`sqrt(k^2-N^2u^2)/sqrt(1-u^2) <= k`, is

```text
F_{n,k}(p) <= (p0/p)^{k/m} < p^{-k/m}.                                     (23)
```

At `m = 1` the new envelope and the old radial ceiling coincide identically:
(14) above is then equation (9) of `CapacitySaturationBridge.md`, and
`F_{n,n-1} = M_n` in its notation. The replay confirms
that agreement to double precision and confirms strict improvement at `m >= 2` on
every sampled row.

**Cross-check against `LastLobeCapacityLaw.md`.** At `m = 1` the defect vanishes
identically, because every degree-one Blaschke product lies in the zero-defect
class of §6. So (20) reads `Psi_{n,n-1}(p(t)) = log(T/t) + Psi_{n,n-1}(p_T)`, and
the envelope is an equality exactly when `p_T = p0`. The last-lobe law proves
`p_T = (n-1)/(n+1) = p0` independently, by a boundary double-zero argument that
uses none of the machinery above. The two results corroborate each other on the
whole `m = 1` family.

A single hanging lobe carrying one root of multiplicity `m` has exterior
Blaschke product `((zeta-a)/(1-conj(a) zeta))^m` with `|a| = (n-m)/(n+m) = p0`,
so it merges at `p = p0^m`. For `m >= 2` that is strictly below `p0`, so
`Psi_{n,k}(p_T) > 0` and the configuration sits strictly inside the envelope,
which is what (20) requires: its Blaschke zeros coincide rather than forming a
regular `m`-gon, so its defect is positive throughout. Both branches are gated
in the replay.

## 9. Ancestral capacity growth

Theorem 1 also survives changes of component, which is what a merge cascade
needs.

> **Proposition 5 (ancestral capacity growth).** Follow one component ancestry
> `C_t` with root count `k(t)` and capacity `c(t)`. For `0 < t0 < S`,
>
> ```text
> c(S) >= c(t0) (S/t0)^{1/k(S)}.                                           (24)
> ```

*Proof.* There are finitely many critical levels. On regular intervals,
`d log c/d log t >= 1/k(t)` by Theorem 1. At an attachment the ancestral compact
set enlarges, so the logarithmic capacity jump is non-negative, including at
simultaneous attachments. Since `k(t) <= k(S)` on `(t0,S)`, integrating gives
(24). ∎

Combined with `c(S) <= cap(K_S) = S^{1/n}`, this gives the capacity-to-arity
alternative: if `S < 1` and `c(t0) > q` then

```text
k(S) > log(S/t0)/log(1/q).                                                 (25)
```

A component that already carries appreciable capacity cannot stay a low-arity
component across a long logarithmic level interval. The statement refers to one
actual ancestor, with no reassignment of capacity between components and no
replacement of the geometric merge tree by an abstract one.

## 10. Consumers, and what this does not prove

Consumers inside this directory:

* `CapacitySaturationBridge.md` §4: its (18) is now Theorem 3 above, and its
  Theorem 3 is superseded for `m >= 2`. Its §5 item 4 (`(18)` is the first
  unsupported implication) is discharged.
* `TwoExteriorSymmetricEnvelope.md` (`m = 2`), `QFoldTwoOrbitSymmetricEnvelope.md`
  (two regular `q`-orbits) and `ThreeExteriorEqualRadiusAngularEnvelope.md`
  (`m = 3` slices) each proved a fragment of the same inequality by pointwise
  radial polarisation. They are now special cases. Their radial arguments retain
  independent value: they produce an explicit attachment-compatible curve, while
  Theorem 3 produces a level bound through an ODE.
* `ExteriorRadialWaterFillingAndSaturationRigidity.md` records that scalar
  `(p,r)` data plus the Boolean speed condition cannot prove the envelope, and
  names angular distribution as the missing datum. Theorem 2 supplies exactly
  that datum, through the complete fibre rather than through a second scalar.
* `ExteriorFibreDefectCriticalStability.md` bounds the full exterior critical set
  using the antipodal fibre. Equation (20) is the dynamic counterpart, and the
  two defect notions should be reconciled before either is spent twice.

What this does not prove:

* It gives no metric conclusion. A bound on `log(T/t)` is a bound on a component
  lifetime in the level parameter. Converting it into a curve of length under
  two requires an access and perimeter selection argument that is untouched here.
* It says nothing about the high-critical regime. The two returns close
  `mu <= 1/8` and `mu <= 2^-40` by separate metric arguments that are owned
  elsewhere, and the surviving regime `1/8 < mu < 1` is where the difficulty sits.
* It supplies no interior control. The exterior angular speed is not transferred
  through a conformal welding anywhere above, and it must not be.
* `Psi_{n,k}` is finite for every admissible `p`, so a single component lifetime
  is always bounded. That alone forces no merge node to cross either of the two
  metric thresholds recorded in `ExteriorBlaschkeFibreCapacityGap.md` §3.

The natural next question for this lane is whether (20) can be spent as a budget
rather than as a bound: the defect integral is an exact quantity, and a component
that survives close to its envelope is forced to be close to the symmetric model
by §6, which is an angular rigidity statement the metric consumers have never
had.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_sharp_merge_envelope.py
```

Gate one is exact rational arithmetic on (9), (11), (17), and the three forms of
(19). The remaining five gates are deterministic floating point at disclosed
tolerances: the closed-form identification `Psi_{n,k} = log F_{n,k}` over fifteen
rows including the three rows of `r06` §9, the polynomial sharpness family, the
fibre identity and defect non-negativity over random and symmetric Blaschke
configurations, the scale corollaries and the comparison against the corpus
radial ceiling, and the corpus cross-checks against `LastLobeCapacityLaw.md` and
the exact cubic merge level `32/675 + 112 sqrt(7)/3375` of `r06` §9.
