# Erdős 1041 for every polynomial with least critical value at most 9/25

## Status

Ordinary complete proof of an unconditional all-degree parent regime, with an
exact rational certificate. Not Lean-checked, not independently reviewed.
Erdős 1041 itself remains open.

This note sharpens [LowCriticalPotentialClosure.md](LowCriticalPotentialClosure.md),
which proves the same shape of theorem with threshold `197/1000`. The single
change is the arity floor: that note uses only the one-root COVER Bergman bound,
which forces `k >= 2x/delta(a)`. Adding the *connected-cluster* Bergman
certificate as a second failure inequality forces, in addition,

```text
k >= 1 + (2x - delta(a)) / tau(a),     tau(a) = -log tanh(1/a),
```

and `tau(a) < delta(a)` for every `a > 0`, so the new floor dominates the old one
as soon as `x` is past the first cell. Larger forced arity means faster forced
area growth in the same boundary-hop inequality, so the failure window closes
earlier. Nothing else in the mechanism moves: the same Lemma 1 perimeter bound,
the same low/high lift split, the same hop, the same monotone comparison ODE, the
same rational rounding discipline.

## Theorem

Let `f` be a squarefree monic polynomial of degree `n >= 2`, and put
`mu = min{ |f(c)| : f'(c) = 0 } > 0`.

> **Theorem A.** If `mu <= 9/25`, then two distinct roots of `f` are joined by
> a rectifiable curve inside `{|f| < 1}` of length strictly less than `2`.

> **Corollary B (scale-free).** Every squarefree monic `f` has two distinct roots
> joined inside `{|f| < (25/9) mu}` by a curve of length below
> `2 ((25/9) mu)^(1/n)`.

At fixed degree the same argument also has the arity cap `k <= n` and the Pólya
cap `Area(K_t)/pi <= t^(2/n)` available. With the *crude* floor (2) those
certified `mu <= 1/2, 9/20, 2/5, 7/20` at `n = 4, 5, 6, 7`, already above the
`1/3, 3/10, 1/4, 199/1000` of the predecessor note; the fixed-degree lane has
**not** been re-run against the sharp floor (2') in this pass, so no fixed-degree
constant is claimed here. The checker carries that arm behind `--per-degree`; it
is slow and its output is the authority for those rows.

No hypothesis is placed on root locations. A repeated root gives the constant
curve, so the squarefree case is the nontrivial branch.

## The second failure inequality

Write `K_t = {|f| <= t}`, and for `t > mu` put `x = log(t/mu)`. Assume for
contradiction that no two distinct roots are joined inside `{|f| < 1}` by a curve
of length below `2`. Fix a least-critical point `c*` and let `Gamma` be the union
of two descending inverse arcs from `c*` into two distinct one-root lobes of
`{|f| < mu}`. For `t > mu` regular let `C_t` be the component of `{|f| < t}`
containing `Gamma`, `k = k(t) >= 2` its root count, and
`a(x) = Area(C_t)/pi` — the **ancestor component's** normalised area, not the
global one. Every ingredient below is per-component, so this substitution is free
and the global Pólya cap `a <= t^{2/n} <= 1` still applies.

Uniformise `C_t` by the disc: `f/t` becomes a finite Blaschke product `B` of
degree `k` with zeros `b_1, ..., b_k` (the roots of `f` in `C_t`). Write `rho` for
the pseudohyperbolic and `d = 2 artanh(rho)` for the hyperbolic metric on the
disc.

> **Lemma 1 (two-point Bergman length).** Let `z_1, z_2` in `C_t` correspond to
> disc points at hyperbolic distance `d`, and put `s = tanh(d/4)`. The hyperbolic
> geodesic of `C_t` between them has Euclidean length `L` with
>
> ```text
> L^2 <= 4 a artanh(s^2).
> ```

*Proof.* Move the two preimages to `-s, s` by a disc automorphism; the geodesic is
the image of the diameter segment under the Riemann map `phi`. Since
`||phi'||^2 = Area(C_t)` in the Bergman space `A^2(D)` with reproducing kernel
`K(z,w) = 1/(pi (1 - z conj(w))^2)`, Cauchy--Schwarz gives
`L^2 <= Area(C_t) · (1/pi) ∫∫_{[-s,s]^2} dx dy/(1-xy)^2 = Area(C_t) · 4 artanh(s^2)/pi`,
using `∫_{-s}^{s}∫_{-s}^{s} dx dy/(1-xy)^2 = 4 artanh(s^2)`. ∎

Lemma 1 with one endpoint moved to zero is the one-root bound of
[R2MergeNodeSeparation.md](R2MergeNodeSeparation.md); with `s = q^{1/k}` it is
exactly the connected-cluster barrier `a log((1+q^{2/k})/(1-q^{2/k})) < 2` of the
corpus. What is used here is not the corpus's *selection* claim (negative result
74 refutes the universal merge-node forcing of that certificate) but its
contrapositive, which needs no selection at all.

**Consequence (pairwise separation).** `C_t` lies in `{|f| < t} ⊂ {|f| < 1}` for
`t < 1`, and its roots are distinct. So if any pair had `a artanh(s^2) < 1` the
geodesic would join two distinct roots inside `{|f| < 1}` with length below `2`.
Failure therefore forces, for **every** pair `i != j`,

```text
d(b_i, b_j) >= d_min(a) := 4 artanh( sqrt( tanh(1/a) ) ).                  (1)
```

**Consequence (the arity floor).** Failure of COVER supplies a point `h in Gamma`
whose intrinsic distance to *every* root exceeds `1`, so by Lemma 1 with one
endpoint at zero, `rho_j := rho(h, b_j) >= sqrt(1 - exp(-1/a))` for every `j`,
i.e. `lambda_j := -log rho_j <= delta(a)/2` with
`delta(a) = -log(1 - exp(-1/a))`. Order `d_1 <= ... <= d_k` where
`d_j = 2 artanh(rho_j)`. By (1) and the triangle inequality
`d_1 + d_2 >= d(b_1,b_2) >= d_min`, hence `d_j >= d_min/2` for every `j >= 2`,
and `-log tanh(d_min/4) = -(1/2) log tanh(1/a) = tau(a)/2`. Since
`sum_j lambda_j = log(t/|f(h)|) >= x`,

```text
x <= delta(a)/2 + (k-1) tau(a)/2,   i.e.   k >= 1 + (2x - delta(a))/tau(a).  (2)
```

Writing `u = exp(-1/a)`, `tau/2 = artanh(u^2)` and `delta/2 = -(1/2)log(1-u)`
differ by `(1/2)(log(1+u^2) - log(1+u)) < 0`, so `tau(a) < delta(a)` always and
(2) strictly dominates the old floor `k >= 2x/delta(a)` once `2x > delta(a)`; for
small `a` it dominates by an exponential factor, `tau ~ 2 e^{-2/a}` against
`delta ~ e^{-1/a}`.

**The sharp ordered form, which is what the certificate uses.** (2) is not tight,
because it lets `d_1 = d_low := 2 artanh(sqrt(1-u))` and `d_j = d_min/2` hold at
the same time, and they cannot: `d_1 + d_2 >= d_min` forces
`d_2 >= d_min - d_1`. With the ordering the only binding pair constraint is
`d_1 + d_2 >= d_min`, so the maximising profile is
`d_j = max(d_1, d_min - d_1)` for every `j >= 2`, and the exact bound is

```text
Lambda(k, a) = max_{d >= d_low} [ lam(d) + (k-1) lam(max(d, d_min - d)) ],
lam(d) = -log tanh(d/2) = 2 artanh(exp(-d)).
```

`lam'' (d) = cosh d / sinh^2 d > 0`, so `lam` is convex; hence on
`[d_low, d_min/2]` the bracket is convex in `d` and attains its maximum at an
endpoint, while on `[d_min/2, infinity)` it is `k lam(d)`, decreasing. Therefore

```text
Lambda(k, a) = max( delta(a)/2 + (k-1) lam(g),  k tau(a)/2 ),
g = d_min - d_low = 2 lam(tau/2) - lam(delta/2),                            (2')
```

using `d_low = lam(delta/2)` and `d_min = 2 lam(tau/2)`. Failure forces
`Lambda(k,a) >= x`. At `a = 1`: `delta/2 = 0.22934`, `tau/2 = 0.13617`,
`g = 3.1745`, `lam(g) = 0.08366`, so `Lambda(7,1) = 0.9532` against the crude
`1.0465` — the sharp form raises the forced arity by about `9%` at every `k`, and
that is the whole difference between `33/100` and `9/25`.

## Assembly

The boundary-hop inequality of `LowCriticalPotentialClosure.md` is unchanged:
failure forces, at every regular `x` with `mu e^x < 1`,

```text
a'(x) >= G(x, a(x)) := (1/(2 pi^2)) [ 2 sqrt(k) - sqrt(2 a (x+2)) ]_+^2,     (3)
```

with `k = k(x, a)` now the smallest arity admitted by (2'), i.e. the maximum of
`2`, the COVER floor `2x/delta(a)`, and `min(k_A, k_B)` from the two branches of
(2'). `G` is still
decreasing in `a` and its `k`-term still increasing in `x`, so the same monotone
implicit-Euler comparison with a geometric grid over the unknown initial area is
rigorous verbatim, and the same rational rounding bounds every transcendental in
the safe direction (`tau` is bounded above by an odd-power series in
`u = exp(-2/a)` with a geometric tail, exactly as `delta` is).

The certified hitting time of the cap `a > 1` drops from `X_cert < 1.6244` to
`X_cert < 1.014374` (quick mode), and `(9/25) exp(1.014374) < 1`.

## Sharpness and what is left

The floating supremum of the sharpened mechanism is `X_* = 0.99500`, attained on a
trajectory that rides with forced arity near `7.1-7.3` and area growth near `0.48`
per unit of `x`; `exp(-0.99500) = 0.36972`, so `0.370` is unreachable by this
mechanism with any certificate. The regime `0.370 < mu < 1` is untouched, and as
`mu` approaches `1` the failure window closes — the near-Fekete shell, again.

Two further couplings were measured and do **not** improve the threshold; they
are recorded so they are not re-attempted.

*Ancestor capacity.* With `c(t) = cap(closure C_t)` and `p(t) = c(t)^n/t`, the
exact component capacity formula, `Area <= pi c^2`, the capacity-speed law
`d log c/d log t >= 1/k` of [SharpSymmetricMergeEnvelope.md](SharpSymmetricMergeEnvelope.md)
Theorem 1 (with non-negative jumps at attachments), and the fibre-coupled gap
`p < k/(2n-k)` of [ExteriorBlaschkeFibreCapacityGap.md](ExteriorBlaschkeFibreCapacityGap.md)
Theorem 2 compose into a degree-free constraint on the failure trajectory: for
all `0 <= x_1 <= x_2 <= X`,

```text
int_{x_1}^{x_2} dxi / k(xi)  <=  (1/2) log(1/a(x_1))  +  (x_2 - X + log p_0)/n .
```

Measured on the extremal trajectory of the sharpened mechanism this holds with
about `18%` slack (worst ratio `0.82` on the baseline mechanism), so it is a true
but non-binding constraint. It binds exactly when `k a' < 2` on the attractor,
and the attractor has `k a' ≈ 3.2`.

*The exterior area theorem names the missing quantity.* With the exterior map
`psi(w) = c(w + beta_0 + beta_1/w + ...)`, `a = c^2 (1 - S)`,
`S = sum_l l |beta_l|^2`, so `a <= 1` is sharp only for a disc. Any uniform lower
bound `S >= s_0` along the failure trajectory replaces the cap `a <= 1` by
`a <= 1 - s_0` and moves the threshold as follows (floating, baseline mechanism):
`s_0 = 0.05, 0.10, 0.15, 0.20, 0.25` gives `mu <= 0.230, 0.264, 0.301, 0.341,
0.385`. On the corpus's own petal computation the `k`-sheeted lemniscate
component at its birth level has `S` between `0.36` (`k=2`) and `1/2`
(`k -> infinity`), but `S -> 0` as the component rounds out well above its birth
level, so no uniform `s_0` is available from that family alone. **`S` on the
ancestor component, as a function of the elapsed log-level `x` and the arity, is
the quantity a proof of the remaining regime must control.**

## Claim boundary

Theorem A is an ordinary argument, not Lean-checked and not independently
reviewed. Lemma 1's constant is validated numerically against the exactly solvable
family `f = z^2 - r^2`, where the geodesic between the two roots is the segment of
length `2r`: the bound is above the truth at every tested `(r,t)` and its ratio to
the truth tends to `1.00000` as `t -> infinity`, so the Bergman constant is sharp
in the limit and not merely safe. Erdős #1041 remains open. No priority or novelty
claim is made against the potential-theory literature; Lemma 1 is the standard
Bergman-kernel Cauchy--Schwarz and should be assumed known.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_cluster_separation_closure.py --quick
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_cluster_separation_closure.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_cluster_separation_closure.py --quick --per-degree
```

Each prints one JSON line; `all_degree.mu_threshold` is the theorem constant for
that run. The first form finishes in a couple of minutes and certifies
`X_cert = 101437302713/100000000000 < 1.014374`, hence `mu <= 9/25`. The third
adds the fixed-degree arm and is slow.
