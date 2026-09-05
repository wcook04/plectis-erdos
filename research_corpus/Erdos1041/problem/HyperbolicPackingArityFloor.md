# Erdős 1041: the arity floor is a hyperbolic packing problem, and the corpus relaxation is not feasible

## Status

Ordinary complete proof of an unconditional all-degree parent regime, with an
exact rational certificate. Not Lean-checked, not independently reviewed. Erdős
#1041 remains open.

This sharpens [ClusterSeparationLowCriticalClosure.md](ClusterSeparationLowCriticalClosure.md)
from `mu <= 9/25` to `mu <= 2/5`. Nothing in the mechanism changes except the
arity floor: the same Lemma 1 Bergman bound, the same COVER failure, the same
boundary hop, the same comparison ODE, the same rational rounding discipline.
The note was written while measuring the exterior-energy question of
[ExteriorEnergyFloorClosure.md](ExteriorEnergyFloorClosure.md), which is where
the feasibility check came from.

## Theorem

> **Theorem A'.** Let `f` be squarefree monic of degree `n >= 2` and
> `mu = min{|f(c)| : f'(c) = 0}`. If `mu <= 2/5`, then two distinct roots of `f`
> are joined by a rectifiable curve inside `{|f| < 1}` of length strictly below
> `2`.

> **Corollary B'.** Every squarefree monic `f` has two distinct roots joined
> inside `{|f| < (5/2) mu}` by a curve of length below `2((5/2) mu)^{1/n}`.

## 1. The gap in the corpus relaxation

Failure, at a regular level `t` with `x = log(t/mu)`, puts `k` points
`b_1, ..., b_k` in the unit disc — the roots of the ancestor component `C_t`,
uniformised so that the COVER-failure point `h` goes to `0` — with

```text
(i)   pairwise hyperbolic distance  d(b_i, b_j) >= D := d_min(a),
(ii)  lam_j := g_D(0, b_j) = -log tanh(d_j/2) <= delta(a)/2,
(iii) sum_j lam_j = log(t/|f(h)|) >= x.
```

`ClusterSeparationLowCriticalClosure.md` (2') bounds `sum_j lam_j` by relaxing
(i) to the single triangle inequality `d_1 + d_2 >= D`, giving

```text
Lambda(k,a) = max( delta/2 + (k-1) lam(g),   k tau/2 ).
```

The second branch is the binding one from `k = 6` up (`Lambda(7,1) = 0.9532`
against `0.7313` for the first), and it is **not geometrically realisable for
`k >= 3`**: it puts every `b_j` at hyperbolic distance exactly `D/2` from `0`,
and two points at distance `R` from a common point are at distance at most `2R`,
with equality only when they are antipodal. Three points cannot be pairwise
antipodal. Direct optimisation of `sum_j lam_j` under the full constraint set
gives, at `a = 1`,

| `k` | 2 | 3 | 4 | 5 | 6 | 7 | 10 | 16 | 20 |
|---|---|---|---|---|---|---|---|---|---|
| `Lambda(k,1)` corpus | 0.3103 | 0.4085 | 0.5447 | 0.6809 | 0.8170 | 0.9532 | 1.3617 | 2.1783 | 2.7234 |
| feasible optimum | 0.3103 | 0.3784 | 0.4306 | 0.4694 | 0.4986 | 0.5208 | 0.5759 | 0.6422 | 0.6745 |

The feasible optimum grows like `0.142 log k`, not linearly: `k` points pairwise
`D`-separated fall into hyperbolic "rings" about `h`, each ring contributing at
most about `pi sqrt(eps/(1-eps))` with `eps = 1 - tanh^2(D/2)`, and consecutive
rings are `D` apart in hyperbolic radius. The corpus bound therefore
under-forces the arity by roughly a factor `e^2` at the working point.

## 2. The replacement bound

> **Lemma P.** Under (i)–(ii), with `E := e^{2/a} - 1` and
> `C := 1 + (k-1) E`,
>
> ```text
> sum_{j=1}^k lam_j  <=  delta(a)/2
>       + [ (C-1)/2 * log((C+1)/(C-1)) + log((C+1)/2) ] / E,
> ```
>
> and also, without the `delta(a)/2` term, the same expression with
> `C = 1 + k E`. The first form holds when some ball contains the base point
> and the second when none does, so the true sum is at most the LARGER of the
> two; inverting each case for `k` and taking the smaller of the two arity
> solutions, as (P) does, is the correct floor. (Wording corrected by the
> conductor, 2026-09-05; the certificate already implemented the correct
> direction.)

*Proof.* First, `cosh(D/2) = e^{2/a}`: with `s = tanh(D/4) = sqrt(tanh(1/a))`,
`cosh(D/2) = (1+s^2)/(1-s^2) = (1 + tanh(1/a))/(1 - tanh(1/a)) = e^{2/a}`. So the
hyperbolic ball `B_j := B(b_j, D/2)` has area `A_0 = 2 pi (e^{2/a} - 1) = 2 pi E`.

By (i) the `B_j` are pairwise disjoint. At most one contains `0`: if
`0 in B_i cap B_j` then `d(b_i,b_j) < D`. That exceptional index, if it exists,
contributes `lam <= delta(a)/2` by (ii); otherwise there is none and all `k`
indices fall in the next paragraph.

`G(z) := g_D(0,z) = -log|z|` is harmonic on `D \ {0}`, and in dimension two
Euclidean and hyperbolic harmonicity coincide, so the hyperbolic spherical-mean
property holds: for every `j` with `0 notin B_j`,
`lam_j = (1/A_0) int_{B_j} G dA_hyp`. Summing over those `j`, the domains are
disjoint with total hyperbolic area `(k-1) A_0` (or `k A_0` in the exceptional-free
case), and `G` is a strictly decreasing function of hyperbolic distance from `0`,
so by the bathtub rearrangement the integral is at most the integral over the
centred ball `B(0,R)` of the same area, `cosh R = C`. Finally

```text
int_{B(0,R)} G dA_hyp
  = 2 pi [ (cosh R - 1)(-log tanh(R/2)) + 2 log cosh(R/2) ]
  = 2 pi [ (C-1)/2 * log((C+1)/(C-1)) + log((C+1)/2) ],
```

by parts, using `d/dR(-log tanh(R/2)) = -1/sinh R` and
`(cosh R - 1)/sinh R = tanh(R/2)`. ∎

Since `(C-1) artanh(1/C) <= 1 - 1/C + 1/(3C(C+1)) <= 1`, the certificate uses the
simpler upper form `delta/2 + [1 + log((C+1)/2)]/E`, which loses `0.4%` at `k=7`
and less thereafter, and reduces every transcendental to a single logarithm.

Inverting: failure at `(x, a)` forces

```text
k >= min( 1 + 2(exp(E(x - delta/2) - 1) - 1)/E,
              2(exp(E x - 1) - 1)/E ),                                   (P)
```

and the certificate takes the maximum of (P), the COVER floor `2x/delta`, and the
corpus profile (2'), each of which is separately valid.

## 3. Assembly

`G(x,a) = (1/(2 pi^2))[2 sqrt(k) - sqrt(2a(x+2))]_+^2` and the monotone
implicit-Euler comparison are verbatim from
`LowCriticalPotentialClosure.md`; only `k = k(x,a)` moves. The arity floor at
`a = 1`:

| `x` | 0.6 | 0.7 | 0.8 | 0.9 | 0.95 | 1.00 |
|---|---|---|---|---|---|---|
| corpus | 4.41 | 5.14 | 5.88 | 6.61 | 6.98 | 7.34 |
| with (P) | 4.41 | 5.14 | 5.88 | 9.20 | 12.35 | 16.68 |

The floating supremum of the hitting time drops from `X_* = 0.99364` to
`0.89374`, and `exp(-0.89374) = 0.40912`, so `0.410` is the new ceiling of this
mechanism. The exact rational certificate in quick mode gives
`X_cert < 0.914374`, and `(2/5) exp(0.914374) < 1`.

Fixed-degree rows were not re-run in this pass; the per-degree arm of the
predecessor note is unchanged and still authoritative there.

## 4. What is still on the table

The feasible optimum table above is a *measurement*: the certificate uses the
rearrangement bound, which is still about `1.6x` loose at the working arity
(`0.852` against `0.521` at `k = 7`). The loss is entirely the hyperbolic
packing inefficiency near the base point — the rearrangement lets `k-1` disjoint
`D/2`-balls fill a centred ball, which no `D`-separated configuration achieves.
Closing that gap would raise the arity floor by roughly a further factor `e^2`
and, on the same ODE, push the ceiling from `0.41` towards `0.5`.

A second, independent source of slack: for `k = 2` the interior Blaschke
structure forces the pseudohyperbolic distance of the two roots to be
`2 sqrt(mu/t)/(1 + mu/t)` exactly, so `x <= tau(a)` — strictly better than both
`Lambda(2,a) = 0.3103` and the packing bound. Whatever the analogue is for
general `k` (a statement about critical values of degree-`k` Blaschke products,
not about point configurations) would tighten the floor everywhere.

## 5. Claim boundary

Theorem A' is an ordinary argument with an exact rational certificate, not
Lean-checked and not independently reviewed. Lemma P's three ingredients were
each verified independently at 25 digits: the hyperbolic mean-value property for
`-log|z|` over hyperbolic balls, the closed form for the centred integral, and
`cosh(d_min/2) = e^{2/a}`. The infeasibility of the corpus's second branch is an
elementary observation about antipodality, not a defect in the predecessor
theorem — that theorem's bound is valid, just not tight. The feasible-optimum
table is numerical (SLSQP with ring-ansatz restarts, feasibility re-checked at
`1e-9`) and carries no universal quantifier. Erdős #1041 remains open. No
priority claim is made; the mean-value/rearrangement pairing is standard
potential theory.

## 6. Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_packing_arity_floor.py --quick
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_packing_arity_floor.py
```

One JSON line; `all_degree.mu_threshold` is the theorem constant for that run.
