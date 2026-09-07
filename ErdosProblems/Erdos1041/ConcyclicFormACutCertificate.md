# Erdős #1041, concyclic zeros: exact Form-A-cut certificates and the concentric-alternation law

Status, corrected 2026-08-25: one exact reduction criterion, one **Lean-checked
potential-domination kernel**, one **proven infeasibility** for first-moment-only
certificates, and one now-**refuted** concentric-alternation conjecture.  The
exact five-root counterexample is in
[ConcyclicAlternationCounterexample.md](ConcyclicAlternationCounterexample.md).
Erdős #1041 remains open.  **The concyclic case remains open.** Nothing below
claims otherwise.

Companions: [ConcyclicAlternation.md](ConcyclicAlternation.md) (radius
`rho <= 2^{-1/n}` by arc alternation), [ConcyclicSpokeCalculus.md](ConcyclicSpokeCalculus.md)
(exact spoke normal form, orbit balance, certified no-gos), and
[TwoSmallestRootTruncation.md](TwoSmallestRootTruncation.md) (modulus-selected
truncation, all degrees, general configurations).

## 0. Setup

`w_1, …, w_n` distinct on the unit circle, `g = prod (z - w_k)`, `s_m` the power
sums.  As in §0 of [ConcyclicSpokeCalculus.md](ConcyclicSpokeCalculus.md):
`|g(0)| = 1` exactly, so a length-`<= 2` path inside `{|g| <= 1}` scales to a
witness of Erdős #1041 at **every** radius `rho < 1`.  The target is the Form
A-cut objective of [TruncatedSpokeReduction.md](TruncatedSpokeReduction.md):

```text
tau_j  =  inf { s :  |g| <= 1 on [s w_j, w_j] },          (entry radii)
V      =  min over adjacent k, min over s in [max(tau_k, tau_{k+1}), 1],
          max over the chord [s w_k, s w_{k+1}] of |g|.
```

`V <= 1` settles the full concyclic class.  The regular `n`-gon has `V = 1`
exactly (attained at `s = 0`: the pair of radii), so `V <= 1` is sharp.

## 1. The certificate criterion (exact)

For an adjacent gap `G_k = [phi_k, phi_{k+1}]` write

```text
C_k(s)   =  max_{psi in G_k} log|g(s e^{i psi})|                    (chord profile)
L_j(t)   =  log|g(t w_j)|                                           (spoke profile)
```

> **Criterion.**  `V <= 1` if and only if some adjacent `k` admits `s` with
> ```text
> (C)  C_k(s) <= 0                                   on the whole gap,
> (S_j)  L_j(t) <= 0    for all t in [s, 1],  j = k, k+1.
> ```
> Both systems are one-dimensional and finitely checkable: `|g|^2` restricted to
> a chord or a spoke is a polynomial of degree `2n` in one real parameter, so
> each constraint reduces to locating real roots of explicit polynomials.

This is definitional, not deep — its value is that it converts the conjecture
into a per-configuration finite certificate problem, implemented by
[scripts/check_erdos1041_concyclic_form_a_cut_certificate.py](scripts/check_erdos1041_concyclic_form_a_cut_certificate.py).

## 2. The potential-domination kernel (Lean-checked)

`ConcyclicPotentialBound.lean` proves, from nothing deeper than
`log(1+u) <= u`:

> **Factor bound.**  For `|w| < 1`,
> ```text
> log|1 - w|  <=  |w|^2 / 2 - Re w.
> ```

> **Fan-in.**  With all `v_i` of unit modulus and `P(z) := sum_i Re(z conj(v_i))`
> (so `P(z) = Re(z conj(s_1))` for `z` a point of the configuration circle),
> ```text
> prod_i |z - v_i|^2  <=  exp( n |z|^2 - 2 P(z) ).
> ```

> **Chord/spoke corollary.**  If `P(z) >= n |z|^2 / 2`, then `|g(z)| <= 1`.

Applied along a chord `[s w_k, s w_{k+1}]` this gives the **cone condition**
`min_{psi in G_k} Re(conj s_1 e^{i psi}) >= n s^2 / 2` as a *sufficient*
chord certificate, and along spokes the analogous window condition
`t Re(conj s_1 w_j) >= n t^2 / 2`.  These are the cheap half of any
certificate; the exact half is the polynomial root-location of §1.

### 2.1 A proven negative: first moments alone cannot suffice

The obvious programme — control chords AND spokes using only `s_1` and the
crude tail `|s_m| <= n` — is **infeasible**, and provably so at the level of
the resulting scalar system.  The spoke requirement under that tail reads

```text
Re(conj s_1 w_j)  >=  n (log 1/(1-t) - t) / t        for all t in [s, 1].
```

The right side diverges as `t -> 1`; switching to the factor bound
`(1-t)(1+t)^{n-1} <= 1` only covers `t >= t*_n` with `t*_3 ~ 0.618`,
`t*_4 ~ 0.84`, `t*_n -> 1`, and the mid-range window stays uncovered.  A
bounded exhaustive scan over admissible `(s, R)` with `R = |s_1| <= n` finds
**no feasible point for any `n >= 4`** (minimum required `R` exceeds `n` by
`4.7` at `n = 4`, `9.2` at `n = 5`, growing linearly), and even with an
artificial spectral cap `|s_m| <= beta` for `m >= 2`, feasibility requires the
endpoint projections `R cos(delta)` to dominate `beta (log 1/(1-t*_n) - t*_n)/t*_n`,
which fails across the near-regular shell where `R` and `beta` are of the same
exponentially small size.  **Consequence:** any proof of `V <= 1` must use
joint multi-harmonic information; there is no shortcut through the first power
sum.  This retires the most tempting cheap route before another session
re-derives it.

## 3. The concentric-alternation law (refuted)

> **Refuted Conjecture U.**  For distinct `w_1..w_n` on the unit circle and **every**
> `s in (0, 1]` simultaneously,
> ```text
> min_k  max_{psi in G_k} log|g(s e^{i psi})|   <=   log(1 + s^n),
> ```
> with equality (for all `s`) exactly at the rotated regular `n`-gon.

This statement is false at `n=5` and `s=3/20`.  The Gaussian-rational witness
in [ConcyclicAlternationCounterexample.md](ConcyclicAlternationCounterexample.md)
places a strict violating point in every one of the five gaps, with squared
product margins between `0.00191` and `0.01910`; the complete rational core is
Lean-checked.  Thus the measurements below recorded only the sampled basins,
exactly as the pre-existing warning from `negative_results` entry 19 required.

The next natural deterministic repair is false as well.  One might select the
uniquely smallest angular gap and then optimize its common truncation radius.
[ConcyclicSmallestGapSelectorCounterexample.md](ConcyclicSmallestGapSelectorCounterexample.md)
gives a near-regular rational pentagon for which that selected pair has an
unsafe full spoke at radius zero, while at every positive radius its chord
midpoint has `|g|>1`.  The all-radius obstruction is an exact positive
degree-ten Bernstein certificate and is Lean-checked.  This is not a
counterexample to Form A: another adjacent pair may still work.  It proves
that gap size alone cannot supply the missing joint pair-radius selector.

At `s = 1` the proposed statement recovers Theorem C/T2 of [ConcyclicAlternation.md](ConcyclicAlternation.md)
(the sharp constant `2`).  At `s -> 0` both sides tend to `0`.  The content is
that **one gap works at every radius at once**, with the regular polygon the
unique extremizer at every scale.  Note the interior subtlety that makes this
non-obvious: `u(r e^{i psi})` is not monotone in `r`, and a gap whose boundary
arc peaks below `1` can still carry large interior values; the conjecture says
some gap nonetheless never does beyond `1 + s^n`.

**Why the s=1 alternation proof does not transport.**  §3 of
[ConcyclicAlternation.md](ConcyclicAlternation.md) consumes two facts specific
to the unit circle: the realification `G(psi) = prod 2 sin((psi - phi_k)/2)`
has simple zeros ON the circle forcing sign alternation between gaps, and
`g - q` drops degree because leading *and* constant coefficients match.  On an
interior circle both inputs vanish: neither `g` nor `Q_s(w) = prod (1 - s w conj(w_k))`
— which IS a genuine degree-`n` polynomial on `|w| = 1` — has any zero on the
comparison circle, so no sign alternation is available, and the degree drop of
`Q_s - mu w^n` yields only modulus information (`|P| > 1` at points), which
cannot count zeros.  A new idea is required; none is claimed here.

**Historical measurement (completed through degree ten, but now falsified as
evidence for the universal law).**
[scripts/check_erdos1041_concyclic_form_a_cut.py](scripts/check_erdos1041_concyclic_form_a_cut.py)
seed `20260825`, adversarial hill-climbing seeded on the regular polygon at
perturbation scales `1e-1 .. 1e-6`:

| `n` | regular `V` | adversarial near-regular max `V` | excess |
|---:|---:|---:|---:|
| 3 | `1.000000000000` | `1.000000000000` | `+0.0` |
| 4 | `1.000000000000` | `0.999999999841`* | `-1.6e-10`* |
| 5 | `1.000000000000` | `0.999999999787`* | `-2.1e-10`* |
| 6 | `1.000000000000` | `0.999999998161` | `-1.839e-09` |
| 7 | `1.000000000000` | `0.999999976307` | `-2.369e-08` |
| 8 | `1.000000000000` | `0.999999988327` | `-1.167e-08` |
| 9 | `1.000000000000` | `0.999999979062` | `-2.094e-08` |
| 10 | `1.000000000000` | `0.999999954121` | `-4.588e-08` |

(\* earlier-session rows retained; `n = 6..10` are the new seed-`20260825` run.)
The producer note's stricture "do not quote `n >= 7` until that rerun exists"
is hereby discharged: the rerun exists, is deterministic, and never crosses
`1`.  Per `negative_results` entry 19 these suprema report basins, not proofs.

## 4. Optimizer anatomy (measured)

For near-regular adversarial maximizers the structure of the *winning
certificate* is rigid:

* the winning pair uses **fully-good spokes** (`max(tau_k, tau_{k+1}) = 0`) in
  15 of 16 recorded rows;
* the losing spokes are precisely those with `Re(conj s_1 w_j) < 0` — the
  back hemisphere — matching the first-order theory of §3 in
  [TruncatedSpokeReduction.md](TruncatedSpokeReduction.md);
* the winning radius tracks the tilt-excess balance
  `s* ~ (|s_1| max_k cos(delta_k) / n)^{1/(n-1)}`, the unique scale where the
  first-harmonic dip `-s Re(conj s_1 e^{i psi})` cancels the regular excess
  `s^n`; measured `s*` runs `~1.1-1.6x` the prediction consistently.

So `V <= 1` off the regular polygon is, mechanistically, a **tilt-versus-cusp**
balance: the cusp supplies a positive `O(s^n)` excess at every gap, and any
nonzero harmonic tilt supplies an `O(s)` dip somewhere; the certificate lives
at the geometric mean scale.  The hard shell is exactly `s_1 -> 0` faster than
every other harmonic — i.e. the Fekete-near shell of
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md).

## 5. Co-connectivity observation (grid-grade)

On dense grids, for clustered and uniform random configurations at `n = 3..6`,
**some connected component of `{u <= 0} cap closed disk` always contains at
least two roots** (probe script, experiment E3).  At the regular polygon all
roots share the component through the origin since `u(0) = 0` exactly.  No
counterexample was sought-and-found; equally, no proof is offered.  Recorded
because it suggests the topological core ("two roots co-connected at level
zero") may be strictly easier than the metric statement, and a proof of it
would combine with the crossing-chord machinery of
[CrossingChordUpperBound.md](CrossingChordUpperBound.md).

## 6. What this does not do

* The concyclic case of Erdős #1041 is **open** at every `n >= 5`.
* Conjecture U is false; the `s=1` transport argument provably does not adapt
  and the exact `n=5`, `s=3/20` witness shows that no proof can exist (§3).
* Choosing the unique smallest angular gap and optimizing only its common
  radius is also false, by the exact all-radius pentagon above.  The surviving
  selector must use spoke/potential information jointly with gap geometry.
* The §2 kernel is a *sufficient* bound; §2.1 shows the corresponding
  first-moment programme is dead, so the surviving route needs joint
  multi-harmonic (cluster-aware) bookkeeping: the reason adversarial mid-range
  spokes cannot coexist with front-cone gaps is that opposite-side clustering
  that inflates `log(1+t)` factors also rotates `s_1` into the gap being used —
  turning the cluster's own factors into `log(1-t)` damping.  Making that
  quantitative is the next real theorem here.

## 7. Relation to neighbouring results

* [TwoSmallestRootTruncation.md](TwoSmallestRootTruncation.md) selects by
  **modulus** and works for general configurations; on concyclic inputs it
  reaches only radii `rho <= q_n` (about `0.53-0.75`).  The present note keeps
  the concyclic scaling axis, which is what can reach every `rho < 1`.
* The movable-hub / area-payment bridge recorded on the unrestricted lane is a
  different selection axis again; nothing here obstructs or duplicates it.

## Replay

```sh
# Exact counterexample to the former Conjecture U
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_concyclic_alternation_counterexample.py

# Exact counterexample to the smallest-gap common-radius selector
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_concyclic_smallest_gap_selector_counterexample.py

# Lean kernel (focused build)
cd formal_math/erdos257_period_noncollapse && ../../repo-python scripts/lean_fast_build.py \
  --jobs 2 ErdosProblems.Erdos1041.ConcyclicPotentialBound

# Certificate battery (regular attainment, near-regular shells, controls)
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_concyclic_form_a_cut_certificate.py

# Degrees 7..10 adversarial rerun (landed 2026-08-25, seed 20260825)
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_concyclic_form_a_cut.py 20260825
```
