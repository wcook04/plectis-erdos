# Erdős #1041 for concyclic zeros: an exact spoke calculus, and a certified no-go

Status, 2026-08-24: three proved identities/inequalities (two of them sharp),
one **exactly certified negative result** at degrees 3 and 5, and one calibrated
sharp conjecture.  Erdős #1041 remains open.  The concyclic case remains open.
Nothing below claims otherwise.

Companion to [ConcyclicAlternation.md](ConcyclicAlternation.md), which settles
the concyclic case for radius `rho <= 2^{-1/n}` by a Chebyshev alternation on
the gap arcs.  That note's §8 names the real target — the truncated-spoke
objective `V <= 1` of [TruncatedSpokeReduction.md](TruncatedSpokeReduction.md) —
and this note attacks the spoke side of it.

## 0. Normalisation, and why the constant is exactly 2

Throughout `w_1, …, w_n` are **distinct** points of the unit circle,
`w_k = e^{i phi_k}`, and

```text
g(z) = prod_{k=1}^n (z - w_k),      s_m = sum_{k=1}^n w_k^m   (m >= 1).
```

For `f` monic of degree `n` with all zeros on the circle of radius `rho < 1`
about `c`, write `f(z) = rho^n g((z - c)/rho)`.  A path joining two `w_j` of
length `<= 2` inside `{|g| <= 1}` scales to a path joining two zeros of `f` of
length `<= 2 rho < 2` inside `{|f| <= rho^n} ⊂ {|f| < 1}`.  Hence

> **Reduction.**  If every `n`-point configuration on the unit circle has two
> points joined by a path of length `<= 2` inside `{|g| <= 1}`, then Erdős #1041
> holds for **all** concyclic zeros, at **every** radius `rho < 1`.

Two facts fix the constant.  `|g(0)| = prod_k |w_k| = 1`, so the origin always
lies on `{|g| = 1}` and is always admissible; and `|w_a| + |w_b| = 2` for any
two zeros, so the broken path `w_a -> 0 -> w_b` has length exactly `2`.  At the
regular `n`-gon `g = z^n - c` the set `{|g| <= 1}` is `n` petals meeting only at
the origin, so `2` is attained and cannot be lowered.  **Every** root chord also
obeys the budget, since `|w_a - w_b| <= 2`; adjacency is a convenience of
Theorem C in the companion note, not a constraint imposed by the length.

## 1. Theorem 1 — the spoke normal form

> **Theorem 1.**  For every `j` and every real `t`,
> ```text
> |g(t w_j)|^2  =  prod_{k=1}^n [ (1-t)^2 + t |w_j - w_k|^2 ].
> ```

*Proof.*  `|t w_j - w_k| = |t - w_k \bar w_j|` because `|w_j| = 1`.  With
`theta = phi_j - phi_k`,

```text
|t - e^{-i theta}|^2 = 1 - 2 t cos theta + t^2
                     = (1-t)^2 + 2t(1 - cos theta)
                     = (1-t)^2 + t |w_j - w_k|^2,
```

the last step from `|w_j - w_k|^2 = 2 - 2 cos theta`.  Multiply over `k`. ∎

The factor at `k = j` is `(1-t)^2`.  So **the entire profile of `|g|` along the
radius `[0, w_j]` is a function of the chord distances from `w_j` alone** — the
angular positions enter only through `|w_j - w_k|`.

**Palindromic form.**  `1 + t^2 - 2 t c = t(y - 2c)` with `y = t + 1/t`, so

```text
|g(t w_j)|^2  =  t^n prod_{k=1}^n ( y - 2 cos(phi_j - phi_k) ),      y = t + 1/t.
```

The right factor is a monic degree-`n` polynomial in `y` with all roots in
`[-2, 2]`, one of them at `y = 2`.  Writing `t = e^{-xi}`, `y = 2 cosh xi`, the
spoke condition `|g| <= 1` on `[0, w_j]` becomes a **Chebyshev-type comparison
outside the interval**:

> **Corollary 1.1.**  The radius `[0, w_j]` lies in `{|g| <= 1}` if and only if
> ```text
> prod_{k=1}^n ( y - 2 cos(phi_j - phi_k) )  <=  ( (y + sqrt(y^2-4)) / 2 )^n
> ```
> for every `y >= 2`.  The right-hand side is `e^{n xi}`, and
> `e^{n xi} + e^{-n xi} = 2 T_n(y/2)` is the monic Chebyshev polynomial of
> `[-2,2]`, so the comparison is with `T` minus its own reciprocal branch.

Necessary at `y -> infinity`: matching the `y^{n-1}` coefficients gives
`sum_k 2 cos(phi_j - phi_k) >= 0`, i.e. `Re(w_j conj(s_1)) >= 0`.  That is
exactly the first-order origin condition recorded in §3 of
[TruncatedSpokeReduction.md](TruncatedSpokeReduction.md), recovered here as the
leading term of an exact statement.

## 2. Theorem 2 — orbit balance, exact and to all orders

> **Theorem 2.**  For `|t| < 1`,
> ```text
> sum_{j=1}^n log |g(t w_j)|  =  - sum_{m>=1} |s_m|^2 t^m / m,
> ```
> equivalently
> ```text
> prod_{j,k=1}^{n} | 1 - t w_j conj(w_k) |  <=  1      (0 <= t < 1),
> ```
> with strict inequality for `t > 0`.

*Proof.*  `g` has no zero in the open disk, so `log g` is single valued there and
`log g(z) = log g(0) - sum_{m>=1} conj(s_m) z^m / m`, because
`sum_k log(1 - z/w_k) = - sum_m (z^m/m) sum_k \bar w_k^m`.  Since `|g(0)| = 1`,
taking real parts gives `log|g(z)| = - sum_m Re(conj(s_m) z^m)/m`.  Put
`z = t w_j` and sum over `j`, using `sum_j w_j^m = s_m`:
`sum_j Re(conj(s_m) w_j^m) = |s_m|^2`.  For the product form use
`|t w_j - w_k| = |1 - t w_j conj(w_k)|`.  Strictness: `s_1 = … = s_n = 0` would
force `e_1 = … = e_n = 0` by Newton's identities, contradicting
`e_n = ± prod_k w_k ≠ 0`; so some `|s_m|^2 > 0` with `m <= n`. ∎

> **Corollary 2.1.**  For every `t ∈ [0,1)` there is an index `j` with
> `|g(t w_j)| <= 1`: at every radius, at least one spoke is inside the
> lemniscate at that radius.

Theorem 2 is the exact, all-order, every-configuration form of the first-order
near-Fekete balance identity recorded as
`exact_results::near_fekete_origin_spoke_balance_and_kernel`, which computes
`sum_j Lambda(t omega^j)` to first order in a perturbation of the regular
`n`-gon.  Here there is no perturbation parameter and no truncation: the deficit
is exactly `sum_m |s_m|^2 t^m / m`, a nonnegative power series whose coefficients
are the squared moduli of the power sums.  The vanishing of the deficit to
order `n-1` characterises the regular `n`-gon.

## 3. Theorem 3 — the sharp radial law

> **Theorem 3.**  Let `t ∈ [0,1]`.
>
> **(i)** `|g(t w_j)| <= (1-t)(1+t)^{n-1}` for every `j`; sharp.
>
> **(ii)** `max_{[0,w_j]} |g| <= 2^n (n-1)^{n-1} / n^n`; sharp, attained in the
> limit in which the other `n-1` zeros approach `-w_j`.
>
> **(iii)** `d/dt log|g(t w_j)| <= 0` for every `t >= (n-2)/n` and every `j`;
> the constant `(n-2)/n` cannot be lowered.
>
> **(iv)** Let `s_n^*` be the unique root in `((n-2)/n, 1)` of
> `(1-s)(1+s)^{n-1} = 1`  (`s_2^* = 0`, `s_3^* = (sqrt 5 - 1)/2 = 0.618034…`).  Then for
> every `j`, the truncated spoke `[s w_j, w_j]` lies in `{|g| <= 1}` whenever
> `s >= s_n^*`.

*Proof.*  (i) `|t w_j - w_j| = 1-t` and `|t w_j - w_k| <= t + 1 `.  Equality in
the limit `w_k -> -w_j` for all `k ≠ j`.  (ii) Maximise `(1-t)(1+t)^{n-1}`: the
derivative vanishes at `t = (n-2)/n`, giving `(2/n)((2n-2)/n)^{n-1}`.
(iii) Differentiating Theorem 1's logarithm,

```text
d/dt log|g(t w_j)|  =  sum_k  (t - cos theta_{jk}) / (1 - 2 t cos theta_{jk} + t^2),
```

and `P(t, theta) := (t - cos theta)/(1 - 2t cos theta + t^2)` has
`∂P/∂(cos theta) = (t^2-1)/(…)^2 < 0`, so `P` is strictly decreasing in
`cos theta` and `P(t, theta) <= P(t, pi) = 1/(1+t)`.  The term `k = j` is
`-1/(1-t)`.  Hence the derivative is at most `-1/(1-t) + (n-1)/(1+t)`, which is
`<= 0` exactly when `(n-1)(1-t) <= 1+t`, i.e. `t >= (n-2)/n`.  Sharpness: in the
limiting configuration of (i) the profile is `(1-t)(1+t)^{n-1}`, whose maximum
is at `t = (n-2)/n` precisely.  (iv) `(1-t)(1+t)^{n-1}` is decreasing for
`t >= (n-2)/n` and equals `1` at `s_n^*`, so it is `<= 1` on `[s_n^*, 1]`; apply
(i). ∎

Numerically `s_n^* = 0, 0.618034, 0.839287, 0.927562, 0.965948` at
`n = 2,…,6`, and `s_n^* = 1 - 2^{1-n}(1 + o(1))`: writing `s = 1 - delta`, the
defining equation is `delta (2 - delta)^{n-1} = 1`.  (iv) is unconditional but
far too conservative in the hard regime: on the near-Fekete quintic the entry
radii of [TruncatedSpokeReduction.md](TruncatedSpokeReduction.md) §3 are about
`0.03–0.05`, more than an order of magnitude below `s_5^* = 0.9276`.

## 4. The no-go: the two endpoint families do not suffice, even together

Form A-cut is a one-parameter family of paths whose two endpoints are

* `s -> 0`: the two full spokes through the centre, refuted by
  `negative_results` entry 8 and `exact_results::two_safe_origin_spokes_counterexample`;
* `s = |a|`: the root chord, refuted by `negative_results` entries 7 and 37.

§2 of [TruncatedSpokeReduction.md](TruncatedSpokeReduction.md) records both
refutations separately, and §5 of that note observes that no single row of its
witness table is covered by both.  The statement proved here is strictly
stronger in two directions: it refutes the **disjunction** (a configuration is
allowed to use whichever endpoint family it likes, and the chord may join **any**
two zeros, not only adjacent ones), and it does so **inside the concyclic
subfamily**, which is a codimension-`n` slice of the configuration space.

Define, for a configuration `w` on the unit circle,

```text
C'(w) = min(  second smallest_j  max_{[0,w_j]} |g| ,   min_{a<b} max_{[w_a,w_b]} |g|  ).
```

`C'(w) <= 1` says: either two full spokes, or one root chord, is contained in
`{|g| <= 1}` — in each case producing an admissible Erdős #1041 path.  Since
`|g(0)| = 1`, every spoke maximum is at least `1`, so the spoke branch is never
below `1` and `C' <= 1` means the second smallest spoke maximum is exactly `1`.
At the regular `n`-gon `C' = 1` (there `|g(t w_j)| = 1 - t^n`, so every spoke
attains its maximum `1` at the origin), so no constant below `1` is available.

> **Theorem 4 (no-go).**  There are concyclic configurations with `C'(w) > 1`,
> at `n = 3`, `n = 5` and `n = 6`.  Explicit witnesses are exhibited with
> Gaussian-rational zeros and all inequalities decided in exact rational
> arithmetic.

The `n = 5` and `n = 6` witnesses matter more than the `n = 3` one: degrees `2, 3, 4` of
Erdős #1041 are already settled unconditionally
(`exact_results::cubic_minimal_critical_value_short_hub`, and Pendyala's
quartic), so `n = 5` is the first open degree.  In the `n = 6` witness five of the
six spokes are certified to leave the lemniscate, so only one contained spoke
survives there as well.

**Witnesses.**  Zeros are `w_k = ((1 - p_k^2) + 2 p_k i)/(1 + p_k^2)`, which lies
exactly on the unit circle for every rational `p_k`.

```text
n = 3:  p = ( 72/1831,  1424/977,  -1761/1424 )
        spoke 1 : |g(t w_1)|^2 = 1.019760845…  at t = 43/300      > 1
        spoke 2 : |g(t w_2)|^2 = 1.019738553…  at t = 43/300      > 1
        all 3 root chords exceed 1 (weakest certificate 1.031512787…)

n = 5:  p = ( 107/129, 165/64, -5309/1883, -1164/1651, -145/1873 )
        spoke 0 : 1.016537298…  at t = 5/24        > 1
        spoke 1 : 1.003317747…  at t = 2/25        > 1
        spoke 2 : 1.009491768…  at t = 17/50       > 1
        spoke 4 : 1.003384236…  at t = 67/300      > 1
        all 10 root chords exceed 1 (weakest certificate 1.004583071…)

n = 6:  p = ( 65/1281, 379/683, 2095/1331, -53395/1323, -601/339, -955/1489 )
        spoke 0 : 1.002293800…  at t = 41/150      > 1
        spoke 2 : 1.002164241…  at t = 223/600     > 1
        spoke 3 : 1.014686187…  at t = 11/30       > 1
        spoke 4 : 1.002069871…  at t = 3/50        > 1
        spoke 5 : 1.054820338…  at t = 257/600     > 1
        all 15 root chords exceed 1 (weakest certificate 1.002409795…)
```

In each case at most one full spoke is contained, so no admissible pair of
spokes exists, and no root chord is contained.  A certificate is one rational
point at which the exact value of `|g|^2` — a rational number — exceeds `1`; no
maximum has to be computed, and no floating point enters the verdict.

> **Corollary 4.1.**  Any proof of Erdős #1041 for concyclic zeros must place
> the hub at a radius that is both **strictly positive** and **strictly below
> the zero modulus**.  The interior of the Form A-cut parameter range is
> necessary, not merely convenient.

**Where the failures live.**  All three witnesses are perturbations of the
regular `n`-gon, and the deficit is small.  The verifier at its default budget
reaches `C' = 1.00982` at `n = 3`, `1.00166` at `n = 5`, `1.00103` at `n = 6`,
and finds nothing above `1` at `n = 4`, `7`, `8`; a longer search off-line
reached `1.0033` at `n = 5`, `1.0021` at `n = 6` and `1.00062` at `n = 7`, so the
`n = 7` failure is real but needs more budget than the verifier spends, and only
the exactly certified witnesses at `n = 3, 5, 6` are claimed.  Every such number
is a **lower** bound on `sup C'` — hill climbing exhibits a configuration, it
does not bound the supremum — so nothing here proves that the deficit stays
below two per cent.  What the measurements do say is that the endpoint families
fail only inside the near-Fekete shell that
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) identifies.  The two even
degrees `n = 4, 8` are the ones where no failure is found at all, and there the
regular polygon has a second tight branch: its own diameter chord passes through
the centre and attains exactly `1`.  The adversarial searcher is calibrated in
§5.

## 5. Calibration

Verifier
[scripts/check_erdos1041_concyclic_spoke_calculus.py](scripts/check_erdos1041_concyclic_spoke_calculus.py);
receipt `concyclic_spoke_calculus_tao_pipeline_receipt.json`.

**Exact arm, no floats.**  Theorem 1 and Theorem 2 are checked in `Fraction`
arithmetic at Gaussian-rational zeros for `n = 2 … 7` over a grid of exact
rational `t`: zero mismatches.  Theorem 4's witnesses are decided exactly.

**Float arm.**  The power-series form of Theorem 2 agrees with the direct
product to `5.7e-14` at `n = 2 … 8` and `t` up to `0.97` (4000 terms).
Theorem 3(iii) is checked on 3000 random configurations per degree at
`n = 2 … 12` with no violation above `(n-2)/n`, and the sharpness configuration
returns `argmax t = (n-2)/n` to five decimals at every degree.

**Instrument discipline.**  Every maximum on a segment or a spoke is computed
from the exact critical points of a real polynomial — `|g|^2` restricted to a
segment is a real polynomial of degree `2n` in the parameter, and on a spoke it
is the palindromic polynomial of Theorem 1 — never from a sample.  This is the
standard imposed by `negative_results` entries 24, 34, 41, 43–44 and by §6b of
[ConcyclicAlternation.md](ConcyclicAlternation.md).

**Negative control** (required by `negative_results` entry 19).  The same
searcher at the same budget must be able to push a neighbouring **false**
statement across the same threshold.  Against "*every* root chord has
`max |g| <= 1`" it reaches `1.185, 1.687, 2.619, 4.279, 7.206` at `n = 3 … 7` —
clearing the budget `1` by 18 % at `n = 3` and by a factor `7.2` at `n = 7`,
which at `n = 3` is close to that false statement's own supremum, so a weaker
searcher would visibly fall short.  Against the true statement `C' <= 1` the
same searcher stalls within two per cent of `1`.  A first version of the search also *reduced*
its own conjecture — the disjunction with adjacent chords only was refuted at
`n = 3, 5, 6, 7`, and widening to all chords changed nothing at those degrees —
so the refutation is not an artefact of the chord family being too narrow.

## 6. What this leaves

The concyclic case is exactly the statement `V <= 1` for the free-hub
two-segment family: there are zeros `w_a, w_b` and a hub `H` with
`|H - w_a| + |H - w_b| <= 2` and `|g| <= 1` on `[H,w_a] ∪ [H,w_b]`.  Measured,
`V = 1` exactly at the regular `n`-gon for `n = 3,4,5,6`, and `V = 0.947` on the
`n = 3` witness of §4.  Theorem 4 says the two endpoints of that family are not
enough; Theorem 2 says at least one arm always exists at every radius; Theorem
3(iii) says every arm above `(n-2)/n` is monotone, so containment of an arm is
decided by its inner endpoint alone.  What is missing is a rule that selects two
arms and one chord simultaneously.

Two producers this opens:

* **Q1.**  Prove `sup_w C'(w) <= 1 + eps_n` with an explicit `eps_n`.  Even a
  crude explicit `eps_n` settles the concyclic case for every
  `rho <= (1+eps_n)^{-1/n}`, and if `eps_n` were of the size the searcher
  reaches from below (`0.0033` at `n = 5`, `0.0006` at `n = 7`) that would put
  the admissible radius far above the `2^{-1/n}` of
  [ConcyclicAlternation.md](ConcyclicAlternation.md).  Nothing here proves any
  such bound, and the measurements bound `sup C'` only from below.
* **Q2.**  Decide whether the failure set of `C' <= 1` is contained in the
  validity region of the near-Fekete cusp expansion.  §8 of
  [ConcyclicAlternation.md](ConcyclicAlternation.md) rules out a deficit split
  based on the **chord** family because its envelope crosses `1` at a deficit
  that decreases with degree; the spoke family does not have that defect, since
  it attains `1` exactly at the regular `n`-gon.  The split is therefore not
  excluded by that argument — but it is not established here either.

## 7. Priority

No literature claim is made.  Theorem 1 is elementary once stated.  Theorem 2 is
the Taylor expansion of `log g` combined with the discrete orthogonality
`sum_j w_j^m = s_m`; the inequality `prod_{j,k} |1 - t w_j conj(w_k)| <= 1` is a
positive-definiteness statement and may well be classical.  What is asserted as
new to this directory is the combination: the normal form of Theorem 1 and its
Chebyshev-comparison corollary, the exact all-order orbit balance of Theorem 2
in place of the recorded first-order near-Fekete version, the sharp constant
`(n-2)/n` of Theorem 3(iii), and the exactly certified refutation of the
endpoint disjunction inside the concyclic family at the first open degree.
A priority search has not been run.
