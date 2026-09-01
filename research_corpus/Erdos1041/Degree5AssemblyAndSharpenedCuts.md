# Erdős 1041 at degree 5: assembly map, two sharpened cuts, and the exact residual

Date: 2026-08-29.  Origin: degree-5 assembly subagent (full report in session
records), decisive derivations re-verified in the main loop.  Checker:
`scripts/check_erdos1041_degree5_sharpened_cuts.py`.

Degree 5 is NOT closed here.  What this note lands: (i) a sharpened two-spoke
threshold (11x over the corpus row, all degrees), (ii) the Grönwall area
identity as a theorem replacing Pólya at the terminal component, (iii) the
certified coverage/residual map at n = 5, (iv) the exact degree-5-only
statement (SPOKE-5) whose proof would finish the degree.

## Lemma S5 (sharpened second-spoke threshold; all degrees)

Let `f` be monic of degree `n` with roots in the closed unit disk and `c` a
critical point with `f(c) != 0`; order the roots by distance `d_1 <= ... <=
d_n` from `c`.  Set `x_k = (a_2 - c)/(a_k - c)` (so `Sigma_k x_k = 0` by
`f'(c) = 0`, `x_2 = 1`, `|x_1| <= n-1`, `|x_k| <= 1` for `k >= 2`) and
`y_k = 1 - Re x_k` (`Sigma y_k = n`, `y_2 = 0`, `y_k in [0,2]` for `k >= 3`,
hence `y_1 >= 4 - n`).  Along the second-nearest spoke `z(t) = c + t(a_2-c)`:

```text
|f(z(t))/f(c)|^2 = prod_k |1 - t x_k|^2,
|1 - t x_k|^2   = (1-t)^2 + 2 t y_k + t^2 (|x_k|^2 - 1),
```

and maximising: monotonicity in `|x_1|` at fixed `y_1` gives
`B_1(y_1) = (1-t)^2 + 2t y_1 + t^2 n(n-2)`, AM-GM over `k >= 3` gives
`B_2(y_1)^{n-2}`, `B_2 = (1-t)^2 + 2t(n-y_1)/(n-2)`, so

```text
|f(z(t))/f(c)|^2  <=  E(t) := max_{y_1 in [4-n, n]} (1-t)^2 B_1(y_1) B_2(y_1)^{n-2}.
```

In `y_1` the product is quasi-CONCAVE (log-derivative `2t/B_1 - 2t/B_2`
changes sign once, from positive to negative), so the inner maximum is at the
INTERIOR stationary point `y_1* = (n - t n(n-2)^2/2)/(n-1)` where
`B_1 = B_2 =: B(t) = (1-t)^2 + (2tn + t^2 n(n-2))/(n-1)`, CLAMPED to the
endpoint `y_1 = 4-n` when `y_1* < 4-n`, which happens exactly for
`t >= t_c(n) = 2/n`.  Hence

```text
sqrt(E(t)) = (1-t) B(t)^{(n-1)/2}          for t <= t_c(n)   (interior branch),
sqrt(E(t)) = Phi_n(t)
           = (1-t)(1+t)^{n-2} sqrt(1+(6-2n)t+(n-1)^2 t^2)
                                            for t >= t_c(n)   (clamped branch),
M_n := max_{t in [0,1]} sqrt(E(t)).
```

For `n >= 4` the global maximum sits on the clamped branch, so
`M_n = max_t Phi_n(t)` (numerically verified per degree: the interior branch
tops out at `1.6875` (n=4) and `2.3050` (n=5) against `Phi`-maxima `1.7895`
and `3.6226`).  For `n = 3` the interior branch rules
(`Phi_3` on `[2/3, 1]` stays below `0.93`) and the maximum is EXACT
RATIONAL: `g(t) = (1-t)(1 + t + 5t^2/2)` has `g' = 3t(1 - 5t/2)`, so
`t* = 2/5` and `M_3 = g(2/5) = 27/25`, threshold `1/M_3 = 25/27 =
0.9259259...` — correcting the subagent's `n = 3` row (`0.9295`; its
`y_1`-endpoint step had the concavity backwards; caught by this session's
checker at sample excess `1.5e-3`, exactly the `n = 3` gap).  All rows
`n >= 4`, including the headline `M_5` and `t*`, are unaffected.

At `n = 5`: `Phi_5(t) = (1-t)(1+t)^3 sqrt(16t^2 - 4t + 1)`, the maximiser is
the root of `40t^2 - 25t - 2`, i.e. `t* = 5/16 + 3 sqrt(105)/80 =
0.6967606537...`, and `M_5 = 3.6225832464...` (`M_5^2` is a root of
`655360000000000 X^2 - 9259803797146875 X + 8653940464249899`).

> **Theorem.** If some critical point has `|f(c)| <= 1/M_n`, then both
> straight segments from `c` to its two nearest roots lie in `{|f| <= 1}`,
> and their total length is `<= 2` by `GlobalCriticalTwoNearestBudget.md`.
> Erdős 1041 holds for `f`.

Nearest-spoke leg: the same machinery relative to the NEAREST root
(`x_k = (a_1-c)/(a_k-c)`, now `|x_k| <= 1` for ALL `k`, `y_1 = 0`,
`Sigma_{k>=2} y_k = n`) gives its own envelope
`N_n = max_t (1-t)[(1-t)^2 + 2tn/(n-1)]^{(n-1)/2}`, with `N_3 = 1` exactly
(`(1-t)(1+t+t^2) = 1-t^3`) and `N_n <= M_n` (verified per degree in the
checker), so BOTH spoke suprema are `<= M_n |f(c)|`.  NOTE (finding): the
POINTWISE nearest-spoke contraction `|f| <= |f(c)|` along `[c, a_1]` is
FALSE for general critical points (sampled excess `1.5e-3`, n >= 4; `N_n >
1` there) — the subagent's citation of the corpus root-ray row for this leg
was a misreading (that row's hypotheses are narrower); the theorem above does
not use it.

Thresholds `1/M_n`: `25/27 = 0.9259259` (n=3, corrected), `0.5588171` (4), **`0.2760461`** (5),
`0.1310548` (6), `0.0622051` (7), `0.0297483` (8), `0.0143372` (9),
`0.0069548` (10) — improving the corpus's deep-low row
(`LowCriticalTwoRootReduction20260826.md`: `1/(n 2^{n-2})`, e.g. `1/40` at
`n = 5`) by factors `5.6x` to `17.8x`.  Evidence class: analytic derivation
(main-loop verified) + exact symbolic maximisation; 120k-sample numeric
verification with zero envelope violations; the interior `t`-`y_1` corner
analysis grid-confirmed, not interval-certified.  The envelope is ~2x lossy:
adversarial search reaches `1.8491`, so the optimal constant lies in
`[0.2760, 0.5408]`.

## Grönwall area identity (terminal component; replaces Pólya there)

For `K_t = {|f| <= t}` CONNECTED, `cap(K_t) = t^{1/n}` exactly, and the
exterior Riemann map `psi(zeta) = t^{1/n} zeta + a_0 + Sigma_{k>=1} a_k
zeta^{-k}` is the inverse near infinity of `(f/t)^{1/n}`, so Grönwall's area
theorem is an identity:

```text
Area(K_t) = pi ( t^{2/n} - Sigma_{k>=1} k |a_k|^2 ),
```

with the `a_k` explicit polynomials in the coefficients; after centring
(`Sigma roots = 0`), `a_0 = 0` and `a_1 = -c_{n-2}/(n t^{1/n})` exactly
(`c_{n-2}` the degree-`(n-2)` coefficient), giving the rigorous truncation

```text
Area(K_t)/ (pi t^{2/n})  <=  1 - |c_{n-2}|^2 / (n^2 t^{4/n}).
```

The corpus used `Area <= pi cap^2` (Pólya) at the terminal merge node
(`MergeTreeDiscriminantDichotomy.md` `Theta_{n,n} = tanh(1)^{n/2}`) and named
the area step as a loss (`UnconditionalConstantFactorBound.md` §names it);
the identity turns the terminal threshold into
`tanh(1/alpha)^{n/2}` with `alpha` the certified area deficit — measured on
the degree-5 residual: median effective threshold `0.674` instead of
`0.506`, newly covering `16.4%` of the residual.  Verified: series vs
grid-measured area to 3-4 decimals on three configs; the `a_1` formula to
machine precision.  Evidence: classical function theory applied where the
corpus had only a measurement gate; no novelty claim.

## Certified coverage map and the exact degree-5 residual

With every named theorem's hypothesis implemented honestly (window join
`x_5* = 1.4289343`, merge dichotomy `Theta_{5,k} = 0.9404/0.8341/0.6826/
0.5062`, Blaschke pair, first-two-critical Bergman, quartic-core, concyclic,
collinear, sparse families, Lemma S5, quintic near-Fekete atlas `NF5`),
sampling MEC-normalised quintics:

- generic families (uniform/boundary/circle): named coverage `100%`;
- near-pentagon shell and the `HubModuliReduction` beta-chart: named coverage
  `13%` and `12%` — the uncovered region is exactly RAPID NEARLY-SIMULTANEOUS
  MERGING NEAR THE REGULAR PENTAGON (`beta_1 > 0.276` after S5, every merge
  ratio above its `Theta`, `D` median `0.986`);
- merge-chain arithmetic: failure of every node forces `beta_1 > 0.2710`
  (worst chain `2->3->4->5`), and `D <= 1` NEVER contradicts the dichotomy's
  `D > prod Theta^{k-1} > 0.0137` — the dichotomy provably cannot close
  degree 5 alone;
- in the residual: `min_c L(c)` max `1.9858` (never above 2); the carrier is
  straight spokes at a critical hub (`104/105` of residual configs), NOT
  descent arcs and NOT chords; the winning hub is the argmin `100/120` times
  but loses by up to `30%` when it loses.

## (SPOKE-5): the exact degree-5-only missing statement

> For every monic quintic with roots in the closed unit disk there is a
> critical point `c` with `|f(c)| <= 1` and two roots `a, b` with
> `|f| <= 1` on `[c,a] u [c,b]` and `|c-a| + |c-b| <= 2`.

By `TwoSegmentContainmentReduction.md` + `GenericSufficiencyClosure.md`
Corollary S this implies Erdős 1041 at `n = 5`.  It is genuinely
degree-specific: FALSE at degrees 6 and 9 (`StraightSpokeHubCriterionLab.md`
witnesses).  Adversarial search in the beta-chart pins its two functionals at
`0.9999997708` and `1.9975399` (both `<=` their budgets, maximised at
`z^5 - 1`), with a methodological control: the same searcher pushed the
known-false origin-spoke family ABOVE `1` in the same run.  This is the
recommended finite-certificate target for closing degree 5 (compact
4-real-parameter families after the session's reduction machinery).

Highest-leverage missing ingredient (would shrink the residual band `58x`):
a two-root component area bound `Area(U) <= A* pi t^{2/5}` with
`A* < (1/4)^{2/5} = 0.5743`; measured max `0.482` overall and `0.264` in the
decisive band `beta_1/t >= 0.99`.  The Grönwall identity above is the natural
route (extend to proper components via the exterior Blaschke factor).

## ADDENDUM (2026-08-29, same day, solve session): (SPOKE-5) fails in the
## rotated-gon pocket; the certificate target redirects to (CUT-5)

The recommendation above is superseded in one respect.  At the exact
on-circle configuration `a_k = exp(i(2 pi k/5 + delta_k))`,
`delta = (0.0689, 0.06052, 0.0681, 0.06473, 0.06125)` (exact rationals),
the 35-dps adjudication in `TwoTierStraightStarSelectorLab.md` (checker
instrument 5b) gives: two critical points admissible
(`|f(c)| = 0.999882188, 0.999886801`), and the MINIMUM over admissible hubs
and all root pairs with `|c-a|+|c-b| <= 2` of `sup |f|` on the two straight
segments is `1.000085364` — every critical-hub straight star escapes.  So
(SPOKE-5) AS STATED IS VIOLATED at degree 5 as well (evidence class:
high-precision numerics on exact rational input; not an interval
certificate); the adversarial pin quoted above (`0.9999997708`) searched
the beta-chart around `z^5 - 1` and did not reach this pocket.  The same
configuration IS closed by the Form A-cut (`sup |f| = 0.999886911` at pair
`(2,4)`, truncations `0.35`), by a free-hub star (`sup = 0.9999668` at
`h = 0.95 c`), and by descent arms (`min_c L(c) = 1.7885`).  The
recommended finite-certificate targets for closing degree 5 are, in order
(third adversarial round, same session: radial-truncation cuts ALSO fail at
two deeper gon-limit corners, `sup |f| = 1.0000067/1.0000084`, while
descent arms close with `min_c L(c) = 1.8307/1.8334` and free-hub stars
close thinly): (i) the DESCENT-ARM bound `min_c L(c) <= 2` — the canonical
FRONTIER carrier, with the biggest measured margins in the pocket — and the
free-hub two-segment family (`TwoSegmentContainmentReduction.md`);
(ii) (CUT-5), the Form A-cut family of `TruncatedSpokeReduction.md`
(length-free, parent-wired, atlas-aligned) on the bulk, carried at real
scale by the exact remainder budget (`FormACutQuantitativeExpansion.md`
(S)), not by model margins alone.  Lemma S5, the Grönwall identity, and
the coverage machinery above are unaffected.

## Claim boundary

Lemma S5 and the Grönwall identity: proved (with the stated grid-vs-interval
caveat on S5's corner analysis).  Coverage fractions, residual geometry,
`(SPOKE-5)` pins: computational (calibrated instrument; three digit-for-digit
corpus cross-checks recorded in the session).  `(SPOKE-5)` itself is
VIOLATED at an explicit on-circle pocket configuration — see the addendum
above; the degree-5 certificate target is now (CUT-5).  Degree 5 remains
OPEN; nothing here is a parent proof.  The degree-5 argmin-arm refutation
upgrade extracted from the same session is landed separately in
`MinimalHubArmBudgetRefutation.md` Addendum 2.
