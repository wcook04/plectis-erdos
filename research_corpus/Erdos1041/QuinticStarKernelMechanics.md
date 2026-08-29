# Erdős 1041: the model star kernel is a THEOREM — optimal-margin connector at the trace-maximal hub, component census, the exceptional orbit in closed form, and the all-degree extension

Date: 2026-08-29.  Origin: two independent solve subagents (mixed-core and
spine; full reports in session records) + main-loop synthesis; EVERY theorem
below re-verified in the main loop before landing (13 + 10 independent
checks, two instrument corrections during verification), computed claims
re-run independently where stated.  Checker:
`scripts/check_erdos1041_quintic_star_kernel_mechanics.py`.
Companions: `NearFeketeAngularSelectorToolkit.md` (trace selector,
sector–ellipse metric, spine containment), `TwoTierStraightStarSelectorLab.md`
(real-scale selector law and adversarial geography).

Model: `H(w) = w^5 + b_2 w^2 + b_1 w`, `b_1, b_2 in C`, safe set
`{Re H >= 0}`, tracts = the five sectors of `{Re w^5 > 0}` at infinity,
centred on the root directions `u_k = zeta^k`, `zeta = e^{2 pi i/5}`.  This
is the first-order model of the on-circle near-pentagon quintic after the
landed radial reduction; `(R1)`'s first-order content is exactly a
contained two-tract connector here.

## 1. MAIN THEOREM (the star kernel, unconditional and sharp)

Let `D = max_j Re H(c_j) >= 0` over the critical points (nonnegativity is
the trace identity, `NearFeketeAngularSelectorToolkit.md` Theorem B).  Then:

1. there is a critical point `c*` attaining `D` and a SIMPLE arc `gamma`
   through `c*`, running to infinity in TWO DISTINCT TRACTS, with
   `Re H >= D >= 0` on all of `gamma`;
2. for every `lambda > D`, NO arc joins two distinct tracts inside
   `{Re H >= lambda}`.

So `sup_{connectors} min_gamma Re H = D`, attained; the model star kernel
holds for EVERY `(b_1, b_2)` — including the tangent stratum `D = 0`,
where the connector touches `{Re H = 0}` only at the hub and clause 2 says
no better connector exists.  Moreover every critical point satisfies
`|c| <= t_0 = 0.8585936...`, the positive root of `5 t^4 - 2t - 1` (from
`5|c|^4 = |2 b_2 c + b_1| <= 2|c| + 1` on the core `max(|b_1|,|b_2|) = 1`);
measured maximum `0.858593` — saturated.

Proof.  Let `c*` attain `D`, `Z* = H(c*)`, and `R° = {Z* + s : s > 0}`.
Any critical value on `R°` would have real part `> D`, contradicting
maximality — so `R°` is critical-value-free, WITHOUT any genericity
choice.  `H` is proper, hence over the simply connected `R°` the map is a
trivial covering: `H^{-1}(R°)` is exactly five disjoint arcs, each mapped
homeomorphically, each with `Re H = D + s > D` at parameter `s`.  As
`s -> 0+`, exactly `m + 1 >= 2` of the arcs limit to `c*`
(`H(w) - Z* = a (w - c*)^{m+1}(1 + o(1))`, `m = mult >= 1`).  As
`s -> infinity`, `|gamma_i(s)| -> infinity` and
`gamma_i(s)^5 ~ s`, so each arc has a tract direction; for large `s` the
five preimages of `Z* + s` are the five fifth roots of `s` up to `o(1)`,
one per tract, and the arcs are distinct sheets — so the five arcs own the
five tracts bijectively.  In particular the two arcs limiting to `c*` own
DISTINCT tracts; their union with `{c*}` is the required `gamma`.  For
clause 2: `{Re Z >= lambda}` contains no critical value, so
`H^{-1}({Re Z >= lambda})` is five disjoint closed sheets, one tract each.
QED

Degree-general extension (proved, same argument verbatim): for
`H(w) = w^n + sum_{k=1}^{K} b_k w^k` the trace identity
`sum_j H(c_j) = 0` holds EXACTLY when `2K <= n - 1` (the coefficient gap
`e_1 = ... = e_{n-1-K} = 0` covers Newton up to `p_K`; sharp — it fails
already at `n = 6, K = 3`, 20/20 nonzero), and the Main Theorem's proof
never uses `n = 5`.  The self-inversive near-Fekete blow-up keeps exactly
the modes `k < n/2`, i.e. `K = floor((n-1)/2)` — precisely the identity's
range.  Hence THE FIRST-ORDER (R1) CONTAINMENT SELECTOR IS A THEOREM AT
EVERY DEGREE at the model level.  (Machine checks: `n <= 17`, trace
`<= 6e-16` relative, connector arms verified, zero same-tract failures.)
It also explains WHY origin selection had to fail
(`NearFeketeRadialAngularSplit.md` Theorem 7): the origin is a critical
point of the model only when `b_1 = 0`; otherwise the hub must move to a
critical point.

## 2. Component census

Theorem CC.  For polynomial `H` of degree `n` and `t` a regular value of
`u = Re H`: `#components{u > t} = n - #{c : Re H(c) > t}` (with
multiplicity), and `#components{u >= t} = n - #{c : Re H(c) >= t}`.
Proof: each component is unbounded and simply connected (max/min
principle), `H` restricted is a proper branched cover onto a half-plane of
degree = its tract count, Riemann–Hurwitz per component, and a large
regular value counts `n` preimages; the closed case glues `mu + 1` petals
of a level-`t` critical point of multiplicity `mu` across `mu + 1` DISTINCT
open components (two petals in one component would trap a bounded
component of `{u < t}`).  QED  (Main loop: 25/25 flood-fill matches; agent
runs: 300/300 and 45/45 including general complex coefficients.)

Corollaries.  `#components{Re H >= 0} = 5 - #{Re H(c) >= 0} <= 4`: two
tracts ALWAYS share a component (now superseded in strength by the Main
Theorem, which names the component and the level).  On the tangent stratum
the closed safe set is CONNECTED and the four zero-level critical points
form a SPANNING TREE on the five tracts (no-loop lemma: a critical point
on `{u = 0}` cannot have two positive sectors in one component);
the measured stratum tree is `{0-2, 0-4, 1-2, 2-3}` — three adjacent
pairs and one skip pair.

## 3. The origin region, exactly

`Re H(t u_j) = t (t^4 + b_j t + a_j)`, `a_j = Re(b_1 zeta^j)`,
`b_j = Re(b_2 zeta^{2j})`; the full ray is safe iff `a_j >= 0` AND
(`b_j >= 0` OR `256 a_j^3 >= 27 b_j^4`) — the exact semialgebraic form
(discriminant `disc_t(t^4 + bt + a) = 256 a^3 - 27 b^4`), equivalent to
the `kappa = 3/4^{4/3}` form in the toolkit note.  Let `J` = safe index
set.  Proved: `#J >= 2` on both pure faces and on the dominance cone
`|b_2| <= 0.7272870 |b_1|^{3/4}` (toolkit E1/E2); `#J <= 3` always (a
closed half-circle holds at most three of five `72°`-spaced points).
Computed: `#J` histogram over 50,000 random core points
`[63, 6328, 29420, 14189, 0, 0]`; origin closes `87.2%` of the core
(two independent implementations, and `0.235%` of the core has NO safe
ray).

## 4. Arm normal form, tail, and the C+ window

At a critical point `c`, with `xi = c/u`, `delta = Re H(c)`:
`Re H(c + tau u) = tau^5 + A_4 tau^4 + A_3 tau^3 + A_2 tau^2 + delta`,
`A_4 = 5 Re xi`, `A_3 = 10 Re xi^2`, `A_2 = 10 Re xi^3 + Re(b_2 u^2)` —
NO linear term (`Re(u H'(c)) = 0`): critical-hub straight arms are
quintics-without-linear-term, a decidable Sturm/Bernstein object.
Sufficient inequalities (exact constants): with `A_4, A_3 >= 0`, the arm
is safe if `delta >= K ((A_2)_-)^{5/3}`, `K = 3 * 2^{2/3}/5^{5/3}
= 0.32573011...`, or if `C_2 A_3^{1/3} delta^{7/15} >= (A_2)_-`,
`C_2 = 5^{1/5} 3^{1/3} (15/7)^{7/15} = 2.8398665...`.  C+ WINDOW: for
`arg c` in the middle `[27°, 45°]` of its sector, both bracketing arms
have `A_4 > 0`, `A_3 >= 0` and the metric gain automatically — the
bisector direction `36°` is the window centre (why the bisector hub
family below works).  Tail lemma (explicit): for `|h| <= R_h`, arms are
unconditionally safe beyond `tau_0(R_h)`; certified pairs
`(0.87, 3.67)`, `(1.2, 4.95)`, `(1.5, 6.20)` — certificates only ever
check a compact segment.

## 5. The excess budget (the exact metric side)

For an arm `alpha` from hub `h` to tract `i`:
`e(alpha) = integral_alpha (|dgamma| - <dgamma, u_i>) - <h, u_i>`
(nonnegative integrand), and the transferred path length is
`2 + rho (e_i + e_j) + o(rho)`.  The metric condition is EXACTLY
`e_i + e_j <= 0`.  Straight rays: `e_i + e_j = -Re(h conj(u_i + u_j))` — a
hub buys a curvature budget, the origin has budget zero (its arms must be
straight), the ten pair directions are `36°`-spaced so about half the
pairs are admissible for any hub direction, and SKIP pairs are genuinely
needed (§6).  Hub-shift lemma (quantitative desingularisation): a
zero-level double contact of an arm with `{Re H = 0}` has normal `+- iu`;
if all contacts on both arms share the sign, a hub shift of size `s`
restores strict positivity at linear rate `|H'(w_k)|`, tail safe by §4.

## 6. The exceptional (tangent) orbit — closed form, two independent derivations

The tangent stratum `{D = 0}` is EXACTLY ONE gauge orbit.  Derivation A
(direct): `5 arg b_1 == pi`, `arg(b_1^2/b_2) == +- pi/2`,
`320 |b_1|^3 = 27 |b_2|^4`; representative
`b_1 = (3/4) 5^{-1/3} e^{i pi/5}` (`|b_1|^3 = 27/320` exactly),
`b_2 = e^{9 i pi/10}`.  Derivation B (via the critical-value quartic
`R(Y) = Y^4 + (18 b_1 b_2^2/25) Y^2 - (4 b_2 (400 b_1^3 - 27 b_2^4)/3125) Y
+ b_1^2 (256 b_1^3 - 27 b_2^4)/3125`): tangency forces `b_1 b_2^2 in R`,
`b_1^5 in R` (the toolkit's Theorem D, now with the twist PINNED:
`psi == pi/2 mod pi`), then reality of all four critical values of the
real form forces `320 A^3 + 27 B^4 = 0`, `A < 0` — the same orbit.  The
discriminant factors as `disc_Y R_real = 256 (80A^3 - 27B^4)^3
(320A^3 + 27B^4)^2 / 5^{18}...` — the stratum is the squared factor.
Main-loop verification: tangency to `1e-41` at 40 dps; global minimisation
of `D` over the compact family finds exactly these zeros
(292/1200 descents, all within `2e-6` of the orbit).

Anti-real normal form: `H(w) = -i G(e^{-3 i pi/10} w)` up to gauge, with
`G` REAL; scaled: `G_0(V) = V^5 + 40 V^2 - 60 V`, safe set
`{Im G_0 <= 0}`, `G_0' = 5 (V^2 + 2V - 2)(V^2 - 2V + 6)`, critical points
`-1 +- sqrt 3`, `1 +- i sqrt 5`, critical values `144 -+ 96 sqrt 3` and
`-144` (double) — ALL REAL (i.e. all `Re H(c) = 0`), sum zero.  This is
exactly the corpus's `QuinticEqualityTetrahedron.md` equality chart
(`u_*^3 = 27/320`); its first-order stability analysis applies here.

Two explicit certificates at the orbit (both main-loop verified):
(i) Main-Theorem arms at the real hub `V_0 = -1 - sqrt 3`: the preimage of
the downward vertical value ray `G_0(V_0) - i s` leaves `V_0` at exactly
`+-45°` and runs to the tracts at `126°` and `198°` (adjacent), with
`Im G_0 = -s <= 0` — verified over `s in [1e-8, 1e6]`, worst
`Im = -1e-8`, exit angles `126.03°, 197.90°`.
(ii) the zero-level saddle hub `c* = 0.12581717 + 0.17317248 i`
(`arg = 54°`, `|c*| = 40^{-1/3}(sqrt 3 - 1)`) with the SKIP pair
`(u_1, u_4)`: straight-arm cubic minima `0.645433` and `0.941146`, metric
budget `Re(c* conj(u_1 + u_4)) = 0.0777592874 > 0`.
Metric budget at all four stratum hubs (curved Main-Theorem arms
included): excess `e_i + e_j in [0.041, 0.323]` against slack
`in [0.078, 1.229]`, clearance factors `1.9x`–`5.0x` — the metric side
clears at the stratum with the measured margins.

## 7. Computed coverage, margins, and certification recipes

(All COMPUTED; instruments stated; independently reproduced in the main
loop where noted.)  Region `O` (origin): `87.2%`.  `O u C+` (bracketing
straight stars at strictly positive critical hubs): `94.65%`; the
residual is entirely `b_2`-dominant (`|b_2| >= 0.9167`), NOT
near-tangent.  BISECTOR HUB FAMILY `h = r e^{i pi (2k+1)/5}`, pair
`{k, k+1}`, one real parameter: closes the whole residual;
`O u B = 100.000%` of 50,000 random core points (main-loop independent
re-run: 400/400).  `D` over the compact family: min `9.1e-4` (nearest
grid point to the orbit), median `0.45`; `D` vanishes LINEARLY in the
distance to the orbit (`D >~ 0.30 dist` in the `(A, psi)` chart) — a
transversal conical zero.  Certification recipes: (a) closed-form
interval/Bernstein certificates for O and B (every arm coefficient is
`const + R cos(theta + const)`; prototype: zero over-claims in 8,000
tests, `~1e6` box tests estimated for the full core, directed rounding
owed); (b) the cheaper recipe: ONE box around the orbit (where the
`QuinticEqualityTetrahedron` stability plus certificate (ii) apply) and
`D >= 0.30 dist` outside it.

## 8. Consistency with the corpus's exact rational witness

The `n = 5` origin-refutation witness (`NearFeketeRadialAngularSplit.md`
Theorem 7) sits at `(b_1, b_2) = (0.271738, 1)` (three independent
computations agree), `psi = 0` — real-spine but NOT tangent:
`D = 0.132267 > 0`, exactly one safe origin ray (matching its "at most
one contained spoke"), `F_+ = 4`, rescue hub at the trace-maximal
critical point (`|c| = 0.6844` model / `0.172` actual, the same hub the
real-scale lab certifies with containment margin `2.2e-4`).  Honest
caveat: the witness's dropped third mode has `|b_3| rho^{-2} = 0.25`, so
the two-mode model is a leading approximation there, not an identity.

## 9. Claim boundary

PROVED (main-loop verified, two agents cross-agreeing where both
derived): the Main Theorem with sharpness and the hub bound `t_0`; the
degree-general trace identity with its exact range `2K <= n - 1` and the
all-degree model selector; Theorem CC and the census corollaries
(spanning tree included); the exact origin region with `#J <= 3`; the arm
normal form, the two C+ inequalities, the C+ window, the tail lemma; the
excess identity and hub-shift lemma; the exceptional orbit's closed form,
its anti-real normal form and exact critical data.  COMPUTED: coverage
fractions, the `O u B` law, `D`-margins and the linear vanishing rate,
certificate prototypes, the stratum metric-budget table, and the two
orbit certificates' numerics (50 dps / 45 dps; the orbit data is closed
form, so exact-rational upgrades are mechanical).  NOT claimed: novelty
(the trace identity and the maximal-value/horizontal-ray construction may
be classical — assume so until searched); the parent theorem; (R1) at
REAL scale — the model decides the first order only, the `D <~ rho`
ball around the orbit needs the next order (one-box recipe above), and
real-scale behaviour of straight mechanisms is measured separately in
`TwoTierStraightStarSelectorLab.md` (its third adversarial round is the
live demonstration that model margins alone do not survive the gon limit
at real scale — the remainder budget must be carried).
