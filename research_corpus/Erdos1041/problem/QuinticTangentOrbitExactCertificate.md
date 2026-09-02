# Erdős 1041: the tangent-orbit skip-pair certificate is now EXACT — elementary positivity proof, exact metric budget, and the quantified stability margin for the one-box recipe

Date: 2026-08-30.  Origin: main-loop proof (this session), independently
re-verified by a subagent (exact algebra + frame identification).
Checker: `scripts/check_erdos1041_tangent_orbit_exact_certificate.py`.

## What this upgrades

`QuinticStarKernelMechanics.md` §6 classifies the quintic tangent
stratum `{D = 0}` as ONE gauge orbit and records two connector
certificates there; its claim boundary files both certificates' numerics
as COMPUTED ("50 dps / 45 dps; the orbit data is closed form, so
exact-rational upgrades are mechanical"), and the actual instrument for
certificate (ii) samples a float64 grid
(`check_erdos1041_quintic_star_kernel_mechanics.py`, `tau` linspace with
`complex(...)` casts).  This note performs the exact-rational upgrade for
certificate (ii) — the zero-level saddle hub with the SKIP pair — turning
containment AND metric budget into ordinary proved mathematics with
explicit margins.  It is the "one box around the orbit" seed of the
recipe in `QuinticStarKernelMechanics.md` §7(b), and it serves the
capture `cap_quick_exact_certificate_upgrade... / exact rational
upgrades of orbit certificates` lane.

## Frame (and a sign flag on the landed text)

Anti-real normal form: `H(w) = w^5 + b_2 w^2 + b_1 w` at the orbit
representative equals, under `w = lambda V` with
`lambda = 40^{-1/3} e^{3 i pi/10}`,

```text
H(lambda V) = lambda^5 G_0(V),   lambda^5 = -i 40^{-5/3},
G_0(V) = V^5 + 40 V^2 - 60 V   (real coefficients),
```

so `Re H = 40^{-5/3} Im G_0` and the safe set is

```text
{Re H >= 0} = {Im G_0 >= 0},
```

with tract centres in `V` at `18° + 72° k`.  FLAG (machine-decided):
`QuinticStarKernelMechanics.md:163` states the safe set as
`{Im G_0 <= 0}` — a SIGN SLIP.  The note's own orbit representative
(`b_1 = (3/4)5^{-1/3} e^{i pi/5}`, `b_2 = e^{9 i pi/10}`) is reproduced
exactly by `H(w) = -i G(e^{-3 i pi/10} w)` (monic `[w^5] = 1`, all three
orbit invariants), which forces `{Re H >= 0} = {Im G_0 >= 0}`; the
alternative `H = +iG` fails monicity and the representative.  Its
certificate (i) (downward value ray `G_0(V_0) - i s`, exits
`126°/198°`) is stated in the MIRROR gauge (conjugation, legitimate
since `G_0` is real); re-run in the primary frame it uses the upward
ray `G_0(V_0) + i s` and exits at `233.97°/162.10°` — the adjacent
tracts `u_4, u_3`.  Certificate (ii)'s hub
`c* = 40^{-1/3}(sqrt 3 - 1) e^{i 54°} = lambda (sqrt 3 - 1)` and skip
pair live in the primary gauge: under the tract map
`u_k <-> arg V = 72k - 54°`, `u_1 -> 18°` and `u_4 -> 234°` — EXACTLY
the ray directions used below.  Both certificates are individually
true, each in its own gauge.

## Theorem (exact skip-pair certificate at the tangent orbit)

Let `a = sqrt 3 - 1` (a critical point of `G_0`:
`G_0' = 5 (V^2 + 2V - 2)(V^2 - 2V + 6)`, critical points
`-1 +- sqrt 3`, `1 +- i sqrt 5`, critical values `144 -+ 96 sqrt 3`,
`-144` (double) — all real, sum zero, so the stratum is trace-tangent).
Set

```text
v_+ = e^{i pi/10},    v_- = e^{13 i pi/10}.
```

Then for every `t >= 0`:

```text
Im G_0(a + t v_+) = t^2 P_+(t) >= 0,
Im G_0(a + t v_-) = t^2 P_-(t) >= 0,
```

with equality only at `t = 0`, where (exactly, by the quintic Taylor
expansion at `a`, using `a^2 = 2 - 2a`)

```text
P_+(t) = 60 a sin 36° + 20(1-a) sin 54° t + 5 a sin 72° t^2 + t^3,
P_-(t) = 60 a sin 72° - 20(1-a) sin 18° t - 5 a sin 36° t^2 + t^3.
```

Hence the two straight rays `a + [0, oo) v_+`, `a + [0, oo) v_-` lie in
the safe set `{Im G_0 >= 0}`, meet only at the critical hub `a`, and run
to two DISTINCT tracts two steps apart (centres `18°` and `234°`) — the
skip pair.  Their combined renormalised excess is exactly

```text
e_+ + e_- = -a (sin 72° - sin 36°) = -0.265933022... < 0,
```

and in the `w`-frame (multiply by `|lambda| = 40^{-1/3}`)

```text
40^{-1/3} a (sin 72° - sin 36°) = 2 cos 72° Re(c*) = 0.0777592874...,
```

recovering the landed metric budget `Re(c* conj(u_1 + u_4))` EXACTLY,
via the identity `2 cos 72° cos 54° = sin 72° - sin 36°`.

## Proof

**Expansion.**  `G_0'(a) = 0` and `a^2 = 2 - 2a` give `a^3 = 6a - 4`,
so `G_0''(a)/2 = 10a^3 + 40 = 60a`, `G_0'''(a)/6 = 10a^2 = 20(1-a)`,
`G_0''''(a)/24 = 5a`; the degree-5 Taylor expansion at `a` is exact and
`G_0(a)` is real, so `Im G_0(a + tv) = t^2 [60a Im(v^2) +
20(1-a) t Im(v^3) + 5a t^2 Im(v^4) + t^3 Im(v^5)]`.  For `v_+`:
`Im(v_+^2, v_+^3, v_+^4, v_+^5) = (sin 36°, sin 54°, sin 72°, 1)`.  For
`v_-`: `v_-^2 = e^{3 i pi/5}`, `v_-^3 = e^{-i pi/10}`,
`v_-^4 = e^{6 i pi/5}`, `v_-^5 = i`, giving
`(sin 72°, -sin 18°, -sin 36°, 1)`.  (Checker section 2, sympy-exact.)

**Positivity of `P_+`.**  All four coefficients are positive
(`0 < a < 1`).

**Positivity of `P_-`, exact — two independent certificates.**

(I) Rational minorant + exact Sturm.  Certify the rational bounds

```text
183/250 < a < 733/1000,   sin 18° < 31/100,
sin 36° < 147/250,        sin 72° > 951/1000
```

by exact squaring (e.g. `a < 733/1000  <=>  3 < (1733/1000)^2`; checker
section 3c does all five).  Termwise, for `t >= 0`,

```text
P_-(t) >= R(t) := t^3 - A t^2 - B t + C,
A = 5 (733/1000)(147/250),  B = 20 (1 - 183/250)(31/100),
C = 60 (183/250)(951/1000),
```

a RATIONAL cubic.  Exact Sturm (sympy `real_roots`) shows `R` has no
root in `[0, oo)` and `R(0) = 41.7679... > 0`; hence `R > 0` on
`[0, oo)` and `P_- >= R > 0`.  Human-checkable branch form (subagent's
sharper constants, also certified): with `|c_2| <= 54/25`,
`|c_1| <= 5/3`, `c_0 >= 41`: on `[0, 3]`, `P_- >= 41 - (54/25)9 -
(5/3)3 = 414/25 > 0`; on `[3, oo)`, `t^3 - (54/25)t^2 >= (21/25)t^2`,
and `(21/25)t^2 - (5/3)t + 41` has discriminant `-30371/225 < 0`.

(II) Discriminant.  The exact discriminant of `P_-` is

```text
Delta = 52750 + 27150 sqrt5 - 47250 sqrt3 - 19200 sqrt15
      = -42741.435315... < 0
```

(minimal polynomial `x^4 - 211000 x^3 - 15130425000 x^2 -
185156387500000 x - 85604540468750000`, `Delta` its least real root;
rigorous interval enclosure).  A monic real cubic with `Delta < 0` has
exactly one real root `r`; `P_-(0) = 60 a sin 72° > 0` forces `r < 0`
(numerically `r = -3.00986276...`), so `P_- > 0` on `[0, oo)`.

**Distinct tracts.**  `Im(v_+^5) = Im(v_-^5) = 1 > 0`, so both
directions are tract centres of `{Im G_0 > 0}`; `18°` and `234°` differ
by `3 x 72°`, i.e. two steps the short way — distinct, non-adjacent
(skip).

**Excess.**  Straight rays from hub `a` (real):
`e_+ + e_- = -Re(a (conj v_+ + conj v_-)) = -a (cos 18° + cos 234°)
= -a (sin 72° - sin 36°)`, negative.  Closed forms:
`a (sin 72° - sin 36°) = (sqrt 3 - 1) sqrt(5 - 2 sqrt 5)/2
= 0.2659330221797290...`; in the `w`-frame,

```text
40^{-1/3} a (sin 72° - sin 36°)
   = 5^{2/3} (sqrt 3 - 1)(sqrt 5 - 1) sqrt(10 - 2 sqrt 5) / 80
   = 0.0777592874030083...
```

(minimal polynomial of the unscaled excess:
`16 x^8 - 320 x^6 + 680 x^4 - 400 x^2 + 25`), so the LANDED figure
`0.0777592874` is exactly the correct rounding.  The `w`-frame identity
`2 cos 72° cos 54° = cos 126° + cos 18° = sin 72° - sin 36°` converts it
to `-2 cos 72° Re(c*)`, matching `QuinticStarKernelMechanics.md` §6(ii).
The landed "straight-arm cubic minima `0.645433` and `0.941146`" are the
core-frame profiles `Q_v(tau) = P_v(40^{1/3} tau)/40`:
`min Q_+ = Q_+(0) = 3 sqrt(5 - sqrt 5)(sqrt 6 - sqrt 2)/8 =
0.6454330029...` and `min Q_- = 0.9411462787...` (at
`tau = 0.5116...`), both exact.  QED

## Stability margin (the R5 data for the one-box recipe)

The certificate survives perturbation with quantified room:

```text
m_- := inf_{t >= 0} P_-(t)/(1+t)^3 = 0.484681094562... > 12/25,
      attained at t_m = 5.06184... (the unique positive root of
      P_-'(t)(1+t) - 3 P_-(t));
m_+ := inf_{t >= 0} P_+(t)/(1+t)^3 = 1  EXACTLY (infimum at infinity,
      not attained): P_+(t) - (1+t)^3 has all three lower coefficients
      positive (exact: 5 a sin72° - 3, 20(1-a) sin54° - 3,
      60 a sin36° - 1 > 0), so P_+ > (1+t)^3 for every t >= 0.
```

Perturbation chain (subagent-verified): write `g_k = G_0^{(k)}(a)/k!`
(`g_2 = 60a`, `g_3 = 20(1-a)`, `g_4 = 5a`, `g_5 = 1`), and for a nearby
monic quintic `G~` with continued critical hub `a~` set
`delta := max_{k=2,3,4} |G~^{(k)}(a~)/k! - g_k|`.  Using
`t^2 + t^3 + t^4 = t^2(1 + t + t^2) <= t^2 (1+t)^3`:

```text
Im G~(a~ + t v) >= Im G~(a~) + t^2 (1+t)^3 (m_v - delta),
```

so `Im G~(a~) >= 0` and `delta < m_- = 0.4846...` keep BOTH rays
strictly safe.  For the coefficient family `G~ = V^5 + beta V^2 +
alpha V` with hub displacement `|a~ - a| <= eta`: binding Lipschitz
constant `30 a^2 = 16.0769...`, giving the explicit box
`eta < 0.028984...` (at `beta = 40`) or `|beta - 40| < 0.4846...` (at
`eta = 0`).  This is exactly the curvature/jet data
`ReciprocalNewtonExpansion.md` R5 demands a transfer-facing certificate
to carry: a cubic profile minorant with explicit positive floor, not a
bare sign.  Combined with the landed conical bound `D >= 0.30 dist`
outside the orbit ball (`QuinticStarKernelMechanics.md` §7), this note
is the missing exact half of the "ONE box around the orbit"
certification recipe.

## Claim boundary

Ordinary proved mathematics (sympy-exact algebra; exact Sturm on a
rational minorant; exact-squaring bounds; the containment grid and
stability infima are 30-dps numerics ON TOP of the exact proof, not its
basis).  Scope: the single tangent-orbit representative in its exact
normal form, plus the quantified perturbation margin above — NOT a
finite neighbourhood theorem by itself (the neighbourhood needs the
`D >= 0.30 dist` complement and the real-scale remainder, which remain
as captured), NOT the parent theorem.  The statement was landed as
certificate (ii) with computed evidence; the contribution here is the
evidence-class upgrade to exact, the gauge repair flag, and the explicit
stability floor.  PRIORITY CAVEAT: no literature search; claim "new to
this directory" only.
