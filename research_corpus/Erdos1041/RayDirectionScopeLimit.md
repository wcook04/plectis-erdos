# Erdős 1041: the cone bound is a fact about one HUB, and the hub is free

Status: one exact identity, an independent proof of a theorem proved four hours
earlier by a disjoint route, one closed form, a fixed-hub obstruction with both
of its natural repairs refuted — and, per §6, **a headline that was wrong**, since
the cusp law is free to choose the hub and always has a good one. 2026-08-24.

> **Read §6 first.** This note originally concluded that the turning route is
> closed at every ray direction but `delta = 0`. That is false. Everything
> measured below is correct **for a fixed hub**, and the obstruction disappears
> under the hub minimisation the cusp law already performs. The surviving content
> is §1, §1a, §2, §4, §5, and the fixed-hub failure itself.

**This does not prove Erdős #1041**, and it does not weaken
[ConeBoundMonotoneFunctional.md](ConeBoundMonotoneFunctional.md)'s Theorem C or
Corollary K, both of which stand exactly as stated. What it does is bound their
reach: §7 of that note proposes to extend Theorem C to every descent-ray
direction "given the confinement statement `sign(Im g') = const` for that
direction", and §8 listed that statement as measured. **Confinement is not merely
unproved at a fixed hub — it is false on an explicit arc, with a closed form for
where, and everything downstream of it fails with it.** At that hub the two
obvious repairs — a larger cone, or splitting the branch at its sign changes —
both fail quantitatively (§3a, §3b).

What that does **not** do is close the route, and §6 is the correction. The arc on
which confinement holds has length exactly one hub spacing, so the `n-1` hubs
between them cover every direction; the cusp law minimises over hubs and always
has a good one. `kappa_n(phi) > 0` is proved at every ray direction by that
note's Theorem R. My contribution here is the converse half — the closed form for
where a *given* hub fails — plus §1, §1a, §4 and §5.

Scope, per `ade3b6ac08`: everything here lives on the fixed near-field model
`g(zeta) = zeta^n + n zeta`, one polynomial per degree. Nothing here is a
statement about a perturbed polynomial.

Notation as in [ConeBoundBranchGeometry.md](ConeBoundBranchGeometry.md):
`zeta = r e^{i phi}`, `phi_c = pi/(n-1)`, `zeta_c = e^{i phi_c}`,
`c_n = (n-1) sin phi_c`, `G = zeta^n + zeta`. The branch at ray direction
`delta` solves `g(zeta(s)) = (n-1) zeta_c + s e^{-i delta}`, `s >= 0`;
`delta = 0` is the aligned direction. Per
[NearFeketeCuspPositivityProof.md](NearFeketeCuspPositivityProof.md) §4,
`delta = n phi/(n-1)` for the ray angle `phi` of `zeta^n + n e^{i phi} zeta`, so
every `delta` is realised.

## 1. An independent proof of (★) at `delta = 0`

This route shares nothing with the harmonic functional `Xi = (n-2)zeta - zeta^{2-n}`.
It is recorded because a theorem that lands and is confirmed the same day by a
disjoint mechanism is worth more than either derivation alone, and because the
identity it turns on answers a question `ConeBoundBranchGeometry.md` §7 leaves
open.

Write `A = sin((n-2)phi/2)`, `B = sin(n phi/2)`,
`Sigma = sin((n-1)phi) + (n-1) sin phi`, and

```text
m(zeta) := e^{-i(n-2)phi/2} (zeta^{n-1} + 1) = r^{n-1} e^{i n phi/2} + e^{-i(n-2)phi/2}.
```

Then `Im m = r^{n-1} B - A`, `Re m = r^{n-1} cos(n phi/2) + cos((n-2)phi/2)`, and
since `(zeta^{n-1}+1)^2/zeta^{n-2} = m^2/r^{n-2}`,

> **(S)**  `sign(dtau/dsigma) = sign(Re m) · sign(Im m)`.

So the two branches want the **same** inequality `Im m > 0`; the sign flip
between them — `Phi > 0` on branch 1 and `Phi < 0` on branch 2, which the
`Xi` note isolates as the reason one argument covers both — is carried entirely
by `Re m`, positive on branch 1 and negative on branch 2. That is a bootstrap:
`arg m = 0` at the hub on branch 1 and `-pi` on branch 2, and `Re m` cannot
vanish first because the cone bound already holds up to the first vanishing.

`Im m > 0` says exactly `r > r_Z(phi)`, where `r_Z := (A/B)^{1/(n-1)}` is the
zero curve. Let `V(r,phi) := Im g = r^n sin(n phi) + n r sin phi` and
`N(phi) := V(r_Z(phi), phi)`. Two elementary facts:

```text
N(phi) = r_Z(phi) · Sigma(phi),            N(phi_c) = c_n,
```

the first because `2 A cos(n phi/2) = sin((n-1)phi) - sin phi`, the second
because `A(phi_c) = B(phi_c)`.

> **KEY LEMMA.** With `L := log N`, on `(0, 2 pi/n)`
>
> ```text
> 2 (n-1) · A · B · Sigma · L'(phi)  =  n (n-2) · sin^2((n-1) phi),
> ```
>
> an exact identity.

*Proof.* `L' = (1/(n-1))[((n-2)/2)cot p - (n/2)cot s] + Sigma'/Sigma` with
`p = (n-2)phi/2`, `s = n phi/2` and `Sigma' = 2(n-1) cos s cos p`. Multiply by
`2(n-1) sin p sin s Sigma`. The bracket contributes
`Sigma · [(n-2)cos p sin s - n sin p cos s] = Sigma · [(n-1)sin phi - sin((n-1)phi)]`,
and the last term contributes `(n-1)^2 sin((n-2)phi) sin(n phi)`. So the total is

```text
(n-1)^2 sin^2 phi - sin^2((n-1)phi) + (n-1)^2 · ½[cos 2phi - cos((2n-2)phi)]
   = ½[(n-1)^2 - 1][1 - cos((2n-2)phi)]  =  n(n-2) sin^2((n-1)phi).   ∎
```

On `(0, 2 pi/n)`: `A > 0` and `B > 0` because the arguments lie in `(0, pi)`, and
`Sigma > 0` because `|sin((n-1)phi)| <= (n-1)|sin phi|` is strict for `n >= 3`
and `sin phi > 0`. So `L' >= 0` with a single zero, at `phi = phi_c`. Hence

```text
N(phi) < c_n   for phi < phi_c,        N(phi) > c_n   for phi > phi_c.
```

Now compare on the level set. `dV/dr = (n/r) Im G`, so `Im G > 0` on branch 1
(Lemma B) puts the branch strictly inside the region where `V` increases in `r`,
and `Im G < 0` on branch 2 puts it strictly inside the region where `V`
decreases. The curve `r_Z` is on the same side in both cases: with
`r_*^{n-1} := sin phi/|sin(n phi)|` the turning radius,

```text
r_Z > r_*   <=>   sin((n-1) phi) < 0,
```

which is false below `phi_c` and true above it — matching the branch each time.
So `r` and `r_Z` are always on one monotone arc of `V(·, phi)`, and
`N(phi) < c_n = V(r,phi)` below `phi_c`, `N(phi) > c_n` above it, both give
`r > r_Z`. That is `Im m > 0` on **both** branches, hence (S) gives the sign of
`dtau/dsigma`, hence monotone turning, hence `|t| <= T_i`. ∎

Only Lemma S and Lemma S2 enter, both proved elsewhere in this directory.

### 1a. The cubic at the hub is a triple zero, and it is general

`ConeBoundBranchGeometry.md` §7 asks whether the `n = 3` factorisation
`3 r y [2r - sin phi (r^2+1)] = -4 (y-1)^3 (y+1)` has a general-`n` analogue and
records that "the cubic vanishing at the hub is the striking feature and is
unexplained."

The Key Lemma explains it. `L'` carries `sin^2((n-1)phi)`, which has a **double**
zero at `phi_c`; so `L - L(phi_c)`, and therefore `N - c_n`, has a **triple**
zero there. The `(y-1)^3` is that triple zero, it is forced, and it is general.
Measured: `(N(phi_c - h) - c_n)/(-h)^3` is constant to better than `0.15%` across
`h = 10^-3, 10^-4, 10^-5` at every degree `3..25`, with limit `1.99997` at
`n = 3` and `5.333287`, `11.715656`, `22.111348` at `n = 4, 5, 6`.

The identity itself holds to `4.1e-48` at `dps = 50` over degrees `3..25`, and
`N(phi_c) - c_n` to `5.3e-51`.

## 2. Lemma S and Lemma S2 do not extend — with the exact crossing

Confinement is the statement that `sin((n-1) arg zeta)` keeps its sign, i.e.
that the branch stays inside one sector `k phi_c < arg zeta < (k+1) phi_c`. A
branch leaves its sector exactly where the **value ray** meets the image of a
sector wall, and both walls have an explicit image: on `arg zeta = 0`,
`g = r^n + n r` sweeps `(0, infinity)`; on `arg zeta = 2 phi_c`,
`g = e^{2 i phi_c}(r^n + n r)`. Solving for the parameter:

> **Wall crossings.**
>
> ```text
> arg zeta = 0        :  s_1 = c_n / sin(delta),
>                        admissible iff sin(delta) > 0 and sin(delta + phi_c) > 0
> arg zeta = 2 phi_c  :  s_2 = -c_n / sin(delta + 2 phi_c),
>                        admissible iff sin(delta + 2 phi_c) < 0 and sin(delta + phi_c) < 0
> ```

At `delta = 0` neither is admissible — `s_1` is infinite and
`sin(2 phi_c) >= 0` — which is Lemma S and Lemma S2, recovered as the degenerate
case. Away from `delta = 0` an admissible crossing appears immediately: at
`n = 3` the union of the two admissible arcs is `delta in (0, pi)`, so
confinement fails on **half the circle of ray directions**, and the failure is
not marginal — the crossing is at `s_1 = c_n/sin delta`, which is `13.4` at
`delta = 0.15` and falls to `c_n` as `delta -> pi/2`.

Checked against Newton continuation of the branch: predicted against traced
crossing, `5.13586` / `5.20795` and `2.55321` / `2.5902` at `n = 3`, `7.54696` /
`7.58578` at `n = 6`, the residual in each case one geometric mesh step.

## 3. The cone bound itself does not extend either

§7's proposal is that supplying confinement would deliver `|t| <= T`. It would
not, because at `n = 6` the inequality `|t| <= T` is itself false. This is the
most visible of the three failures and, as §3a shows, the least important of
them — but it is the one that rules out treating confinement as a technicality.

Sweeping `delta` over a full turn, taking `alpha` from the traced asymptote
rather than from a formula (so that a branch-attribution swap cannot fake a
violation) and `T = |t(0^+)|` exactly from the saddle:

| `n` | directions sampled | `sup|t|/T` |
|---|---|---|
| 3 | 24 | `1.0` at every one |
| 6 | 24 | `1.0` at 20; **`1.31`, `5.22`, `5.25`, `1.36`** at `delta = 1.6008, 2.3862, 2.648, 3.4334` |

(The shipped check runs a 12-direction grid for runtime and so sees two of the
four, `delta = 1.6008` at `1.294` and `delta = 2.64799` at `5.229`; the 24-point
row above is the finer sweep.)

The failures are not conditioning. Re-run at `dps = 60` with `30000` continuation
steps, at `delta = 1.6` and `delta = 2.4` on branch 2, the argmax of `|t|` sits at
`s = 6.42` and `s = 11.79`, at `|zeta| = 0.914` and `0.999` — interior, smooth in
a neighbourhood, largest relative step `0.0024`, Newton residual `5e-61`.
Controls run in the same pass return the supremum **at the hub** with ratio `1.0`:
`delta = 0` on branch 1, and `delta = 3.2` on branch 2, which has three sign flips
and still obeys the bound.

The conditioning trap is worth naming because it caught this pass twice. `sup|t|`
is attained **at the hub**, where `g' = 0`; so the one point that decides the
bound is the one point where `arg g'` is worst conditioned. A sweep at `dps = 30`
reports `sup/T = 1.10` at `delta = 0`, where the answer is a theorem. Every
number in this section therefore takes `T = |t(0^+)|` from the closed form at the
saddle, `tau(0^+) = arg(sqrt(2 e^{-i delta}/g''(zeta_c)))`, and never from a
traced sample.

And the failures cluster near the *singular* directions — call `delta` singular
when the descent ray from the hub value passes through another critical value,
so two hubs collide in the value plane. These are
`delta = -arg((n-1)(zeta_c^{(j)} - zeta_c))`: a single direction `pi/2` at
`n = 3`, and `{1.570796, 2.199115, 2.827433, 3.455752}` at `n = 6`. Every `n = 6`
failure lies in the arc those directions span, and none lies outside it.

### 3a. But the cone is not what breaks first — the sign is

The cone bound is the *third* thing to fail, and the least important. §2's
confinement failure propagates straight through Lemma M, and it does so in three
tiers.

**Tier 1 — monotonicity, on the whole arc, immediately.** Lemma M is
`d(Im Xi)/d sigma = -((n-2)/n) sin((n-1)phi)/r^{n-1}`, and the Corollary is
`sign(dt/d sigma) = sign(Phi) = sign(c_n - Im Xi)`. So the moment the branch
leaves its sector, `sin((n-1)phi)` changes sign, `Im Xi` turns around, `Phi`
eventually changes sign, and **`t` stops being monotone**. Theorem C derives
*both* of its conclusions — constant sign and `|t| <= T` — from monotonicity, so
its proof fails on the entire arc of §2, at every degree, not just where the
conclusions fail.

**Tier 2 — constant sign, on a sub-arc, and this one admits no repair.**
`TurningLengthBound.md` §2's Theorem needs `t` of constant sign, because it
converts `int |sin t| dl` into `|int sin t dl| = |sin gamma|` by Lemma T. Taking
the sign test above the tail (where `t -> 0` and its sign is roundoff), `t`
genuinely changes sign at 6 of 12 sampled directions at `n = 3` and 9 of 12 at
`n = 6`. At `n = 3` the correspondence with §2 is exact over all twelve samples,
**including which branch**: branch 1 flips for `delta in {0.03, 0.5536, 1.077}`,
which is `(0, pi - phi_c) = (0, pi/2)`; branch 2 flips for
`delta in {1.601, 2.124, 2.648}`, which is `(pi - phi_c, 2 pi - 2 phi_c) =
(pi/2, pi)`; and neither flips for `delta > pi`. Those are exactly §2's two
admissible arcs.

The two events are not simultaneous — the wall crossing comes **first**, and the
sign change follows once the reversal has had room to work:

| `delta` (`n = 3`) | branch | `s` at wall crossing | `c_n/sin(delta)` | `s` at `t` sign change |
|---|---|---|---|---|
| `0.03` | 1 | `66.886` | `66.677` | `299341` |
| `0.5536` | 1 | `3.8165` | `3.8041` | `50.58` |
| `1.077` | 1 | `2.2716` | `2.2713` | `8.437` |
| `1.601` | 2 | `2.0052` | `2.0009` | `4.093` |
| `2.648` | 2 | `4.2381` | `4.2213` | `70.31` |

The middle two columns are §2's closed form against the trace, agreeing to three
or four digits; the last column is the downstream consequence. So the wall
crossing is **necessary but not sufficient** for the sign change — at `n = 6`,
`delta = 0.03` the branch leaves its sector and `t` still keeps its sign, because
so near alignment the reversal is too small to reach zero.

**Tier 3 — the cone bound, at `n = 6` only**, as tabulated above.

This inverts the reading. The route is not one lemma short of working; it fails
for exactly the reason §2 identifies, and **`T` is not the problem**. Replacing
the closed-form `T_i` by the *measured* `sup|t|` — which the Theorem permits,
since nothing forces `T = |t(0^+)|` — leaves `C_n - B_n > 0` at 23 of the 24
sampled directions, the exception being `n = 6`, `delta = 2.648`, where `C_n`
happens to vanish. So the cone is generous enough everywhere it matters. What is
missing is the sign.

### 3b. And the sign cannot be bought back

The Theorem's real content is `D_i <= tan(T_i/2) · TV_i` with
`TV_i := int_Gamma |sin(tau - alpha)| dl` the **total variation** of the
transverse displacement. Constant sign is exactly the hypothesis under which
Lemma T's *net* value `|int sin(tau-alpha) dl| = |sin gamma_i|` may be
substituted for it. Without constant sign one can still split the branch at each
sign change and apply the Theorem piecewise — the honest form of the bound is
then `TV_i`, not `|sin gamma_i|`. That is the natural repair, and it fails
quantitatively:

| `n` | `delta` | `\|sin gamma\|` | `TV` | `C_n - sum tan(T_i/2) TV_i` | true `kappa_n` |
|---|---|---|---|---|---|
| 3 | `3.172` | `0.508635` | `0.508605` | `+0.391454` | `0.615995` |
| 3 | `0.5536` | `0.983022` | `1.08861` | `+0.220374` | `0.425095` |
| 3 | `1.077` | `0.936225` | `1.38590` | **`-0.097508`** | `0.161230` |
| 3 | `2.124` | `0.943066` | `1.33589` | **`-0.049235`** | `0.198753` |
| 6 | `2.124` | `0.896591` | `1.35718` | **`-0.119526`** | `0.094922` |

Two readings, and both matter.

* **Lemma T is tight exactly where the sign is constant.** In the top row, and at
  every direction with `delta > pi` at `n = 3`, `TV` agrees with `|sin gamma|` to
  five digits — the two are the same integral there. The excess appears only on
  §2's arc, and it reaches `157%` (`n = 3`, `delta = 1.601`: `|sin gamma_2| =
  0.871` against `TV_2 = 2.241`).
* **The excess is big enough to eat the budget.** `C_n - sum tan(T_i/2) TV_i`
  goes negative at 5 of the 24 sampled directions. So the turning route is closed
  off-alignment in the strong sense: not by the choice of `T`, and not by
  splitting at the sign changes either.

The last column is the reassurance: `kappa_n` itself stays **positive** at every
one of those directions. The statement is intact; it is the instrument that
fails. A general-`phi` proof needs a different estimate, and §3b names the exact
quantity a repair of *this* one would have to control — `TV`, not the net.

## 4. The parametrisation is right, and the recorded sweep survives

Two things had to be checked before §2 and §3 mean anything, because both are
statements about a family indexed by `delta`, and `delta` is only meaningful if
it is the parameter the cusp law actually varies. The check went against a first
reading of mine, and the record is here because the correction is the useful part.

**The parametrisation is confirmed.** [NearFeketeCuspLaw.md](NearFeketeCuspLaw.md)
§3 carries two *independently obtained* values of `kappa_3`: `0.60802134` from the
`eps`-limit table at `phi = 0`, and `0.812598` from the random-`h` universality
check, which reached `phi = pi` through a perturbation with `h'(0) < 0` and never
through the sweep. Measuring `kappa_3` on the `delta`-family under
`delta = n phi/(n-1)`:

| `phi` | `delta` | measured here | recorded |
|---|---|---|---|
| `0` | `0` | `0.608018` | `0.60802134` |
| `2 pi/3` | `pi` | `0.608018` | `0.6080216` |
| `pi` | `3 pi/2` | `0.812595` | `0.812598` |
| `pi/3` | `pi/2` | `-2.2282` | `0.8125984` |

Three of the four agree to six digits, including the one anchor that does not
come from the sweep. So `delta = n phi/(n-1)` is the right parametrisation and
**the general-`delta` family is the family the near-Fekete half needs** — §7's
programme is required, not optional. That is what gives §2 and §3 their force.

**The fourth row is my instrument failing, not the record.** `phi = pi/3` is
`delta = pi/2`, the unique singular direction at `n = 3`, where the descent ray
from the hub value runs into the other critical value. `kappa_3` has period
`2 pi/3` in `phi`, i.e. `pi` in `delta`, so rows 3 and 4 are the *same point* and
must agree. Mine do not — `-2.2282` against `0.812595` — while rows 1 and 2, also
a period apart, agree to all digits shown. **A computation that breaks a
periodicity it should respect, at exactly one point, and respects it everywhere
else, is broken at that point.** The recorded `0.8125984` is corroborated by my
own `phi = pi` value; my `phi = pi/3` value is discarded.

So: no caution attaches to the recorded sweep, `min_phi kappa_n` at `phi = 0`
stands as measured, and the singular directions are a defect of the *continuation
method* — the branch runs into a second critical point at finite `s` — rather than
of `kappa_n`. What they are not is a defect of §3: the two `n = 6` cone-bound
failures were re-examined at their argmax and sit at `|g'| = 5.08` and `11.46`,
at distance `0.209` and `0.506` from the nearest critical point. Nothing is
degenerate there.

## 5. A receipt correction

`ConeBoundMonotoneFunctional.md`'s claim boundary lists, under *Measured, not
proved*, "the confinement statement at ray directions other than `delta = 0`
(97 directions x every hub x both branches, degrees 3–10)", and §8 lists
confinement as measured. Its own shipped script does not support that.

```sh
python3 research_corpus/Erdos1041/\
scripts/check_erdos1041_cone_bound_all_degrees.py
```

`check_ray_directions()` returns `passes: False` with **92 violations out of 96
traces**. So the note's own receipt reports the opposite of what its claim
boundary records.

The violations are a mixture of true and false, which is the harder problem.
Resolving the two `n = 3`, `delta = 0.0013` flags against §2's closed form:

| branch | genuine `Im g'` sign changes | genuine `Phi` sign changes | §2's prediction |
|---|---|---|---|
| 1 | **1**, at `s = 1538.5` | 0 | crossing at `c_n/sin(delta) = 1538.462` |
| 2 | 0 | 0 | no crossing for `delta < pi/2` |

Branch 1's flag is **real** — and is in fact the earliest evidence in this
directory that confinement fails off-alignment, sitting unread in a `passes:
False` field. Branch 2's flag is **spurious**: neither quantity changes sign
there at all. The defect is the initialisation — the sign is fixed at the fourth
sample, `s ~ 1e-26`, which is essentially the hub, where `Phi` and the tangent
both vanish, at `dps = 20` across 32 decades in 300 steps.

So the check both under- and over-reports, and its `passes` field cannot be read
in either direction. The `97 directions` line should be withdrawn rather than
corrected — but the failure it was reporting was real.

This is the same class as `research_packet.json::negative_results` entry 19 and
the precision trap in `LemniscateCapacityBudget.md`'s branch-tracking section: a
sweep that reports cleanly and a sweep that reports failure are equally
worthless until the instrument is calibrated on a case whose answer is known.
The calibration here is cheap and was available — `delta = 0` is a theorem.

## 6. The correction: the window is one hub spacing, and the hub is free

`ConeBoundMonotoneFunctional.md` §7 and §7c answer this note, and they are right.
The error above is that **§2 and §3 fix the hub at `zeta_c = e^{i phi_c}` and vary
the direction, while the cusp law minimises `L(c)` over all `n-1` hubs.**

That note's **Proposition W** shows the both-branches confinement window is
`delta in (0, 2 pi/(n-1))` — length exactly the spacing of the hub orbit under
`g(omega zeta) = omega g(zeta)`. So the `n-1` translates tile the circle and
**exactly one hub is good at every direction**. Its Theorem R then closes the
near-Fekete half at every ray direction.

Verified here rather than accepted, and not through that note's reduction:
tracing at each of the five **actual** hubs `e^{i pi (2k+1)/5}` at `n = 6`, at each
of my four failure directions —

| my `delta` | hub 0 | hub 1 | hub 2 | hub 3 | hub 4 | good hub |
|---|---|---|---|---|---|---|
| `1.6008` | `1.305` | `1.0` | `1.0` | `1.0` ✔ | `1.0` | **3** |
| `2.3862` | `5.2201` | `1.0` | `1.0` | `1.0` ✔ | `1.0` | **3** |
| `2.648` | `5.2494` | `1.0` | `1.0` ✔ | `1.0` | `1.0` | **2** |
| `3.4334` | `1.3583` | `1.0` | `1.0` ✔ | `1.0` | `1.0` | **2** |

(entry is `max(sup|t|/T)` over both branches; ✔ marks the hub that also passes the
constant-sign test — **exactly one per row**, which is Proposition W's content, and
the failing hub is always the one this note fixed.)

My own data already said this and I misread it. In §3a's constant-sign sweep the
sign is constant at `n = 3` precisely for `delta in (pi, 2 pi)` and at `n = 6`
precisely for `delta > 5.03` — arcs of length `pi = 2 pi/(n-1)` and
`2 pi/5 = 2 pi/(n-1)`. I recorded those as "the route fails at most directions"
when the arc lengths were stating Proposition W outright.

**Retracted:** the claim that the turning route is closed off-alignment, together
with the "What survives" bullet that called the general-`phi` case open. **Stands:** §2's
wall-crossing closed form, which that note accepts as the converse half of
Proposition W; the fixed-hub failures of §3, which reproduce there to three digits
on an independent instrument; §1 and §1a; §4; §5.

## 7. What survives

* Theorem C and Corollary K at `delta = 0`, at every degree, on both branches:
  **untouched**, and independently reconfirmed here by a disjoint route.
* The `Xi` family of §6 of that note: untouched; it is a statement about branch 1
  under Lemma S, which is a `delta = 0` fact.
* Everything the near-Fekete half needs beyond the aligned direction: **closed**,
  by that note's Theorem R, on the hub the cusp law is entitled to pick. §6.
* What §3 does establish is that the good hub is *not* an arbitrary one: outside
  its window a hub's branches genuinely violate both hypotheses, so any argument
  that fixes the hub first — as this note did — must first show the direction lies
  in that hub's window. That is Proposition W's job, and §2 is its converse half.

## Claim boundary

Proved, by ordinary mathematics: the identity (S); the Key Lemma and its
consequences `N(phi_c) = c_n`, strict monotonicity of `N`, and the triple zero at
`phi_c`; the comparison giving `Im m > 0` on both branches, hence (★) at
`delta = 0` — this is a second proof of `ConeBoundMonotoneFunctional.md`'s
Theorem C, not a new theorem; and the wall-crossing formulas of §2 with their
admissibility conditions.

Proved as an immediate consequence of Lemma M and its Corollary, both
`ConeBoundMonotoneFunctional.md`'s: §3a's Tier 1, that `t` ceases to be monotone
as soon as the branch leaves its sector. That is a deduction, not a measurement,
and it is what makes Theorem C's *proof* fail on the whole arc of §2.

Measured, not proved, with the instrument calibrated against `delta = 0` where
the answer is a theorem: the failure of the cone bound at the four `n = 6`
directions of §3 (`dps = 60`, `30000` steps, continuity and residual receipts
reported, and the argmax shown to sit at `|g'| = 5.08` and `11.46`, well away from
any critical point); the absence of cone failures at `n = 3` over 24 directions;
§3a's Tier 2, the constant-sign failures and their exact agreement with §2's arcs
over the twelve `n = 3` samples, and the wall-crossing-then-sign-change ordering;
§3b's total-variation table and the negativity of the repaired budget; the
agreement of the three `kappa_3` anchors in §4. The location of the singular
directions is exact arithmetic, but the claim that every `n = 6` failure lies in
the arc they span is a statement about 24 samples.

Retracted within this note, twice. A first draft read the recorded
`max_phi kappa_3` as a sample taken at a degeneracy and asked for the direction
sweep to be redone; §4 shows that was my continuation failing at one point,
caught by a periodicity the recorded table respects and my value did not. And the
headline — that the turning route is closed off the aligned direction — is
withdrawn in §7: it fixes the hub, which the cusp law does not.

Not established here: `kappa_n(phi) > 0` away from `phi = 0` is **not** mine and
is not open — it is `ConeBoundMonotoneFunctional.md`'s Theorem R. Nothing here
bears on the constant 2, on finite perturbations, on the `O(rho^2)` remainder, or
on the two-segment mechanism of
[TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md).

Novelty: none claimed. The Key Lemma is one differentiation and two
product-to-sum identities; the wall crossings are one linear equation each.

**Erdős #1041 remains open.**

## Replay

```sh
python3 research_corpus/Erdos1041/\
scripts/check_erdos1041_ray_direction_scope.py
```
