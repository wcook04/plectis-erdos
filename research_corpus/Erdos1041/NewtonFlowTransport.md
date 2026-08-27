# Erdős 1041: containment is free, and what the transport costs

Status: one exact reduction, three exact identities, one new negative result,
and calibrated evidence for a strictly weakened form of the surviving
conjecture. Current through 2026-08-27 source audit. Erdős #1041 remains open;
nothing below claims otherwise.

Receipt: [`formal_math/probes/erdos1041_newton_flow_transport.py`](../../../../probes/erdos1041_newton_flow_transport.py).

```sh
./repo-python formal_math/probes/erdos1041_newton_flow_transport.py --no-sweeps
./repo-python formal_math/probes/erdos1041_newton_flow_transport.py \
    --only __none__ --extremal-closed-form
```

The probe fails if any configuration transports to `2` or above, if a
transported curve leaves `{|f| < 1}`, if the integral and polyline lengths
disagree, if the chord-maximum lemma drifts, or if the set of degrees at which
the transported chord is eliminated stops being `{3}`.

## 0. The observation this starts from

Read `research_packet.json::negative_results` for what actually killed each
constructive route. At least nine of the thirty-seven entries are the same
kind of failure:

| entry | what fails |
|---|---|
| 4 | the metric-selected nearest-root spoke **exits** the lemniscate |
| 6 | the midpoint of **every** root chord lies outside `{\|f\|<1}` |
| 7 | four of five root-to-origin spokes have waypoints with `\|f\|>1` |
| 8 | the minimum-critical-value hub has four **unsafe** root spokes |
| 10 | all ten chords **unsafe**, at most one safe MEC radial arm |
| 13 | at most one **sublevel-contained** straight spoke at any hub |
| 17 | no critical hub carries **two contained** spokes |
| 25 | "**Containment breaks, not the budget.**" `d1+d2` is 1.717 and 1.498 |
| 36 | no safe root chord and at most one safe origin spoke |

Every one of them is a **containment** failure at a configuration where the
length budget is comfortably satisfied. Entry 25 says it in those words.

The point of this note is that containment failures of this kind are not
obstructions at all. A curve that leaves the lemniscate can be carried back
inside by the Newton flow, keeping its endpoints fixed. What it cannot keep is
its length, and that is the only thing left to bound.

## 1. The transport reduction

For `λ ∈ (0,1]` define `N_λ(z)` to be the endpoint of the lift, starting at `z`,
of the value path `s ↦ s·f(z)`, `s: 1 → λ`. Where it is defined,

```text
f(N_λ(z)) = λ f(z),      N_λ(a) = a for every root a.
```

This is the Newton flow at time `T = log(1/λ)`: `dz/dt = −f/f'` gives
`f(z(t)) = e^{−t} f(z(0))`.

**Theorem T1 (transport).** Let `f` be monic of degree `n ≥ 2`, let `Γ` be a
rectifiable path joining two roots `a ≠ b`, and put `M = max_Γ |f|`. Fix
`λ ∈ (0,1]` and let

```text
C_λ(Γ) = { s·f(z) : z ∈ Γ, s ∈ [λ,1] }
```

be the radial cone in the value plane between the loop `f(Γ)` and its scaled
copy `λ·f(Γ)`. If `C_λ(Γ)` contains no critical value of `f`, then `N_λ` is
defined and continuous on `Γ`, and `N_λ(Γ)` is a path from `a` to `b` with

```text
max |f| on N_λ(Γ)  =  λ M.
```

In particular, taking `λ = (1−ε)/M` for any `ε ∈ (0,1)` when `M > 1`, the
transported curve lies in `{|f| ≤ 1−ε} ⊂ {|f| < 1}`.

*Proof.* `f` is a branched cover of the plane; the lift of a path avoiding
critical values exists, is unique given its start, and depends continuously on
the start. The homotopy `(z,s) ↦ s f(z)` on `Γ × [λ,1]` has image `C_λ(Γ)`, so
under the hypothesis the whole homotopy lifts continuously; the lift at `s = 1`
is the identity on `Γ` and the lift at `s = λ` is `N_λ|_Γ`. The endpoints are
fixed because `f(a) = f(b) = 0` forces `s f(a) = 0` for all `s`, so the lifted
endpoint stays at the root it started from. The level statement is
`|f(N_λ z)| = λ|f(z)|`. ∎

So **the containment obligation disappears**. Every witness in the table of §0
is a curve with `M` slightly above one; transporting it puts it inside. What
survives is one number.

## 2. What the transport costs — an exact identity

Write `N = f'/f = Σ_i 1/(z − z_i)` for the logarithmic derivative, and
`S = |f/f'| = 1/|N|` for the Newton step length.

**Theorem T2 (stretch identity).** Wherever `N_λ` is defined and `f(z) ≠ 0`,

```text
N_λ'(z)  =  N(z) / N(N_λ z)                    (an identity of complex numbers)
```

and hence the transported length is

```text
Λ(Γ,λ)  =  ∫_Γ  |N(z)| / |N(N_λ z)|  |dz|  =  ∫_Γ  S(N_λ z) / S(z)  |dz|.
```

*Proof.* Differentiating `f(N_λ(z)) = λ f(z)` gives
`N_λ'(z) = λ f'(z)/f'(ζ)` with `ζ = N_λ(z)`. Substituting `f' = f·N` twice,

```text
λ f'(z)/f'(ζ) = λ f(z) N(z) / (f(ζ) N(ζ)) = λ f(z) N(z) / (λ f(z) N(ζ)) = N(z)/N(ζ),
```

the `λ` and the `|f|` cancelling identically because `f(ζ) = λ f(z)` exactly. ∎

Verified numerically: the two forms `λ|f'(z)|/|f'(ζ)|` and `|N(z)|/|N(ζ)|`
agree to a maximum relative deviation of `2.9e-14` over four configurations and
39 chord points each.

**The transported connector is the original connector reweighted by the ratio of
Newton steps at target and source.** The flow shortens exactly where it
shortens the Newton step. That is the whole cost.

**Corollary (contraction criterion).** Along the flow,

```text
d/dt log|N_t'(z)|  =  − Re (f/f')'(z),        (f/f')' = 1 − f f''/(f')²,
```

and in root coordinates, with `u_i = 1/(z − z_i)`,

```text
(f/f')'  =  ( Σ_i u_i² ) / ( Σ_i u_i )².
```

So if `Re(1 − f f''/(f')²) ≥ 0` on the swept region then `Λ ≤ len(Γ)`, and since
`len([a,b]) = |a−b| < 2` for roots in the open unit disk, the problem would
follow. The criterion holds far from the roots — the ratio tends to `1/n` as
`z → ∞`, and lies in the cone of half-angle `4α` about `1` whenever all roots
are seen from `z` within a sector of half-angle `α`, so it is positive for
`α < π/8`. It **fails** near critical points, where the denominator vanishes,
and in particular it fails on the extremal family: at the midpoint of the
adjacent chord of `zⁿ − rⁿ` the criterion asks for `cosⁿ(π/n) ≥ n−1`, which is
false at every `n ≥ 2`. The mechanism therefore does not rest on pointwise
contraction; only the integral `Λ` matters.

## 3. Where the transport is available, and where it pinches

The hypothesis of T1 is sharp in the sense that it is exactly the condition
under which the lift stays single-valued. When a critical value enters
`C_λ(Γ)`, the flow carries an interior point of `Γ` into the corresponding
saddle and the curve splits: the two sides descend along the two descending
separatrices and the transported set acquires a gap that must be repaired
through the saddle.

Measured on `z³ − r³` at `r = 0.999` (critical value `r³ = 0.997`): transport to
stop level `1` gives `1.96753`, and forcing the stop level to `0.5, 0.2, 0.05`
— i.e. below the critical value — returns `1118, 1259, 1389`, which are broken
curves, not lengths. Same shape on `z⁵ − r⁵`.

This locates the descent route inside the family. The inverse-ray descent path
of [FirstMergeReductionState.md](FirstMergeReductionState.md) is the limit of
the transport **after** the pinch, at stop level `μ = |f(c*)|`. The problem
only asks for stop level `1`. Every route in this directory that computes
`L(c*)` is therefore paying to descend from level `1` to level `μ`, which the
statement does not require.

## 4. The extremal family, in closed form

On `f = zⁿ − rⁿ` the transport needs no branch tracking at all: the defining
equation `ζⁿ = rⁿ + λ(zⁿ − rⁿ)` determines `|ζ|` outright, so

```text
Λ  =  2r sin(πj/n) · λ · ∫_0^1  |z(t)|^{n−1} / |rⁿ + λ(z(t)ⁿ − rⁿ)|^{(n−1)/n} dt,
z(t) = r[(1−t) + t ω^j],   ω = e^{2πi/n}.
```

**Lemma (chord maximum).** Writing `z(t) = r e^{iθ}(cos θ + i s sin θ)` with
`θ = πj/n`, `s = 2t−1`, one gets `f = rⁿ[(−1)^j(cos θ + i s sin θ)ⁿ − 1]`, so at
the midpoint `s = 0` and odd `j`,

```text
M_j = rⁿ (1 + cosⁿ(πj/n)).
```

Verified equal to the sampled maximum over 20001 chord points at
`n = 3,4,6,10` with difference `0` or `2.2e−16`. (For `j = 1` this is the
escape criterion `rⁿ(1 + cosⁿ(π/n)) > 1` already recorded in
[FirstMergeReductionState.md](FirstMergeReductionState.md).)

**Theorem T3 (the transported chord touches the sharpness radius exactly).**
For `f = zⁿ − rⁿ` and the adjacent chord, transport to stop level exactly `1`
(`λ = 1/M_1`) sends the chord midpoint `m` to a point `ζ` with

```text
ζⁿ = rⁿ − 1,        so   |ζ| = (1 − rⁿ)^{1/n}.
```

*Proof.* `f(ζ) = λ f(m) = −λM_1 = −1`, so `ζⁿ − rⁿ = −1`. ∎

`(1 − rⁿ)^{1/n}` is exactly the constant `ε` of
[TrueGeodesicLab.md](TrueGeodesicLab.md)'s sharpness theorem, which proves that
**every** path joining two roots inside `{|f| < 1}` comes within `ε` of the
origin. The transported chord attains that bound with equality: it approaches
the origin exactly as closely as any admissible path is permitted to, and no
closer. `ζⁿ` is negative real, so `ζ` sits on a ray bisecting two roots — the
gap between two petals. Verified to relative error `1.6e−12 … 1.1e−9` at
`n = 3,4,5,6,8` and `r = 0.99, 0.999, 0.9999`.

## 5. New negative result: the transported chord alone is not a mechanism

Transported adjacent-chord length on `zⁿ − rⁿ` from the closed form of §4,
with `λ = min(1, 1/M)` so that a chord already inside the lemniscate is left
alone:

| `n` | `r=0.9` | `r=0.99` | `r=0.999` | `r=0.9999` | `r=0.999999` | `r=1` |
|---|---|---|---|---|---|---|
| 3 | 1.558846 | 1.780845 | 1.967531 | **2.075117** | **2.152600** | **2.174146** |
| 4 | 1.272792 | 1.527492 | 1.789435 | 1.961265 | **2.117879** | **2.190982** |
| 5 | 1.058013 | 1.306212 | 1.596734 | 1.807523 | **2.031290** | **2.180095** |
| 6 | 0.900000 | 1.127845 | 1.423741 | 1.654911 | 1.927546 | **2.167337** |
| 8 | 0.688830 | 0.870988 | 1.149891 | 1.391048 | 1.716773 | **2.142709** |
| 10 | 0.556231 | 0.700670 | 0.952499 | 1.185621 | 1.528070 | **2.204148** |

**The transported adjacent chord crosses 2** — at `n = 3` between `r = 0.999`
and `r = 0.9999`, and at every degree tabulated as `r → 1`. Minimising over
**all** pairs at `r = 1 − 10⁻⁹` (`j` = angular step):

| `n` | best over pairs | verdict |
|---|---|---|
| 3 | **2.171978** (`j=1`, the only pair) | **above 2 — eliminated** |
| 4 | 2.000000 (`j=2`) | below 2 |
| 5 | 1.879060 (`j=2`) | below 2 |
| 6 | 1.821612 (`j=2`) | below 2 |
| 8 | 1.383939 (`j=3`) | below 2 |
| 10 | 1.180156 (`j=4`) | below 2 |

So **"transport the best root chord" is eliminated at degree three**, on this
problem's own extremal family, by an exact closed-form computation on an
explicit one-parameter family rather than by a search. It belongs in
`negative_results`.

Why the higher degrees survive is worth stating, because it is not margin. At
**even** `n` the diametral chord passes through the origin — it *is* the origin
broken line — and has `M = rⁿ < 1`, so it needs no transport and has length
exactly `2r`; that is the `2.000000` at `n = 4`. At **odd** `n ≥ 5` a
non-adjacent chord (`j = 2`) still has `M > 1` but transports to well under 2.
Degree three is the only degree with neither escape: it has a single pair, and
that pair's chord is adjacent.

Two corrections to earlier passes of this same computation, recorded because
both produced confident wrong tables and both were caught only by disagreement
with the independent flow-tracked method.

* Omitting the clamp `λ ≤ 1` transports an already-admissible curve *upward* to
  level one and lengthens it. That reported a spurious elimination at `n = 4`
  and inflated the whole `r = 0.9` column.
* Evaluating `d = rⁿ + λ(zⁿ − rⁿ)` in that literal form loses every significant
  digit when `λ` is near one and the chord passes through the origin, because
  `rⁿ` cancels against `λrⁿ`. It returned a "length" of `4.5 × 10⁴` for the
  `n = 4` diametral pair. The stable rearrangement `d = rⁿ(1−λ) + λzⁿ` is exact
  when `λ = 1`.

Cross-check after both fixes: the flow-tracked probe at mpmath 40 digits
returns best `2.172537` at `n = 3` and `1.99999999800011` at `n = 4` and `n = 6`,
against the closed form's `2.171978`, `2.000000`, `1.821612` — the same verdict
at every degree, with the closed form sharper at `n = 6` because it can evaluate
the `j = 2` pair that the flow tracker flags as pinched.

What is **not** eliminated is the transport reduction itself. On the same family
the origin broken line `[a,0] ∪ [0,b]` has `M = rⁿ < 1` at every degree, so it
needs no transport at all and its length is exactly `2r < 2`. The two starting
curves are complementary: the chord carries the higher degrees with growing
margin, the origin path carries degree three, and at even degree they coincide.

## 6. The measurement on the stored witnesses

`min` over pairs and over the two canonical starting curves of the transported
length, with every transport certified continuous by refinement (the polyline
gap must collapse) and cross-checked against the integral form of T2:

| configuration | `n` | winner | `M` | transported | `2 − Λ` | `Λ − 2R` | Form A slack |
|---|---|---|---|---|---|---|---|
| `origin_spoke_quintic` | 5 | chord | 0.25367 | **0.480737** | 1.51926 | −1.53903 | −0.05117 |
| `chord_or_origin_cubic` | 3 | chord | 1.00915 | **1.598953** | 0.40105 | −0.39905 | −0.01090 |
| `qc_witness_n6` | 6 | chord | 1.42067 | **1.773562** | 0.22644 | −0.22644 | −0.00000 |
| `qc_witness_n9` | 9 | chord | 1.57066 | **1.463179** | 0.53682 | −0.53682 | −0.00000 |
| `extremal_n3_r0.999` | 3 | chord | 1.12163 | 1.967543 | 0.03246 | −0.03046 | 0.00000 |
| `extremal_n3_r0.9999` | 3 | origin | 0.99970 | 1.999800 | 0.00020 | 0.00000 | 0.00000 |
| `extremal_n6_r0.9999` | 6 | chord | 1.42102 | 1.654949 | 0.34505 | −0.34485 | 0.00000 |
| `extremal_n8_r0.9999` | 8 | chord | 1.52957 | 1.391094 | 0.60891 | −0.60871 | 0.00000 |

Full battery: 24 configurations (the extremal family at `n = 3,4,5,6,8` and
`r = 0.9 … 0.9999`, the origin-spoke quintic, the two QC witnesses, and the
minimal degree-three chord-or-origin witness), **zero failures** — every one
transported strictly below `2`, every transported curve certified interior,
integral and polyline lengths agreeing. The near-Fekete sweep is a separate
mode of the probe (the default, `--no-sweeps` omitted); it is slow enough that
it did not complete inside this pass and is **not** part of the figure above.

**Adversarial search with a negative control.** Hill-climbing on root positions
capped at modulus `1 − 10⁻⁹`, three restarts (seeded at the regular polygon,
at a near-Fekete perturbation, and at random), thirty steps, maximising the
transported objective:

| `n` | 3 | 4 | 5 | 6 |
|---|---|---|---|---|
| `sup` of the transported objective | 1.9999999980 | 1.9999999980 | 1.9999999980 | 1.9999999980 |
| `sup` of the Form A′ control | **inf** | 1.999999998 | 1.999999998 | 1.999999998 |

`negative_results` entry 18 warns that a supremum pinned just below a threshold
is not evidence, "with one exception worth stating — a pin is not suspicious
when a *known extremal family explains it*". This pin is explained exactly:
`zⁿ − rⁿ` at `r = 1 − 10⁻⁹` gives `2r = 1.999999998`, which is the pinned value
to ten digits. The searcher is not stuck below a threshold it cannot reach; it
has found the extremal family and sits on it.

The control is Form A′ — two *untransported* straight origin spokes — run by the
same searcher at the same budget. It returns `inf` at `n = 3`, i.e. it finds a
configuration with no admissible pair at all, which is the correct behaviour:
Form A′ is false, and `negative_results` entry 36 records that it fails "already
at DEGREE THREE, which is minimal". At `n = 4,5,6` the control returns `2r`
because the diametral or a near pair is admissible there, so the control
discriminates exactly at the degree where the two statements differ.

Three readings worth stating.

* The three witnesses that killed the straight-spoke and chord-or-origin
  routes transport with margins `0.23` to `1.52`. They are not near-misses under
  this mechanism; they are not hard for it at all. Their difficulty was entirely
  containment.
* `Λ − 2R ≤ 0` at every configuration, so the transported curve satisfies
  [TrueGeodesicLab.md](TrueGeodesicLab.md)'s **radius bound** conjecture
  everywhere tested, with equality only in the `r → 1` limit of the extremal
  family.
* The **Form A** slack `Λ_origin − (|a| + |b|)` is `≤ 0` at every configuration,
  strictly negative at both the quintic and the cubic witness, and exactly `0`
  on the extremal family. TrueGeodesicLab.md states the gap between Form A and
  Form A′ as "the *length* `|z_a| + |z_b|` is affordable, but the straight
  broken line realising it is not always available. A proof needs a path of that
  length taking some other route." **The transported origin path is that other
  route**. At the quintic where Form A′ fails it delivers a certified-continuous
  `Λ = 1.958583` on the pair `1-2` against a budget of `2.009758`, slack
  `−0.05117`. Measured there, **no** straight origin spoke is admissible at all —
  `max |f| > 1` on all five — which is the stronger reading
  [FirstMergeReductionState.md](FirstMergeReductionState.md) already records
  ("not 'at most one safe spoke' but **none**"). Four of the ten origin paths
  pinch under transport and are excluded by the continuity certificate; the six
  that survive all have negative slack.

## 7. Relation to what is already in this directory

**The value-plane lens is not new here.**
[LemniscateCapacityBudget.md](LemniscateCapacityBudget.md) already records the
reformulation in full: *"Let γ be any loop in the open unit value-disk based at
0. Each of its n lifts is a path in `{|f| < 1}` joining a root to the root given
by the monodromy of γ, of length `∫_γ |dv|/|f'(z(v))|`. The descent arc at a
critical point c is exactly the degenerate loop."* That file also records
`Area(Ω) ≤ π t^{2/n}` and eliminates the area currency by `√n` on the extremal
family. None of that is claimed here.

What §1 adds to that family is **which loop**. That file exhibits two: the
degenerate lasso (the descent path) and the level circle. The transport supplies
a third — `λ·f(Γ)`, the scaled image of an ordinary curve joining two roots —
and it is the one that covers the regime the other two miss:

| loop | `n=3` | `n=6` | `n=8` | `n=10` | tight where |
|---|---|---|---|---|---|
| level circle (that file's table, `r = 1−10⁻⁹`) | 3.566 | 2.565 | 2.223 | 1.965 | large `n` |
| transported chord (§5, `r = 1−10⁻⁹`) | 2.172 | 1.822 | 1.384 | 1.180 | `n ≥ 4` |
| transported origin path (exact, any `r`) | `2r` | `2r` | `2r` | `2r` | all `n` |

That file observes that its level-circle route's degree dependence "runs the
*opposite* way to every hub route: hub routes are tight at small `n` and this is
tight at large `n`". The transport sits between them and, in the disjunction
with the origin path, is below `2` at every degree.

**Relation to the free-hub two-segment mechanism.**
[TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md) §5
conjectures a pair `a,b` and a hub `h` in the closed ellipse with foci `a,b` and
major axis `2` such that `|f| ≤ 1` on both `[h,a]` and `[h,b]`. Transport
**strictly subsumes** it: if such a hub exists then `M ≤ 1`, the transport is
the identity, and `Λ = |h−a| + |h−b| ≤ 2`. So the free-hub conjecture implies
the transported statement and not conversely, and the calibrated evidence that
file reports — an adversarial searcher unable to move its objective off `1` by
more than `5×10⁻⁷` — transfers to the weaker statement below.

## 8. The surviving conjecture

> **Conjecture (transported two-segment).** For every monic `f` with all roots
> in the open unit disk there are distinct roots `a, b` and a point `h` in the
> closed ellipse with foci `a, b` and major axis `2` such that the Newton
> transport of `[a,h] ∪ [h,b]` to level `1` is defined and has length below `2`.

The hypothesis is strictly weaker than
`TwoSegmentContainmentReduction.md` §5 — the two segments need not be contained
— and the conclusion is the same. Its degenerate cases are the chord (`h` on
`[a,b]`) and the origin path (`h = 0`), and §5 above shows neither of those
alone suffices: the chord fails at `n = 3` in the sharp limit, and the origin
path is exactly tight — length `2r` — at every degree.

The obligation that is left is now purely a length statement about one explicit
curve, with the exact integrand of T2:

```text
Λ  =  ∫_Γ  S(N_λ z) / S(z)  |dz|,        S = |f/f'|,
```

and no containment side condition anywhere.

## 9. Claim boundary

**Primary-source boundary (read 2026-08-27).** The standard ingredients are
attributed only to the downloaded primary sources recorded in
[`value_ray_transport_polynomial_lemniscates_v0.json`](../../prior_art_routes/value_ray_transport_polynomial_lemniscates_v0.json).
Hatcher's *Algebraic Topology*, §1.3 Proposition 1.30 and the following
path-homotopy paragraph (printed pp. 60--61; local PDF SHA-256
`50b1632a200c66eeef2efba61fec49bb6d80442269f766df38817f23a01bde7c`) supports
homotopy lifting, unique path lifting, and fixed endpoints. Sutherland's *Bad
Polynomials for Newton's Method*, §5 (printed p. 42; local PDF SHA-256
`e0dbfa6ad56d14971d4f901dc8568731e22359feeb1efb429b240f156b88d29e`) supports
the Newton-flow name, radial value-space trajectories, and the critical-value
obstruction. The local files are
[`Hatcher source.pdf`](../../../../annexes/hatcher-2002-algebraic-topology-covering-spaces/source.pdf)
and
[`Sutherland source.pdf`](../../../../annexes/sutherland-1992-newton-flow/source.pdf).
Those sources do **not** state this note's endpoint-preserving polynomial
transport, exact stretch identity, binomial falsifier, or any global
length-below-two result. Those are ordinary arguments and diagnostics of this
repository; no priority or novelty claim is made for the standard transport
technology or the local packaging.

Proved by ordinary mathematics: T1, T2 and its corollary (including the root
form `(f/f')' = Σu_i² / (Σu_i)²`, the `1/n` limit at infinity, the `α < π/8`
cone criterion, and the failure of the criterion on the extremal family), the
chord-maximum lemma's midpoint value, T3, and the subsumption of the free-hub
mechanism in §7.

Exact computation on an explicit family, not a search: the §5 tables and the
elimination of the transported chord at `n = 3`.

Measured, not proved: the §6 battery; the claim that the chord-maximum lemma's
midpoint value is the maximum over the whole chord (verified against a
20001-point sample, difference `0` or `2.2e−16`, not proved); the §3 pinch
figures; the conjecture of §8.

Not established: any bound on `Λ`. The `D`-bounded-away-from-1 half named in
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md) is untouched by this
note, and so is the `O(ρ²)` remainder of the near-Fekete route.

**Erdős #1041 remains open.** What this note changes is which obligation is
load-bearing: not containment, which the transport supplies for free, but the
length of one transported curve.
