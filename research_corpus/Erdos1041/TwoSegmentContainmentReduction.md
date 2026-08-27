# Erdős 1041: the two-segment containment reduction

Status: one exact new elimination, one reformulation, and calibrated evidence
for the surviving conjecture. Current through 2026-08-27 source audit. Erdős
#1041 remains open; nothing below claims otherwise.

## 1. The reduction, and what it removes

**Reduction.** Suppose that for every monic `f` with all roots in the open unit
disk there are distinct roots `a, b` and a point `h` with

```text
(i)   max_{[h,a]} |f| < 1,
(ii)  max_{[h,b]} |f| < 1,
(iii) |h - a| + |h - b| < 2.
```

Then Erdős #1041 holds: the polygonal path `a -> h -> b` is admissible and has
length below two.

The content is condition (iii). It says exactly that `h` lies in the **open
ellipse with foci `a, b` and major axis 2**. So under this mechanism the length
obligation is a two-real-dimensional membership test on a single point, not a
functional inequality along a curve. Everything the descent route has to fight —
`D(c) = int (1 - cos theta) ds`, the turning floor of
[TurningFloorRefutation.md](TurningFloorRefutation.md), the branch-length
integral `L(c*) = int_0^mu ds/|f'|` of
[FirstMergeReductionState.md](FirstMergeReductionState.md) — is absent, because
straight segments have no deficit.

Two remarks fix the geometry.

* The ellipse always contains the chord `[a, b]`, so the chord family is the
  degenerate case `h in [a, b]`.
* It always contains the origin, since `|a| + |b| < 2` for roots in the open
  disk. When `|a| = |b| = 1` the origin sits **exactly on** the ellipse: the
  two-radius broken line of the extremal family `z^n - r^n` is the boundary
  case of the whole mechanism.

This is a *sufficient* family. It could fail while Erdős #1041 is true, so a
refutation of the conjecture below would not refute the problem.

## 2. Two of the three sub-families can fail at the same configuration

The three named sub-families are chords, spokes to the minimum-enclosing-disc
centre, and spokes to a critical point. The coverage table already recorded in
[FirstMergeReductionState.md](FirstMergeReductionState.md) shows that each one
fails *somewhere*. It does **not** show two of them failing *together*, and
that is the load-bearing question: if chord and centre always covered each
other, the critical-hub family would be redundant and the mechanism would
reduce to two elementary families.

They are not redundant, and the failure is already available at degree three.

**Witness.** Let `L = 999/1000` and

```text
a_1 = L (7 + 24i)/25,    a_2 = L (7 - 24i)/25,    a_3 = -L.
```

These are three distinct Gaussian rationals of common modulus `L < 1`, so all
roots lie in the open unit disk. The positive rational barycentric weights
`(25/64, 25/64, 7/32)` sum to one and annihilate the three unit directions, so
the origin lies strictly inside their convex hull and `D(0, L)` is the minimum
enclosing disc: **the centre hub is the origin.** Then, in exact rational
arithmetic,

| segment | exact waypoint | `|f|^2` | verdict |
|---|---|---|---|
| chord `a_1 a_2` | midpoint | `1.383240833211...` | exits |
| chord `a_1 a_3` | midpoint | `1.011031244134...` | exits |
| chord `a_2 a_3` | midpoint | `1.011031244134...` | exits |
| spoke `[0, a_1]` | `t = 1/10` | `1.011617488722...` | exits |
| spoke `[0, a_2]` | `t = 1/10` | `1.011617488722...` | exits |

So **no chord is safe and at most one origin spoke is safe**. Neither branch of
the disjunction "one safe chord or two safe centre arms" is available.

Certificates and receipt:
[scripts/check_erdos1041_two_segment_containment.py](scripts/check_erdos1041_two_segment_containment.py).
Every comparison is a comparison of integers; no floating point enters the
elimination. A float cross-check gives true segment maxima
`1.1761125938` (chord `a_1a_2`), `1.0091482833` (the other two chords) and
`1.0067918993` (the two escaping spokes), with the third spoke at `0.9970029990`.

**Degree three is minimal.** For `n = 2`, parametrising `[a, b]` by
`z = a + t(b-a)` gives `|f| = t(1-t)|a-b|^2 <= |a-b|^2/4 <= 1`, so the chord
between the two roots is always safe. The disjunction is therefore unbreakable
at degree two and broken at degree three.

**Relation to what was already recorded.** `research_packet.json` already holds
`adaptive_mec_chord_or_radial_counterexample`, the same elimination at **degree
five** with five Gaussian-rational roots of norm `9999/10000` and fourteen
waypoints. The witness above lowers that to the minimal degree, with three
roots and five waypoints, and supplies the structural reason for it.

## 3. Why it happens: a first-order half-plane count

Put all roots on a common circle of radius `L` and write `p_1 = sum_k a_k`. Then
`|f(0)| = L^n`, and along the spoke `z = t a_j`,

```text
d/dt log|f(t a_j)| at t = 0   =   - Re( conj(p_1) a_j ) / L.
```

As `L -> 1` the spoke starts at `|f| = L^n -> 1`, so it has no room to rise:
only roots in the closed half plane `Re(conj(p_1) z) >= 0` can carry a contained
spoke. The count in that half plane is scale-invariant, since scaling multiplies
every `Re(conj(p_1) a_j)` by `L^2 > 0`.

Meanwhile `sum_j Re(conj(p_1) a_j) = |p_1|^2 >= 0`, so the half plane is never
empty when `p_1 != 0` — but it can contain **exactly one** root. The witness of
§2 realises that: the exact values are

```text
Re(conj(p_1) a_j)  =  -76846077/625000000,  -76846077/625000000,  +10978011/25000000,
```

one positive and two negative. This is what an adversarial search converges to,
and it is why the centre-hub family caps at one spoke rather than failing by a
thin margin: the obstruction is a sign condition, not a near-miss.

## 4. The free-hub mechanism at every recorded hard witness

Minimising `max(max_{[h,a]}|f|, max_{[h,b]}|f|)` over hubs `h` in the ellipse,
over all pairs, at 40-digit exact segment maxima for the verdict column:

| witness | `n` | chords safe | origin spokes safe | critical hubs with 2 spokes | best hub `max|f|` |
|---|---|---|---|---|---|
| degree-3 witness of §2 | 3 | 0 | 1 | 2 | `0.943047` |
| cubic `z^3-(99/100)^3` | 3 | 0 | 3 | 2 | `0.970299` |
| degree-5 origin-spoke lab | 5 | 2 | 0 | 3 | `0.004772` |
| degree-5 adaptive-MEC | 5 | 0 | 1 | 3 | `0.956409` |
| degree-6 `QC = infinity` | 6 | 0 | 3 | **0** | `0.999951` |
| degree-9 `QC = infinity` | 9 | 0 | 4 | **0** | `0.999942` |

Read the three middle columns as the failure pattern: rows 1 and 4 have no
chord and one spoke, rows 5 and 6 have no critical hub at all, row 3 has no
spoke. **Every sub-family is empty somewhere, and rows 1 and 4 show two of them
empty at once.** The free hub is feasible in every row.

Approximate cheapest feasible connection, minimising length subject to
containment (the minimiser sits on the feasibility boundary, so these are
infima approached rather than attained):

| witness | `2R` | cheapest feasible | ratio |
|---|---|---|---|
| degree-3 witness of §2 | `1.998000` | `1.598720` | `0.800` |
| cubic `z^3-(99/100)^3` | `1.980000` | `1.756011` | `0.887` |
| degree-5 origin-spoke lab | `1.999980` | `0.056714` | `0.028` |
| degree-5 adaptive-MEC | `1.999800` | `1.090747` | `0.545` |
| degree-6 `QC = infinity` | `2.000000` | `1.680197` | `0.840` |
| degree-9 `QC = infinity` | `2.000000` | `1.445390` | `0.723` |

## 5. The surviving conjecture, and why the evidence is calibrated

**Conjecture (free-hub two-segment containment).** Every monic `f` with all
roots in the closed unit disk admits distinct roots `a, b` and a hub `h` in the
closed ellipse with foci `a, b` and major axis 2 such that `|f| <= 1` on both
`[h, a]` and `[h, b]`.

Adversarial hill-climbing on

```text
V = min over pairs  min over hubs in the ellipse  max( max_[h,a]|f| , max_[h,b]|f| ),
```

roots capped at modulus one, six restarts per degree seeded from the regular
polygon and from random boundary configurations:

| `n` | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|
| `sup V`, sampled objective, 6 restarts | `0.99999989` | `1.0000000000` | `1.0000000000` | `1.0000000000` | `1.0000000000` | `1.0000000000` | `1.0000000000` |
| `sup V`, exact scores, 3 restarts | `1.0000005438` | `1.0000000000` | `1.0000000003` | `1.0000000000` | — | — | — |

**Neither row is a bound on `V`, and they err in opposite directions.** The
first uses sampled segment maxima throughout, which under-reports a maximum. The
second scores the winning hub with the exact segment maximum of §4, but the hub
itself comes from a finite grid plus local refinement, so its value is an
**upper** bound on the true inner minimum: `1.0000005438` at `n = 3` is
inner-search truncation, not a configuration on which the mechanism fails. What
both rows say is that the searcher cannot move `V` off one by more than about
`5 x 10^-7`.

Reproduce with
[scripts/check_erdos1041_free_hub_two_segment.py](scripts/check_erdos1041_free_hub_two_segment.py)
`calibrate` (`coverage` reproduces §4); `--restarts` and `--iterations` set the
budget. The maximiser is the regular polygon at every degree, with the optimal
hub a short distance off the origin — precisely the corner-cut that buys
strictness in the open disk. That is the signature of a sharp inequality with a
known extremal family, in the sense §7 of
[StraightSpokeHubCriterionLab.md](StraightSpokeHubCriterionLab.md) demands.

`research_packet.json::negative_results` entry 19 warns that an adversarial
supremum pinned just below a threshold is not evidence that the threshold is
never crossed. The warning is answered here by a **negative control with a
margin gap**. The same searcher, same budget, pointed at the weaker "one safe
chord or two safe origin spokes" breaks it at `n = 3, 5, 6`, returning
`V = 1.0098, 1.0012, 1.0003`; the `n = 3` return is the witness of §2,
exactified above. So the discriminator is not that one number sits under a
threshold and the other over it — it is that **the false disjunction breaks by
`9.7 x 10^-3` where the free-hub residual is `5.4 x 10^-7`, four orders of
magnitude apart, on the same searcher at the same budget and the same degree.**

Two caveats stay attached. Random sampling is worthless here: 4000 draws from
six structured families gave **zero** failures of the chord-or-origin
disjunction that the adversarial searcher broke immediately. And the search is
capped at degree nine.

## 6. A recorded obstruction, re-read

`negative_results` entry 27 records that the reciprocal sweep cannot join two
roots on the extremal family: with `g = f* = 1 - r^n z^n`, the set `{|g| < 1}`
splits into `n` components, one per root, meeting only at `z = 0`, where
`|g| = 1` exactly.

Under the two-segment lens that configuration is the mechanism rather than the
obstruction. The components meet at the origin, and a hub at the origin joins
two of them; the extremal path *is* the two-radius broken line through the
meeting point. What blocks the sweep is only that the majorant `|f| <= |f*|` is
exactly saturated at the one point that matters. The true lemniscate is not:
`|f(0)| = prod_k |a_k| = r^n < 1` strictly, so the origin has a genuine open
neighbourhood inside `{|f| < 1}`, of size governed by `n log(1/r)`. The
reciprocal sweep loses its slack precisely where the two-segment mechanism finds
its hub.

This does not repair the sweep, and the majorant is already recorded in
[RootCentredReciprocalSweep.md](RootCentredReciprocalSweep.md) together with the
harmonicity of `log|f*|` and the power-sum identity — none of that is new here.
What is new is the reading of entry 27 as a statement about where the majorant
is lossy rather than about where the route dies.

## 7. Claim boundary

**Primary-source boundary (read 2026-08-27).** The degree-four comparison
underlying this reduction is Venkata Siddharth Pendyala, arXiv:2606.24875,
whose downloaded LaTeX source states the theorem at `extracted.md` lines 6--9,
26--32 and the four-point radial lemma at lines 34--45. The source bundle is
[`source.tar.gz`](../../../../annexes/arxiv-2606-24875-pendyala-degree-four-lemniscate-path/source.tar.gz),
SHA-256
`678a6e830e1bef8fc9e64326fbb40f10616cd48c401aeee49202bc81d905d42b`; the
official record is [arXiv:2606.24875](https://arxiv.org/abs/2606.24875).
That source proves only the degree-four case and its bounded geometric lemma;
it does not supply the general two-segment reduction, the degree-three
elimination here, or an unrestricted Erdős #1041 solution. No priority or
novelty claim is made for the local reduction.

Proved here, exactly: the degree-three elimination of §2, and the minimality of
degree three for it. Elementary and proved: the reduction of §1 and the
first-order count of §3. Measured, not proved: the tables of §4 and the
conjecture of §5.

Erdős #1041 remains open. Its degree-three case is proved in
[CubicCriticalHub.md](CubicCriticalHub.md) by a critical-point hub — which is
exactly the family the §2 witness shows cannot be dispensed with.
