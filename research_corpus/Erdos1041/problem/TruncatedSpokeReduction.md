# Erdős 1041: the truncated-spoke reduction, where the length obligation is free

Status: one elementary reduction, one structural observation about the recorded
refutation, and calibrated evidence for the surviving conjecture. 2026-08-24.
Erdős #1041 remains open; nothing below claims otherwise.

## 1. The reduction

Write `â = a/|a|` for a nonzero root `a`.

> **Reduction (Form A-cut).** Suppose that for every monic `f` with all roots in
> the open unit disk there are distinct roots `a, b` and radii
> `s_a ∈ (0,|a|]`, `s_b ∈ (0,|b|]` with
>
> ```text
> (i)   max_{[s_a â, a]} |f|  < 1,
> (ii)  max_{[s_b b̂, b]} |f|  < 1,
> (iii) max_{[s_a â, s_b b̂]} |f|  < 1.
> ```
>
> Then Erdős #1041 holds.

*Proof.* The path `a → s_a â → s_b b̂ → b` lies in `{|f| < 1}` and has length

```text
(|a| − s_a) + |s_a â − s_b b̂| + (|b| − s_b)
      ≤  (|a| − s_a) + (s_a + s_b) + (|b| − s_b)  =  |a| + |b|  <  2,
```

the middle step being the triangle inequality, with equality only when
`â = −b̂`. ∎

**What this removes.** The two-segment reduction of
[TwoSegmentContainmentReduction.md](TwoSegmentContainmentReduction.md) carries a
length obligation as its condition (iii): the hub must lie in the open ellipse
with foci `a, b` and major axis 2, a two-real-dimensional membership test. Here
there is **no length condition at all** — every admissible pair of radii is
inside the budget automatically. The entire statement is containment.

## 2. It is exactly the span of the two refuted families

* `s_a = |a|`, `s_b = |b|` is the **root chord**, refuted by
  `negative_results` entries 7 and 37.
* `s_a, s_b → 0` is **Form A′** of [TrueGeodesicLab.md](TrueGeodesicLab.md),
  both full radii interior, refuted by `negative_results` entry 8 and
  `exact_results` `two_safe_origin_spokes_counterexample`.

TrueGeodesicLab.md states the gap between its Form A and Form A′ as "the whole
difficulty": the length `|z_a| + |z_b|` is affordable, but the straight broken
line realising it is not always available. Form A-cut is a family of paths that
respects that length budget without being that broken line, and it is the
smallest natural family containing both refuted endpoints.

## 3. Why truncation is the right repair: the obstruction is a germ at the origin

§3 of TwoSegmentContainmentReduction.md computes, for roots on a common circle
of radius `L`,

```text
d/dt log|f(t a_j)|  at t = 0   =   − Re( conj(p_1) a_j ) / L,
```

so only roots in the closed half plane `Re(conj(p_1) z) ≥ 0` can carry a full
spoke, and that half plane can hold exactly one root. **That is a first-order
condition at the origin.** Truncating at any `s > 0` deletes it: the arm never
visits the neighbourhood where the sign condition lives.

The recorded witness confirms it quantitatively. Define the **entry radius**

```text
τ(a)  =  inf{ s ∈ [0,|a|] : |f| ≤ 1 on [s â, a] }.
```

On the five-root configuration that refutes Form A′ — `r = 99999/100000`, roots
`r`, `r(−20 ± 99i)/101`, `r(−28 ± 195i)/197` — **zero** of the five full spokes
are interior, but

```text
τ(a_k)/|a_k|  =  0.542751,  0.047854,  0.047854,  0.032779,  0.032779.
```

Four of the five spokes are interior from under **5 %** of the way out. The
refutation of Form A′ is a statement about a neighbourhood of the origin of
relative size about `0.05`, not about the spokes.

## 4. The common-radius form: one parameter, two computable scalars

Take `s_a = s_b = s`. Conditions (i) and (ii) become `s ≥ max(τ(a), τ(b))` and
nothing else, because a shorter segment is contained in a longer one, so the arm
condition is **monotone in `s`**. Define

```text
V  =  min over pairs (a,b)   min over  max(τ(a),τ(b)) ≤ s ≤ min(|a|,|b|)
          max_{[s â, s b̂]} |f|.
```

Form A-cut with a common radius holds exactly when `V ≤ 1`. One free real
parameter; two exactly computable scalars per pair; no length condition.

**The restriction costs nothing at the hardest recorded witnesses.** At the two
`QC = infinity` configurations — where no chord is safe and *no* admissible
critical point carries two contained spokes — `V` reproduces the full free-hub
optimum of TwoSegmentContainmentReduction.md §4 to every digit that note prints:

| witness | free hub, §4 of that note | `V`, common radius |
|---|---|---|
| degree-6 `QC = infinity` | `0.999951` | `0.9999510` |
| degree-9 `QC = infinity` | `0.999942` | `0.9999415` |
| degree-3 two-segment witness | `0.943047` | `0.9430963` |

So at the hardest configurations on file the optimal free hub already sits on a
common-radius chord between two root directions: the two-dimensional hub search
and the ellipse condition are both buying nothing there.

## 5. Coverage

Exact segment maxima throughout — the maximum of `|f|²` along a segment is a real
polynomial of degree `2n` in the parameter, so its critical points are located as
polynomial roots, never sampled.

| witness | `n` | safe chords | safe FULL spokes | `V` | verdict |
|---|---|---|---|---|---|
| degree-3 two-segment witness | 3 | 0 | 1 | `0.9430963` | feasible |
| cubic `z³−(99/100)³` | 3 | 0 | 3 | `0.9702990` | feasible |
| degree-5 origin-spoke lab | 5 | 2 | **0** | `0.0047742` | feasible |
| near-Fekete quintic | 5 | 0 | 3 | `0.9999973` | feasible |
| degree-6 `QC = infinity` | 6 | **0** | 3 | `0.9999510` | feasible |
| degree-9 `QC = infinity` | 9 | **0** | 4 | `0.9999415` | feasible |
| regular 3-gon, `r = 0.999` | 3 | 0 | 3 | `0.9970030` | feasible |
| regular 4-gon, `r = 0.999` | 4 | 2 | 4 | `0.9960060` | feasible |
| regular 5-gon, `r = 0.999` | 5 | 0 | 5 | `0.9950100` | feasible |
| regular 6-gon, `r = 0.999` | 6 | 3 | 6 | `0.9940150` | feasible |
| regular 8-gon, `r = 0.999` | 8 | 4 | 8 | `0.9920279` | feasible |
| regular 12-gon, `r = 0.999` | 12 | 18 | 12 | `0.9880658` | feasible |

The rows that matter are the ones with a zero: the degree-5 lab has **no** safe
full spoke, and the two `QC = infinity` rows have **no** safe chord. Neither
refuted endpoint of §2 covers all of them; the interior of the parameter range
does.

On the regular `n`-gon the optimal common radius is exactly the crossing radius
of [CrossingChordUpperBound.md](CrossingChordUpperBound.md), and the value
`V = rⁿ` there is `|f|` at the chord's midpoint — the two notes describe the same
path on that family.

## 6. Calibration, with the packet's required negative control

`research_packet.json::negative_results` entry 19 rules that a supremum pinned
just under a threshold is informative only if the **same searcher, at the same
budget and the same degree, can push a neighbouring false statement over it.**

Adversarial hill-climbing, roots capped at modulus one, four restarts seeded from
the regular polygon and from random draws. Both searches are now complete; the
general-form run took 10054 s.

**Common-radius form, against the chord-or-origin control.**

| `n` | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|
| `sup V` (Form A-cut) | `1.00000000` | `1.00000000` | `1.00000000` | `1.00000000` | `1.00000000` | `1.00000000` | `1.00000000` | `1.00000000` |
| `sup V` (chord-or-origin, **false**) | `1.00981517` | `1.00000000` | `1.00108881` | `1.00000000` | `1.00000000` | `1.00000000` | `1.00000000` | `1.00000000` |
| control fires? | **yes** | no | **yes** | no | no | no | no | no |

**General form (`s_a` and `s_b` independent), against the Form A′ control.**

| `n` | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|
| `sup V` (Form A-cut) | `1.0000010` | `1.0000000` | `1.0000000` | `1.0000000` | `1.0000000` | `1.0000000` | `1.0000000` |
| `sup V` (Form A′, **false**) | `1.0097269` | `1.0000000` | `1.0000000` | `1.0000398` | `1.0000000` | `1.0000000` | `1.0000000` |
| control fires? | **yes** | no | no | **yes** | no | no | no |

**Read only the columns where a control fires; the rest carry no information.** A
searcher that leaves both a statement and its known-false neighbour at exactly one
has demonstrated nothing about either.

Four such columns exist across the two runs, at `n = 3, 5` and `n = 3, 6`. In
every one, Form A-cut's residual is at float noise (below `1e-8` in the
common-radius form; the `1e-6` at `n = 3` in the general form is its coarser radius
grid, i.e. inner-search truncation) while the false statement is broken by
`4.0 × 10⁻⁵` to `9.8 × 10⁻³`.

**The controls are calibrated against recorded values, not only against
themselves.** TwoSegmentContainmentReduction.md §5 records the chord-or-origin
disjunction breaking at `n = 3, 5, 6` with `V = 1.0098, 1.0012, 1.0003`. This
searcher — different code, different seeds — breaks it at `n = 3` with `1.00982`
and at `n = 5` with `1.00109`, agreeing to three digits, and misses the `n = 6`
break, whose recorded margin is `3 × 10⁻⁴` and so the smallest of the three. The
Form A′ control fires at a different pair of degrees again, `n = 3` and `n = 6`.

Two caveats stay attached, both inherited. The search is capped at degree ten. And
per `negative_results` entry 19, a reported supremum describes the basin explored,
not the space.

## 7. Claim boundary

Proved here, and elementary: the reduction of §1, the monotonicity of the arm
condition in `s` in §4, and the identification of the refuted endpoints in §2.
Exact computations: the entry radii of §3, the coverage values of §5, and every
segment maximum. Measured: the agreement with the free-hub optimum in §4 and the
calibration of §6.

Form A-cut is a **sufficient** family, like the two-segment family before it: its
failure would not refute Erdős #1041. The common-radius restriction of §4 is a
further restriction of it and could fail where the general form succeeds. Erdős
#1041 is open, and no negative result is retracted.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_truncated_spoke_chord.py mechanism
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_truncated_spoke_chord.py coverage --grid 30
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_truncated_spoke_chord.py calibrate --max-degree 4
```
