# Erdős 1041: DEPTH-ALL is false, and the length budget does not split per branch

Status: one exact witness, one rigorous lower bound, one robustness measurement.
2026-08-24. This note **refutes** the componentwise conjecture that
[LemniscateCapacityBudget.md](LemniscateCapacityBudget.md) proposes as the
hub-free statement that would settle Erdős #1041. The standing obligation
`min_c L(c) <= 2R` is **untouched** — it holds at the witness, with room.
Erdős #1041 remains open.

## 1. What is refuted

At the first-merge level `mu = min_k |f(c_k)|` every component of `{|f| < mu}`
holds exactly one root, and `f` maps it conformally onto `D_mu`. The depth

```text
Delta_j = max over theta of  length{ z : f(z) = t e^{i theta}, t in [0, mu] }  ending at z_j
```

carries no hub selection and no pair selection, and satisfies
`L(c*) <= Delta_a + Delta_b`. So

> **DEPTH-ALL.** `Delta_j <= R` for every `j`  ⟹  `L(c*) <= 2R < 2`  ⟹  Erdős #1041.

It is *exactly* tight on both equality families — every monic quadratic, and
`z^n - r^n` — which is what made it attractive, and is exactly the trap
`negative_results` entry 17 names: **equality on `z^n - r^n` is what makes a
bound look canonical, and is not evidence.**

## 2. The witness

Three Gaussian rationals of denominator `1000`:

```text
a_1 =  99/100,        a_2 = -1/2 + (43/50) i,        a_3 = -497/1000 - (171/200) i
```

with `|a_j|^2 = 9801/10000`, `1237/1250`, `489017/500000` — every one exactly
below one, so **all roots lie in the open unit disk**. The triangle is acute
(exact rational test), so its minimum enclosing circle **is** the circumcircle
and

```text
R^2 = 64030749341959853/65166346729000000   exactly,     R = 0.991248640647713…
```

That matters: an approximate smallest enclosing circle *inflates* `R`, which
sits in the denominator, and would flatter the conjecture — `negative_results`
entry 34 records Badoiu–Clarkson returning `1.0000724` where the true radius was
`0.99999985`. Here `R` is exact.

The minimal critical value is `mu = 0.973950491450026…`, so
`mu^(1/3) = 0.991240322583947… < R`: the Fekete deficit is a hair,
`R/mu^(1/3) = 1.0000084`. At `theta = arg f(c*)` the three inverse rays have

| branch ends at | chord sum / `R` |
|---|---|
| `a_1` | `0.929917…` |
| `a_2` | `0.963510…` |
| `a_3` | **`1.007129199984958…`** |

**`Delta_3 > R`. DEPTH-ALL is false at degree three.**

## 3. Why the number is a lower bound, not an estimate

The figure quoted is a **chord sum** over `1500`–`4000` points located on the
branch at 50–60 digits. An inscribed polygon never exceeds the arclength, so
`1.0071292 <= Delta_3 / R` is a *rigorous lower bound*, and the true ratio is
larger. This closes the failure mode the directory has been bitten by four
times: every recorded integrator fault here — the `f(z(u)) = v(1-u^m)` scale
truncation, the `sigma < eps_mach` collapse, the principal-branch `n`-th root,
the inflated MEC (`negative_results` 24, 34) — **under-reports**, and so does a
chord sum. All the known biases run the same way, and they run *against* this
refutation rather than for it.

The parametrisation is the second half of that: `s = 1 - t/mu = v^2` makes the
branch **linear** in `v` at the hub, where a uniform grid in `t` resolves the
square-root approach only as `sqrt`. Three independent arms agree —
Gauss–Legendre on a geometric mesh in `v` (float64) `1.0061239555` on the nearby
float configuration, a 60 000-step chord sum `1.00612396`, and mpmath at 60 dps
`1.00612397319989306`.

## 4. The content: the budget is a PAIR budget

The violating branch is **one of the two that merge at `c*`** — not an artifact
of the maximum over `theta`, and `theta` is exactly `arg f(c*)`. Its partner is
short, and the pair survives:

```text
Delta_2 + Delta_3 = 1.953394…   against   2R = 1.982497…      L(c*)/2R = 0.98532
```

So the two branches **compensate**: one exceeds `R` by 0.71%, the other falls
short by 3.6%. This is `negative_results` entry 21 — *"the exact charge identity
does not split into separately nonnegative pieces … cancellation must couple
endpoint deficit and curvature"* — reappearing one level up, now about
**length** rather than charge, and now with an exact witness. Any future
componentwise, per-branch, or per-root allocation of the length budget is
eliminated by this witness, whatever normalisation it uses, because the failure
is not a near-miss in the normalising constant: the long branch also beats the
other natural scale at this level, `mu^(1/n)`, at ratio `1.0071377`.

## 5. It is robust, which the earlier refutations of this shape were not

`negative_results` entry 29 attaches a caveat to its `1.0042` violation: the two
smallest critical values agree to `2.3e-9`, and *"the violation dies under a
1e-3 perturbation (0/12)"*. This one does not.

| perturbation | still violating | max ratio |
|---|---|---|
| `1e-4` | 24/24 | `1.008553` |
| `1e-3` | 18/24 | `1.008225` |
| `1e-2` | 4/24 | `1.004331` |
| `3e-2` | 1/24 | `1.011573` |

The violating set is **open with substantial measure**, not a tie-tolerant
corner. The witness is also not the extreme of its own family: rounding the
underlying float configuration to denominator `1000` *raised* the ratio from
`1.006124` to `1.007129`.

## 6. Why it was missed, and the instrument lesson

[`scripts/check_erdos1041_component_depth.py`](scripts/check_erdos1041_component_depth.py)
returns `1.00492` on this very configuration — **already above one**. It detects
the violation. What it never did was look here: its hill-climb seeds roots from
`standard_normal * 0.6`, i.e. at modulus about `0.6`, with 2 restarts of 18
steps, and the violating set sits in the near-Fekete shell at modulus `0.99`.
That is `negative_results` entry 19 word for word — *a supremum pinned just under
a threshold is one basin* — and it is the second time in two days that the basin,
not the bound, explained a pin. The instrument's own recorded worst value,
`Delta/R = 1.000000 attained at n = 2 where equality is proved`, is exactly what
a search that never enters the shell reports.

Two mechanical contributors, both under-reporting, on top of the seeding: a
`sin^2` mesh with 200 chord steps, and an iterative minimum enclosing circle
that returns `0.9923007` here against the exact `0.9912486`.

## 7. What survives

* `min_c L(c) <= 2R`, the standing obligation **as stated** — a minimum over
  admissible hubs — is untouched and holds here at `0.98532`.
* ~~`L(c*) <= 2R` at the minimal hub is untouched and holds here.~~ **Retracted
  the same day: see §8. It holds at THIS witness, and it is false at degree
  four.**
* The near-Fekete half — `kappa_n > 0`, now proved at every degree on the limit
  model by [ConeBoundMonotoneFunctional.md](ConeBoundMonotoneFunctional.md) and
  [TurningLengthBound.md](TurningLengthBound.md) — is untouched: it is a
  statement about the **pair**, and the pair is what this witness leaves alone.
* What dies is the hope of a hub-free componentwise route. `Delta_a + Delta_b`
  is not a usable majorant of `L(c*)`, because each summand is not individually
  bounded by `R`.

Two consequences worth stating. First, `min_c L(c) <= 2R` is now the *only*
recorded survivor at this level, and it is a genuinely coupled statement: the
proof must produce the cancellation between the two branches, not bound them
separately. Second, the sibling strong form `min_c L(c) <= 2 mu^{1/n}` — with
the minimum over hubs, which `negative_results` entry 29 does *not* refute,
since it reports `0.9608` at that witness's runner-up hub — is now the cleanest
open statement in this directory: it has no circumradius, no minimum enclosing
circle and no unit disk in it, it is exact on both equality families, and with
Fekete (`mu^{1/n} <= R`) it implies the obligation. It is untested at scale.

## 8. The same lesson one step further: `L(c*) <= 2R` is false at degree four

Searching the affine moduli space of
[HubModuliReduction.md](HubModuliReduction.md) — where a hub is `n-2` complex
parameters `beta` and admissibility is an explicit inequality — turns up a
degree-four configuration at which the obligation fails **at the minimal hub**.

Pinned as exact IEEE-754 hexadecimal, since the margin is `1.6e-4`:

```text
beta_2 = 0x1.8c5640e53fa34p-9  + 0x1.69a016b3f0c4ap-9  i
beta_3 = -0x1.6fa15252d066ep-5 - 0x1.3895293ffc3ebp-6  i
```

i.e. `G(zeta) = zeta^4 - beta_3 zeta^3 - beta_2 zeta^2`, whose four roots of
`G = 1`, rescaled by `1/max_k|z_k|` so that they lie in the closed unit disk
(the statement is scale invariant), are a perturbed square. At 50 dps, with an
exact-form minimum enclosing circle and the chord sum again a **rigorous lower
bound**:

```text
                          unscaled            after scaling to max|z_k| = 1
mu                        0.99999999999999866  0.952813605747859
R                         1.00091105331881554  0.988888833349971
L(c*)  >=                 2.00214647079466592  1.978036621855795

        L(c*)/2R           >=  1.00016203   (6000 vertices)   <-- ABOVE ONE
        L(c*)/(2 mu^{1/4}) >=  1.00107324
        min over admissible hubs / 2R  =  0.97245              <-- survives
```

Both ratios are scale invariant; the receipt runs the scaled form with 1200
vertices and returns `1.0001309`, lower than the 6000-vertex `1.0001620` exactly
as a coarser inscribed polygon must be. Stable to ten digits across four mesh
depths and reproduced by the independent root-coordinate engine. The runner-up
critical value is larger by `1.868e-7` relative. The two branches land on distinct roots (separation
`1.998`).

**So the minimum over admissible hubs is not a convenience of the argument; it
is the statement.** `research_packet.json`'s claim ceiling already words the
obligation with that minimum, and this witness is what the wording is buying:
`negative_results` entry 23 says of the level condition that *"what the
discriminant/Fekete sandwich supplies is a bound at the MINIMUM-critical hub"*,
and entry 29 says its refutation of the strong form leaves *"the scale-normalized
2R completion untouched"*. Both readings suggest the minimal hub is the safe one.
It is not — at this configuration the Fekete deficit `R/mu^{1/4} = 1.00091` is
**smaller** than the strong-form excess `1.00107`, so the deficit does not cover
it, and only the runner-up hub does.

The mechanism is the one §5 of `HubModuliReduction.md` predicts: the violation
sits at a critical-value near-tie (`1.9e-7` relative), which is exactly where the
plurisubharmonic maximum principle puts the extremum of `L(c*)`. Both witnesses
in this note are near-ties — `2.5e-5` at degree three, `1.9e-7` at degree four.

## Claim boundary

Exact: the witness, its moduli, the acute test, `R^2`, and the assertion that
every quoted branch length is a lower bound. Computed at 50–60 dps and
reproducible: `mu`, the chord sums, the pair ratio. Measured, not proved: the
robustness table, and that the maximum over `theta` sits at `arg f(c*)`.

Not established: any statement about `min_c L(c) <= 2R` with the minimum over
admissible hubs, which neither elimination touches and which survives at both
witnesses; any supremum for `Delta_j/R`; anything at degrees above four.
**Erdős #1041 remains open.**

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_component_depth_refutation.py
```
