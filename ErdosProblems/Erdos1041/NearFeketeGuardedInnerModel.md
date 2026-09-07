# Erdős 1041: the wall-guarded inner model, and the minimum form refuted off the wall

Status, 2026-09-05. Four things. (i) Two proved lemmas that fix what the
saddle-connection wall guard is actually testing: the value-plane test
`|Im V_i − Im V_j| < g` is NECESSARY for a saddle connection and not
sufficient, and the sharp test is the geometric clearance of the traced arms
from the other critical points. (ii) The wall limit, computed both ways: on the
wall the ambiguous hub's `A_j` is set-valued with exactly two values, the two
continuations through the two outgoing arms of the hub its arm runs into, and
they coincide with the two one-sided limits; the lower one is negative, so
`(MIN-inner)` survives ON the wall in the lower-continuation reading. (iii) The
wall-guarded suprema `M_n^{(g)}`, which do NOT tend to zero as `g → 0`: at
degree five they are already positive at `g = 10^-3` and `g = 10^-4` and only
turn negative at `g = 10^-2`, and at degree six they are positive at
`g = 10^-4` by a larger margin. (iv) The consequence: a wall-separated degree-five
configuration at which every `A_j` is strictly positive, carried to actual monic
quintics with all roots strictly inside the open unit disc, at which
`min_c L(c) > 2R`. **`(MIN)` is refuted again, this time off the wall.** Erdős
#1041 is NOT refuted, and section 5 exhibits the same family at `c → 1` where
every descending branch pair exceeds length `2` while the origin's two straight
spokes are contained and total below `2`.

This note is a successor to `NearFeketeInnerModelWidening.md`, whose §5.4
degree-five witness the conductor withdrew on 2026-09-05 as a wall specimen.
**That withdrawal was correct for that specimen**, and §2 below reproves it by
computing the specimen's two continuations. What was not correct is the
inference drawn from it, that the positive sign is a wall artefact: the positive
region is a ONE-SIDED collar of the wall which extends to genuine off-wall
distance, and random perturbation, which crosses the wall in about half of its
draws, reads that collar as instability.

## 0. Authority boundary

* The object refuted is `(MIN) : min over critical points c with |f(c)| < 1 of
  L(c) <= 2R`, the conclusion of the open producer
  `critical_point_selection_with_inverse_ray_length_control`. Erdős #1041 is
  untouched and every polynomial below satisfies it.
* `NearFeketeInnerModelWidening.md` Propositions 1, 2, 4 and Corollary 5 are
  used, not re-derived. Its §5.4 withdrawal is confirmed for its own specimen
  and its scope corrected.
* `NearFeketeCuspLaw.md` §1 (Theorem A) is untouched.
* Every number below is recomputed in this pass by
  `scripts/check_erdos1041_guarded_inner_model.py`; nothing is inherited.
* Evidence class of the refutation: **finite computational evidence at the
  strength of `negative_results` entry 73**, i.e. three branch integrators that
  share no code, exact-coefficient input at 80–120 mpmath digits, a chord-sum
  audit, and an inner/outer cross-check over a factor of eight in `rho`. The
  arm-length continuation itself is NOT formalised and the specimen is NOT
  exactly certified. It is a LEAD of refutation strength, not a proof.

## 1. What the wall guard tests, and what it should test

Recall the inner model. Fix `Z_1, ..., Z_{n-1}` with `sum_j Z_j = 0` and
`max_j |Z_j| = 1`, put `Q'(Z) = n prod_j (Z - Z_j)` and `Q(Z) = int_0^Z Q'`, so
`Q(0) = 0`. Write `V_j = Q(Z_j)`. The two outgoing arms of hub `j` are the two
lifts of the horizontal ray `Q = V_j + s`, `s >= 0`, leaving `Z_j`, and

```text
A_j = -2|Z_j| + int over both arms of (1 - cos chi) ds,        K_j = -A_j,
(MIN-inner)   min_j A_j <= 0,   equivalently   max_j K_j >= 0.
```

> **Lemma 1 (renormalised length).** Let `Gamma_j` be the union of the two
> outgoing arms of hub `j`, a properly embedded curve through `Z_j` whose two
> ends are asymptotically radial in two of the `n` directions `omega^n = 1`.
> Then `A_j = lim_{T -> oo} ( length(Gamma_j ∩ {|Z| <= T}) - 2T )`.
>
> *Proof.* Along an arm `d|Z|/ds_arc = cos chi`, so for the arm traced to
> `|Z| = T`, `length - (T - |Z_j|) = int (1 - cos chi) ds`. Summing the two arms
> gives `length(Gamma_j ∩ B_T) - 2T = int_{both}(1 - cos chi) ds - 2|Z_j|`. ∎

So `(MIN-inner)` says: **some hub's outgoing arm pair is no longer than a
straight line, renormalised**, since a straight line has renormalised length `0`
(its length inside `B_T` is `2T` exactly, and `2 sqrt(T^2 - d^2) -> 2T` for a
line at distance `d`). Three immediate consequences, all proved.

> **Lemma 2 (base point).** If the two arms escape in directions
> `omega_a, omega_b` and the renormalisation is taken about a point `p` instead
> of the origin, then `A_j^{(p)} = A_j^{(0)} + <p, omega_a + omega_b>`.
>
> *Proof.* The circle `|Z - p| = T` meets an asymptotically radial end in
> direction `omega` at arclength `T + <p, omega> + o(1)` measured from the
> origin's circle. Add the two ends. ∎

The base point is therefore load-bearing: it is the centroid of the critical
points, which in the outer problem is the centre of the near-Fekete root
configuration. `A_j` is base-point free exactly when `omega_b = -omega_a`.

> **Lemma 3 (origin criterion).** `A_j >= -2 dist(0, Gamma_j) >= -2|Z_j|`, and
> if the origin lies ON `Gamma_j` then `A_j >= 0`, with equality iff both arms
> are radial rays.
>
> *Proof.* For `P in Gamma_j`, each end has length at least `T - |P|` inside
> `B_T`, so `length - 2T >= -2|P|`; minimise over `P`. If `0 in Gamma_j` take
> `P = 0`. Equality forces each end to be a radius. ∎

Lemma 3 is the exact mechanism behind `NearFeketeInnerModelWidening.md`
Proposition 6: at `Z = (-1, 0, 1)`, `n = 4`, the origin hub has both arms on the
imaginary axis, so `A = 0` by equality in Lemma 3.

Now the guard. An arm of hub `j` follows `Q = V_j + s` with `s` real and
increasing, so:

> **Lemma 4 (the value-plane test is necessary, not sufficient).** If an arm of
> hub `j` reaches the critical point `Z_i`, then `V_i - V_j` is real and
> strictly positive. The converse is false.
>
> *Proof of the implication.* `Q(Z_i) = V_j + s` for the arrival parameter
> `s > 0`. *Failure of the converse.* `Q^{-1}(V_i)` has `n - 1` points; the arm
> of hub `j` passes through the value `V_i` at SOME preimage, which need not be
> `Z_i`. At the guarded maximiser of §4 the tightest ordered pair is
> `(i, j) = (4, 3)`, with `Re V_4 > Re V_3` and
> `|Im V_4 - Im V_3| = 1.214e-4` of the value scale, so the mandated test at
> `g = 10^-3` rejects the configuration; yet neither arm of hub `3` ever comes
> closer than `1.44e-2` to any other critical point, and the same holds at every
> hub. ∎

Two guards therefore, and the note reports both:

```text
(G1)  value-plane, MANDATED:  reject if some ordered pair has Re V_i > Re V_j
      and |Im V_i - Im V_j| < g * max_k |V_k|;  also reject |Z_i - Z_j| < 1e-3.
(G2)  geometric, SHARP:  reject if some traced arm passes within kappa of a
      critical point other than its own hub.
```

`(G1)` is conservative: it rejects a superset of the configurations `(G2)`
rejects, and by Lemma 4 the rejected extra configurations are not saddle
connections at all. Every positive value reported below is reported with BOTH
numbers.

*Calibration.* On the withdrawn §5.4 specimen `(G1)` gives `2.04e-12` and `(G2)`
gives `7.6e-6` — both fire, and the arrival distance to hub `1` is `7.6e-6`,
i.e. the arm really does run into the hub. On `negative_results` entry 73's
blown-up saddle-wall quartic `(G1)` gives `6.4e-7` and `(G2)` gives `8.9e-4`:
that family also sits close to the wall, which is unsurprising since its
`delta = 1e-6` is exactly a small transversal displacement off the real (fully
degenerate) wall. This is recorded as an observation. It does not retract entry
73, whose configuration is off the wall and whose arithmetic is exact.

## 2. The wall limit, and the reading of `(MIN)` that survives on the wall

Take the withdrawn degree-five specimen `Z` of
`NearFeketeInnerModelWidening.md` §5.4. Hub `2`'s arm runs into hub `1`:
`Re V_1 - Re V_2 = 3.3219e-06 > 0` and `|Im V_1 - Im V_2| = 2.04e-12` of the
value scale. Its arm arrives at `Z_1` — the Newton continuation along
`Q = V_2 + tau`, `tau in (0, s*]`, ends `7.6e-6` from `Z_1`, which is the
resolution of the arrival, not a clearance.

On the wall `L(c_2)` is not a branch pair: the branch ends at a critical point,
not at a root. `A_2` is then **set-valued with exactly two values**, one per
outgoing arm of hub `1`. Both are computed here, by surgery (arc to the saddle,
then the two continuations) and independently as the two one-sided limits of
`A_2` along a transversal `Z_1 -> Z_1 + it`, `Z_2 -> Z_2 - it`, which moves
`Im(V_1 - V_2)` at rate `6.49e-4` per unit `t`:

| relative `Im` gap | `A_1` | `A_2` | `A_3` | `A_4` | `min_j A_j` |
|---|---|---|---|---|---|
| `+1e-6` | `+0.021870` | `+0.018248` | `+0.021718` | `+0.022724` | `+0.018248` |
| `+1e-7` | `+0.022636` | `+0.021154` | `+0.022621` | `+0.022724` | `+0.021154` |
| `+1e-8` | `+0.022715` | `+0.022309` | `+0.022714` | `+0.022724` | `+0.022309` |
| `-1e-8` | `+0.022733` | `-0.753487` | `+0.022734` | `+0.022724` | `-0.753487` |
| `-1e-7` | `+0.022812` | `-0.754790` | `+0.022827` | `+0.022724` | `-0.754790` |
| `-1e-6` | `+0.023629` | `-0.758552` | `+0.023781` | `+0.022724` | `-0.758552` |

(`NearFeketeInnerModelWidening.md` §5.4 also records that "hub `3`'s arm passes
hub `4` at an imaginary gap of `1.1e-4`". By Lemma 4 that is a value-plane
reading only: the geometric clearance of hub `3`'s arms at this configuration is
`1.34e-2`, so hub `3` is not near a saddle connection and `A_3` is
single-valued. The same for hub `1`, clearance `1.77e-2`, and hub `4`, clearance
`4.73e-1`.)

Both columns converge at rate `sqrt(gap)`, and the limits are

```text
A_2^+ = +0.022910,        A_2^- = -0.752866,
```

against the surgery values `+0.022910` and `-0.752866` (agreement `5e-6`, which
is the arrival resolution). Only `A_2` jumps; `A_1`, `A_3`, `A_4` are continuous
across the wall, as they must be, since only hub `2`'s arm is saddle-connected.

**The reading that survives.** `(MIN)`'s hub set is "critical points `c` with
`|f(c)| < 1`", and admissibility is vacuous in the cusp
(`NearFeketeInnerModelWidening.md` §4), so no hub can be discarded on
admissibility. On the wall the correct object is therefore

```text
(MIN-wall)   min_j  min over continuations of  A_j   <=   0,
```

the lower continuation being the lower one-sided limit. In that reading the
degree-five wall specimen gives `-0.752866 < 0` and does not refute anything,
and the degree-four configuration `Z = (-1, 0, 1)` gives `0` at every hub (both
continuations through the origin hub are radial, so both give `A = 0` by Lemma
3), so it is an equality case and not a violation. The runner-up reading — drop
the ambiguous hub and take the minimum over the rest — does NOT survive: at the
degree-five specimen the unambiguous hubs are `1`, `3`, `4` with
`A = +0.022724, +0.022724, +0.022724`, all positive. **Only the
lower-continuation reading saves `(MIN)` on the wall.**

And it does not save it off the wall, which is §4.

## 3. The wall-guarded suprema

```text
M_n^{(g)} := sup over configurations passing (G1) at width g of  min_j A_j.
```

Deterministic Nelder-Mead over the `2(n-2)`-real-parameter widened model
(`Z_1, ..., Z_{n-2}` free, `Z_{n-1} = -sum`, then normalised), four annealing
step scales, seeded restarts, guard violations returned as a penalised value so
the simplex is pushed back inside.

| `n` | `g = 1e-2` | `g = 1e-3` | `g = 1e-4` |
|---|---|---|---|
| 4 | `-0.082220` | `-0.026541` | `-0.008447` |
| 5 | `-0.034194` | **`+0.0022916`** | **`+0.0382254`** |
| 6 | `-0.004935` | `-0.093174` (weak) | **`+0.0614192`** |

Every entry is a LOWER BOUND for the supremum, being search output. The true
`M_n^{(g)}` is non-decreasing as `g` decreases, since a smaller guard admits
more configurations; the `n = 6`, `g = 10^-3` entry violates that and is
therefore simply an unconverged row, not a measurement — the honest reading of
that line is `M_6^{(10^-3)} >= M_6^{(10^-2)} >= -0.004935`. The three positive
entries are the ones that matter, and each was verified independently (§4).
Reading:

* **`M_n^{(g)}` does NOT tend to `0` as `g -> 0`.** At degree five it is
  positive already at `g = 10^-3`, i.e. at the width the corpus's own instrument
  discipline mandates, and grows as the guard is loosened toward the wall; at
  degree six it is positive at `g = 10^-4` by a larger margin, `+0.0614`. The
  hypothesis in the brief — that the guarded supremum degenerates to `0` and the
  min form holds strictly off the wall — is FALSE at degrees five and six, and
  the failure is not a degree-five accident.
* The degree-five `g = 10^-3` maximiser has hub separation `0.1185` (118 times
  the collision guard) and geometric clearance `3.99e-2`; the degree-five
  `g = 10^-4` maximiser has hub separation `0.1021` and clearance `1.44e-2`; the
  degree-six `g = 10^-4` maximiser has separation `0.0954` and clearance
  `2.60e-2`. None is anywhere near a saddle connection under `(G2)`.
* At the degree-five `g = 10^-4` maximiser **all four `A_j` agree to seven digits**
  (`+0.0382255, +0.0382255, +0.0382254, +0.0382254`), the signature of an
  interior maximin stationary point rather than a guard-boundary artefact; the
  `(G1)` gap there relaxes to `1.214e-4`, i.e. the guard is not active at the
  optimum.
* At degree four the guarded climbs converge on the degenerate real family
  around `Z = (-1, 0, 1)` and stay negative at `g = 10^-2`, consistent with
  `NearFeketeInnerModelWidening.md` §5.1's `M_4 = 0` being a supremum over WALL
  configurations.

The degree-five `g = 10^-4` maximiser, normalised (`sum Z_j = 0`,
`max_j |Z_j| = 1`):

```text
Z_1 = -0.484542215051725 + 0.051442066839730 i      |Z_1| = 0.487265271088
Z_2 = -0.479022587265705 - 0.050481780679960 i      |Z_2| = 0.481675252936
Z_3 = +0.999999981121244 - 0.000194312921754 i      |Z_3| = 1.000000000000
Z_4 = -0.036435178803814 - 0.000765973238017 i      |Z_4| = 0.036443229405

V   = (-0.020900146 + 0.000367744 i, -0.020807641 - 0.000209271 i,
       -0.912889033 - 0.000080599 i, +0.000749324 + 0.000030189 i)
A   = (+0.038225466, +0.038225512, +0.038225410, +0.038225436)
min_j A_j            = +0.0382254105
hub separation       = 0.102073
(G1) rel Im gap      = 1.2136e-04
(G2) arm clearances  = (2.60e-2, 2.18e-2, 1.44e-2, 4.44e-1)
escape sectors       = ((1,2), (4,3), (0,1), (4,1))     all distinct
```

Instrument spread over tracing radii `|Z| = 60, 300` and tolerances
`1e-11, 1e-13`: `1.5e-9`. A second integrator (scipy DOP853, no shared code with
the Cash-Karp tracer) reproduces every `A_j` to `1.1e-12`.

The degree-six `g = 10^-4` maximiser, found by an independent deterministic
sweep-and-polish (2000 guarded draws, seed 15, then Nelder-Mead), is
geometrically cleaner still:

```text
Z_1 = -0.264444437439377 + 0.129793133069512 i
Z_2 = -0.436636733906751 - 0.498530096588616 i
Z_3 = -0.028065563413444 + 0.111176154500578 i
Z_4 = -0.270323173438702 + 0.225004663575095 i
Z_5 = +0.999469908198274 + 0.032556145443431 i

A   = (+0.084566418, +0.118041383, +0.061634115, +0.061419246, +0.104618679)
min_j A_j            = +0.0614192457       (every hub positive)
hub separation       = 0.095393
(G1) rel Im gap      = 1.0001e-04
(G2) arm clearances  = (3.68e-2, 1.06e-1, 2.36e-1, 2.60e-2, 4.02e-2)
```

## 4. The refutation of `(MIN)`, off the wall

Carry the `g = 10^-4` maximiser to actual polynomials by
`f'(z) = 5 prod_j (z - rho Z_j)`, `f(0) = -c^5`, `c = 9/10`, built from the
polynomial's OWN exact coefficients at 80 mpmath digits.

| `rho` | `max_k |a_k|` | `2R` (upper) | `min_c L(c)` | `min_c L(c) - 2R` | `/rho` |
|---|---|---|---|---|---|
| `0.02` | `0.900109481` | `1.800135318` | `1.800587397` | `+4.5208e-04` | `+0.0226040` |
| `0.01` | `0.900027206` | `1.800033628` | `1.800338236` | `+3.0461e-04` | `+0.0304608` |
| `0.005` | `0.900006781` | `1.800008382` | `1.800180155` | `+1.7177e-04` | `+0.0343546` |
| `0.0025` | `0.900001693` | `1.800002092` | `1.800092825` | `+9.0732e-05` | `+0.0362929` |

`min_c L(c) > 2R` at every row, with every root strictly inside the open unit
disc, `|f(c)| = 0.59049 < 1` at all four critical points (so all four are
admissible), every branch endpoint within `2.2e-14` of a root, and the two
branches of every hub reaching DISTINCT roots.

The degree-six maximiser gives the same thing with a larger margin, on actual
monic sextics `f'(z) = 6 prod_j (z - rho Z_j)`, `f(0) = -c^6`, `c = 9/10`:

| `rho` | `max_k |a_k|` | `2R` (upper) | `min_c L(c)` | `min_c L(c) - 2R` | `/rho` |
|---|---|---|---|---|---|
| `0.02` | `0.900057167` | `1.800111579` | `1.801143347` | `+1.0318e-03` | `+0.0515884` |
| `0.01` | `0.900014117` | `1.800027890` | `1.800592937` | `+5.6505e-04` | `+0.0565047` |
| `0.005` | `0.900003508` | `1.800006972` | `1.800301783` | `+2.9481e-04` | `+0.0589621` |

`(min_c L(c) - 2R)/rho = A_min - 0.4915 rho` to four digits at every row, and
Richardson gives `+0.0614195` against the inner model's `+0.0614192`, an
agreement of `3e-7`. All five hubs are admissible, all five branch pairs reach
distinct roots, every endpoint is within `1.9e-14` of a root.

Five things make the sign safe, and they are the five the directory's six
retracted counterexamples failed.

* **The wall guard, in both forms.** `(G1)` at `1.21e-4`, `(G2)` at `1.44e-2`.
  The configuration is not saddle-connected and is not within numerical reach of
  a saddle connection. The same climb under `(G1)` at the full mandated
  `g = 10^-3` still returns a positive value, `+0.0022916`, whose actual quintic
  at `rho = 0.0025` gives `min_c L(c) - 2R = +2.79e-06`.
* **`R` is used in the safe direction.** `R` is `max_k |a_k - o|` for an
  exhibited centre `o` from an exact pairs-and-triples minimum enclosing circle,
  hence an UPPER bound; `min_c L(c) > 2R_upper >= 2R_true`.
* **The `rho` scaling matches the inner prediction.** `(min_c L(c) - 2R)/rho`
  runs `+0.022604, +0.030461, +0.034355, +0.036293` over a factor of eight in
  `rho`, i.e. `A_min - 0.776 rho` to four digits at every row, and Richardson on
  the last two rows gives `+0.038231` against the inner model's `+0.0382254`.
  Two instruments that share no code, one integrating in the `Q` plane to
  `|Z| = 300` and one integrating the descending branch of the actual polynomial
  to a root, agree on a nontrivial extrapolated constant to `6e-6`.
* **The chord-sum test passes at every hub.** A chord sum never exceeds the
  length of the path it samples, so a reported length below its own chord sum is
  proof of a sheet hop. At `rho = 0.005` the four hubs report lengths
  `1.8001924, 1.8001802, 1.8001877, 1.8001877` against chord sums
  `1.8001355, 1.8001802, 1.8001877, 1.8001877`.
* **The launch point does not move the answer.** A descending branch is started
  at `z(u_0) = c + alpha u_0` with `|alpha| = sqrt(|v|/|A_2|)` enormous inside a
  tight critical cluster, and the note's own §5.4 records that a bad `u_0` puts
  the launch further from the hub than the whole cluster. At `rho = 0.005`,
  `min_c L(c) = 1.800180155063` at `u_0 = 10^-11` and `10^-15` and at step caps
  `hmax = 2e-2 u` and `5e-3 u`, spread `4.3e-14`.
* **It is an open condition, and openness was tested by moving `Z`, not by
  moving `(c, rho)`.** Gaussian perturbations of `Z` (seed 31, renormalised,
  20 draws per scale): at `eps = 1e-4`, `20/20` keep `min_j A_j > 0` and `19/20`
  also keep `(G2) > 10^-2`; at `eps = 3e-4`, `12/20`; at `eps = 1e-3`, `3/20`;
  at `eps = 3e-3`, `1/20`; at `eps = 10^-2`, `0/20`. The positive set is open
  with diameter of order `10^-3` in the normalised `Z` space, which is small but
  is an open set, not a wall.

**Why the earlier withdrawal saw instability.** The positive region is a
ONE-SIDED collar of the saddle-connection wall. A random Gaussian perturbation
of an on-wall configuration crosses the wall in about half its draws, and across
the wall `A_2` jumps from `+0.0229` to `-0.7529` (§2). A perturbation table that
reports "median negative" is therefore reporting the wall crossing, not
instability of the positive branch. Moving along the collar instead — which is
what a guarded climb does — the positive value grows from `+0.0229` at the wall
to `+0.0382` at an interior maximin point with clearance `1.44e-2`.

## 5. The near-Fekete shell: every branch pair longer than 2

Nothing forces `c = 9/10`. Push the same configuration to `c = 9999/10000`,
`rho = 1/50`, still monic of degree five, coefficients exact at 120 digits:

```text
max_k |a_k|             = 0.999998424336917   < 1
|f(c_j)|                = 0.999500102911      < 1 at all four hubs
branch pair lengths     = 2.000583245, 2.000405278, 2.000515252, 2.000515340
min_c L(c)              = 2.000405278363      >  2
```

All four descending branch pairs exceed `2`. Every one of the ten root chords
leaves the lemniscate (`max |f|` on the chord is at least `1.010807`). And yet
Erdős #1041 holds on this polynomial by the ORIGIN hub: all five radial spokes
from `0` to the roots are contained and the two shortest total
`1.999641 < 2`.

That containment is not sampled, it is certified. Write
`f(z) = z^n + sum_{j=0}^{n-1} p_j z^j`. For a root `a` and `t in [0,1]`,
`a^n = -sum_j p_j a^j`, so

```text
f(ta) = p_0 (1 - t^n) + sum_{j=1}^{n-1} p_j (t^j - t^n) a^j,
```

an identity; with `|a| <= 1` and `0 <= t <= 1` every weight is at most `1`, so

> **Corollary O (coefficient-sum origin certificate).** Let `f` be monic of
> degree `n` with all roots in the OPEN unit disc and
> `S := sum_{j=0}^{n-1} |p_j| < 1`. Then `|f| <= S < 1` on every
> origin-to-root segment, so any two roots are joined through the origin inside
> `{|f| < 1}`, and the two roots of smallest modulus give a path of length
> `|a_(1)| + |a_(2)| <= 2 max_k |a_k| < 2`.
>
> *Proof.* `|f(ta)| <= |p_0|(1 - t^n) + sum_{j>=1} |p_j| |t^j - t^n| |a|^j <= S`
> by the displayed identity, since `|a| <= 1`, `1 - t^n <= 1` and
> `|t^j - t^n| <= 1` on `[0,1]`. ∎

This is the coefficient-sum special case of `BernsteinOriginSpokeCertificate.md`
Theorem C (`|B_j(a)| <= 1` for all `j`), since
`|B_j(a)| <= sum_{k<=j} |p_k| binom(j,k)/binom(n,k) <= sum_k |p_k|`; it is
recorded here because it is a pure inequality on the exhibited coefficients and
therefore certifies the shell specimen without any tracer. For the specimen
above `sum_{j=0}^{4} |p_j| = 0.9999921244 < 1`, with margin `7.9e-6` against
120-digit arithmetic.

So this specimen separates two mechanisms that the corpus has treated as
interchangeable:

```text
straight origin spokes  1.999641  <  2  <  2.000405  descending branch pair.
```

Curved Newton branches are the LONGER object in the near-Fekete shell. Any
producer that reaches Erdős #1041 through the descending branch pair is paying
a first-order price it does not have to pay, and in this family that price is
exactly what breaks it.

## 6. The proof attempt, and what it killed

The task was to prove `max_j K_j >= 0`. Section 4 says the statement is false,
so what follows is a record of the routes, so that nobody re-runs them.

* **Summation over hubs.** Dead before this note: `sum_j A_j` has no sign
  (`negative_results` entry 73, replayed in `NearFeketeInnerModelWidening.md`
  §6). Confirmed here under the guard: `sum_j A_j` reaches `+0.0329` at `(G1)`
  gap `1.22e-4` in the collar, so entry 73's finding is not a wall artefact
  either.
* **Selection by the outermost hub** (`|Z_j| = 1`, the natural candidate since
  `A_j >= -2|Z_j|` is weakest there). REFUTED. Over 1000 guarded random
  configurations at `n = 3..7`, `A` at the outermost hub is positive in
  `1%`–`10%` of draws, reaching `+0.53`; the deterministic lattice in the
  checker reaches `+0.2246`.
* **Selection by the innermost hub.** REFUTED, `+0.1658` on the same lattice
  (and `A_j > 0` at the innermost hub in `43%`–`57%` of random draws at
  `n >= 4`).
* **Selection by the largest `Re V_j`.** This is the one hub that can never be
  saddle-connected, by Lemma 4, so it is the only selector immune to the wall.
  REFUTED: `+0.0430` on the lattice, and `+0.0382` at the §3 maximiser.
* **Gauss–Bonnet / argument principle over the arm tree.** Not attempted to
  completion. The identity `d arg T = -Im((Q''/Q') dZ)` and Lemma 1 make
  `A_j` a renormalised length rather than a total turning, and the natural
  global object — the total renormalised length of `Q^{-1}(line)`, which is
  `sum_i E_i(c)` over the `n` disjoint level curves at height `c` — is NOT
  sign-definite either: it is `0` for `Q = Z^n` at `c = 0` (the `n` straight
  lines through the origin) and negative for `c != 0` there — at `n = 2` the
  level curve is the hyperbola `xy = c/2`, whose renormalised length is
  `-1.62 sqrt(c/2)` by an elementary quadrature — while the component through
  `Z = 0` at the level `c = 0` always has `E >= 0` by Lemma 3, so the sum
  competes against itself. A proof of `(MIN-inner)` cannot come from any symmetric
  aggregate: §4 exhibits a configuration where every hub is positive at once,
  so no selection rule whatsoever can work.
* **Variational argument "the maximum is attained only on the wall".** FALSE.
  The degree-five `g = 10^-4` maximiser is an interior maximin stationary point
  at which all four `A_j` are equal to seven digits, with clearance `1.44e-2`.

What survives as proved, and is landed here: Lemmas 1–4.

## 7. Claim boundary

* **Proved.** Lemma 1 (renormalised-length reading), Lemma 2 (base-point law),
  Lemma 3 (origin criterion, and `A_j >= -2 dist(0, Gamma_j)`), Lemma 4 (the
  value-plane wall test is necessary, not sufficient — the implication is
  proved, the failure of the converse is exhibited), Corollary O (the
  coefficient-sum origin certificate; a special case of
  `BernsteinOriginSpokeCertificate.md` Theorem C, not new, but the form that
  certifies §5 without a tracer).
* **Refuted, by finite computation with a stated margin, at the evidence
  strength of `negative_results` entry 73.** `(MIN-inner)` and hence `(MIN)`,
  at degree five AND degree six, at configurations that pass BOTH wall guards.
  At degree five the margin is
  `min_c L(c) - 2R = +4.52e-04` at `rho = 1/50` (degree six: `+1.03e-03` at the
  same `rho`), against an instrument spread
  of `1.5e-9` in the inner model and `1e-12` between the outer integrators, with
  all roots strictly inside the open unit disc, all four hubs admissible, every
  branch endpoint within `2.2e-14` of a root, distinct root pairs at every hub,
  and the chord-sum test passing at every hub. **NOT exactly certified.** The
  certification route is the one entry 73 did not take either: Rouché discs for
  the roots and critical points, plus an interval-arithmetic enclosure of the
  branch-length ODE. Until that is done this is a LEAD of refutation strength.
* **Computed.** The `M_n^{(g)}` table; the two one-sided limits and the two
  continuations at the wall specimen (agreeing to `5e-6`); the perturbation
  tables; the shell row at `c = 9999/10000`; the selector refutations.
* **Not established.** The exact values of `M_5` and `M_6`; the sign of
  `M_4^{(g)}` for small `g` (the searches reach `-0.008447` at `g = 10^-4` and
  are consistent with `M_4 = 0` as a supremum, per
  `NearFeketeInnerModelWidening.md` §5.1, but do not decide it); the sign of
  `M_6^{(g)}` at `g = 10^-3` and `10^-2`; whether the positive region persists
  at every degree `n >= 5`; any claim that Erdős #1041 is false.
* **Superseded.** `NearFeketeInnerModelWidening.md` §5.4's boxed sentence "the
  guarded state of `(MIN)` in the widened model is ... strictly negative in
  every wall-guarded configuration found at `n = 4, 5`" is false at `n = 5` and
  at `n = 6`. The withdrawal of that note's own specimen stands; the
  generalisation drawn from it does not. Its §5.2 conjecture that `M_n < 0`
  strictly for `n >= 5` while `M_4 = 0`, argued from the real-axis
  local-extremum parity, is also false: the parity argument is about REAL
  configurations, which are wall configurations, and the positive region is not
  real.
* **Consumers to update.** `critical_point_selection_with_inverse_ray_length_control`
  is dead in the min form as well as the sum form, and this time off the wall.
  Any consumer reading "the min statement stands" from the 2026-09-05 conductor
  audit needs this note's §4.

## 8. Replay

```bash
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_guarded_inner_model.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_guarded_inner_model.py --part wall
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_guarded_inner_model.py --part guarded
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_guarded_inner_model.py --part refute
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_guarded_inner_model.py --part shell
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_guarded_inner_model.py --part selectors
```

Parts: `wall`, `guarded`, `refute`, `shell`, `selectors`. The script is stdlib
plus numpy plus mpmath; the inner tracer and the outer tracer are both adaptive
Cash-Karp RK45 written out inside it, arc length is carried as an integrated ODE
state and never as a chord sum, and no random number generator is used, so a
failure is reproducible. It prints one JSON line carrying `status` and
`evidence_class` and exits `0`.
