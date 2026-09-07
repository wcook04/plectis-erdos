# Erdős 1041: the minimal-hub two-arm budget is refuted; critical-value envelopes cannot repair it

Date: 2026-08-29.  Checker:
`scripts/check_erdos1041_minimal_hub_arm_budget_refutation.py` (all claims
replay; PASS).  Evidence class: 50-dps mpmath reconstruction with a certified
inscribed-polyline lower bound, cross-checked by an independent float64 DOP853
integration; no exact rational certificate is claimed (same class as
`ClaimLRefutation.md`).

## Result A (refutation of the universal row `L(c*) < 2`)

> There is a monic degree-4 polynomial with all roots in the CLOSED unit disk
> whose strict-argmin first-merge hub `c*` has two-arm inverse-ray length
> `L(c*) >= 2.000146 > 2`; shrinking by any factor in `(1 - 7e-5, 1)` gives a
> configuration with all roots in the OPEN unit disk and `L(c*) > 2` still.

Consequently the open row of `FirstMergeReductionState.md`,

```text
| **`L(c*) < 2`** | **OPEN — this is the whole problem** |
```

is **false as a universal statement**: the argmin-hub two-arm connector is not
a valid witness for Erdős 1041 in general.  The parent theorem is untouched
(at the witness the runner-up hub's arms already join two roots at length
`1.956 < 2`; see Result C), but the first-merge lane must route through hub
*selection*, not through the argmin hub.

### The witness and the unmade inference

The configuration is the stored `ComponentDepthRefutation.md` degree-4 moduli
witness (`HubModuliReduction.md` chart `f(rho zeta)/f(c*) = 1 - G(zeta)`,
`G = zeta^4 - beta_3 zeta^3 - beta_2 zeta^2`):

```text
beta_2 = 0x1.8c5640e53fa34p-9  + 0x1.69a016b3f0c4ap-9  i
beta_3 = -0x1.6fa15252d066ep-5 - 0x1.3895293ffc3ebp-6  i
```

i.e. the model polynomial `ftil(z) = z^4 - beta_3 z^3 - beta_2 z^2 - 1` with
hub exactly at `0`, hub value exactly `-1`, and roots (50 dps, 20 shown)

```text
z_1 =  0.98967983345462363642 - 0.00394448452754675668 i
z_2 = -1.01214154926450268760 - 0.00564692736452371643 i
z_3 = -0.01035817083836329958 + 0.99434586214545651239 i
z_4 = -0.01205684216118225070 - 1.00383298178867501140 i
```

`ComponentDepthRefutation.md` already recorded `L(c*) >= 2.00214647` and the
circumradius ratio `L(c*)/(2R) >= 1.00016203`, but then rescaled by the
origin-anchored radius `max|z_k| = 1.0122` (obtaining `1.978 < 2`) and left
the row open.  The unmade move is a **translation**: centring at the
minimum-enclosing-circle centre before rescaling.  The MEC of the four roots
is determined by the diameter pair `(z_1, z_2)`:

```text
R_MEC  = 1.0009110533188161373      (interior margins +0.00177, +0.00187)
L(c*)  = 2.002149188  (DOP853, rtol 1e-12; endpoint landing 1.1e-15)
       >= 2.0019682   (inscribed polyline, 1602 vertices on the arms,
                       every vertex on the fiber to residual 5.3e-51)
L(c*) / R_MEC >= 2.00014599...
```

Translating by the MEC centre and scaling by `1/R_MEC` preserves the critical
structure (values scale uniformly, so the argmin hub, its strictness, and the
arms are preserved), puts every root in the closed unit disk (the diameter
pair on the boundary), and leaves the normalized level
`mu' = R_MEC^{-4} = 0.99636 < 1`, so the arms stay inside the open unit
lemniscate.  The two-arm length is `>= 2.000146`.  A further shrink by
`1 - eps`, `eps < 7.29e-5`, moves all roots strictly inside the disk while the
arm length stays above `2`.  QED

Strictness bookkeeping: the hub is a simple critical point
(`f''(0) = -2 beta_2 != 0`), the argmin is strict at 50 dps (the other two
critical values exceed `mu` by `1.868e-7` and `7.057e-7` relative), and the
two arms land on the two roots `z_3, z_4` (endpoint error `1.1e-15`; the
merging pair is NOT the MEC diameter pair — the budget is broken by
spectator-determined MEC geometry).

## Result B (conjecture NF and every critical-value-slack envelope refuted)

During this session the following replacement for the refuted sharp bound was
proposed and named **NF**: with `D = prod_k |f(c_k)|` over all critical
points,

```text
L(c*) <= 2 * D^{1/(n(n-1))}
```

equivalently `L(c*) <= (2/n^{1/(n-1)}) |disc f|^{1/(n(n-1))}` (Lemma 1 below),
equivalently the margin form `n(n-1) log(L/(2 mu^{1/n})) <= S`,
`S = sum_k log(|f(c_k)|/mu)`.  NF is exactly tight on the radial family
`(z-tau)^n - lambda`, strictly weaker than the refuted sharp bound, and
implies Erdős 1041 outright through Hadamard (`D <= 1` on the closed disk,
strict inside).  Moreover NF is **extremal**: inside the family
`L <= 2 mu^{1/n} exp(theta S/(n-1))`, the member `theta = 1/n` is NF, and any
`theta > 1/n` no longer implies the parent through Hadamard (take `S` large at
fixed `D`), so NF is the *weakest* Hadamard-sufficient member.

**NF is false.**  At the witness above the three critical values tie to
`7.06e-7` relative, so `S = 8.93e-7` and

```text
2 * D^{1/12} = 2.000000148760  <  2.0019682 <= L(c*),
```

margin `1.97e-3`.  By the extremality remark this refutes not just NF but the
entire critical-value-slack family: **the critical-value moduli vector cannot
separate this configuration from the radial equality family** — all values
tie, exactly as at `z^4 - lambda`, yet the arms exceed the radial budget by
`0.107%`.  Any arm envelope through critical-value moduli alone, calibrated to
equality on the radial family, is dead.  (This sharpens
`HubModuliReduction.md` §5, which proves `L(beta)` plurisubharmonic so its
extremum lives on the tie locus: the tie-locus supremum is not only `> 1` in
the sharp normalisation, it exceeds the whole slack family.)

**Exact Gaussian-rational second witness (falsifier follow-up, same session).**
The independent adversarial search then produced a rational-coefficient
witness of the same phenomenon: roots

```text
-1/100 + 99/100 i,   99/100,   -101/100 - 1/100 i,   -1/100 - i
```

(monic quartic with Gaussian-rational coefficients, e.g. constant term
`-99/100 - 495099/50000000 i`).  There `mu = 0.990049750625`, the three
critical values tie to `2.52e-7` relative (`S = 5.04e-7`), and two independent
instruments agree to ten digits on `L(c*) = 1.9956279006`, giving
`sharp = 1.00031163` and NF margin `M = +0.0037384` (`+0.0037273` already from
the inscribed-chord lower bound `1.9956261`).  Being exactly rational, this
witness is the natural target for the interval/Lean certificate upgrade.  (It
kills the envelope family only; its MEC diameter is `~2.00002`, so it does not
by itself break the closed-disk arm budget — Result A's witness remains the
carrier for that.)

What any surviving envelope must use: data that separates this witness from
the radial family — the saddle *positions* (here `|c_2 - c*| = 0.0305`,
`|c_3 - c*| = 0.0671`, versus `0` for the radial family), the root radii, or
hub-resolved data (Result C).

## Result C (redirect: hub selection survives)

At the same witness the two runner-up hubs have

```text
hub_2: |w| = 1.000000186843,  L = 1.956184654   (joins z_1, z_3)
hub_3: |w| = 1.000000705715,  L = 1.946673310   (joins z_4, z_2)
```

both below budget, and even below `2 mu^{1/n}`.  So the statement

```text
min over admissible hubs c of  L(c)  <  2        (roots in the open disk)
```

— the `min_c L(c) <= 2 mu^{1/n}` form is `ComponentDepthRefutation.md`'s
"cleanest open statement" — survives this witness with room (`0.973` in sharp
units), and every root of the witness is reached by some hub's arm pair.  The
refutation therefore *redirects* the metric lane from the argmin hub to hub
selection: the corpus's open producers `critical_point_selection_with_
inverse_ray_length_control` and COVER are now the canonical carriers, and the
selection cannot be by minimal critical value (Result A), nor filtered through
any critical-value-moduli functional (Result B).

## Proved collaterals (independent of the refutations)

The following were proved en route and remain true and useful.

### Lemma 1 (fiber derivative product identity)

For every complex `w`:  `prod_{f(z)=w} f'(z) = n^n prod_{k=1}^{n-1}(f(c_k)-w)`.

Proof.  `Res(f-w, f') = lc(f')^{deg(f-w)} prod_{f'(c)=0}(f(c)-w)
= n^n prod_k (f(c_k)-w)`, and exchanging arguments
`Res(f-w, f') = (-1)^{n(n-1)} lc(f-w)^{deg f'} prod_{f(z)=w} f'(z)
= prod_{f(z)=w} f'(z)` (`n(n-1)` even, `f - w` monic).  QED

At `w = 0` this gives `n^n prod_k |f(c_k)| = |disc f|`; on any disk carrying
all `n` inverse branches `f_j` (e.g. `D(0,mu)`),

```text
prod_j |f_j'(w)| = 1 / ( n^n prod_k |f(c_k) - w| ),
```

and minimality of `mu` dominates every kernel factor by the radial model's
(`|w_k - w| >= mu - t` on `|w| = t`), with equality iff all values sit at `v`.
Replayed in the checker to residual `5.3e-51`.

### Lemma 2 (weighted-mean form of the arm functional)

With `u(z) = sum_k log|z - c_k| - ((n-1)/n) sum_j log|z - a_j|` (so
`|f'| = n |f|^{(n-1)/n} e^u`, `u(inf) = 0`), level-parametrising each arm:

```text
L(c*) = (1/n) int_0^mu t^{-(n-1)/n} ( e^{-u(z_a(t))} + e^{-u(z_b(t))} ) dt,
```

and the constant `2` calibration `(1/n) int_0^mu t^{-(n-1)/n} 2 dt
= 2 mu^{1/n}`.  Any arm bound is a weighted-mean bound on `e^{-u}` along the
arms.

### Proposition 3 (GM-damped quadratic consumer)

For each arm, with `J = int_0^mu |f_arm'(t vhat)|^2 prod_j |f_j'(t vhat)|^{-1/n} dt`
(the quadratic arm energy damped by the fiber geometric mean; by Lemma 1 the
damping equals `n prod_k |f(c_k) - t vhat|^{1/n}`),

```text
L_arm^2  <=  mu^{1/n} * J,
```

with equality throughout on the radial family.  Proof: Cauchy–Schwarz against
the weight `(mu-t)^{-(n-1)/n}` (whose integral is `n mu^{1/n}`), then
`(mu-t)^{(n-1)/n} <= prod_k |f(c_k) - t vhat|^{1/n}` by minimality of `mu`,
then Lemma 1.  Integrability at the saddle end: `|f_arm'|^2 ~ C (mu-t)^{-1}`
against the damping's `(mu-t)^{1/n}` factor.  QED.  This is a concrete
instance of the weighted-`L^2` shape requested by
`FirstMergeReductionState.md`; Results A–B locate exactly where its right side
must exceed `mu^{1/n}` (the tie locus), so any future use must couple `J` to
position data, not to critical values.

### Proposition 4 (localisation of any surviving envelope)

`MinimalHubWindowJoin.md` Theorem 1 gives `L(c*) <= Psi_n(T*/mu) mu^{1/n}`
(`Psi_n(y) = y^{1/n} sqrt(2 log((y+1)/(y-1)))`, decreasing; `T*` the two-root
persistence level), so `L(c*) < 2 mu^{1/n}` whenever `T*/mu >= x_n*`
(`Psi_n(x_n*) = 2`; `x_4* = 1.4784372`).  Hence every violation of the
two-arm budget — including Result A's — lives in the thin-window shell
`T*/mu < x_n*`, and (Result B) carries an all-tie critical-value vector there.
The enemy profile is now exact: thin window, all values tied, saddles
position-separated (`d_pt/R_MEC ~ 0.03`), MEC determined by spectator roots.

## Consequences for the packet

- `FirstMergeReductionState.md` row `L(c*) < 2`: flip from OPEN to REFUTED
  (this note); the live metric obligation becomes `min_c L(c) < 2` over
  admissible hubs (equivalently the corpus's selection/COVER producers).
- `negative_results`: add Result A (universal argmin-arm budget false in the
  open disk) and Result B (critical-value-slack envelope family false,
  including the geometric-mean/discriminant form `L <= (2/n^{1/(n-1)})
  |disc f|^{1/(n(n-1))}`).
- `ComponentDepthRefutation.md`: its witness upgrades from "scale-invariant
  ratio > 1" to a genuine open-disk refutation via MEC centring; its
  "cleanest open statement" (min-hub form) is now the canonical row and
  survives this witness at `0.973`.
- The guarded adversarial campaign of this session (DOP853 instrument,
  cluster-aware step caps, shell exclusion `d_pt < 0.02 max|a_j|`) observed
  the min-hub form comfortably satisfied on every seeded family (`0.55--0.98`
  in sharp units at `n = 3..8`, including tie shells); it adversarially
  targeted the argmin-hub ratio, not the min-hub ratio, so the min-hub row
  remains open-but-unviolated and untested at adversarial scale.

## Addendum 2 (same day): Result A upgrades to degree 5 with 97x the margin

MEC-centring the DEGREE-5 tie-locus witness (hex betas below in Addendum 1;
chart `ftil = z^5 - b4 z^4 - b3 z^3 - b2 z^2 - 1`, hub at `0`, chart arms
`L(c*) = 2.057343275393654508` certified at 50 dps by two independent
instruments) gives, at 50 dps (main-loop verification):

```text
R_MEC = 1.021393477405696164   (circumcircle of roots {0,2,3}; the MEC is
                                TRIPLE-determined, interior margins
                                +0.0247518 and +0.0796025 -- far better
                                conditioned than the degree-4 diameter case)
L(c*) / R_MEC = 2.01425143287505     mu' = R_MEC^{-5} = 0.899569245
```

So there is a monic QUINTIC with all roots in the closed unit disk whose
strict-argmin first-merge hub has two-arm length `2.0142514 > 2`, arms inside
`{|f| <= 0.8996} subset {|f| < 1}`; shrinking by `1 - eps`, `eps <
7.0753e-3`, keeps the violation with all roots in the OPEN disk.  The margin
is `~97x` the degree-4 witness's (`7.08e-3` vs `7.29e-5`), making this the
preferred interval/Lean certificate target for Result A.  At the same
configuration the straight spokes at the same hub are SHORTER than the
descent arms (`1.8126 < 2.0143`) and `min_c L(c) = 1.525` at a runner-up hub
(degree-5 assembly report) -- Result C's redirect stands at degree 5 too.

## Addendum (same day): falsifier final report — tie-locus law, corrected suprema

The independent adversarial engine (written from scratch against this
session's instruments; 50-dps certificates with inscribed-chord lower bounds
throughout) closed with four upgrades, replayed live before landing:

1. **Tie-locus law.**  On the all-tie locus `|w_1| = .. = |w_{n-1}| = mu` one
   has `D = mu^{n-1}` exactly, so NF degenerates *identically* into the
   refuted sharp bound; and along weighted rays `beta_2 = eps^2 B_2,
   beta_3 = eps B_3` into the degenerate extremal `z^4 - lambda`, the length
   excess `log(sharp)` is first order in `eps` (measured slope `0.982 -> 1`)
   while the slack `S` is fourth order (slope `4.0000` over ten halvings).
   The Fekete credit can never pay the first-order debt; `sup M =
   n(n-1) log(sup sharp)` by `HubModuliReduction.md` §5's plurisubharmonic
   maximum principle.
2. **The stored moduli suprema are basin-pinned.**  `HubModuliReduction.md`'s
   records `sup L/2 = 1.00107` (`n=4`) and `1.00438` (`n=5`) are undershoots
   by factors `6.1` and `6.5`: certified strictly-minimal-hub witnesses reach

   ```text
   n=4:  sharp = 1.0065472440,  L = 2.0130945 (mu = 1),  M_chord = +0.0783108
         beta_2 = 0x1.9b73f0ef75d0cp-11 - 0x1.f9f51c318c348p-13 i
         beta_3 = 0x1.0bddcc73f5e5cp-2  - 0x1.c3dec89f5b0e8p-4  i
   n=5:  sharp = 1.0286716377,  L = 2.0573433 (mu = 1),  M_chord = +0.5640967
         beta_2 = -0x1.2183ccac6f670p-10 + 0x1.50ddf5037d660p-11 i
         beta_3 =  0x1.370006ed7cdcfp-4  - 0x1.59fe20382e38cp-8  i
         beta_4 = -0x1.d66cd4b049c9fp-2  + 0x1.0a1a32e370c42p-2  i
   ```

   (chart of `HubModuliReduction.md`, hub pinned at `zeta = 0`; endpoint
   landings `~5e-43`; caveat: both hubs sit near a second saddle,
   `d_pt = 0.0019` and `0.0119`, i.e. inside this note's excluded numeric
   shell — the certificates rest on the falsifier's exact-fiber branch
   tracking plus strict 50-dps argmin margins `>= 1e-9`, not on the DOP853
   sweep instrument.)  This is the corpus's own adversarial-supremum lesson
   (`negative_results` 19) recurring inside the moduli engine.
3. **The violating set is open with substantial measure**: at the true argmin
   on a converged mesh, `M > 0` in 60/60 samples at relative
   `beta`-perturbations `1e-4 .. 3e-3`, 50/60 at `1e-2`, 19/60 at `1e-1`.
4. **Separated saddles produce no violations found**: every optimizer run in
   root coordinates converged back to collapsed critical-point clusters
   (best separated-saddle attempt `M = +0.0381` at saddle gap `6e-4`).  The
   violation mechanism lives on the near-degenerate saddle stratum.

Instrument findings worth keeping: float64 cannot arbitrate the argmin inside
sub-`1e-16` ties (two fake `M > 0` candidates died at 50 dps with the argmin
at a different critical point), and a `slack` computed as
`min_k |w_k| - |w_hub|` over ALL `k` is `<= 0` by construction — the margin
must be over `k != hub`.

## Claim boundary

- Results A and B are computational refutations at the stated evidence class
  (50-dps reconstruction; polyline lower bound with on-fiber vertices at
  residual `5e-51`; two independent integrators agreeing to `1e-9`; MEC by
  diameter pair with interior margins `+1.8e-3`).  An exact rational
  certificate (interval arithmetic over the hex-float moduli) is a follow-up,
  not done here.
- Result A refutes the universal two-arm row, not the parent theorem and not
  the first-merge topology (containment and the merge structure are intact).
- Result C is evidence at one witness plus the campaign, not a theorem; the
  min-hub form remains open.
- Lemmas 1–2 and Propositions 3–4 are proved (Proposition 4 by citation to
  the proved window machinery).
