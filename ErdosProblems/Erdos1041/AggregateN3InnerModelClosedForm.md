# Erdős 1041: the AGG3 radial constant in closed form — `D(0) = 3E(1/4) - (9/4)K(1/4) - 1/2 > (3pi-8)/16`, the wall is the minimum, and the matched asymptotics is an exact reduction

Date: 2026-08-30.  Origin: subagent derivation (matched asymptotics /
exact reduction, three independent instruments), main-loop
re-verification and one subagent-claim correction (the campaign checker
DOES exist on disk — the agent's contrary claim was dropped after a
direct listing; and the C-conversion factor is settled by measurement
below, correcting the agent's `1/2` to `2`).  Checker:
`scripts/check_erdos1041_aggregate_n3_inner_model.py`.

Serves: FRONTIER §4.2's theorem-shaped target ("the matched-asymptotic
derivation of `C(phase) > 0`", capture
`cap_quick_derive_the_agg3_radial_constant_c_phase_3876935d5231`), the
owner campaign note `AggregateN3GateFreeCampaign.md` (whose addendum's
inner model this makes exact and corrects), and the instrument law of
FRONTIER §4.6 (a THIRD float-defect direction is exhibited).

## 1. Exact reductions (identities, not approximations)

**(R1) Normal form.**  Every monic cubic with nonzero critical-point
split reduces by translation + complex scaling to

```text
f_s(z) = z^3 - 3 s^2 z - 1,     s in C,
```

and `Sigma_c L(c) / (4 R_MEC)` is invariant.  So AGG3 is a TWO-real-
parameter problem (`s^2`, modulo the order-6 group `s^2 -> omega s^2`,
conjugation) — the quadratic coefficient is pure gauge, the scale is
pure gauge.  Hubs `+-s`, values `v_pm = f(+-s) = -1 -+ 2 s^3` (exact;
in the campaign's `eps`-frame this reads
`v_pm = -1 +- (2/3) eps b_1 s`, correcting the factor-2 slip
`(4/3)` at `AggregateN3GateFreeCampaign.md:174`).

**(R2) Exact inner equation.**  The arm equations FACTOR exactly:

```text
f_s(z) = v_+ (1 - t)  <=>  (z - s)^2 (z + 2s) = (1 + 2 s^3) t,
f_s(z) = v_- (1 - t)  <=>  (z + s)^2 (z - 2s) = (1 - 2 s^3) t,
```

so with `z = s w` BOTH hubs solve the single inner problem

```text
g(w) := w^3 - 3w + 2 = sigma,      sigma on a fixed-argument ray,
```

with `arg sigma = phi_+ = arg((1+2s^3)/s^3)` for hub `+` and
`phi_- = arg(-(1-2s^3)/s^3)` for hub `-`; as `s -> 0` these tend to
`phi` and `phi + pi`, `phi := arg(1/s^3) = -3 arg s`.  There is NO
matching error: the reduction is an identity at every `t in [0, 1]`.

**(R3) Single-valued parametrization.**  `w = 2 cos(2 nu/3)` gives
`g(w) = 2 + 2 cos(2 nu) = 4 cos^2 nu`, i.e. `kappa := cos nu =
sqrt(sigma)/2 = xi e^{i phi/2}` — a GLOBALLY single-valued branch label
(the reason the instrument of §5 cannot sheet-jump).  The two arms of
hub `w = 1` are `w_k = 2 cos(alpha + 4 pi k/3)`, `k = 0, 1`,
`alpha = (2/3) arccos kappa`, and the total arm length is the explicit
1-D integral

```text
Lambda(P, phi) = int_0^{sqrt P / 2}
    (4/3) (|sin alpha| + |sin(alpha + 4pi/3)|) / |sin nu_0| d xi,
Sigma_c L(c) = |s| [ Lambda(P_+, phi_+) + Lambda(P_-, phi_-) ],
P_pm = |1 +- 2 s^3| / |s|^3.
```

## 2. The deficit law and the closed form at the wall

Expanding `Lambda(P, phi) = 2 P^{1/3} + A(phi) + O(P^{-1/3})` (the
renormaliser integrates exactly:
`int sinh(3m/2) cosh^{-1/3}(3m/2) dm = cosh^{2/3}(3m/2)`), and using
`|s| P_pm^{1/3} = 1 + O(|s|^3)`, `R_MEC = 1 + O(|s|^2)`:

```text
4 R_MEC - Sigma_c L(c) = 2 |s| D(phi) + O(|s|^2),
D(phi) = -( A(phi) + A(phi + pi) ) / 2.
```

`D` is even, `pi`-periodic, analytic except at the SADDLE-CONNECTION
WALL `phi == 0 (mod pi)` (where the middle arm hits the sibling
critical point, `sigma = g(-1) = 4`).  At the wall both integrals
collapse to elementary/elliptic form:

```text
A(0) = 1 + Ecal,   A(pi) = 2 Ecal,
Ecal = int_0^oo [ sqrt(4 cosh^2 m - 1) - 2 cosh m ] dm
     = - int_0^{pi/2} d theta / ( 2 + sqrt(3 + sin^2 theta) )
     = (3/2) K - 2 E        (elliptic integrals at parameter m = 1/4),

D(0) = -(1 + 3 Ecal)/2 = 3 E - (9/4) K - 1/2 = 0.10944832968994037...
```

**Positivity, two-line elementary proof.**
`sqrt(3 + sin^2 theta) <= 2` gives `-Ecal >= (pi/2)/4 = pi/8 > 1/3`,
hence

```text
D(0) = (3(-Ecal) - 1)/2  >=  (3 pi - 8)/16  =  0.0890486... > 0,
```

with the companion upper bound `D(0) <= 3 pi (2 - sqrt 3)/4 - 1/2 =
0.13134...` from `sqrt(3 + sin^2) >= sqrt 3`.

**The wall is the global minimum**, with a square-root cusp:
`D(phi) = D(0) + c sqrt(phi) + O(phi)`,
`c = 2 sqrt 2 pi^{3/2} / (sqrt 3 Gamma(1/4)^2) = 0.6917...`; the sweep
(checker section 4) gives `min D = D(0)`, `max D = D(pi/2) =
0.6080213...`, symmetric to `1e-14`.  So on the near-radial family the
AGG3 ratio approaches 1 STRICTLY FROM BELOW at scale `|s|`, with the
worst phase at the saddle-connection wall and the deficit there proved
positive in closed form.

**Global-in-phase positivity — PROVED 2026-08-30.**
`AggregateN3PshUniformityClosure.md` closes the analytic step that was
still owed here.  The exact arm reduction gives the locally uniform
wall-free expansion

```text
Sigma_c L(c) = 4 - 2|s|D(-3 arg s) + O(|s|^2).
```

The first tangent of a subharmonic function has nonnegative angular
operator `a+a''`; with `a(theta)=-2D(-3theta)` this is exactly
`D+9D''<=0`.  A Wronskian comparison with
`h(phi)=D(0)cos((phi-pi/2)/3)/cos(pi/6)` then proves

```text
D(phi) >= h(phi) >= D(0) >= (3pi-8)/16 > 0
```

on every phase.  Thus the wall is the global minimum by proof, and the
former numerical psh-uniformity row is superseded by that owner note.

## 3. The campaign-frame conversion (measured, settling the factor)

In `AggregateN3GateFreeCampaign.md`'s frame (`f = z^3 + eps(b_2 z^2 +
b_1 z) - 1`, `s^2 = -eps b_1/3 + O(eps^2)`):

```text
C(phase) = 2 sqrt(|b_1|/3) * D(phi),        phi = -3 arg s,
```

verified by DIRECT measurement (checker section 7: `eps = 1e-8`,
`theta = 0.4 pi`, measured `C = 0.4007` vs `2 sqrt(0.7/3) D = 0.4025`;
the `1/2`-factor alternative is off by 4x).  Consequences for the
recorded campaign rows:

- the addendum's `D = 0.375, 0.489` sit EXACTLY on the derived curve,
  at `phi/pi = 0.07059, 0.17101` (checker, bisection) — the campaign's
  arm-resolved instrument was measuring the right function;
- the headline constant `C = 0.0705(1)` is NOT on the curve: with the
  measured conversion, `min_phase C = 2 sqrt(0.7/3) D(0) = 0.1057` at
  `|b_1| = 0.7`.  The subagent's three-instrument adjudication locates
  the `0.0705` as a WALL-ADJACENT ARTIFACT: at the exact wall the
  middle arm hits the sibling critical point, a real-arithmetic Newton
  march jumps branches, and the reported deficit is depressed — pushed
  further, the same instrument reports `D < 0`, i.e. a FALSE AGG3
  violation (`D_march = -0.18` at `|s| = 1e-6` where the exact-identity
  instrument gives `+0.1212`).  This is a THIRD instrument-defect
  direction — branch-jump at a FOREIGN critical value on the ray —
  complementing the under-report (NEG 32/42/49) and over-report
  (campaign Result 3) directions; it is exactly the `value_gap`
  degeneracy of FRONTIER §4.6, and the single-valued `nu`-label of (R3)
  is the admissible instrument there.

## 4. Claim boundary

PROVED (ordinary mathematics, checker-replayed): the exact reductions
(R1)–(R3); the deficit law with `D(phi) = -(A(phi)+A(phi+pi))/2`; the
closed form and the elementary positivity bounds at the wall; the
sqrt-cusp form.  PROVED in the source-current companion
`AggregateN3PshUniformityClosure.md`: `D+9D''<=0`, the explicit comparison
barrier, all-phase positivity, and the wall's global-minimum property.
COMPUTED: the original phase sweep, the conversion measurement, and the
artifact adjudication table (subagent scratch, session record).  NOT
claimed: (AGG) at n = 3 beyond
the near-radial regime (though (R1) reduces the global question to two
real parameters modulo a finite group — recorded as the natural
certified-computation target), anything at n >= 4 (where AGG is FALSE),
or the parent theorem.  PRIORITY CAVEAT: no literature search; the
trinomial-cubic normal form and elliptic evaluations are
classical-flavoured; claim "new to this directory" only.
