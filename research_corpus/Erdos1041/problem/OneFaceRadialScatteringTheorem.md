# Erdős 1041: the radial value-ray connector has strictly negative excess on every one-Newton-face model — the `|M| = 1` case of the tied-face metric functional, at every degree

Date: 2026-08-30.  Origin: main-loop proof (this session), independently
re-verified by a subagent (symbolic + numeric).  Checker:
`scripts/check_erdos1041_one_face_radial_scattering.py`.

## What this is and is not

The one-face MODEL is already closed in the corpus, with length free, by
straight origin spokes: `FormACutFirstNonzeroMode.md` (two contained
complete spokes for `H = Re(A z^m - z^n)`, `n >= 4`, `1 <= m < n`,
Lean-checked), carried to actual polynomials by
`NearFeketeUniqueNewtonFaceClosure.md`, with exact trinomials closed
globally by `CyclicTrinomialFiberCase.md`.  This note does NOT re-close
the one-face model and must not be cited for that.

What it proves is different and aims at the OPEN metric half of (R1)
(FRONTIER §4.3(a), capture
`cap_quick_prove_the_model_excess_inequality_ex_the_c88f4d5faf54`): a
CRITICAL-HUB connector with STRICTLY NEGATIVE renormalised excess, with
an explicit degree-uniform constant.  The origin connector has excess
exactly `0` (`QuinticStarKernelMechanics.md` §5: straight-ray excess
`-Re(h conj(u_i+u_j))`, zero at `h = 0`) and the origin mechanism is
REFUTED off the one-face stratum (`NearFeketeRadialAngularSplit.md`
Theorem 7).  A hub mechanism with a strict margin is the tied-face-ready
object: in the vocabulary of `TiedNewtonFaceMonodromyLoopSelector.md`,
the theorem below is exactly (MLS-strict) at `|M| = 1`, for every degree
and every mode — the base stratum of the tied-face metric problem, with
the margin quantified.  Scope guard: this is a statement about a specific
connector on the one-face MODEL; it neither asserts nor implies the
refuted general radial-credit form (RD) of `RadialDeficitIdentity.md`.

## Theorem (one-face radial scattering)

Let `n >= 4`, `1 <= m < n/2`, `lambda != 0`, `q = n - m`, and

```text
H(z) = z^n + lambda z^m.
```

Then there is a nonzero critical point `c*` with `Re H(c*) >= 0` such
that the two lifts through `c*` of the OUTWARD radial value ray
`{t H(c*) : t >= 1}` are contained in `{Re H >= Re H(c*)} subset
{Re H >= 0}`, meet only at `c*`, have distinct asymptotic directions
`arg c* +- pi/n` — two DISTINCT adjacent CLOSED tracts, interior tract
rays whenever `Re H(c*) > 0` (see the degeneracy remark below for the
`Re H(c*) = 0` family) — and have renormalised excesses satisfying,
PER ARM,

```text
e(arm)  <=  |c*| (pi/n - 1)  <  0,
```

hence for the pair

```text
e_i + e_j  <=  2 |c*| (pi/n - 1)  <  0.
```

Here `|c*| = (m/n)^{1/q} |lambda|^{1/q}`; the excess is
`lim (length - |z|)` along the arm, which for these arms equals the
tract-projection excess `e(alpha)` of `QuinticStarKernelMechanics.md` §5
(the difference `|z| - <z, u>` tends to `0` like
`(pi/n - theta)^{2 - 1/q}`).

On the core normalization `max(|b_1|, |b_2|) = 1` of the quintic model
this gives guaranteed pair margins

```text
m = 1:  2 (1 - pi/5) 5^{-1/4}    = 0.497117...,
m = 2:  2 (1 - pi/5) (2/5)^{1/3} = 0.547714...,
```

while the measured pair excesses are `-0.8796` and `-1.0009` (the bound
is not tight; checker section 6 tabulates nine `(n, m)` pairs).

## Proof

**Step 1 (critical orbit and the nonnegative hub).**  Nonzero critical
points satisfy `n c^{n-1} + m lambda c^{m-1} = 0`, i.e.
`c^q = -(m/n) lambda`; there are exactly `q` of them, `c_0 zeta` with
`zeta^q = 1`.  At each, `H(c) = c^m (c^q + lambda) = (q/n) lambda c^m
= -(q/m) c^n`, and since `zeta^n = zeta^m`, the orbit's critical values
are `H(c_0) zeta^m`.  As `0 < m < q`, `sum_{zeta^q = 1} zeta^m = 0`, so
the nonzero critical values SUM TO ZERO and some `c*` has
`Re H(c*) >= 0`.  (For `m >= 2` the origin is also critical with
`H(0) = 0`; it is not used.)

**Step 2 (hub-free normalization).**  For any nonzero critical `c`,
using `lambda c^m = -(n/m) c^n`:

```text
H(c y)/H(c) = F(y) := (n y^m - m y^n)/q,     F(1) = 1.
```

`F` has critical points `y = 0` (value `0`) and `y^q = 1` (values
`y^m`, on the unit circle), so the OPEN ray `(1, oo)` is free of
critical values of `F`; `F''(1) = -nm != 0`.  The two branches of
`F^{-1}([1, oo))` through `y = 1` are therefore complete, meet only at
`y = 1`, and — since `F` has real coefficients — are complex conjugates
of each other.  Along them `F` is real, starts at `1`, is locally
injective, hence strictly monotone, and is unbounded: `F` increases from
`1` to `oo`.  Consequently along the corresponding z-curves
`H = F * H(c*)`, so `Re H = F Re H(c*) >= Re H(c*) >= 0`: containment,
at level `>= Re H(c*)` throughout.

**Step 3 (polar law).**  Write the upper branch as `y = r(theta)
e^{i theta}`.  `Im F = 0` gives `n r^m sin(m theta) = m r^n
sin(n theta)`, i.e.

```text
r(theta)^q = A(theta) := (n sin(m theta))/(m sin(n theta)),
theta in (0, pi/n),   r(0+) = 1,   r -> oo  as  theta -> pi/n.
```

`A > 1` on `(0, pi/n)` because `sin t / t` is strictly decreasing.  On
the curve, `F` has the closed form `F = n r^m sin(q theta) /
(q sin(n theta)) > 0`, and monotonicity needs no inequality at all:
`|y^q| = A > 1` keeps `y` off the critical set (`y = 0`, `y^q = 1`), so
`F'(y) != 0` along the curve, and a real-valued locally-injective
continuous function on an interval is strictly monotone — increasing,
by `F(0+) = 1` and `F -> oo`.  The asymptotic directions of the two
branches are `e^{+- i pi/n}`, hence `arg c* +- pi/n` in `z` — distinct
adjacent closed tracts.  (The curve itself is independent of `lambda`;
only the scale `|c*|` depends on it.)

**Step 4 (the sine-quotient lemma).**  For `0 < y <= x < pi`:

```text
(y/x) cot y - cot x  >=  sin y / sin x - y/x.
```

Proof: `R(x) := x (cot x + sin y / sin x)` satisfies

```text
sin^2 x * R'(x) = -(x - sin x cos x) + sin y (sin x - x cos x),
```

(checker: sympy-exact); `B_0 := sin x - x cos x >= 0` on `(0, pi)`
(`B_0(0) = 0`, `B_0' = x sin x >= 0`), and

```text
(x - sin x cos x) - B_0 = (1 + cos x)(x - sin x) >= 0
```

(sympy-exact), so with `sin y <= 1`, `R' <= 0` and
`R(x) <= R(y) = y (cot y + 1)`; divide by `x`.  QED (lemma)

**Step 5 (Riccati domination).**  With `h = log r`,

```text
q h'(theta) = m cot(m theta) - n cot(n theta)
```

(differentiate `log A`).  The lemma at `(y, x) = (m theta, n theta)`,
multiplied by `n`, gives `q h' >= m (A - 1)`, and then

```text
h' >= (m/q)(r^q - 1) >= (r^q - 1)/q >= r - 1 > sinh h
```

for `r > 1`, using `r^q - 1 >= q(r - 1)` and
`(r - 1) - sinh(log r) = (r - 1)^2/(2r) > 0`.

**Step 6 (length).**  `|dy| = r sqrt(1 + h'^2) d theta` and

```text
|dy| - dr = r (sqrt(1 + h'^2) - h') d theta
          = r / (sqrt(1 + h'^2) + h') d theta
          < r / (cosh h + sinh h) d theta = d theta,
```

using `h' > sinh h` (so `sqrt(1 + h'^2) > cosh h`).  Integrating from
`0` to `theta`: `length <= (r(theta) - 1) + theta`, strictly.  Hence the
per-arm excess in y-units is `<= pi/n - 1 < 0` for `n >= 4`; multiply by
`|c*|` for z-units, and by `2` for the conjugate pair.  QED

**Degeneracy remark (subagent-located, exact).**  Inside the
hypotheses, `Re H(c*) = 0` can occur — the orbit sum vanishes AND every
critical value is purely imaginary exactly on the family
`gcd(m, q) = q/2` with `H(c_0)` imaginary, i.e. `n = 3m` (examples:
`z^6 + z^2` with all four nonzero critical values `+- 2i/(3 sqrt 3)`;
also `z^3 + z`).  There the arms run ALONG `{Re H = 0}` (contained in
the closed safe set; the asymptotic directions are tract-boundary
rays), and the excess bound is unaffected.  Whenever `Re H(c*) > 0` —
generic in `arg lambda`, and guaranteed off `n = 3m` when the orbit
values are not all imaginary — the arms are interior-tract and the ray
`{t H(c*)}` is critical-value-free by trace-maximality alone.

**Sharpness of the hypothesis (subagent-verified).**  The mode range
`m < n/2` is used ONLY in Step 1, where the true condition is
`q = (n - m)` does not divide `m` (which `m < q` implies).  Steps 2–6
hold verbatim for every `1 <= m < n` with `q` not dividing `m`
(spot-verified through `(13, 9)`).  When `q | m` the selection
genuinely fails: `z^6 - z^4` has BOTH nonzero critical values equal to
`-4/27 < 0` — no admissible hub exists.  The near-Fekete blow-up range
`m <= (n-1)/2` always satisfies `m < q`.

## Theorem (n = 3)

For `H = z^3 + lambda z` the same construction at the trace-nonnegative
critical point gives PER-ARM excess `<= (sqrt 3)/2 - 1` in y-units and
pair excess `<= (sqrt 3 - 2) |c*| < 0`.  Here the polar law closes to
`r^2 = 1/(1 - (4/3) sin^2 theta)` on `(0, pi/3)`, and the sharper bound
`r (sqrt(1 + h'^2) - h') <= cos theta` holds; it is equivalent to the
rational quartic inequality

```text
192 - 531 x + 556 x^2 - 272 x^3 + 64 x^4 >= 0,   x = sin^2 theta in [0, 3/4],
```

verified by exact Sturm (checker section 7; in fact the quartic is
POSITIVE-DEFINITE — discriminant `1872384491520 > 0`, no real roots at
all, minimum on `[0, 3/4]` equal to `P(3/4) = 12`).  The reduction is
fully rational (subagent-verified): `h'^2 = 16x(1-x)/(3-4x)^2`, so

```text
E <= cos theta  <=>  r^2 - (1-x) <= 2 sqrt(1-x) r h'
                <=>  [r^2 - (1-x)]^2 <= 4 (1-x) r^2 h'^2
                <=>  x P(x)/(3-4x)^3 >= 0,
```

with every squaring between positive quantities.  Integrating
`cos theta` over `(0, pi/3)` gives the `sqrt(3)/2` budget.  Note
`z^3 + lambda z` with `lambda > 0` sits on the degenerate family
`n = 3m` (critical values `+- 2i lambda^{3/2}/(3 sqrt 3)` for
`lambda > 0`): the closed-tract reading applies.  (The corpus's
phase-count spoke supply fails at `n = 3` by design —
`FormACutFirstNonzeroMode.md` records the sharp degree threshold — so
at `n = 3` this hub connector is not competing with a landed origin
closure.)

## Remarks

1. **The outward radial ray is a new carrier.**  Every landed value-ray
   use is inward (`s f(c)`, `0 <= s <= 1`) or additive
   (`H(c) + s`, `G_0(V_0) - i s`); the outward-scaling ray
   `{t H(c) : t >= 1}` appears nowhere else in this directory.  At any
   trace-maximal hub with `D = Re H(c*) > 0` it is critical-value-free
   FOR FREE: a critical value on it would have real part `t D > D`,
   contradicting maximality.  (On the tangent stratum `D = 0` the ray
   degenerates to the imaginary axis; there the exact certificate of
   `QuinticTangentOrbitExactCertificate.md` takes over.)
2. **Docking — and a hard scope boundary (same-day, measured).**  In
   `TiedNewtonFaceMonodromyLoopSelector.md`'s frame the theorem is
   (MLS-strict) restricted to one active mode, with the systolic
   constant quantified as `2 |c*| (pi/n - 1)`.  It is the base case of
   the excess obligation of FRONTIER §4.3(a).  DO NOT extend the
   RADIAL carrier to the mixed core: `TraceMaxRadialExcessLaw.md`
   (2026-08-30) measures an OPEN failure pocket near the tangent orbit
   (`sup E_radial = +0.358`; the ray is blocked by a collinear double
   foreign value), while the corpus's RIGHTWARD carrier keeps a uniform
   measured margin (`sup = -0.0363`) on the whole core.  On the
   one-face stratum itself the radial excess is exactly constant per
   line and equals the rightward minimum there — this theorem's
   territory is safe; the mixed-core (EX) attempt must use the
   rightward arms.
3. **Renormalizer equivalence.**  `lim(len - |z|) = lim(len - <z, u>)`
   for these arms since `|z| (arg z - arg u)^2 -> 0` at rate
   `(pi/n - theta)^{2 - 1/q}`, `q >= 2`; so the bound speaks the same
   excess language as `QuinticStarKernelMechanics.md` §5 and
   `RadialDeficitIdentity.md` §2 (`kappa_k`).
4. **What transfer still needs.**  Converting a negative MODEL excess
   into an actual-polynomial length bound is exactly the open
   obligation (R1)(b): the `o(rho)` in `2 + rho(e_i + e_j) + o(rho)` is
   unquantified at real scale (`RadialDeficitIdentity.md` claim
   boundary; `ReciprocalNewtonExpansion.md` R5 requires the curvature
   and transverse jet to be retained).  This note supplies the strict
   first-order margin, uniform in the mode and the degree — not the
   remainder.

## Claim boundary

Ordinary proved mathematics (main-loop; the two symbolic identities and
the `n = 3` quartic are sympy/Sturm-exact in the checker; the excess
quadratures are 25-dps mpmath).  Model-level only; NOT a closure of
one-face polynomials (occupied, see header); NOT the parent theorem; no
claim about tied faces beyond the `|M| = 1` base case.  PRIORITY
CAVEAT: no literature search; the polar law and the
`h' > sinh h` mechanism are classical-flavoured; claim "new to this
directory" only.
