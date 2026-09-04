# Erdős 1041: a finite-capacity mixed connector beyond Bernstein and J2

## Status

This note gives an exact actual-polynomial neighbourhood theorem around the
mixed-mode witness of `QuinticBernsteinJ2MixedModeNoGo.md`.  That witness has
only one Bernstein-safe root and defeats the full critical `J2` selector at
every admissible critical point.  Nevertheless a fixed truncated connector,
suggested by the candidate chosen by `QuinticMixedGlobalAtlas.md`, works with
a strict rational margin throughout a nonzero root-coordinate box.

This is an ordinary interval/Bernstein proof with an exact rational checker.
It closes a genuine local cell of the finite mixed band.  Its half-width is
more than one hundred times the radial boundary headroom of the centre; the
conditional disk restriction below is therefore essential.  It does not yet
cover the entire band or unrestricted degree five.

## 1. Root box and fixed connector

Let the exact centres be

```text
a0 =  0.9976274963 - 0.0688286176 i,
a1 =  0.2336442603 + 0.9723211196 i,
a2 = -0.8077935542 + 0.5894638019 i,
a3 = -0.8347956985 - 0.5505580276 i,
a4 =  0.3448410498 - 0.9386600292 i.                       (1)
```

For `delta=11/100000`, take arbitrary points `alpha_j` in the closed rectangles

```text
|Re(alpha_j-a_j)|<=delta,       |Im(alpha_j-a_j)|<=delta.  (2)
```

and restrict to target configurations for which `|alpha_j|<1`.  (The
certificate below is actually valid on the whole rectangles, including the
irrelevant portion outside the disk.)  Put

```text
P_alpha(z)=product_(j=0)^4(z-alpha_j),       s=87/200.      (3)
```

Use roots `alpha_2,alpha_3` and the three-segment Form A-cut path

```text
alpha_2 -> s alpha_2 -> s alpha_3 -> alpha_3.              (4)
```

The fraction `s=0.435` is the physical version of the normalized mixed-atlas
candidate with pair `(2,3)` and model radius approximately `0.69`: for the
centre of (2), the Fourier normalization has `rho=0.630629...` and the atlas
selects `rho*0.69=0.43513...`.  The rational value in (3) moves slightly
inward and is verified directly on the actual polynomial; no asymptotic
remainder estimate is used.

## 2. Exact interval Bernstein certificate

Parameterize each segment of (4) as `z(u)=z_0+u z_1`, `0<=u<=1`.  The real
polynomial

```text
G(u)=|P_alpha(z(u))|^2-1                                    (5)
```

has degree at most ten.  The checker performs natural complex interval
arithmetic on all ten real root coordinates, expands (5) in the power basis,
and converts it exactly to degree-ten Bernstein form.  Every arithmetic
endpoint is a `Fraction`; no floating-point value decides a sign.

For the whole box (2), the largest upper endpoints among all Bernstein
controls are

```text
outer arm to alpha_2       < -0.10681,
outer arm to alpha_3       < -0.03653,
inner connector            < -0.00112.                    (6)
```

In particular every control is below `-1/1000`.  Since the Bernstein basis is
nonnegative and sums to one,

```text
|P_alpha(z)|^2-1 < -1/1000                                 (7)
```

on all three segments.  Thus (4) lies strictly in `{|P_alpha|<1}`.
`TruncatedSpokeReduction.md` then gives

```text
length(4) <= |alpha_2|+|alpha_3| < 2.                      (8)
```

This proves Erdős 1041 for every polynomial in the box (2).

## 3. Why this advances the transfer problem

The centre of (2) is the exact obstruction to the proposed
Bernstein-or-critical-`J2` disjunction, with normalized Vandermonde
`0.9597967...`.  The theorem therefore demonstrates, with capacity rather
than at one isolated point, that the compact mixed-model connector survives
at visible actual-polynomial scale even where both straight selector families
fail.

It also exposes a practical globalization route.  Each accepted model-atlas
candidate supplies a root pair and truncation fraction.  The same degree-ten
interval Bernstein calculation used here can certify a box of actual root
coordinates directly, avoiding the very coarse uniform `10^6 rho` remainder
that limits `QuinticTransverseFiniteTransfer.md` to `rho<=10^(-20)`.  An
adaptive actual-root atlas can reuse the model candidates as proposals and
accept a cell only after the direct three-segment sign test succeeds.

`QuinticTraceMinQualitativeTransfer.md` remains the complementary curved-arm
consumer: it removes finite hub-selection anomalies once the all-sheet
trace-max excess theorem is available.  The present certificate instead
uses Form A-cut and needs no critical hub.

## Exact open boundary

This theorem covers only the explicit `1.1*10^(-4)` root-coordinate box (2),
intersected with the open-unit-disk constraint.  It does not prove that the
model candidate works on every configuration with
Vandermonde near `0.96`, does not provide the finite atlas covering the full
compact middle, and does not prove the still-open all-sheet trace-max excess
theorem.  The next bounded computation is an adaptive box cover of the
remaining mixed band, with direct degree-ten Bernstein acceptance as above.

## 4. A complete actual-root atlas chain from the regular pentagon

The local box is not isolated.  Let `g_j` be the radius-`999999/1000000`
regular pentagon, with its unit directions rounded to the displayed exact
17-digit rational coordinates used by the checker, and let `a_j` be (1).
Consider the exact affine root family

```text
alpha_j(t)=(1-t)g_j+t a_j,                    0<=t<=1.     (9)
```

Both endpoints lie strictly in the unit disk, so convexity puts every root in
(9) strictly in the disk.  An adaptive exact atlas covers the whole parameter
interval.  On each dyadic `t`-cell it forms the full Cartesian root-coordinate
rectangle swept out by that cell, keeps the fixed pair `(2,3)`, and lets a
floating-point scout propose one truncation fraction from

```text
{1/100,2/100,...,50/100}.                                  (10)
```

Acceptance is again only by the exact degree-ten interval Bernstein test.
Failure at depth 24 is fatal.  The replay closes with

```text
accepted Cartesian root boxes       300,
maximum dyadic depth                  16,
smallest t-width                    2^(-16),
weakest exact Bernstein upper      < -4*10^(-7).           (11)
```

The accepted scales range from `2/100` near the regular endpoint through
`48/100`; no critical hub or straight-selector inequality is used.  The
accepted rectangles cover (9) exactly, and also certify every off-family
root configuration in their Cartesian union that still satisfies the unit
disk constraint.  Thus (11) is a finite-capacity tube, not merely a sampled
one-dimensional plot.

This is the first complete visible-scale chain in this lane from a regular
pentagon to the exact mixed Bernstein/J2 obstruction.  It also identifies the
remaining globalization issue more sharply: the direct actual-root atlas is
already stable across the equality-to-mixed transition along a hard
mode-1/mode-2 direction; what remains is covering the transverse angular and
radial parameter faces, not repairing the failed straight selectors.
