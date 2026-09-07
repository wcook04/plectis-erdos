# Erdős 269 dyadic-window computational lab

## Claim boundary

The target is irrationality for the first unresolved running-LCM series with
prime support `{2,3,5}`.  The exact consumer in `ResidueEscape.lean` turns a
cofinal supply of denominator-adaptive residue-escaping windows into carry
extinction.  Every scan here is finite evidence for a producer; it is not the
universal denominator or cofinal-anchor theorem.

## Why the old rectangle is not enough

The existing checker found a firing window of length at most 14 for every one
of 106,666 pairs with `B <= 1000`, `gcd(B,30)=1`, and `100 <= a <= 500`.
That horizon does not say which part of the inequality is difficult.  A window
can fail because its product base has not yet exceeded the analytic short
bound, or because the base is already large enough but the canonical residue
remains trapped below that bound.  Only the second failure is genuinely
arithmetic.

## Discriminating coordinate

For each denominator/start pair `(B,a)`, define

- `ell_base`: the first window length for which `window_base > short_bound`;
- `ell_fire`: the first length for which both the base and residue inequalities
  hold;
- `residue_delay = ell_fire - ell_base`.

The tested mechanism is:

> Once deterministic base growth clears the short bound, the actual canonical
> residue escapes within a uniformly bounded number of additional blocks.

This is not a coordinate change.  A universal bound `K` would combine with
elementary growth of the block base to produce an escaping window for every
denominator and every sufficiently late anchor, which is exactly the shape
consumed by the Lean theorem.

The first exact pair with `residue_delay > K` falsifies the proposed constant.
Its full denominator, anchor, base, forcing, residue, short bound, first
base-clear length, and firing length are retained as the next arithmetic
witness.  A failure to fire by the configured maximum length is recorded
separately from a true bounded-delay counterexample.

There is an exact analytic simplification inside a trapped post-clear chain.
If the next block has base `b` and digit `d`, the least-positive residues obey

\[
\rho_{t+1}\equiv b\rho_t-Bd\pmod {bM_t}.
\]

For every delay-five witness in the canonical scan, the modular lift is zero
at all five transitions, so the hard segment is the literal affine recurrence

\[
\rho_{t+1}=b\rho_t-Bd.
\]

After dividing by `B`, the denominator disappears from the recurrence:
`x_{t+1}=b*x_t-d`.  Thus any proposed universal delay bound can target the
intersection of explicit short-bound cylinders for the actual block base/digit
word.  It need not control arbitrary residues modulo the full window base.

## Reproducible receipt

The canonical finite scan is generated with

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_dyadic_windows.py \
  --max-denominator 1000 \
  --start-min 100 \
  --start-max 500 \
  --max-length 24 \
  --residue-delay-threshold 5 \
  --assert-packet \
  --output state/formal_math/erdos257_period_noncollapse/erdos269_dyadic_window_receipt.json
```

Replay adds `--check`.  The receipt's `experiment_contract` links this analysis,
the exact generator, the Lean consumer, the falsifier, and the analytic
consequences of either polarity.  Its `source` row binds the generator bytes.

## Rotation rule

- Delay `5` is retired by the adversarial extension below; do not replace it
  with delay `7` without a new mechanism.
- The affine-cylinder reconstruction below now retires every cap through
  `100`; do not replace it with `101`.
- Use the exact cylinder intervals to prove a scale-dependent delay law or an
  arbitrary-depth construction.
- Do not count a larger zero-failure rectangle as proof progress by itself.

## Canonical result at the linked revision

All 106,666 pairs fire.  The largest minimal length is 14 and the largest
post-clear residue delay is 5.  The exact delay histogram is

| Delay | Pair count |
|---:|---:|
| 0 | 66,546 |
| 1 | 31,713 |
| 2 | 7,429 |
| 3 | 865 |
| 4 | 100 |
| 5 | 13 |

The receipt retains all 13 maximal witnesses and their post-clear trajectories.
They realize eight base words; all 65 recorded transitions have modular lift
zero.  This opened the finite-word affine-cylinder route above and motivated
the sharper `K=5` falsification run.

## Adversarial extension: `K=5` is false

Detached job `cf_b94d58fce1b24c07a6b7` scanned 2,402,066 exact pairs with
`B <= 10000`, `gcd(B,30)=1`, and `100 <= a <= 1000`.  Every pair still found
an escaping window, but 31 pairs have residue delay greater than 5.  The
largest observed delay is 7, first at `(B,a)=(1961,221)` and again at
`(7591,460)` and `(7591,461)`.

This is a one-way negative result: the five-block post-clear mechanism is
retired.  It is not repaired by changing the constant to 7.  Focused exact
replay of the three delay-seven witnesses shows zero modular lift at all seven
transitions, so the counterexamples are genuine long affine-cylinder orbits,
not wraparound accidents.

The compact durable receipt is
`state/formal_math/erdos257_period_noncollapse/erdos269_residue_delay_five_nogo_receipt.json`.
It binds the terminal job id, the 29,866-byte source receipt hash, the original
computation-source hash, all three maximal trajectories, the first 20 of 31
threshold violations, and the exact delay histogram.  It was compacted from
the completed output without rerunning the scan.

The next structurally distinct question is whether delay is provably
sublogarithmic/logarithmic in `B` and the anchor, or whether the nested affine
cylinders can construct arbitrarily long traps.  Either answer changes the
proof geometry; another fixed constant does not.

## Exact affine-cylinder reconstruction: structural probe through depth `200`

The zero-lift observation admits a denominator-free exact formulation. For a
full window ending at stage `t`, write its base, forcing and ending jump index
as `M_t`, `F_t` and `j_t`, and put

\[
A_t=j_t^2+10j_t+27.
\]

If `z=q/B`, then the integer `r_t=qM_t-BF_t` is the actual canonical residue
and remains trapped under the proved short bound exactly when

\[
  \frac{F_t}{M_t}<z\leq
  \frac{9F_t+A_t}{9M_t}.
\]

Thus a depth-`d` zero-lift trap is an exact rational interval: take the maximum
of the `d` lower endpoints and the minimum of the `d` upper endpoints. The
condition that the first window in the chain is *the first* base-clear window
is also an exact denominator band,

\[
 \left\lceil\frac{9M_{-1}}{A_{-1}}\right\rceil
 \leq B\leq
 \left\lfloor\frac{9M_0-1}{A_0}\right\rfloor.
\]

There is a further one-way simplification.  If the next block has base `b`
and digit `d`, then its lower endpoint increases automatically.  Its upper
endpoint decreases exactly when

\[
  9d+A_{t+1}\leq bA_t.
\]

`ErdosProblems.Erdos269.affineCylinder_step_nested` proves this implication
over the rationals.  Two further Lean lemmas now expose the analytic producer
behind it. `tailCap_step_of_shellMass` turns the one-shell quadratic bound into
the required cap inequality for every multiplier at least two, and
`tailCap_step_compose` composes consecutive jump factors and digits without
loss. Thus the remaining source-specific task is sharply localized: identify
the actual checker digit as the ordered composition of the one-shell masses
already bounded in `smoothExponentShell_card_quadratic`.

The exact checker evaluates the integer slack
`b*A_t-9*d-A_(t+1)` at every transition.  Every canonical witness through
depth `200` has nonnegative slack, so each full intersection is exactly its
final window constraint.  This deletes the generic multi-constraint geometry:
the surviving arithmetic problem is only whether that final one-sided interval
contains a denominator coprime to `30` inside the first-clear band.  The finite
slack check does not prove the source-specific inequality for all later blocks.

The reusable helper `system/lib/formal_math_affine_cylinder.py` intersects
these constraints, certifies exact consecutive containment, and performs deterministic continued-fraction
reconstruction inside a requested denominator band. The specialized checker
then replays the original integer-only canonical-residue engine; the interval
calculation is never trusted in place of the consumer coordinates.

At the fixed actual dyadic anchor `a=100`, the canonical run reconstructs
traps at requested depths `8, 16, 24, 32, 40, 50, 64, 80, 100, 120, 150, 200`.
The depth-`200` witness has

- first base-clear length `206`;
- a `181`-digit denominator coprime to `30`;
- `200` requested trapped steps with zero modular lift throughout;
- first firing length `406`, hence exact residue delay `200`;
- maximum exact digit/capacity utilization `7041/24200 < 1` and minimum
  cap slack numerator `299668`.

This extends the exact falsification range through `K <= 199`, but it is
deliberately **not counted as mathematical progress by itself**: it is a
longer finite horizon and does not prove unbounded delay. Its purpose is to
discriminate the analytic mechanism. The increasing positive slack and low
capacity utilization support the all-step shell-mass composition route now
isolated by the Lean lemmas; the final rational-point construction and an
arbitrary-depth theorem remain open.

Generate and replay the durable receipt with

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_affine_cylinders.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_affine_cylinders.py --check
```

The output is
`state/formal_math/erdos257_period_noncollapse/erdos269_affine_cylinder_depth_receipt.json`.
It binds the analytic question, the exact interval utility, both computation
sources, the Lean consumer, every reconstructed witness, and a canonical hash
of each full trajectory through escape.

The constructor treats an empty first-clear denominator band as an
inadmissible candidate length and continues.  This matters for adversarial
small-depth runs: an empty band is arithmetic evidence, not an exception in
the generic interval utility.

## Exact Farey-band decision: monotone continuation is false

Continued-fraction reconstruction was a witness heuristic, so its success did
not decide whether a band was empty or whether the returned denominator was
forced.  The generic affine-cylinder utility now has a complete exact decision
procedure.  For an interval `l < q/B <= u`, it counts

\[
  \sum_{L\leq B\leq U,\ (B,30)=1}
    \bigl(\lfloor Bu\rfloor-\lfloor Bl\rfloor\bigr)
\]

by logarithmic floor-sum reciprocity and inclusion-exclusion.  It therefore
handles the 100-digit denominator bands directly, without scanning them.

At the actual anchor `a=100`, complete counts give occupied-to-empty adjacent
first-clear shifts at `(depth,L)=(16,19)->(16,20)`, `(24,27)->(24,28)`, and
`(50,54)->(50,55)`.  The reverse transition occurs at depths `32`, `40`, `64`,
and `80`.  Every cylinder in these comparisons is exactly nested and collapses
to its final constraint.  Moreover the populated bands at `(8,13)`, `(24,27)`,
`(32,36)`, `(40,45)`, `(50,54)`, and `(80,85)` contain exactly one admissible
rational; in each case the earlier continued-fraction constructor found that
unique denominator.

This is a one-way mechanism elimination, not a longer-horizon audit.  Exact
nesting, a later first-clear length, and coarse interval width do not propagate
rational-point admissibility.  An arbitrary-depth producer must instead
control the arithmetic Farey phase of the actual endpoint, or prove a cofinal
anchor-selection law.  The complete receipt is
`state/formal_math/erdos257_period_noncollapse/erdos269_farey_band_receipt.json`;
generate or replay it with

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_farey_band.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_farey_band.py --check
```

## Source-faithful block-mass normalization

The checker digit has now been compared against an independent enumeration of
the actual smooth source rather than against another recurrence coordinate.
For the half-open dyadic shell `2^a <= x < 2^(a+1)`, write `H(x)` for the
literal `{2,3,5}` running height.  Exact computation gives

```text
sum H(2^(a+1)) / H(x) = 2 * block_digit(a).
```

The factor `2` is the terminal dyadic jump.  Lean now proves at every scale and
for every actual smooth shell point that the right-endpoint height is exactly
the point height times `2` and an odd suffix product.  After removing `2`, the
point contributes the product of the zero, one, or two odd-channel jumps that
occur after it.  `DyadicBlockMassIdentity.lean` also checks the complete cell
algebra for all possible jump shapes.  Direct enumeration independently agrees
with the checker for every `1 <= a <= 100` (50,134 smooth source values, zero
failures).

The endpoint convention is essential.  A first right-closed probe disagreed;
replacing the included right endpoint of cleared weight `1` with the included
left endpoint of cleared weight `block_base` changes the mass by exactly
`block_base-1` and restores the identity in every shell.  The receipt therefore
binds the half-open interval explicitly rather than treating it as an
implementation detail.

The finite horizon is not counted as progress.  The terminal-factor theorem
first removed endpoint normalization as an analytic ambiguity.  The follow-up
module `DyadicBlockThresholdPartition.lean` now closes the all-scale source
partition: each odd suffix is the product of the indicators for lying before
the unique new `3`- and `5`-power thresholds.  Consequently the half-cleared
mass is exactly

```text
N + 2*C3 + 4*C5 + 8*C35,
```

where `N` is the actual half-open shell cardinality.  Threshold order then
eliminates the interaction count at every scale.  If the new `3`-power comes
first, `C35=C3` and the ordered digit is `N+10*C3+4*C5`; if the new `5`-power
comes first, `C35=C5` and it is `N+2*C3+12*C5`.  These are precisely the two
suffix-product coefficient patterns produced by processing the later odd jump
first.  This is counted: it is an all-scale Lean identity that closes the
summation/ordering mechanism, rather than a longer source enumeration.

The remaining #269 throat is no longer cell combinatorics.  It is to bind this
ordered digit into the actual rationality carry recurrence and then control
the arithmetic Farey phase cofinally (or construct admissible cylinders at
arbitrary depth).  Generate or replay the independent source-bound regression
receipt with

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_block_mass_identity.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_block_mass_identity.py --check
```

## The actual infinite shell tail now reaches the bounded-radix dichotomy

`DyadicOrderedTailRecurrence.lean` closes the algebraic source-to-carry seam.
Define the literal rational shell mass

```text
M_a = sum_{x smooth, 2^a <= x < 2^(a+1)} 1/H(x).
```

The all-scale threshold identity and the pointwise height factorization imply

```text
H(2^(a+1))/2 * M_a = d_a,
```

where `d_a` is exactly `dyadicOrderedBlockDigit235 a`.  Consequently, for
every tail decomposition `T_a=M_a+T_(a+1)`, the normalized state
`X_a=H(2^a)T_a/2` satisfies

```text
X_(a+1) = dyadicBlockBase235(a) * X_a - d_a.
```

`DyadicShellSummability.lean` closes the remaining analytic specialization.
The shell contains at most `(a+1)^2` points, so `d_a <= 15(a+1)^2`; together
with `2^(a+1) <= H(2^(a+1))` this gives a summable polynomial-geometric
majorant for `M_a`.  Lean therefore constructs the genuine infinite tail

```text
T_a = sum'_{n>=0} M_(a+n),
```

proves `T_a=M_a+T_(a+1)`, and applies the exact recurrence above to this
specific `tsum`.  The existing bounded-radix theorem now yields the direct
one-way dichotomy: the actual normalized infinite tail either reaches an exact
integral state or returns cofinally to distance at least `1/31` from every
integer.  The abstract-tail and infinite-specialization seams are closed.  The
remaining branch is to exclude exact integral normalized states; irrationality
is not yet proved.

The linked checker independently enumerates literal smooth points, constructs
all finite source tails with exact `Fraction` arithmetic, and replays the
cleared-shell identity, affine update, quadratic digit bound, and
polynomial-geometric shell bound.  Its horizon is regression evidence; the
all-scale Lean declarations carry summability and the infinite dichotomy.

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_ordered_tail_recurrence.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_ordered_tail_recurrence.py --check
```

## The integral branch has a denominator-one post-clear automaton

The infinite-tail dichotomy leaves one exact alternative: some normalized
state `X_a` is an integer.  From that point onward every state is a positive
integer satisfying the actual affine recurrence.  For a local window with
base `M`, forcing `F`, and endpoint cap `K`, once `M>K` the endpoint is forced
to equal the least positive residue of `-F mod M`.  This turns the remaining
branch into a source-faithful denominator-one automaton rather than a search
over arbitrary rational denominators.

`scripts/check_erdos269_integral_tail_escape.py` tests a new falsifiable law:
after the window base first clears the analytic cap, the canonical `B=1`
state escapes within at most three further actual block transitions.  The law
survives every start through `2000`, but the bounded falsifier search then
finds an exact counterexample at `a=2295`.  Its first base-clear window has
length `7`, after which the canonical states

```text
385235 -> 217423 -> 432920 -> 1100228
```

remain below their respective caps.  Only the next state, `8326020`, exceeds
the cap `2514339`.  Thus the post-clear delay is `4`, decisively eliminating
the proposed three-transition classification.  All `3000` tested starts still
escape by total length at most `11`, but that larger bounded fact is not
promoted to a uniform theorem or a new cap conjecture.

The one-way result is the no-go: a proof may use the denominator-one automaton,
but it cannot reduce it to the first three post-clear updates.  The exact
longer survivor is now the object to explain—either as the first member of an
unbounded expanding-error cone or through a genuinely different invariant.

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_integral_tail_escape.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_integral_tail_escape.py --check
```

## Projective window pairs beat both local residue tests

`HalfHeightDenominatorTransport.lean::reducedCarry_projective_shadow` gives a
second, genuinely cross-window consumer.  If reduced carries `d_a,d_b` arise
from one rational numerator at running heights `H_a,H_b`, then

```text
d_a * H_b = d_b * H_a  (mod B).
```

The unknown absorbed smooth denominator cancels because it is coprime to the
reduced denominator `B`.  This relation can fail even when each carry is
separately small enough and coprime to `B`, so it is not another presentation
of the one-window size or nonunit-residue obstruction.

`scripts/check_erdos269_projective_window_pair.py` supplies the first exact
source-faithful witness.  For `B=11`, the actual window from scale 1 through 4
has base 360, forcing 289, canonical carry 61, and short bound 150.  The window
from scale 4 through 7 has base 1800, forcing 4231, canonical carry 259, and
short bound 398.  Both residues are below their bounds and coprime to 11, so
neither local consumer fires.  The corresponding running heights are 5 and 2
modulo 11, but

```text
61 * 2 - 259 * 5 = 4  (mod 11),
```

so the pair cannot belong to one rational candidate.  This decisively opens a
structurally different producer: construct cofinal endpoint pairs whose local
residues may stay small but whose projective shadows disagree.  The single
finite witness does not supply the universal denominator/cofinal-anchor
quantifiers and proves no irrationality theorem.

Replay and freshness check:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_projective_window_pair.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_projective_window_pair.py --check
```

## Quotient normalization kills the small-defect shortcut

For a window write its canonical carry and endpoint height as

```text
d_i = k_i M_i - B F_i,       H_i = S_i M_i.
```

`HalfHeightDenominatorTransport.lean::projectiveDefect_eq_windowQuotientDefect`
kernel-checks the exact factorization

```text
d_1 H_2 - d_2 H_1
  = M_1 M_2 (k_1 S_2 - k_2 S_1)
    + B (F_2 S_1 M_1 - F_1 S_2 M_2).
```

Because every actual window base is `{2,3,5}`-smooth and the reduced
denominator is coprime to 30, projective incoherence can therefore be probed
through the ceiling-quotient defect `k_1 S_2-k_2 S_1`.  This is a useful
computational compression, but the natural next shortcut is false: centered
defects do not remain in a small interval around zero.

The exact first counterexample already occurs at `B=7`.  Two base-clear,
locally bounded, denominator-coprime endpoint carries give quotient defect
`129120`, whose centered residue is `-2 mod 7`; hence its magnitude exceeds
`B/4`.  The corresponding original projective defect is `1 mod 7`, so the
Lean consumer fires.  The durable scan maps the first violating pair for every
reduced denominator through its configured bound and verifies the displayed
factorization on every pair.  That finite rectangle is not a universal or
cofinal theorem.  Its one-way consequence is narrower and analytic: abandon a
uniform small-centered-error proof and study the full modular discrepancy of
the weighted ceiling quotients.

Replay and freshness check:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_projective_quotient_scan.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_projective_quotient_scan.py --check
```

## Integral branch extinction: pinning windows and forced equality

The remaining #269 throat is the dichotomy's integral-state branch.  Three
new structural facts convert it into a decidable object.

**Upward closure and pinning (now in Lean).**  The recurrence has integer
coefficients, so if some `X_A` is an integer every later state is integral:
the integral-index set is empty or a final segment.  Positivity of the
genuine tails unrolls to the exact pinning identity

```text
X_a = d_a / b_a + X_(a+1) / b_a,
```

so every true state sits strictly above its anchor `d_a / b_a`, and when
`b_a | d_a` integrality would force `X_(a+1) = 0` - killed outright.
These are landed with the zero-gap kill and upward closure in
`IntegralBranchExtinction.lean`.

**Forced equality (Lean).**  Any real orbit following the recurrence from
index `A` onward inside windows of a reproducing, vanishing width function
must equal the true state: deviations multiply by at least `2` per shell
while window widths grow submultiplicatively.  Hence "an integer seed
survives all windows" is equivalent to "the true state is an integer",
which would make `T_0` rational and settle #269 negatively; eliminating
all seeds closes the branch.

**Exact seed-extinction census.**  For every candidate first integral index
`A <= 400`, every integer seed inside its rigorous Cantor-series window was
propagated through `w' = b_a w - d_a` requiring positivity and membership
in each later window (exact rational arithmetic throughout):

| Outcome | Count |
|---|---:|
| First indices probed | 400 |
| Seeds killed at depth 0 | 64,822+ (see receipt histogram) |
| Deepest seed death | 6 steps (at A=295) |
| Survivors after depth 256 | **0** |
| Zero-gap scales (`b_a | d_a`) killed outright | 80 through scale 80 |
| Windows containing no integer at all | 5 through index 400 |

The uniform shallow-death signature discriminates pinned-seed extinction
from the retired unbounded-cylinder mechanisms (delay caps through 199 are
false there).  The analytic target this opens: prove the cubic width
function `W_m = 40(m+4)^3` bounds every true state (its two defining
inequalities are machine-verified), discharge it into the Lean
forced-equality theorem, and the census becomes cofinally decisive.

**Parity gate against even stabilized denominators.**  If `T_0 = u/v` is
rational then monotone height divisibility (`H(x) | H(y)` for `x <= y`)
collapses every normalized denominator: writing the stabilized chain as
`Q`, one gets `Q | 2v`.  Under `2 | Q`, the forward congruence on the
integer numerators forces `d_a` even for all large `a`; since
`d_a ≡ N_a (mod 2)` with `N_a` the literal shell cardinality, rationality
would force `N_a` eventually even.  The exact odd-channel lattice census
shows the opposite through scale 4000:

| Statistic | Value |
|---|---:|
| Odd shells among scales 1..4000 | 2,055 |
| Longest consecutive even run | 10 |
| Last four odd shells | 3995, 3996, 3997, 3998 |

Odd shells persist cofinally with bounded gaps, so any proof that they
occur unboundedly often (e.g. via the odd-channel count `O_a =
#{(j,k) : 2^a <= 3^j 5^k < 2^(a+1)}` taking odd values infinitely often)
eliminates `2 | Q` under rationality.

Replay and freshness check:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_integral_branch.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_integral_branch.py --check
```

The receipt binds the shared engine
(`system/lib/formal_math_erdos269_orbit_engine.py`), both source hashes,
the Lean consumer declarations, and the full per-depth death histogram.

## Rotation rule update

- Do not rerun the seed census with a larger first-index cap and call it
  progress; the mechanism question is now the width-function instantiation
  and the cofinal odd-shell theorem.
- Do not propose bounded post-clear delay laws (retired through 199) or
  global linear/quadratic source potentials (retired exactly); the live
  lanes are pinned-seed extinction formalization and stabilized-denominator
  parity elimination.

## Denominator collapse, rigidity residues, and the reduced problem

One result this wave shrinks the denominator, and one refutation machine
sharpens the residues.

**Rationality forces the stabilized denominator coprime to 30 (analytic,
unconditional).**
If `T_0 = u/v` is rational then every normalized state `X_a` is rational,
and the recurrence makes denominators a divisibility-decreasing chain:
writing the stabilized value as `Q`, reduction at every late index forces
`gcd(b_a w_a - d_a Q, Q) = 1`.  Any prime of `Q` dividing any late block
base would break this: if `p | Q` and `p | b_a` then `p` divides
`b_a w_a - d_a Q`, contradicting the displayed gcd.  Now `2 | b_a` at
*every* scale, and `3 | b_a`, `5 | b_a` at infinitely many scales (the
log-ratio floors increase forever).  Hence

```text
T_0 rational  =>  gcd(Q, 30) = 1.
```

**Correction, 2026-08-23.  This paragraph previously concluded `Q = 1` and
therefore that `X_a` is eventually integral.  That step does not follow and
is retracted.**  The block bases satisfy `b_a in {2, 6, 10, 30}`, so their
prime factors lie entirely in `{2, 3, 5}`.  The argument can only eliminate
primes of `Q` that divide some late `b_a`, so a prime `p >= 7` dividing `Q`
is never reached by it.  What is established is exactly the packet's
`denominator_reduction_coprime_thirty`: the remaining denominator is the
coprime-to-30 part.

Consequently this does **not** supply upstream input (1) of
`ResidueEscape.lean` outright, and the parity-gate lane is not superseded.
Irrationality of `T_0` does **not** reduce to "no normalized state is an
integer"; that reduction is available only on the `Q = 1` fibre.  The
obligation that covers every denominator is the collision criterion of
`RationalLatticeReduction.lean:280`, whose docstring already scopes `q = 1`
as "the special case", and the standing statement of the obligation in
[RationalLatticeTorusSqueezeLab.md](RationalLatticeTorusSqueezeLab.md):
for every denominator, not more finite exclusions.

**Window-residue rigidity (exact refutation machine).**  Assume `X_A = w`
integral.  The telescope identity `X_(A+k) + N_k = w B_k` with exact
recursion `N_0 = 0`, `N_(k+1) = b_(A+k) N_k + d_(A+k)` holds by induction.
Multiplying by `b_(A+k)` and clearing one pinning step gives the exact
congruence

```text
X_(A+k+1) === -( d_(A+k) + b_(A+k) N_k )   (mod M_k),  M_k = prod_{j<=k} b_(A+j),
```

with `M_k >= 2^(k+1)`.  Positivity and the rigorous Cantor-series enclosure
confine the true state to `(0, hi]`; once `M_k > hi` the least residue must
land in `(0, hi]` exactly or the hypothesis dies.  Two synthetic positive
controls (digit worlds with exact integer states via constant and
nonconstant integer potentials) survive every checked step, so the
elimination logic is sound in both directions.

Exact scan over first indices `A <= 6000`:

| Statistic | Value |
|---|---:|
| First indices refuted exactly | 6000 / 6000 |
| Unresolved | 0 |
| Refutation-depth histogram | {0:5, 1:12, 2:54, 3:120, 4:378, 5:1100, 6:2565, 7:1504, 8:240, 9:22} |
| Deepest refutation depth | 9 |

The depth grows logarithmically while `A` ranges over nearly four orders of
magnitude (mode drifts 5 -> 6; the tail mass moves smoothly upward).
The analytic target is now sharp: prove a universal refutation bound (the
histogram suggests one exists), formalize the rigidity congruence against
the landed forced-equality theorem, and combine with denominator collapse.

Replay and freshness check:

```bash
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_erdos269_two_adic_rigidity.py --check
```

## Rotation rule update (supersedes previous)

- The parity/odd-shell lane is closed as a *requirement* (input (1) is
  proved by denominator collapse); do not invest further there.
- Do not rerun either census with larger ranges and call it progress; the
  open object is the uniform refutation-bound theorem and its Lean
  formalization.
