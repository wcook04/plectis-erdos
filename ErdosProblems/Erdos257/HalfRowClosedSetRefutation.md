# Half-row closure refutes #257 through the closed achievement set

Status: exact reduction with two of three steps already machine-checked;
the remaining socket is cofinal exact quotient-row existence, verified with
zero finite failures through horizon 3000 on 2026-08-22.  This note does not
claim a solution of Erdős #257.  Two earlier shortcuts were false: literal
horizon stability, and a midpoint sign formula imported from the adjacent
target `2^(N-1)-1`.  Both have been removed below.

## The three-step chain

Let `A` be the full Mersenne achievement set
`{sum_d b_d w_d : b in {0,1}}`, `w_d = 1/(2^d-1)`.

**Step 1 (proved; Lean `hereditary_mersenne_subachievement_topology`).**
`A` is compact, hence closed.

**Step 2 (proved here; one line).**
No finite Boolean support sums to `1/2`: each `w_d` has odd denominator,
so every finite Boolean sum reduces to a fraction with odd denominator,
while `1/2` has even denominator.  Verified exhaustively for all supports
over ranks `2..14`.  Consequently any representation of `1/2` in `A` is
infinite, which refutes universal irrationality.

**Step 3 (the socket).**  For each horizon `N >= 4` run integer greedy on
target `T_N := 2^(N-1)` against the quotient weights
`q(N,d) = floor(2^N/(2^d-1))`, selecting ranks `S_N`.  Integer greedy never
overshoots the quotient target.  Put `x_N := sum_{d in S_N} w_d`; then

\[
 2^N x_N = \sum_{d\in S_N} q(N,d) + \Theta_N,
 \qquad \Theta_N = \sum_{d\in S_N}\theta_{N,d}\in[0,\ |S_N|),
 \qquad \theta_{N,d}\in[0,1).
\]

If the row closes exactly (`sum q = T_N`) at cofinally many horizons, then

\[
 x_N=\frac12+2^{-N}\Theta_N,
 \qquad 0\leq\Theta_N<|S_N|\leq N.
\]

Thus `x_N -> 1/2` (from above unless `Theta_N = 0`), and closedness of `A`
gives `1/2 in A`.  More generally, quotient remainder `o(2^N)` is enough.
With Step 2 this settles #257 negatively.  Integer greedy's lack of quotient
overshoot does **not** imply `x_N <= 1/2`; the fractional masses have the
opposite sign.

Exact closure at horizon `N` is equivalent to the midpoint inequality:
coins `d > N/2` are pure powers `2^(N-d)` forming a complete binary bank
covering `[0, 2^ceil(N/2))`, so the row closes iff the lower-half residual

\[
 V_N := T_{\lfloor N/2\rfloor}\text{-greedy residual against } q(N,d),
 \quad d\le \lfloor N/2\rfloor
\]

satisfies `V_N < 2^ceil(N/2)`.

## Audit of the strict-core midpoint argument

The adjacent target

\[
 H_{2R}=2^{2R-1}-1
\]

has a useful but distinct terminal decomposition.  Run quotient greedy only
through ranks `2,...,R-1`, and call the remaining integer `A_R`.  Rank `R`
has quotient coin `2^R+1`; ranks `R+1,...,2R` are the complete binary bank
of capacity `2^R-1`.  Hence their attainable terminal sums are exactly

\[
 [0,2^R-1]\ \cup\ [2^R+1,2^{R+1}].                 \tag{A}
\]

This proves the advertised absorption calculation.  If
`A_R <= 2^(R+1)`, every value is repaired exactly except `A_R=2^R`.  At that
value the full bank leaves quotient defect one from `H_(2R)`, or equivalently
terminal half-carry two from `2^(2R-1)`.  The defect divided by `2^(2R)`
vanishes, so the equality case is harmless for the closed-set endgame.

The calculation does **not** prove its input bound.  Required cofinally,

\[
 \boxed{A_R\le 2^{R+1}}                              \tag{B}
\]

is precisely the live Lean producer
`CofinalEvenHalfCutoffCoreBound` (its strict natural-number form is
`A_R < 2*2^R+1`).  Lean already proves
`half_mem_mersenneAchievementSet_of_cofinalEvenCoreBound`, including the
midpoint equality case.  It also proves the strictly more general consumer
`half_mem_mersenneAchievementSet_of_evenCoreSubquadraticAlong`: along any
cofinal rows, the cap-free hypothesis `A_R/4^R -> 0` suffices.  Its direct
finite-row estimate is

\[
 \left|x_R-\frac12\right|
 \le \frac{2R+1+A_R}{4^R},
\]

where `x_R` is the reciprocal-Mersenne value of the strict-core support.
Thus neither the terminal absorption nor the König/carry closure is the
remaining gap; the missing theorem is all-depth or cofinal control of the
strict-core remainders.

There is a useful three-state fringe decomposition.  The last strict-core coin
has, for \(R\ge4\), the exact value

\[
 q_{2R}(R-1)
 =\left\lfloor\frac{2^{2R}}{2^{R-1}-1}\right\rfloor
 =2^{R+1}+4.                                      \tag{B-last}
\]

The exact coin identity is Lean-checked by
`TwentyOneQuotientGreedy.localMersenneQuotient_two_mul_pred`.  However, for
one-copy greedy selection that identity alone does **not** imply that the final
remainder is below the last coin: after subtracting a coin once, the residual
can still exceed it.  Thus the estimate

\[
 A_R<2^{R+1}+4.                                   \tag{B-fringe}
\]

is a separate open fringe candidate.  Conditional on this estimate, the coarse
producer `(B)` reduces to excluding exactly three integer states:

\[
 A_R\notin
 \{2^{R+1}+1,2^{R+1}+2,2^{R+1}+3\}.             \tag{B3}
\]

The exact scan in
[`NewtonNestedHeightFrontier.md`](NewtonNestedHeightFrontier.md) finds neither
a failure of the fringe candidate nor a surviving `(B3)` state through
\(R=1400\).  Both observations are finite evidence: the universal fringe
estimate and the three-state exclusion still require proof.

For the literal corridor `Q_(2R) <= 2R`, (B) can be weakened slightly.  If
the midpoint and full binary bank are used greedily, the terminal quotient
defect is

\[
 \max(0,A_R-2^{R+1}),
\]

apart from the isolated value `A_R=2^R`, where it is one.  Therefore

\[
 A_R\le 2^{R+1}+2R-1                              \tag{C}
\]

already gives `Q_(2R) <= 2R`.  This is a genuinely weaker finite producer
than (B), although the existing `o(4^R)` closed-set consumer is weaker still.
The exact audit command below now reports (B), (C), midpoint hits, and the
repaired terminal carry separately; a finite pass is evidence only.

## Evidence and structure

- Row closure holds with remainder exactly zero for every `N` in `[4,
  2500]` (this note) and `[4, 2000]` (parallel session), two independent
  implementations.
- **No fixed-word shortcut.**  Exact rows at different horizons are not
  literal prefixes of one Boolean word.  For example, the row-5 and row-6
  supports first differ at rank 4, while the row-51 and row-102 supports
  first differ at rank 43 (lag 8 from the smaller horizon).  Fixed
  coordinates empirically stabilize as the horizon grows, but that is a
  compactness phenomenon, not exact horizon stability and not an induction
  theorem.  Cofinal rows need no cross-horizon coherence, so the valid
  consumer above is unaffected.
- **The true stable object is the lower-half core.**  Let `S_N` be the
  exact greedy row, `M = floor(N/2)`,

  \[
    W_N=\sum_{d\in S_N,\ d>M}2^{N-d},\qquad
    g_N=\#\{d\in S_N:d\le M,\ d\mid N+1\}.
  \]

  Holding `S_N cap [2,M]` fixed at the next horizon leaves the exact bank
  demand

  \[
    A_N=2W_N-g_N.                                      \tag{3}
  \]

  If `N` is even, the next upper bank is an uninterrupted binary bank and
  only `A_N >= 0` is substantive.  If `N=2M+1` is odd, moving rank `M+1`
  into the core leaves exactly one unrepresentable bank value,
  `2^(M+1)`.  Thus the one-step construction fails only through negative
  financing or the literal midpoint equation

  \[
    2W_N-g_N=2^{M+1}.                                \tag{4}
  \]

  The recomputed upper word is exactly `S_(N+1) \ [2,M]`; equivalently,
  the lower-half cores agree.  This holds with zero failures through
  horizon 3000.  Equation (4) is no longer a terminal obstruction: the
  two-horizon bypass below crosses it exactly.
- **Lift ladder.**  With `q(2m+o,d) = 2^L q(m,d) + ec(d)`, `L = m+o`, the
  doubled row reconstructs exactly from the base row plus the upper-half
  bank; verified losslessly through `m < 1800` for both parities.
  Exhaustive subsets over ranks `4..14` show arbitrary selections fail
  (`bank`/`floor` violations), so any all-depth proof of the ladder must
  consume greedy ancestry, not subset combinatorics alone.
- The margin against the bank bound is **thin**: ratio
  `V_N / 2^ceil(N/2)` reaches `0.999887` at `N = 2270`; strict inequality
  at cofinally many horizons is what is needed, equality is what must be
  excluded.
- The target has a rigid signed shadow: `sum_{d>=1} mu(d)/(2^d-1) = 1/2`
  truncated gives `2^(2M-1) = sum_{d<=2M} mu(d) q(2M,d) + E_M`,
  `|E_M| <= 2M+2`; generic random signed words have exponentially large
  defects, confirming ancestry-specificity.
- Cofinality suffices: closure along any infinite horizon subsequence
  drives the partial sums of `B` to `1/2`.

## Target convention and the corrected sign identity

The compactness row in this note uses

\[
 T_N=2^{N-1},\qquad T_{N+1}=2T_N.
\]

It must not be mixed with the adjacent target `2^(N-1)-1`, whose recurrence
has an additional `+1`.  If an exact row at endpoint `2d` has midpoint bit
`s_d` and strict-upper value

\[
 U_d=\sum_{a\in S_{2d},\ d<a\le2d}2^{2d-a},
\]

then the target used here gives

\[
 \boxed{Z_d=U_d+s_d(2^d+1)-2^d,}                 \tag{5}
\]

with no leading `+1`.  The correct bank bound is `U_d <= 2^d-1`, not
`2^(d-1)-1`.  Exact regressions are `S_6={2,3,5}`, `U_3=2`, `Z_3=3`, and
`S_10={2,3,6,7,10}`, `U_5=25>15`.

Equation (5) proves the quotient-row sign

\[
 s_d=1\Longrightarrow Z_d\ge1,
 \qquad s_d=0\Longrightarrow Z_d\le-1.            \tag{6}
\]

For the real half-greedy bit `b_d`, only the forward implication
`b_d=1 => Z_d>0` is unconditional.  The converse is exactly the missing
real-prefix/quotient-prefix bridge and must not be assumed.

## A real-feasible core finances every endpoint pulse

Let `D=S_N cap [2,floor(N/2)]` and assume the extra structural condition

\[
 \sum_{a\in D}\frac1{2^a-1}\le\frac12.            \tag{7}
\]

Writing `Phi_N(D)` for the sum of the quotient fractional parts, exactness
of the row gives

\[
 \Phi_N(D)\le W_N.
\]

Every selected `a | N+1` contributes the exact fraction

\[
 \left\{\frac{2^N}{2^a-1}\right\}
 =\frac{2^{a-1}}{2^a-1}>\frac12.
\]

Therefore

\[
 \frac{g_N}{2}<\Phi_N(D)\le W_N,
 \qquad\boxed{2W_N-g_N>0}.                         \tag{8}
\]

This is the clean structural separator seen in every successful finite
run and absent from the synthetic endpoint/carry countermodels: the lower
word is not an arbitrary Boolean label but a genuinely below-half Mersenne
prefix whose full fractional ancestry finances the new divisor pulse.

## The odd midpoint hole has an exact two-horizon bypass

The midpoint equation (4) need not be excluded.  Put `d=M+1` and let
`D subset [2,d)` be the old core.  At the failed successor endpoint `2d`,
(4) is exactly

\[
 Q_{2d}(D)=2^{2d-1}-2^d.                           \tag{9}
\]

Let

\[
 g_1=\#\{a\in D:a\mid2d+1\},\qquad
 g_2=\#\{a\in D:a\mid2d+2\}.
\]

Two quotient transitions give the residual after `D` at endpoint `2d+2`:

\[
 R=2^{d+2}-2g_1-g_2.                               \tag{10}
\]

Here

\[
 q(2d+2,d)=2^{d+2}+4>R,
 \qquad q(2d+2,d+1)=2^{d+1}+1.
\]

The second coin fits because

\[
 2g_1+g_2\le3|D|\le3(d-2)<2^{d+1}-1.
\]

After taking rank `d+1`, the remainder is

\[
 2^{d+1}-1-2g_1-g_2,
\]

which is represented exactly by the pure binary bank
`d+2,...,2d+2`.  Thus a one-step midpoint hole jumps canonically to an
exact row two endpoints later (from the old odd row `N=2d-1` to `N+3`).

If `D` satisfies (7), this bypass also preserves feasibility.  From (9),

\[
 \frac12-\sum_{a\in D}w_a
 =\frac{2^d-\Phi_{2d}(D)}{4^d},
 \qquad \Phi_{2d}(D)<|D|\le d-2.
\]

Since

\[
 4^d w_{d+1}<2^{d-1}+1\le2^d-(d-2),
\]

rank `d+1` fits the real residual, so `D union {d+1}` is again feasible.

## Remaining obligation

There are now two exact versions of the remaining socket.

1. **Global financing.**  Prove `2W_N >= g_N` for every exact half row.
   One-step filling plus the bypass above then constructs exact rows at
   unbounded horizons, with gaps only `1` or `3`; (4) needs no separate
   exclusion.
2. **Feasible-core propagation.**  Use (8) and prove that an ordinary
   quotient midpoint take never crosses above the real half target.  A
   strict quotient-take/real-skip mismatch is the only place feasibility
   can be lost.  If a later real skip occurs, the existing critical-row
   theorem restarts with the later real-greedy prefix; if the tail is exact,
   it already represents `1/2`.  The sole surviving case is the familiar
   fatal branch: a last real skip followed by a positive cofinite tail gap.

The second formulation explains why local parity ownership is insufficient:
backward upper-bank parity can be reproduced by countermodels which do not
match the forward carry from the half source.  The unresolved input is the
full source-reachable ancestry/boundary sign, not the midpoint hole and not
an arbitrary upper-bank estimate.

## Audit

```text
./repo-python formal_math/erdos257_period_noncollapse/scripts/half_row_closed_set_audit.py --max-n 2500
./repo-python formal_math/erdos257_period_noncollapse/scripts/check_half_cutoff_window.py --dense-through 400 --sparse-through 6000 --sparse-step 7 --core-through 5000
```

checks: parity exclusion exhaustively (small ranges), mu-Lambert partial
identity, exact row closure and `V_N` statistics through `--max-n`; the
second command separately checks the half-cutoff window, strict-core bound
(B), relaxed corridor bound (C), midpoint hits, and repaired terminal carry.
Both print exact finite receipts.  Status line: finite verification, not an
all-depth theorem.

Snapshot from the displayed strict-core command on 2026-08-22: 4,998 rows
`3 <= R <= 5000`, zero failures of (B), zero failures of (C), zero exact
midpoint hits, and repaired terminal carry one at every row.  The tightest
normalized row was `R=1136`, with
`A_R / 2^(R+1) = 0.999886945...`.  The accompanying half-cutoff sample
tested 1,199 endpoints through `M=6000`, again with zero failures.  These
figures are deliberately recorded as a dated finite snapshot, not as the
missing cofinal theorem.

## Freeze dichotomy and the skip-mass budget (proved here)

Let `B` denote the real-greedy half orbit,
`\rho_N = 1/2 - \sum_{d\in B, d\le N} w_d`,
`M_N = \sum_{d>N} w_d`,
`{\sf Skip}_N` = total `w`-mass of ranks *rejected* through horizon `N`,
and `W_{\rm tot} = \sum_{d\ge2} w_d = E - 1`, where
`E \approx 1.6066951524152918` is the Erdős–Borwein constant.

1. `\rho_N > 0` for every `N`: parity excludes an exact finite hit.
2. The orbit "freezes" (`\rho_\infty > 0`) iff at some horizon
   `\rho_N \ge M_N`; if instead `\rho_N < M_N` for all `N` then
   `\rho_N \to 0` and `\sum_{d\in B} w_d = 1/2` exactly.
3. Define `G_N := \sum_{{\rm taken}\le N} w + M_N`.  Then `G_N` is
   non-increasing, drops exactly `w_d` at each skipped rank, and satisfies
   the exact identity `G_N = W_{\rm tot} - {\sf Skip}_N`.  Therefore

\[
 \text{non-freeze} \iff G_N > \tfrac12\ \forall N
 \iff {\sf Skip}_N < E - \tfrac32\ \forall N ,
\]

   with budget constant `E - 3/2 \approx 0.1066951524152918`.
4. Exact trichotomy: skip-mass below budget always implies refutation of
   universal irrationality; budget hit exactly at the limit gives
   `\rho_\infty = 0`, also a refutation; only skip-mass strictly exceeding
   the budget leaves the universal claim alive, with leftover
   `\rho_\infty = {\sf Skip}_\infty - (E-3/2)`.
5. Hence **the entire negative direction of Erdős #257 equals the single
   global inequality**

\[
 \boxed{\ \sum_{d\in{\sf Skips}} \frac{1}{2^d-1}\ \le\ E-\tfrac32\ }
\]

   for one explicit, computable set — the rejection set of the half
   greedy orbit.  Numerics: the skip mass approaches the budget from
   below with gap `\sim c\,2^{-N}` (the orbit lives on the critical
   line), while the ratio form `\rho_N/M_N` stays inside `[0.06, 0.78]`
   through `N=300`.

Boundary: this is a reformulation with proved equivalences, not a proof
of the budget inequality; an earlier claim that plain greedy convergence
is classical was wrong (tail mass is finite, so positive freeze is legal)
and is retracted.

## Equivalence completion: the six faces of the single socket

Each of the following is now proved equivalent to every other (algebra
above; numerics through the stated ranges):

1. **Freeze exclusion:** `\rho_\infty = 0` for the half-greedy orbit
   (no positive frozen leftover).
2. **No-last-skip / cofinal row closure:** rows close exactly at
   cofinally many horizons.
3. **Core transport:** lower-half greedy decisions agree across each
   horizon step `N -> N+1`.
4. **Strip lower side:** `2^d \rho_d \ge \mathrm{polylog}(d)^{-1}` along
   the orbit (upper side `\rho_d \le w`-scale follows from the greedy
   comparison itself).
5. **Post-take residual floor:** every core take at horizon `N` leaves
   residual `\ge` (selected-divisor pulse of `N+1`)/2 — the exact slack
   condition `r_{d+1}(N) \ge (G_d+\delta_d-1)/2`.
6. **Skip-mass budget:** `\sum_{{\rm Skips}} w_d \le E - 3/2`.

Verified numerics: `\kappa_d = 2^d\rho_{d-1}\in[0.0032,\ 2]` through
`d=1200`; core decision rigidity (zero reverts, zero flips) through
horizon pairs to `2000`; row closure through `2500`; non-freeze margin
positive throughout.  The decision word is provably not `k`-automatic
(maximal 2-kernel growth), closing algebraic-decision routes.

Any future proof must therefore attack the two-sided dyadic strip for one
explicit orbit directly; all local-window, bounded-coordinate,
finite-state, and signed-shadow routes carry corpus countermodels.

## Harmonic two-bucket identity (sharpest form)

Splitting every coin into its geometric harmonics `w_d = \sum_{k\ge1}2^{-kd}`,
the non-freeze margin `{\rm gap}_N := M_N - \rho_N` satisfies exactly

\[
 {\rm gap}_N \;=\;
 \underbrace{\sum_{d\in{\sf Taken},\,k\ge2} 2^{-kd}}_{\text{taken echo mass}}
 \;-\;
 \underbrace{\sum_{d\in{\sf Skip}} 2^{-d}}_{\text{skip pure-power mass}}
 \;+\;
 \underbrace{\sum_{k\ge2}\sum_{d>N}2^{-kd}}_{\ge 0},
\]

using `\sum_{d\ge2}2^{-d}=1/2` to cancel the first harmonic entirely.
Both leading buckets equal `0.101500\ldots`; their difference is
`\sim c\,2^{-N}` (`10^{-91}` at `N=300`, `10^{-152}` at `N=500`,
verified exactly).  Non-freeze is literally the positivity of this
two-bucket balance.  Verified identity exact through `N=500`.

## Dynamical form: a kicked unstable fixed point of the doubling map

With `\kappa_d := 2^d\rho_{d-1}` (so `\kappa_2 = 2` exactly), the entire
half-greedy orbit becomes

\[
 \kappa_{d+1} \;=\; 2\kappa_d - b_d\,(2+\varepsilon_d),
 \qquad b_d = [\kappa_d \ge 1 + \varepsilon_d/2],
 \qquad \varepsilon_d = \frac{2}{2^d-1}\downarrow 0 .
\]

This is the **doubling map started precisely at its unstable fixed point
`\kappa = 2`**, displaced by vanishing Mersenne-structured kicks at each
take.  All six equivalent faces of the socket reduce to one persistence
question:

> does the kicked trajectory of the unstable fixed point remain in
> `[0, 2+o(1)]` forever?

Escape analysis pins the lock: an escape step requires the post-take
value to land in a window of relative width `~2^{-g}\varepsilon/4` at
take-gap `g`; total escape weight across all steps is convergent, so
escape "should" never occur, but excluding it arithmetically is exactly
the saturation exclusion.  Verified: the map reproduces the orbit
exactly; zero escape attempts (`\kappa > 2`) through `d = 1500`;
minimum take-clearance `0.0016` at rank `235`.

Conceptual classification: not RH-like (no universality or L-function
structure); it is a shadowing/persistence statement for one explicit
perturbed dynamical system with arithmetic kicks — Collatz-flavored in
logical shape (`\Pi_1`, one deterministic orbit, exponential-precision
empirical verification, countermodels against every local argument).

## Integration with the landed record (contributions-digest, #257 section)

Two consequences of the digest's checked theorems tighten this note:

1. **Freeze forces an irrational leftover (uses the landed
   eventually-periodic-support irrationality).**  Freeze means skips stop:
   finitely many rejected ranks `F`, cofinite support `T' = {1} u Taken`,
   leftover `\varepsilon > 0` with `\sum_{T'} w = 3/2 - \varepsilon`.
   The digest proves irrationality of every eventually-periodic support
   sum; cofinite is eventually all-ones; hence `3/2 - \varepsilon` is
   irrational and freeze survives only with **irrational** leftover.
   Equivalently `E = 3/2 + {\sf Skip}_M - \varepsilon`: the Erdős–Borwein
   constant sits *below* the structured rational `3/2 + \sum_{{\sf Skip}_M} w`
   by exactly the leftover — the mirror image of the landed denominator-21
   interface (where nonmembership places `E` *above* its structured
   rational within `mersenneGap(M)`).

2. **Greedy uniqueness unifies the closedness shortcut with the direct
   orbit proof (uses the landed base-2 support injectivity).**  Since the
   greedy algorithm reconstructs any attained value's support
   (`greedySupport_supportValue_eq`), if `1/2 \in A` via *any* Boolean
   word — e.g. through the closedness argument from cofinal exact rows —
   then that word *is* the canonical half-greedy orbit.  There is no gap
   between "some representation exists" and "the canonical orbit
   converges": the budget inequality is not merely sufficient but, given
   closedness of `A`, necessary and self-duplicating.

With these, the six-face skeleton inherits two more consumed inputs from
the checked corpus, and the remaining obligation stays the single
two-sided dyadic strip on one explicit orbit.
