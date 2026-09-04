# Erdős 257 historical mechanism closeout

Date: 2026-08-21.

> **Non-authority notice.** This file is a dated evidence and deduplication map.
> It is not a current objective, work queue, route selector, target selector, or
> priority surface.  The objective is always to solve Erdős 257.  Every named
> target, mechanism, lemma, and “frontier” below is a disposable historical probe.
> Current work must select probes afresh by discriminatory power and information
> gain, without incumbency advantage.

## Status

Erdős 257 is **not solved** in this repository.  No file in the corpus proves
the full irrationality statement, and no file constructs an infinite Boolean
support with rational Mersenne sum.

The strongest completed positive theorem is the machine-checked
reciprocal-summable case:

\[
  A\text{ infinite},\qquad \sum_{a\in A}\frac1a<\infty
  \quad\Longrightarrow\quad
  \sum_{a\in A}\frac1{2^a-1}\text{ is irrational}.
\]

The proof authority is
`irrational_erdosSupportSeries_two_of_summable_reciprocal` in
`ReciprocalSupportIrrationality.lean`.  The unresolved positive regime is
therefore the dense-support case

\[
  \sum_{a\in A}\frac1a=\infty.                  \tag{1}
\]

On the construction side, historical work developed exact finite corridor
constructions for $1/465$ and $4/9$.  Both stopped at the same kind of globally
reachable binary seam.  This records what happened; it does not nominate either
target for further work.

## Counting rule

Excluding this closeout, the directory contains 128 Erdős-257 research notes
as of this date.  The
private Lean project contains 193 top-level Lean source modules, including
shared foundations and related supporting developments.  Neither number is a
meaningful count of mathematical attacks.

The table below counts a route only when its main state, transport law, or
success mechanism is genuinely different.  Changing a rational target,
strengthening a finite audit, or restating the same fatal seam in another
normalization does not create a new route.  Under that rule the corpus has
tested **25 distinct mechanism families**.

## The 25 mechanism families

| # | Mechanism family | Durable outcome |
|---:|---|---|
| 1 | Shifted-atom LCM averaging | Solves the reciprocal-summable support case in Lean; fails in (1) because the natural $1/a$ majorant is not summable. |
| 2 | Rational-support carry and denominator height | Gives exact common-multiple lower bounds and unbounded carry, but the LCM scale can dwarf the Archimedean scale. |
| 3 | Digital-height / no-large-gap irrationality | Proves irrationality when the next support rank outruns the reduced denominator height; leaves an LCM-dense branch. |
| 4 | Burst and sparse-block escape | Proves irrationality for superquadratically separated dense bursts; does not touch densely interlaced supports. |
| 5 | Tao--Teräväinen incidence/correlation transfer | Explains prime and prime-power special cases; arbitrary supports can lack both coprime dilation supply and usable decorrelation. |
| 6 | Weighted gcd-frame and overlap energy | Supplies an exact positive variance identity; moving semiprime cliques move all energy to fresh frames and defeat coercivity. |
| 7 | Primitive $p$-adic / adelic channel accumulation | Retains exact prime-power ancestry, but shared descendants can service arbitrarily many channels at arbitrarily late heights. |
| 8 | Real greedy remainder and fatal gap | Gives the canonical membership dichotomy.  The unresolved branch is a last skip followed by a positive homogeneous escape. |
| 9 | Binary perturbation / fixed-point correction | Identifies the Mersenne gap with a broken binary carry; loses stability exactly at dyadic discontinuity surfaces. |
| 10 | Dyadic cylinders, critical bands, and seam transport | Gives exact affine endpoint propagation and compactness consumers; the producer can create a moving one-point hole. |
| 11 | $1/21$ quotient rows and one-step borrow | Failed borrow cofinally would prove membership; nonmembership forces an indefinitely legal expanding carry instead. |
| 12 | Density, reservoir, and greedy variational principles | Couples cumulative borrow area to divisor incidence.  The strongest reservoir sign remains equivalent to the fatal boundary sign. |
| 13 | Negacyclic, phase-winding, mod-6, and mixed-cohort carries | Excludes equal-phase impostors and contracts exact-valuation migration; cross-valuation bank carries evade every bounded phase state. |
| 14 | Bellman / six-step / fat-Cantor dynamics | Proves the invariant set has empty interior and identifies exact point membership; interval trapping cannot locate the required rational point. |
| 15 | Unit-fraction dyadic slivers and reciprocal-power descent | Produces exact unsafe-skip criteria.  A varying-unit-fraction counterfamily kills the universal theorem; fixed $1/465$ ancestry remains special. |
| 16 | Cyclotomic and primitive-prime corridor quantisation | Makes dangerous genealogies unique/rare and separates adjacent ranks; dense lower clocks make the remaining corridor too wide for one-sided quantisation. |
| 17 | Fixed-source backward descent and Euclidean residues | A final unsafe cell yields smaller least representatives, but they leave the coefficient-one Boolean prefix orbit and cannot be recursively re-entered. |
| 18 | $1/465$ source clock and fixed-horizon quotient comparator | Terminal coherence is proved.  Terminal representability reduces to one comparator / saturated final-gate event, still unexcluded globally. |
| 19 | Dynamic ownership, packet parking, carry tax, and nonlocal recuts | Gives exact positive physical recuts and contracting local packet laws.  Cross-lineage ownership cycles kill every scalar or laminar stabilization rule. |
| 20 | Positive product-cylinder Booleanisation | Starts from rational products $M(a,b)$ and exact primitive lattice expansions.  Universal first collisions and vanishing boundary supply rule out static finite-depth normalization. |
| 21 | Signed Möbius Lambert Booleanisation | Supplies rational signed identities such as the Möbius identity.  Formal Lambert Booleanisation is rigid by Möbius inversion, so any success must be point-specific at $1/2$. |
| 22 | Totient, primitive-conductor, Witt, and multiplicity normal forms | Positive or signed rational identities exist, but the canonical Euler/Witt/Lambert normalizations first leave $\{0,1\}$ at explicit small ranks. |
| 23 | Periodic, automatic, and finite-state supports/carries | Eventual periodic divisor multiplicity forces finite support; finite-state self-similarity either collapses to an easy irrational class or retains an uncontrolled boundary mode. |
| 24 | Cross-target sparse clocks and zero-buffer searches | $1/21$, $90/511$, $1/465$, and many product targets expose the same seam.  Target changes improve margins but do not remove full-ancestry reachability. |
| 25 | Higher-source corridors: $1/651$ and the totient $4/9$ reset | Exact finite endpoint families are exceptionally large.  For $4/9$, two bits give a complete base-four reset and the exact cylinder audit reaches two million; an all-depth midpoint-seam exclusion is still missing. |

## What all serious surviving routes now share

Let $b_d\in\{0,1\}$ and

\[
  f_b(n)=\sum_{d\mid n}b_d.
\]

Every quotient/carry construction has the lossless transport law

\[
  Q_n=2Q_{n-1}+t_n-f_b(n).                      \tag{2}
\]

The dyadic/cylinder side asks whether a short suffix interval crosses a moving
binary boundary.  The arithmetic side asks whether the proper-divisor pulses
in $f_b(n)$ place the carry in exactly that interval.  These are not two
obstructions.  They are the two terms of (2).

The corpus contains exact countermodels to every proposed theorem that uses
only:

- a bounded window of divisor loads;
- a fixed collection of $2$-adic or primitive-prime coordinates;
- scalar residual mass, denominator height, support count, or phase;
- local ownership without the complete rank-one history; or
- an eventually periodic/finite-state carry rule.

The countermodels can reproduce an arbitrarily long dangerous suffix together
with all local divisor congruences.  They fail only at reachability from the
actual initial state and its complete Boolean ancestry.

## The exact missing mathematical piece

The common missing theorem is a **global ancestry--boundary exclusion**:

> A divisor-forced Boolean carry trajectory that starts at the exact rational
> source state cannot place its full binary suffix on the fatal dyadic seam
> while satisfying the complete earlier divisor ancestry.

Equivalent concrete sockets are:

1. **$1/465$:** exclude the globally reachable saturated final gate
   $\rho_L=2^L$, $D_L=-1$, or prove the fixed-horizon comparator at every
   horizon.
2. **$4/9$:** exclude the first midpoint crossing of the globally reachable
   even cylinder.  This would immediately give a rational infinite Boolean
   Mersenne subseries and disprove the problem.
3. **Dense-support irrationality:** prove that the full Boolean divisor forcing
   in (2) cannot support a nonzero homogeneous boundary mode when (1) holds.

These are three consumers of the same missing law.  A theorem about average
divisor density, fixed-window anti-concentration, or one more scalar potential
cannot supply it: the repository contains exact counterexamples to each such
projection.

## Honest conclusion

The project has solved a substantial special case and eliminated many broad
classes of proof.  It has not solved Erdős 257.  The remaining obstruction is
not twenty-five unrelated gaps; it is one global reachability problem coupling
binary suffix capacity, divisor/LCM pulses, and the boundary condition at
infinity.

## Research-allocation guard

The anti-Kakeya inequality is a route exclusion, not a new producer.  The
checked strict tail dominance

\[
  \frac1{2^n-1}>\sum_{k>n}\frac1{2^k-1}
\]

prevents the usual complete-interval and generic greedy-convergence arguments
from applying.  Consequently, another appeal to ordinary achievement-set
convergence cannot close the half-target route.

The kicked-doubling coordinate added on 2026-08-21 is also exactly the Bellman
coordinate already counted in family 14.  Indeed, put

\[
 z_d=\frac1{2^d-1},\qquad
 y_d=\frac{\kappa_d}{1+z_d}.
\]

From

\[
 \kappa_{d+1}=2\kappa_d-b_d(2+2z_d),
 \qquad b_d={\bf1}_{\kappa_d\geq1+z_d},
 \qquad z_{d+1}=\frac{z_d}{2+z_d},
\]

one obtains

\[
 y_{d+1}=(2+z_d)(y_d-b_d),
 \qquad b_d={\bf1}_{y_d\geq1},
\]

which is the Bellman map in `SixStepBellmanFatCantorNoGo.md`.  Thus the kicked
fixed-point description, half-row closure, freeze exclusion, core transport,
strip trapping, post-take pulses, and the skip budget are one mechanism family,
not independent evidence that a proof is near.

Future attacks should not be admitted as new routes merely because they change
the rational target, normalize the same residual differently, extend a finite
audit, or prove another condition equivalent to membership.  A reopened route
must supply at least one genuinely new producer: a one-way theorem from the
actual initial state that uses the complete Boolean/divisor ancestry (or proves
why a smaller state is sufficient) and forces a cofinal return, excludes the
boundary mode, or constructs an admissible infinite support.  Finite checks are
consistency and falsification evidence only.  This guard is intended to prevent
further allocation to coordinate changes around the same unresolved boundary
statement.

## Post-closeout reconciliation: 2026-08-22

The source-current worktree and the post-closeout tracked audit contain more
than two dozen additional attack and representation notes, one attempted
private Lean module, and a strengthened private `4/9` module.  They do not
create a new mechanism family.  Classified by retained state and success event,
every item belongs to one of the existing families.

| Delta cluster | Existing families | Authority and mathematical effect | Allocation decision |
|---|---:|---|---|
| Actual-prefix boundary and forced-doubling charge | 11, 12 | Exact deductions remove an unnecessary eventual-alignment premise from one `1/21` dictionary and show that a hypothetical final skip is already at quotient supercapacity.  The proposed forced-block lower bound is then proved to be exactly the missing boundary conclusion in another coordinate. | Retain the dictionary; retire the lower-bound proposal as tautological. |
| One-step `1/21` borrow propagation | 11 | The worktree-only module `TwentyOneOneStepPropagation.lean` attempts to prove the exact one-bit cocycle, safe-prefix borrow payment, a failed-borrow overshoot bound, and a cofinal-failure membership consumer.  The focused build on 2026-08-22 exits `1` with multiple proof errors, and the printed declarations contain `sorryAx`.  None of these attempted declarations is presently proof authority. | Keep as an unverified proposed interface only.  Repair and rebuild it before assimilation; do not count either the declarations or the unsupplied cofinal-failure hypothesis as progress. |
| Delayed-density reservoir and variational principle | 11, 12 | Exact deductions show that real greedy lexicographically maximizes the delayed reservoir, so the exchange step is complete.  The proposed comparator-existence statement is equivalent to the desired sign.  The stronger source-sensitive all-depth reservoir inequality remains sufficient and is not a one-rank restatement. | Retire generic exchange/comparator searches; reopen only for an absolute bound using the actual period-six source, divisor feedback, and greedy decisions simultaneously. |
| Shifted quotient comparator | 11, 12 | An ordinary all-depth deduction gives horizon monotonicity of the shifted quotient-greedy words.  The terminal remainder still carries the surviving homogeneous mode, and generic coin estimates admit exponentially large cross-target remainders. | Retain monotonicity; do not count the limiting zero-gap assertion as a new route. |
| Stable boundary, complementarity, adjoint, energy, and least action | 2, 8, 12 | Exact identities and explicit Boolean/greedy countermodels show that positivity, Boolean Möbius ancestry, local complementarity, linear adjoints, quadratic endpoint energy, and periodic or multiplicative test functions do not kill positive homogeneous flux. | Retire their scalar and local forms.  Any revival must include a source-sensitive global inequality absent from these coordinates. |
| Fixed-point and kicked-doubling descriptions | 9, 14 | The fixed-point map fails only at exact dyadic seams, while the kicked coordinate is conjugate to the existing Bellman map. | Deduplicate completely; no further allocation for coordinate changes or generic contraction. |
| Möbius-sign and multiplicity Booleanisation | 21, 22 | Injectivity of normalized Mersenne coding rules out the proposed equality between distinct positive and negative Möbius supports.  Exact local multiplicity carries immediately expose the live `1/21` defect and do not preserve Booleanity. | Retire the sign-subset construction and every local carry that silently drops its defect. |
| Dense-support shifted atoms and LCM clocks | 1--7 | The new audits disprove universal pairwise-coprime, sunflower, small-reset, pulse-divisibility, and unbounded-carry dichotomies.  Reciprocal divergence supplies mass and common multiples supply pulses, but no theorem controls pulse phase and carry scale together. | Preserve as the main orthogonal positive route, with phase--scale coupling as the required new content. |
| Concrete `4/9` diagonal | 25 | Source-current private Lean work now closes every skipped row once `2*s<=3*rho` holds and reduces global nonnegativity to the selected-landing producer `b_d=1 -> 2*s_d<=3*rho_d`.  A second checked reduction shows that the sharper socket `b_d=1 -> d<=rho_d` is sufficient because `s_d<=d`.  Exact audits remain nonnegative through ten million ranks, and the targeted selected-margin/rank audit has zero violations through rank 200,000. | Retain the selected-landing socket as the exact residual and the selected-rank socket as a stronger sufficient target; all computations remain finite evidence.  Prove a reachable selected-boundary anti-concentration theorem rather than extending an undirected horizon. |
| Rational residual numerator residues | 7, 17, 23 | For a selected period `k` and primitive prime `p`, the exact coordinate `(a_N mod p)^k` identifies the numerator's coset modulo the dyadic subgroup `<2>`.  On five source-reachable rational prefixes, all `117/117` nontrivial channels escape their initial coset; one channel visits `74` distinct cosets.  This is bounded computational evidence, not a cross-prime theorem. | Retire single-prime dyadic-coset/projective trapping.  Reopen the numerator route only with simultaneous cross-prime compatibility or a source-specific boundary condition. |
| Binary, arithmetic, and cross-representation corpus maps | all | These maps distinguish genuinely lossy projections from lossless full states and show that information loss is common but not the entire obstruction. | Use as navigation and adversarial review surfaces, not as proof claims. |

The mechanism-family count remains twenty-five.  The important negative update
is that a generic global exchange principle is not a free remaining option:
every tested version either admits a positive-flux countermodel or becomes
equivalent to the desired boundary sign.  Worktree theorem text is not counted
until the exact module builds without `sorryAx`.

The former ranked “proof-producing throats” section was removed on 2026-08-22.
It had turned a dated assessment into a persistent focus projection.  That was
the wrong authority boundary: route and target rankings are experimental output,
not the programme objective.  The negative results above remain useful as
falsifiers, but no entry or working-memory surface may inherit a next route from
this document.
